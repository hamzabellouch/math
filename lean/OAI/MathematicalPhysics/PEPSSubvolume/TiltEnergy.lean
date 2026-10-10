import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.ContourEnergy
import OAI.MathematicalPhysics.PEPSSubvolume.GroundTilt

namespace OAI

/-! Summed physical Schmidt-tilt energy estimates. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open scoped ComplexOrder BigOperators Matrix.Norms.L2Operator
open Matrix
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.GroundTilt
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.PhysicalModular PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.TiltScalar
open PolynomialPEPS.Subvolume.BipartiteEnergy PolynomialPEPS.Subvolume.ModularMatrix PolynomialPEPS.Subvolume.CrossingIdentity
variable {L q : ℕ}

lemma tilt_product_error (X : Finset (Vertex L)) (ψ : State L q)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (hp : ∀ i, 0≤p i)
    (hρ : reducedDensity ψ X=spectralHom U (fun i => (p i:ℂ)))
    (u : ℝ) (hu : |u|≤1/4)
    (A : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B : Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ) :
    let R := liftLocal X (tiltFilter X U p u)
    let D := liftLocal X (inverseOnSupport U (fun i => (p i)^(-u/2)))
    let v := tilt X U p u ψ
    ‖inner ℂ v (asMap (modularError R D (tensorAcross X A B)) v)‖ ≤
      32*u^2*‖v‖^2*(‖A‖*‖B‖) := by
  classical
  have hu1 : u<1 := by have h := (abs_le.mp hu).2; linarith
  let w := fun i => (p i)^(1-u)
  let θ := -u/(2*(1-u))
  have hpow : weightPower w θ = diagonal (fun i => (((p i)^(-u/2):ℝ):ℂ)) := by
    ext i j
    simp only [weightPower,diagonal_apply,w,θ]
    split_ifs <;> simp only [tilt_recovery _ u (hp _) hu1]
  have hinv : weightInverse w θ = diagonal (fun i => ((((p i)^(-u/2))⁻¹:ℝ):ℂ)) := by
    ext i j
    simp only [weightInverse,diagonal_apply,w,θ]
    split_ifs <;> simp only [tilt_recovery _ u (hp _) hu1,Complex.ofReal_inv]
  have hd : tensorAcross X (distortionInBasis U A w θ) B =
      modularError (liftLocal X (tiltFilter X U p u))
        (liftLocal X (inverseOnSupport U (fun i => (p i)^(-u/2)))) (tensorAcross X A B) := by
    rw [distortionInBasis_eq,hpow,hinv]
    unfold modularError
    rw [tensorAcross_sub,tensorAcross_smul,tensorAcross_add]
    simp only [tensorAcross_sandwich,tiltFilter,inverseOnSupport,spectralHom_apply,
      Unitary.conjStarAlgAut_apply,Complex.ofReal_inv]
  dsimp only
  rw [← hd,inner_tensorAcross]
  have hwρ : coefficientMatrix (tilt X U p u ψ) X * (coefficientMatrix (tilt X U p u ψ) X).conjTranspose =
      ((1:ℝ)^2:ℂ) • ((U:Matrix _ _ ℂ)*diagonal (fun i => (w i:ℂ))*(U:Matrix _ _ ℂ).conjTranspose) := by
    simpa only [one_pow,Complex.ofReal_one,one_smul,reducedDensity,spectralHom_apply,w,Matrix.star_eq_conjTranspose] using tilt_density X ψ U p hp hρ u hu1
  have hh := basis_product_error_le (coefficientMatrix (tilt X U p u ψ) X) U w
    (fun i => Real.rpow_nonneg (hp i) _) 1 (by norm_num) hwρ A B θ (exponent_small u hu).1
  have hz := tilt_norm_sq X ψ U p hp hρ u hu1
  change ‖tilt X U p u ψ‖^2=∑ i,w i at hz
  simp only [one_pow,mul_one,← hz] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (exponent_small u hu).2 (by norm_num))
      (sq_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

lemma tilt_sum_error {ι : Type*} [Fintype ι] (X : Finset (Vertex L)) (ψ : State L q)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (hp : ∀ i, 0≤p i)
    (hρ : reducedDensity ψ X=spectralHom U (fun i => (p i:ℂ)))
    (u : ℝ) (hu : |u|≤1/4)
    (A : ι → Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)
    (B : ι → Matrix (RegionConfiguration q Xᶜ) (RegionConfiguration q Xᶜ) ℂ) :
    let R := liftLocal X (tiltFilter X U p u)
    let D := liftLocal X (inverseOnSupport U (fun i => (p i)^(-u/2)))
    let v := tilt X U p u ψ
    ‖inner ℂ v (asMap (modularError R D (∑ i,tensorAcross X (A i) (B i))) v)‖ ≤
      32*u^2*‖v‖^2*(∑ i,‖A i‖*‖B i‖) := by
  dsimp only
  rw [modularError_sum]
  simp only [asMap,map_sum,_root_.sum_apply,inner_sum]
  calc
    _ ≤ ∑ i, ‖inner ℂ (tilt X U p u ψ) (asMap
      (modularError (liftLocal X (tiltFilter X U p u))
        (liftLocal X (inverseOnSupport U (fun i => (p i)^(-u/2)))) (tensorAcross X (A i) (B i)))
      (tilt X U p u ψ))‖ := norm_sum_le _ _
    _ ≤ ∑ i,32*u^2*‖tilt X U p u ψ‖^2*(‖A i‖*‖B i‖) := by
      apply Finset.sum_le_sum
      intro i hi
      exact tilt_product_error X ψ U p hp hρ u hu (A i) (B i)
    _ = _ := (Finset.mul_sum ..).symm

end PolynomialPEPS.Subvolume.GroundTilt

namespace PolynomialPEPS.Subvolume.GroundTilt
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.CrossingIdentity
open PolynomialPEPS.Subvolume.PhysicalModular PolynomialPEPS.Subvolume.ContourEnergy PolynomialPEPS.Subvolume.OptimizerNeutral
variable {L q : ℕ}

lemma asMap_mul_apply (A B : Operator L q) (ψ : State L q) :
    asMap (A*B) ψ=asMap A (asMap B ψ) := by
  simp only [asMap,map_mul,mul_apply_eq_comp]

lemma tilt_balance (X : Finset (Vertex L))
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (hp : ∀ i, 0≤p i) (u : ℝ) (hu : u<1) :
    inverseOnSupport U (fun i => (p i)^(-u/2)) *
      spectralHom U (fun i => (((p i)^(1-u):ℝ):ℂ)) * tiltFilter X U p u =
        spectralHom U (fun i => (((p i)^(1-u):ℝ):ℂ)) := by
  unfold inverseOnSupport tiltFilter
  rw [← map_mul,← map_mul]
  congr 1
  funext i
  simp only [Pi.mul_apply,← Complex.ofReal_inv,← Complex.ofReal_mul]
  congr 1
  by_cases hi : p i=0
  · simp [hi,Real.zero_rpow (show 1-u≠0 by linarith)]
  · have hn := (Real.rpow_pos_of_pos (lt_of_le_of_ne (hp i) (Ne.symm hi)) (-u/2)).ne'
    calc
      _ = (((p i)^(-u/2))⁻¹ * (p i)^(-u/2))*(p i)^(1-u) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hn,one_mul]

lemma tilt_inside_identity (X : Finset (Vertex L)) (ψ : State L q)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (hp : ∀ i, 0≤p i)
    (hρ : reducedDensity ψ X=spectralHom U (fun i => (p i:ℂ)))
    (u : ℝ) (hu : u<1) (H : Operator L q) (hH : SupportedOn H X) :
    let R := liftLocal X (tiltFilter X U p u)
    let v := tilt X U p u ψ
    inner ℂ v (asMap H v)=inner ℂ v (asMap (R*H) ψ) := by
  obtain ⟨A,rfl⟩ := hH
  let R := liftLocal X (tiltFilter X U p u)
  let D := liftLocal X (inverseOnSupport U (fun i => (p i)^(-u/2)))
  let v := tilt X U p u ψ
  change inner ℂ v (asMap (liftLocal X A) v)=inner ℂ v (asMap (R*liftLocal X A) ψ)
  have hd : asMap D v=ψ := untilt X ψ U p hp hρ u
  rw [← hd,← asMap_mul_apply]
  change inner ℂ v (asMap (liftLocal X A) v)=
    inner ℂ v (asMap ((liftLocal X (tiltFilter X U p u)*liftLocal X A)*
      liftLocal X (inverseOnSupport U (fun i => (p i)^(-u/2)))) v)
  rw [← liftLocal_mul,← liftLocal_mul,inner_liftLocal_trace,inner_liftLocal_trace]
  dsimp only [v]
  rw [tilt_density X ψ U p hp hρ u hu]
  rw [mul_assoc (tiltFilter X U p u * A),
    Matrix.trace_mul_cycle (tiltFilter X U p u) A]
  rw [tilt_balance X U p hp u hu,Matrix.trace_mul_comm]

lemma tilt_outside_identity (X S : Finset (Vertex L)) (hSX : Disjoint S X)
    (ψ : State L q)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (u : ℝ)
    (H : Operator L q) (hH : SupportedOn H S) :
    let R := liftLocal X (tiltFilter X U p u)
    let v := tilt X U p u ψ
    inner ℂ v (asMap H v)=inner ℂ v (asMap (R*H) ψ) := by
  have hc := commute_of_disjoint hSX H (liftLocal X (tiltFilter X U p u)) hH
    ⟨tiltFilter X U p u,rfl⟩
  dsimp only
  rw [hc.eq.symm,asMap_mul_apply]
  rfl

lemma tilt_neutral_identity (X S : Finset (Vertex L)) (hn : ¬Splits S X)
    (ψ : State L q)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (hp : ∀ i, 0≤p i)
    (hρ : reducedDensity ψ X=spectralHom U (fun i => (p i:ℂ)))
    (u : ℝ) (hu : u<1) (H : Operator L q) (hH : SupportedOn H S) :
    let R := liftLocal X (tiltFilter X U p u)
    let v := tilt X U p u ψ
    inner ℂ v (asMap H v)=inner ℂ v (asMap (R*H) ψ) := by
  rcases not_splits S X hn with hs|hs
  · exact tilt_inside_identity X ψ U p hp hρ u hu H (SupportedOn.mono hs hH)
  · exact tilt_outside_identity X S hs ψ U p u H hH

lemma tilt_modular_transition (X : Finset (Vertex L)) (ψ : State L q)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (hp : ∀ i, 0≤p i)
    (hρ : reducedDensity ψ X=spectralHom U (fun i => (p i:ℂ)))
    (u : ℝ) (H : Operator L q) (hH : H.IsHermitian) :
    let R := liftLocal X (tiltFilter X U p u)
    let D := liftLocal X (inverseOnSupport U (fun i => (p i)^(-u/2)))
    let v := tilt X U p u ψ
    (inner ℂ v (asMap (modularError R D H) v)).re =
      (inner ℂ v (asMap (R*H) ψ)).re-(inner ℂ v (asMap H v)).re := by
  let R := liftLocal X (tiltFilter X U p u)
  let D := liftLocal X (inverseOnSupport U (fun i => (p i)^(-u/2)))
  let v := tilt X U p u ψ
  have hR : R.IsHermitian := spectral_lift_hermitian X U _
  have hD : D.IsHermitian := by
    have hh := spectral_lift_hermitian (q := q) X U (fun i => ((p i)^(-u/2))⁻¹)
    simpa only [D,inverseOnSupport,Complex.ofReal_inv] using hh
  have hi := modularError_real R D H hR hD hH v
  dsimp only
  change (inner ℂ v (asMap (modularError R D H) v)).re=_
  rw [hi,asMap_mul_apply,untilt X ψ U p hp hρ u]

end PolynomialPEPS.Subvolume.GroundTilt

namespace PolynomialPEPS.Subvolume.GroundTilt
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.CrossingIdentity
open PolynomialPEPS.Subvolume.PhysicalModular PolynomialPEPS.Subvolume.ContourEnergy PolynomialPEPS.Subvolume.OptimizerNeutral
variable {L q : ℕ}

lemma tilt_crossing_edge (hq : 0<q) (X : Finset (Vertex L)) (ψ : State L q)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (hp : ∀ i, 0≤p i)
    (hρ : reducedDensity ψ X=spectralHom U (fun i => (p i:ℂ)))
    (u : ℝ) (hu : |u|≤1/4) (e : Edge L) (he : Splits (EdgeSites e) X)
    (H : Operator L q) (hH : H.IsHermitian) (hHs : SupportedOn H (EdgeSites e)) :
    let R := liftLocal X (tiltFilter X U p u)
    let v := tilt X U p u ψ
    |(inner ℂ v (asMap H v)).re-(inner ℂ v (asMap (R*H) ψ)).re| ≤
      32*u^2*‖v‖^2*((q:ℝ)^2*opNorm H) := by
  let R := liftLocal X (tiltFilter X U p u)
  let D := liftLocal X (inverseOnSupport U (fun i => (p i)^(-u/2)))
  let v := tilt X U p u ψ
  have hb (z w : Vertex L) (hs : EdgeSites e={z,w}) (hz : z∈X) (hw : w∉X) :
      |(inner ℂ v (asMap H v)).re-(inner ℂ v (asMap (R*H) ψ)).re| ≤
        32*u^2*‖v‖^2*((q:ℝ)^2*opNorm H) := by
    obtain ⟨A,B,hAB,hcost⟩ := edge_decomposition hq e X z w hs hz hw H hHs
    have hm := tilt_sum_error X ψ U p hp hρ u hu A B
    dsimp only at hm
    rw [← hAB] at hm
    have heq := tilt_modular_transition X ψ U p hp hρ u H hH
    change (inner ℂ v (asMap (modularError R D H) v)).re=
      (inner ℂ v (asMap (R*H) ψ)).re-(inner ℂ v (asMap H v)).re at heq
    rw [abs_sub_comm,← heq]
    exact (Complex.abs_re_le_norm _).trans
      (hm.trans (mul_le_mul_of_nonneg_left hcost (by positivity)))
  rcases (edge_splits_iff e X).mp he with h|h
  · exact hb e.val.1 e.val.2 rfl h.1 h.2
  · exact hb e.val.2 e.val.1 (by simp [EdgeSites,Finset.pair_comm]) h.2 h.1

theorem tilt_excitation_bound (hq : 0<q) (X : Finset (Vertex L)) (Ω : State L q)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (hp : ∀ i, 0≤p i)
    (hρ : reducedDensity Ω X=spectralHom U (fun i => (p i:ℂ)))
    (u : ℝ) (hu : |u|≤1/4)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q)
    (hvs : ∀ v, SupportedOn (hv v) {v})
    (hes : ∀ e, SupportedOn (he e) (EdgeSites e)) (heH : ∀ e, (he e).IsHermitian)
    (J E₀ : ℝ) (_hJ : 0≤J) (heJ : ∀ e, opNorm (he e)≤J)
    (hg : asMap (Hamiltonian hv he) Ω=(E₀:ℂ) • Ω) :
    let v := tilt X U p u Ω
    (inner ℂ v (asMap (Hamiltonian hv he) v)).re-E₀*‖v‖^2 ≤
      (32*(q:ℝ)^2*J*(boundaryCard X:ℝ)*u^2)*‖v‖^2 := by
  classical
  let R := liftLocal X (tiltFilter X U p u)
  let v := tilt X U p u Ω
  let h : Vertex L ⊕ Edge L → Operator L q := Sum.elim hv he
  let ε : Vertex L ⊕ Edge L → ℝ := Sum.elim (fun _ => 0) (fun e =>
    if Splits (EdgeSites e) X then 32*u^2*‖v‖^2*((q:ℝ)^2*J) else 0)
  have hh : ∑ i,h i=Hamiltonian hv he := by simp [h,Hamiltonian,Fintype.sum_sum_type]
  have hu1 : u<1 := by have h := (abs_le.mp hu).2; linarith
  have herr (i : Vertex L ⊕ Edge L) :
      |(inner ℂ v (asMap (h i) v)).re-(inner ℂ v (asMap (R*h i) Ω)).re| ≤ ε i := by
    cases i with
    | inl z =>
      have hz := tilt_neutral_identity X {z} (single_not_splits z X) Ω U p hp hρ u hu1 (hv z) (hvs z)
      change inner ℂ v (asMap (hv z) v)=inner ℂ v (asMap (R*hv z) Ω) at hz
      change |(inner ℂ v (asMap (hv z) v)).re-(inner ℂ v (asMap (R*hv z) Ω)).re|≤0
      rw [hz,sub_self,abs_zero]
    | inr e =>
      change |(inner ℂ v (asMap (he e) v)).re-(inner ℂ v (asMap (R*he e) Ω)).re| ≤
        if Splits (EdgeSites e) X then _ else 0
      split_ifs with hc
      · have hb := tilt_crossing_edge hq X Ω U p hp hρ u hu e hc (he e) (heH e) (hes e)
        exact hb.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (heJ e) (sq_nonneg _)) (by positivity))
      · have hz := tilt_neutral_identity X (EdgeSites e) hc Ω U p hp hρ u hu1 (he e) (hes e)
        change inner ℂ v (asMap (he e) v)=inner ℂ v (asMap (R*he e) Ω) at hz
        rw [hz,sub_self,abs_zero]
  have hb := excitation_of_transition_errors h Ω E₀ (by simpa only [hh] using hg) R ε herr
  rw [hh] at hb
  have hsum : ∑ i,ε i=(32*(q:ℝ)^2*J*(boundaryCard X:ℝ)*u^2)*‖v‖^2 := by
    simp only [ε,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Finset.sum_const_zero,zero_add]
    have heq (e : Edge L) :
        (if Splits (EdgeSites e) X then 32*u^2*‖v‖^2*((q:ℝ)^2*J) else 0) =
          (32*u^2*‖v‖^2*((q:ℝ)^2*J))*(if Splits (EdgeSites e) X then (1:ℝ) else 0) := by
      split_ifs <;> simp
    simp only [heq,← Finset.mul_sum,boundary_sum]
    ring
  exact hb.trans_eq hsum

end PolynomialPEPS.Subvolume.GroundTilt

end

end OAI
