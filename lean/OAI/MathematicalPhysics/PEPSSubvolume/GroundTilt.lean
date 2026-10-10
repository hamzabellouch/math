import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.PhysicalModular

namespace OAI

/-! Ground-state Schmidt tilts and scalar zero-weight identities. -/

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
open Matrix PolynomialPEPS.Subvolume.PhysicalModular PolynomialPEPS.Subvolume.SpectralCurve
variable {L q : ℕ}

lemma coefficient_lift (X : Finset (Vertex L))
    (A : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ) (ψ : State L q) :
    coefficientMatrix (asMap (liftLocal X A) ψ) X = A * coefficientMatrix ψ X := by
  classical
  ext x z
  rw [← tensorAcross_one X A]
  simp [coefficientMatrix,Matrix.mul_apply]

lemma reducedDensity_lift (X : Finset (Vertex L))
    (A : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ) (ψ : State L q) :
    reducedDensity (asMap (liftLocal X A) ψ) X = A * reducedDensity ψ X * A.conjTranspose := by
  unfold reducedDensity
  rw [coefficient_lift,Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

lemma coefficient_injective (X : Finset (Vertex L)) :
    Function.Injective (fun ψ : State L q => coefficientMatrix ψ X) := by
  intro ψ φ h
  ext x
  obtain ⟨⟨y,z⟩,rfl⟩ := (joinEquiv (q := q) X).surjective x
  exact congrFun (congrFun h y) z

lemma lift_action_eq_of_mul_density (X : Finset (Vertex L))
    (A B : Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ) (ψ : State L q)
    (h : A*reducedDensity ψ X = B*reducedDensity ψ X) :
    asMap (liftLocal X A) ψ = asMap (liftLocal X B) ψ := by
  apply coefficient_injective X
  dsimp only
  rw [coefficient_lift,coefficient_lift]
  apply sub_eq_zero.mp
  rw [← Matrix.sub_mul]
  apply Matrix.self_mul_conjTranspose_eq_zero.mp
  rw [Matrix.conjTranspose_mul]
  have hz : (A-B)*reducedDensity ψ X=0 := by rw [Matrix.sub_mul,h,sub_self]
  change (A-B)*coefficientMatrix ψ X*((coefficientMatrix ψ X).conjTranspose*(A-B).conjTranspose)=0
  rw [← Matrix.mul_assoc,Matrix.mul_assoc (A-B)]
  change ((A-B)*reducedDensity ψ X)*(A-B).conjTranspose=0
  rw [hz,zero_mul]

lemma spectral_action_eq (X : Finset (Vertex L)) (ψ : State L q)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ)
    (hρ : reducedDensity ψ X = spectralHom U (fun i => (p i:ℂ)))
    (f g : RegionConfiguration q X → ℂ)
    (hfg : ∀ i, p i ≠ 0 → f i=g i) :
    asMap (liftLocal X (spectralHom U f)) ψ = asMap (liftLocal X (spectralHom U g)) ψ := by
  apply lift_action_eq_of_mul_density
  rw [hρ,← map_mul,← map_mul]
  apply congrArg (spectralHom U)
  funext i
  by_cases hi : p i=0
  · simp [hi]
  · simp [hfg i hi]

lemma norm_sq_density_trace (X : Finset (Vertex L)) (ψ : State L q) :
    (reducedDensity ψ X).trace = (‖ψ‖^2:ℂ) := by
  have h := inner_liftLocal_trace X (1:Matrix (RegionConfiguration q X) _ ℂ) ψ
  rw [liftLocal_one] at h
  have hid : asMap (L := L) (q := q) 1 ψ=ψ := by
    change Matrix.toEuclideanCLM (𝕜 := ℂ) 1 ψ=ψ
    rw [map_one]
    rfl
  rw [hid,one_mul,inner_self_eq_norm_sq_to_K] at h
  exact h.symm

lemma trace_spectral (X : Finset (Vertex L))
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (f : RegionConfiguration q X → ℂ) : (spectralHom U f).trace = ∑ i, f i := by
  rw [spectralHom_apply,Matrix.trace_mul_cycle]
  simp

lemma spectral_lift_hermitian (X : Finset (Vertex L))
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (f : RegionConfiguration q X → ℝ) :
    (liftLocal X (spectralHom U (fun i => (f i:ℂ)))).IsHermitian := by
  have hh : (spectralHom U (fun i => (f i:ℂ))).IsHermitian := by
    have hf : IsSelfAdjoint (fun i => (f i:ℂ)) := by
      rw [isSelfAdjoint_iff]
      ext i
      simp
    exact (hf.map (spectralHom U)).isHermitian
  exact hh.isSelfAdjoint.map (localLiftHom X)

end PolynomialPEPS.Subvolume.GroundTilt

namespace PolynomialPEPS.Subvolume.TiltScalar

lemma tilted_weight (p u : ℝ) (hp : 0≤p) (hu : u<1) :
    (p^(-u/2))^2*p = p^(1-u) := by
  by_cases h : p=0
  · subst p
    rw [mul_zero,Real.zero_rpow (by linarith : 1-u ≠ 0)]
  · have hp' : 0<p := lt_of_le_of_ne hp (Ne.symm h)
    rw [← Real.rpow_mul_natCast hp]
    calc
      _ = p^(-u/2*(2:ℝ))*p^(1:ℝ) := by rw [Real.rpow_one]; norm_num
      _ = p^(1-u) := by
        rw [← Real.rpow_add hp']
        congr 1
        ring

lemma tilt_exponent (u : ℝ) (hu : u<1) : (1-u)*(-u/(2*(1-u)))=-u/2 := by
  field_simp [ne_of_gt (show 0<1-u by linarith)]

lemma tilt_recovery (p u : ℝ) (hp : 0≤p) (hu : u<1) :
    (p^(1-u))^(-u/(2*(1-u)))=p^(-u/2) := by
  rw [← Real.rpow_mul hp,tilt_exponent u hu]

lemma tilt_inverse_recovery (p u : ℝ) (hp : 0<p) :
    (p^(-u/2))⁻¹*p^(-u/2)=1 := inv_mul_cancel₀ (Real.rpow_pos_of_pos hp _).ne'

lemma tilt_pairing (p u : ℝ) (hp : 0≤p) (hu : u<1) :
    p^(-u/2)*p = p^(1-u/2) := by
  by_cases h : p=0
  · subst p
    rw [mul_zero,Real.zero_rpow (by linarith : 1-u/2 ≠ 0)]
  · have hp' : 0<p := lt_of_le_of_ne hp (Ne.symm h)
    nth_rw 2 [← Real.rpow_one p]
    rw [← Real.rpow_add hp']
    congr 1
    ring

lemma exponent_small (u : ℝ) (hu : |u|≤1/4) :
    |-u/(2*(1-u))|≤1/4 ∧ (-u/(2*(1-u)))^2≤u^2 := by
  have hu' := abs_le.mp hu
  have hd : 0<2*(1-u) := by linarith
  rw [abs_div,abs_neg,abs_of_pos hd]
  constructor
  · apply (div_le_iff₀ hd).mpr
    have hab : |u|≤(1-u)/2 := by
      apply abs_le.mpr
      constructor <;> linarith
    nlinarith
  · have hden : 1≤2*(1-u) := by linarith
    have hfrac : |u|/(2*(1-u))≤|u| := (div_le_iff₀ hd).mpr (by nlinarith [abs_nonneg u])
    have h := sq_le_sq₀ (show 0≤|u|/(2*(1-u)) by positivity) (abs_nonneg u) |>.mpr hfrac
    simpa [div_pow,sq_abs] using h

end PolynomialPEPS.Subvolume.TiltScalar

namespace PolynomialPEPS.Subvolume.GroundTilt
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix PolynomialPEPS.Subvolume.PhysicalModular PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.TiltScalar
variable {L q : ℕ}

lemma spectral_real_star (X : Finset (Vertex L))
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (f : RegionConfiguration q X → ℝ) :
    (spectralHom U (fun i => (f i:ℂ))).conjTranspose=spectralHom U (fun i => (f i:ℂ)) := by
  have hf : IsSelfAdjoint (fun i => (f i:ℂ)) := by
    rw [isSelfAdjoint_iff]
    ext i
    simp
  exact (hf.map (spectralHom U)).isHermitian

def tiltFilter (X : Finset (Vertex L))
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (u : ℝ) :
    Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ :=
  spectralHom U (fun i => (((p i)^(-u/2):ℝ):ℂ))

def tilt (X : Finset (Vertex L))
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (u : ℝ) (ψ : State L q) : State L q :=
  asMap (liftLocal X (tiltFilter X U p u)) ψ

lemma tilt_density (X : Finset (Vertex L)) (ψ : State L q)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (hp : ∀ i, 0≤p i)
    (hρ : reducedDensity ψ X=spectralHom U (fun i => (p i:ℂ)))
    (u : ℝ) (hu : u<1) :
    reducedDensity (tilt X U p u ψ) X=spectralHom U (fun i => (((p i)^(1-u):ℝ):ℂ)) := by
  unfold tilt tiltFilter
  rw [reducedDensity_lift,hρ,spectral_real_star,← map_mul,← map_mul]
  apply congrArg (spectralHom U)
  funext i
  simp only [Pi.mul_apply]
  have h := tilted_weight (p i) u (hp i) hu
  have hc := congrArg (fun x : ℝ => (x:ℂ)) h
  push_cast at hc
  calc
    _ = ((((p i)^(-u/2):ℝ):ℂ))^2*(p i:ℂ) := by ring
    _ = _ := hc

lemma tilt_norm_sq (X : Finset (Vertex L)) (ψ : State L q)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (hp : ∀ i, 0≤p i)
    (hρ : reducedDensity ψ X=spectralHom U (fun i => (p i:ℂ)))
    (u : ℝ) (hu : u<1) :
    ‖tilt X U p u ψ‖^2 = ∑ i, (p i)^(1-u) := by
  have h := norm_sq_density_trace X (tilt X U p u ψ)
  rw [tilt_density X ψ U p hp hρ u hu,trace_spectral] at h
  exact Complex.ofReal_injective (by simpa only [Complex.ofReal_sum,Complex.ofReal_pow] using h.symm)

lemma tilt_pairing_eq (X : Finset (Vertex L)) (ψ : State L q)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (hp : ∀ i, 0≤p i)
    (hρ : reducedDensity ψ X=spectralHom U (fun i => (p i:ℂ)))
    (u : ℝ) (hu : u<1) :
    inner ℂ ψ (tilt X U p u ψ) = ((∑ i, (p i)^(1-u/2):ℝ):ℂ) := by
  rw [tilt,inner_liftLocal_trace,tiltFilter,hρ,← map_mul,trace_spectral,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.mul_apply]
  exact (Complex.ofReal_mul _ _).symm.trans (congrArg (fun x : ℝ => (x:ℂ))
    (tilt_pairing (p i) u (hp i) hu))

lemma untilt (X : Finset (Vertex L)) (ψ : State L q)
    (U : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ))
    (p : RegionConfiguration q X → ℝ) (hp : ∀ i, 0≤p i)
    (hρ : reducedDensity ψ X=spectralHom U (fun i => (p i:ℂ))) (u : ℝ) :
    asMap (liftLocal X (CrossingIdentity.inverseOnSupport U (fun i => (p i)^(-u/2))))
      (tilt X U p u ψ) = ψ := by
  let g := fun i => (((p i)^(-u/2):ℝ):ℂ)
  have hmul : (liftLocal X (CrossingIdentity.inverseOnSupport U (fun i => (p i)^(-u/2)))) *
      liftLocal X (tiltFilter X U p u) = liftLocal X (spectralHom U (fun i => (g i)⁻¹*g i)) := by
    rw [← liftLocal_mul]
    unfold CrossingIdentity.inverseOnSupport tiltFilter
    rw [← map_mul]
    rfl
  have heq := spectral_action_eq X ψ U p hρ (fun i => (g i)⁻¹*g i) 1 (by
    intro i hi
    have hpos : 0<p i := lt_of_le_of_ne (hp i) (Ne.symm hi)
    have hn : g i ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hpos _).ne'
    simp [hn])
  have hid : asMap (liftLocal X (spectralHom U 1)) ψ=ψ := by
    rw [map_one,liftLocal_one]
    change Matrix.toEuclideanCLM (𝕜 := ℂ) 1 ψ=ψ
    rw [map_one]
    rfl
  rw [hid] at heq
  have happ (A B : Operator L q) : asMap (A*B) ψ=asMap A (asMap B ψ) := by
    simp only [asMap,map_mul,mul_apply_eq_comp]
  unfold tilt
  rw [← happ,hmul]
  exact heq

end PolynomialPEPS.Subvolume.GroundTilt

end

end OAI
