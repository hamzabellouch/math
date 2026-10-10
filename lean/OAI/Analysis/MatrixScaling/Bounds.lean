import OAI.Analysis.MatrixScaling.Spectrum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.Order.Compact

namespace OAI

/-! Top spectral projections, uniform scaling bounds, and compact sublevels. -/

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky

def spectralIndex (d : ℕ) : Fin d ≃ Fin d :=
  (finCongr (Fintype.card_fin d).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin _))

theorem eigenvalues_spectralIndex {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (i : Fin d) :
    hA.eigenvalues (spectralIndex d i) = decreasingEigenvalues hA i := by
  unfold spectralIndex Matrix.IsHermitian.eigenvalues
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, decreasingEigenvalues]
  rfl

theorem decreasingEigenvalues_pos {d : ℕ} {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosDef) (i : Fin d) : 0 < decreasingEigenvalues hP.1 i := by
  rw [← eigenvalues_spectralIndex]
  exact hP.eigenvalues_pos _

theorem exists_top_spectral_projection {d : ℕ} {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosDef) (k : Fin d) :
    ∃ p : projectionSpace d (k.val+1),
      (P - decreasingEigenvalues hP.1 k • p.val).PosSemidef := by
  let e := spectralIndex d
  let f : Fin d → ℂ := fun i => if e.symm i ≤ k then 1 else 0
  let U := Unitary.conjStarAlgAut ℂ _ hP.1.eigenvectorUnitary
  let p := U (diagonal f)
  have hf : IsSelfAdjoint (diagonal f) := by
    apply isHermitian_diagonal_of_self_adjoint
    funext i
    simp [f]
  have hp : p.IsHermitian := by
    change star (U (diagonal f)) = U (diagonal f)
    rw [← map_star, hf.star_eq]
  have hpp : p*p=p := by
    change U (diagonal f) * U (diagonal f) = U (diagonal f)
    rw [← map_mul, diagonal_mul_diagonal]
    congr 2
    funext i
    simp [f]
  have ht : p.trace = ((k.val+1 : ℕ) : ℂ) := by
    change (U (diagonal f)).trace = _
    dsimp [U]
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
      one_mul, Matrix.trace_diagonal]
    change (∑ i, (fun j : Fin d => if j ≤ k then (1 : ℂ) else 0) (e.symm i)) = _
    rw [e.symm.sum_comp (fun j : Fin d => if j ≤ k then (1 : ℂ) else 0), Finset.sum_boole]
    have heq : Finset.univ.filter (fun i : Fin d => i ≤ k) = Finset.Iic k := by
      ext i; simp
    rw [heq, Fin.card_Iic]
  refine ⟨⟨p, hp, hpp, ?_⟩, ?_⟩
  · simpa only [Complex.natCast_re] using congrArg Complex.re ht
  · have hd : (diagonal (fun i => (hP.1.eigenvalues i : ℂ)) -
        (decreasingEigenvalues hP.1 k : ℂ) • diagonal f).PosSemidef := by
      rw [← diagonal_smul, diagonal_sub, posSemidef_diagonal_iff]
      intro i
      have he : hP.1.eigenvalues i = decreasingEigenvalues hP.1 (e.symm i) := by
        simpa only [e, Equiv.apply_symm_apply] using eigenvalues_spectralIndex hP.1 (e.symm i)
      by_cases hi : e.symm i ≤ k
      · have hm := decreasingEigenvalues_antitone hP.1 hi
        simp only [Pi.smul_apply, f, ite_eq_left hi, smul_eq_mul, mul_one]
        rw [he, ← Complex.ofReal_sub]
        exact_mod_cast sub_nonneg.mpr hm
      · simp only [Pi.smul_apply, f, ite_eq_right hi, smul_eq_mul, mul_zero, sub_zero]
        exact_mod_cast (hP.eigenvalues_pos i).le
    have hu := hd.mul_mul_conjTranspose_same (hP.1.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
    change (U (diagonal (fun i => (hP.1.eigenvalues i : ℂ)) -
      (decreasingEigenvalues hP.1 k : ℂ) • diagonal f)).PosSemidef at hu
    rw [map_sub, map_smul] at hu
    have hspec : U (diagonal (fun i => (hP.1.eigenvalues i : ℂ))) = P :=
      hP.1.spectral_theorem.symm
    rw [hspec, Complex.coe_smul] at hu
    exact hu

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem continuous_scalingMap {Y : Type*} [TopologicalSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hT : Continuous T) (P : Y → Matrix (Fin d) (Fin d) ℂ) (hP : Continuous P) :
    Continuous (fun y => scalingMap (T y) (P y)) := by
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i |>.comp hT).matrix_mul hP).matrix_mul
    ((continuous_apply i |>.comp hT).matrix_conjTranspose)

theorem uniform_projection_spectral_bound {Y : Type*}
    [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (hexpand : ∀ y (S : Submodule ℂ (Fin d → ℂ)),
      2 * Module.finrank ℂ S ≤
        Module.finrank ℂ (⨆ i, S.map (T y i).mulVecLin : Submodule ℂ (Fin r → ℂ)))
    (hdr : 2*d ≤ r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y (s : Fin d) (p : projectionSpace d (s.val+1)),
      ε ≤ decreasingEigenvalues
        (scalingMap_projection_positive (T y) p.property.1 p.property.2.1).1
        ⟨2*s.val+1, by omega⟩ := by
  let X := Σ s : Fin d, Y × projectionSpace d (s.val+1)
  let f : X → ℝ := fun x => decreasingEigenvalues
    (scalingMap_projection_positive (T x.2.1) x.2.2.property.1 x.2.2.property.2.1).1
    ⟨2*x.1.val+1, by omega⟩
  have hf : Continuous f := by
    apply continuous_sigma
    intro s
    let D : Y × projectionSpace d (s.val+1) → Matrix (Fin r) (Fin r) ℂ :=
      fun x => scalingMap (T x.1) x.2.val
    have hD : Continuous D := continuous_scalingMap
      (fun x : Y × projectionSpace d (s.val+1) => T x.1)
      (hT.comp continuous_fst) (fun x => x.2.val) (continuous_subtype_val.comp continuous_snd)
    have hDh (x : Y × projectionSpace d (s.val+1)) : (D x).IsHermitian :=
      (scalingMap_projection_positive (T x.1) x.2.property.1 x.2.property.2.1).1
    let k : Fin r := ⟨2*s.val+1, by omega⟩
    have hc := (continuous_decreasingEigenvalues k).comp (hD.subtype_mk hDh)
    change Continuous (fun x : Y × projectionSpace d (s.val+1) =>
      decreasingEigenvalues (hDh x) k)
    exact hc
  have hpos (x : X) : 0 < f x := by
    have hr := scalingMap_projection_rank (T x.2.1) (hexpand x.2.1)
      x.2.2.property.1 x.2.2.property.2.1
    rw [projectionSpace_rank] at hr
    exact decreasingEigenvalues_pos_of_lt_rank
      (scalingMap_projection_positive (T x.2.1) x.2.2.property.1 x.2.2.property.2.1)
      ⟨2*x.1.val+1, by omega⟩ (by change 2*x.1.val+1 < _; omega)
  cases isEmpty_or_nonempty X with
  | inl h =>
    let := h
    refine ⟨1, zero_lt_one, ?_⟩
    intro y s p
    exact isEmptyElim (⟨s,y,p⟩ : X)
  | inr h =>
    let := h
    obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (Set.univ : Set X).Nonempty)
      hf.continuousOn
    exact ⟨f x, hpos x, fun y s p => hx (Set.mem_univ (⟨s,y,p⟩ : X))⟩

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem expansion_dimension (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hexpand : ∀ S : Submodule ℂ (Fin d → ℂ),
      2 * Module.finrank ℂ S ≤
        Module.finrank ℂ (⨆ i, S.map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ))) :
    2*d ≤ r := by
  have h := hexpand ⊤
  have hb := Submodule.finrank_le (⨆ i,
    (⊤ : Submodule ℂ (Fin d → ℂ)).map (T i).mulVecLin : Submodule ℂ (Fin r → ℂ))
  simp only [finrank_top, Module.finrank_pi, Fintype.card_fin] at h hb
  omega

theorem scaling_spectral_bound (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (hdr : 2*d ≤ r) (ε : ℝ)
    (hmin : ∀ (s : Fin d) (p : projectionSpace d (s.val+1)),
      ε ≤ decreasingEigenvalues (scalingMap_projection_positive T p.property.1 p.property.2.1).1
        ⟨2*s.val+1, by omega⟩)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef) (s : Fin d) :
    ε * decreasingEigenvalues hP.1 s ≤
      decreasingEigenvalues (scalingMap_positive T hP.posSemidef).1 ⟨2*s.val+1, by omega⟩ := by
  obtain ⟨p,hp⟩ := exists_top_spectral_projection hP s
  have hc := scalingMap_comparison T (decreasingEigenvalues hP.1 s) hp
  have hLam := decreasingEigenvalues_pos hP s
  have hs := decreasingEigenvalues_smul_le
    (scalingMap_projection_positive T p.property.1 p.property.2.1).1
    (scalingMap_positive T hP.posSemidef).1 _ hLam.le hc
    (⟨2*s.val+1, by omega⟩ : Fin r)
  calc
    ε * decreasingEigenvalues hP.1 s = decreasingEigenvalues hP.1 s * ε := mul_comm _ _
    _ ≤ decreasingEigenvalues hP.1 s *
        decreasingEigenvalues (scalingMap_projection_positive T p.property.1 p.property.2.1).1
          ⟨2*s.val+1, by omega⟩ := mul_le_mul_of_nonneg_left (hmin s p) hLam.le
    _ ≤ _ := hs

theorem uniform_scaling_estimate {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (hexpand : ∀ y (S : Submodule ℂ (Fin d → ℂ)),
      2 * Module.finrank ℂ S ≤
        Module.finrank ℂ (⨆ i, S.map (T y i).mulVecLin : Submodule ℂ (Fin r → ℂ)))
    (hdr : 2*d ≤ r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.PosDef),
      (∀ s : Fin d, ε * decreasingEigenvalues hP.1 s ≤
        decreasingEigenvalues (scalingMap_positive (T y) hP.posSemidef).1
          ⟨2*s.val+1, by omega⟩) ∧
      2 * ∑ s, Real.log (1+ε*decreasingEigenvalues hP.1 s) ≤
        Real.log ((1+scalingMap (T y) P).det.re) := by
  obtain ⟨ε,hε,hm⟩ := uniform_projection_spectral_bound T hT hexpand hdr
  refine ⟨ε,hε,?_⟩
  intro y P hP
  have hs := scaling_spectral_bound (T y) hdr ε (hm y) hP
  refine ⟨hs, ?_⟩
  exact scaling_log_det_of_spectral_bound hdr (scalingMap_positive (T y) hP.posSemidef)
    (decreasingEigenvalues hP.1) (decreasingEigenvalues_pos hP) hε hs

/-- The uniform determinant bound with no extra dimension or nonempty-base
hypothesis. The dimension inequality is deduced from expansion when needed. -/
theorem uniform_scaling_log_det {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (hexpand : ∀ y (S : Submodule ℂ (Fin d → ℂ)),
      2 * Module.finrank ℂ S ≤
        Module.finrank ℂ (⨆ i, S.map (T y i).mulVecLin : Submodule ℂ (Fin r → ℂ))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.PosDef),
      2 * ∑ s, Real.log (1+ε*decreasingEigenvalues hP.1 s) ≤
        Real.log ((1+scalingMap (T y) P).det.re) := by
  cases isEmpty_or_nonempty Y with
  | inl h =>
    let := h
    exact ⟨1, zero_lt_one, fun y => isEmptyElim y⟩
  | inr h =>
    let := h
    let y := Classical.arbitrary Y
    obtain ⟨ε,hε,he⟩ := uniform_scaling_estimate T hT hexpand
      (expansion_dimension (T y) (hexpand y))
    exact ⟨ε,hε,fun y P hP => (he y P hP).2⟩

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {n d r : ℕ}

theorem det_eq_prod_decreasing {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian) :
    P.det = ∏ i, (decreasingEigenvalues hP i : ℂ) := by
  rw [hP.det_eq_prod_eigenvalues]
  calc
    ∏ i, (hP.eigenvalues i : ℂ) = ∏ i, (hP.eigenvalues (spectralIndex d i) : ℂ) :=
      ((spectralIndex d).prod_comp (fun i => (hP.eigenvalues i : ℂ))).symm
    _ = _ := by simp only [eigenvalues_spectralIndex]

theorem log_det_posDef {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef) :
    Real.log P.det.re = ∑ i, Real.log (decreasingEigenvalues hP.1 i) := by
  rw [det_eq_prod_decreasing hP.1, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact Real.log_prod (fun i _ => ne_of_gt (decreasingEigenvalues_pos hP i))

def scalingPotential (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Real.log (1+scalingMap T P).det.re - (3/2)*Real.log P.det.re

theorem scalingScalar_sum_le_potential
    (T : Fin n → Matrix (Fin r) (Fin d) ℂ)
    {P : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosDef) (ε : ℝ)
    (hdet : 2 * ∑ s, Real.log (1+ε*decreasingEigenvalues hP.1 s) ≤
      Real.log ((1+scalingMap T P).det.re)) :
    ∑ s, scalingScalar ε (decreasingEigenvalues hP.1 s) ≤ scalingPotential T P := by
  simp only [scalingScalar, Finset.sum_sub_distrib, ← Finset.mul_sum,
    scalingPotential, log_det_posDef hP]
  linarith

theorem uniform_scaling_sublevels {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (T : Y → Fin n → Matrix (Fin r) (Fin d) ℂ) (hT : Continuous T)
    (hexpand : ∀ y (S : Submodule ℂ (Fin d → ℂ)),
      2 * Module.finrank ℂ S ≤
        Module.finrank ℂ (⨆ i, S.map (T y i).mulVecLin : Submodule ℂ (Fin r → ℂ))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (C : ℝ) y (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.PosDef),
      scalingPotential (T y) P ≤ C → ∀ i : Fin d,
        let B := C - (d-1)*((3/2)*Real.log ε)
        Real.exp (-2*B/3) ≤ decreasingEigenvalues hP.1 i ∧
          decreasingEigenvalues hP.1 i ≤ Real.exp (2*B-4*Real.log ε) := by
  obtain ⟨ε,hε,he⟩ := uniform_scaling_log_det T hT hexpand
  refine ⟨ε,hε,?_⟩
  intro C y P hP hC i
  exact scaling_eigenvalue_bounds hε (decreasingEigenvalues hP.1)
    (decreasingEigenvalues_pos hP)
    ((scalingScalar_sum_le_potential (T y) hP ε (he y P hP)).trans hC) i

end Kaplansky

end

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace Kaplansky
variable {d : ℕ}

abbrev HermitianMatrices (d : ℕ) := {P : Matrix (Fin d) (Fin d) ℂ // P.IsHermitian}

instance : ProperSpace (HermitianMatrices d) :=
  ProperSpace.of_isClosed (isClosed_eq continuous_star continuous_id)

def spectralWindow (d : ℕ) (a b : ℝ) : Set (HermitianMatrices d) :=
  {P | ∀ i, a ≤ decreasingEigenvalues P.property i ∧ decreasingEigenvalues P.property i ≤ b}

theorem isClosed_spectralWindow (a b : ℝ) : IsClosed (spectralWindow d a b) := by
  simp only [spectralWindow, Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  exact (isClosed_le continuous_const (continuous_decreasingEigenvalues i)).inter
    (isClosed_le (continuous_decreasingEigenvalues i) continuous_const)

theorem norm_le_of_decreasingEigenvalues {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.IsHermitian) {b : ℝ} (hb : 0 ≤ b)
    (he : ∀ i, 0 ≤ decreasingEigenvalues hP i ∧ decreasingEigenvalues hP i ≤ b) :
    ‖P‖ ≤ b := by
  conv_lhs => rw [hP.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro i
  have he' := he ((spectralIndex d).symm i)
  rw [← eigenvalues_spectralIndex, Equiv.apply_symm_apply] at he'
  simpa only [Function.comp_apply, RCLike.norm_ofReal, Real.norm_eq_abs, abs_of_nonneg he'.1]
    using he'.2

theorem isCompact_spectralWindow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsCompact (spectralWindow d a b) := by
  let z : HermitianMatrices d := ⟨0, isHermitian_zero⟩
  apply (isCompact_closedBall z b).of_isClosed_subset (isClosed_spectralWindow a b)
  intro P hP
  rw [Metric.mem_closedBall, Subtype.dist_eq]
  change dist P.val 0 ≤ b
  rw [dist_zero_right]
  exact norm_le_of_decreasingEigenvalues P.property hb (fun i => ⟨ha.trans (hP i).1, (hP i).2⟩)

theorem spectralWindow_posDef {a b : ℝ} (ha : 0 < a) {P : HermitianMatrices d}
    (hP : P ∈ spectralWindow d a b) : P.val.PosDef := by
  apply P.property.posDef_iff_eigenvalues_pos.mpr
  intro i
  have h := lt_of_lt_of_le ha (hP ((spectralIndex d).symm i)).1
  rwa [← eigenvalues_spectralIndex, Equiv.apply_symm_apply] at h

end Kaplansky

end

end OAI
