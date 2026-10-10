import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace Generator

/-! Operator norm geometry for the original existential Banach-predual gap.
These statements use only concrete Hilbert operators. They do not identify
any predual or prove trace-orbit separability. -/
section
open scoped ComplexConjugate
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_imaginary_shift_apply_sq (A : H →L[ℂ] H) (t : ℝ) (x : H) :
    ‖(A + ((t : ℂ)*Complex.I) • 1) x‖^2 =
      ‖A x‖^2 - 2*t*(inner ℂ (A x) x).im + t^2*‖x‖^2 := by
  change ‖A x + ((t : ℂ)*Complex.I) • x‖^2 = _
  rw [norm_add_sq (𝕜 := ℂ),inner_smul_right]
  change ‖A x‖^2 + 2*((t : ℂ)*Complex.I*inner ℂ (A x) x).re +
    ‖((t : ℂ)*Complex.I) • x‖^2 = _
  simp only [
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero,mul_one,
    norm_smul,norm_mul,Complex.norm_real,Complex.norm_I,mul_pow,
    Real.norm_eq_abs,sq_abs]
  ring

variable [CompleteSpace H]

/-- Self-adjointness and a norm bound are characterized by translated norm balls. -/
theorem selfAdjoint_norm_le_iff_imaginary_shifts (A : H →L[ℂ] H) (C : ℝ) (hC : 0 ≤ C) :
    (IsSelfAdjoint A ∧ ‖A‖ ≤ C) ↔
      ∀ t : ℝ, ‖A + ((t : ℂ)*Complex.I) • 1‖ ≤ Real.sqrt (C^2+t^2) := by
  constructor
  · rintro ⟨ha,hn⟩ t
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    have hi : (inner ℂ (A x) x).im = 0 := by
      have h := congrArg Complex.im
        ((LinearMap.isSymmetric_iff_inner_map_self_real A.toLinearMap).mp ha.isSymmetric x)
      simp only [Complex.conj_im,ContinuousLinearMap.coe_coe] at h
      linarith
    have hx := (A.le_opNorm x).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg x))
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mpr hx
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
    rw [norm_imaginary_shift_apply_sq,hi,mul_zero,sub_zero,mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ C^2+t^2)]
    nlinarith
  · intro h
    have hn : ‖A‖ ≤ C := by
      simpa only [Complex.ofReal_zero,zero_mul,zero_smul,add_zero,zero_pow (by decide : 2 ≠ 0),
        Real.sqrt_sq hC] using h 0
    refine ⟨?_,hn⟩
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    apply (LinearMap.isSymmetric_iff_inner_map_self_real A.toLinearMap).mpr
    intro x
    have hb (t : ℝ) : -2*t*(inner ℂ (A x) x).im ≤ C^2*‖x‖^2 := by
      have hx := ((A + ((t : ℂ)*Complex.I) • 1).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (h t) (norm_nonneg x))
      have hs := (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mpr hx
      rw [norm_imaginary_shift_apply_sq,mul_pow,
        Real.sq_sqrt (by positivity : 0 ≤ C^2+t^2)] at hs
      nlinarith [sq_nonneg ‖A x‖]
    have hi : (inner ℂ (A x) x).im = 0 := by
      by_contra hi
      have ht := hb ((C^2*‖x‖^2+1)/(-2*(inner ℂ (A x) x).im))
      have he : -2*((C^2*‖x‖^2+1)/(-2*(inner ℂ (A x) x).im)) *
          (inner ℂ (A x) x).im = C^2*‖x‖^2+1 := by
        field_simp [hi]
      rw [he] at ht
      linarith
    apply Complex.ext
    · rfl
    · simp only [Complex.conj_im,ContinuousLinearMap.coe_coe,hi,neg_zero]

end

/-! Bounded self-adjoint sets are weak-star compact for the actual Banach
predual isometry. No predual uniqueness or WOT compatibility is assumed. -/
section
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S) (C : ℝ) (hC : 0 ≤ C)

include hC

/-- The self-adjoint ball pulled back to the given weak-star dual is closed. -/
theorem predual_selfAdjointBall_isClosed :
    IsClosed {φ : WeakDual ℂ X |
      IsSelfAdjoint (e (WeakDual.toStrongDual φ)).val ∧ ‖e (WeakDual.toStrongDual φ)‖ ≤ C} := by
  have he : {φ : WeakDual ℂ X |
      IsSelfAdjoint (e (WeakDual.toStrongDual φ)).val ∧ ‖e (WeakDual.toStrongDual φ)‖ ≤ C} =
      ⋂ t : ℝ, WeakDual.toStrongDual ⁻¹'
        Metric.closedBall (-e.symm (((t : ℂ)*Complex.I) • (1 : S))) (Real.sqrt (C^2+t^2)) := by
    ext φ
    simp only [Set.mem_iInter,Set.mem_preimage,Metric.mem_closedBall,dist_eq_norm,sub_neg_eq_add]
    change (IsSelfAdjoint (e (WeakDual.toStrongDual φ)).val ∧
      ‖(e (WeakDual.toStrongDual φ)).val‖ ≤ C) ↔ _
    rw [selfAdjoint_norm_le_iff_imaginary_shifts _ C hC]
    apply forall_congr'
    intro t
    rw [← e.norm_map (WeakDual.toStrongDual φ + e.symm (((t : ℂ)*Complex.I) • (1 : S))),
      map_add,e.apply_symm_apply]
    rfl
  rw [he]
  exact isClosed_iInter (fun t => WeakDual.isClosed_closedBall _ _)

/-- The same set is compact without adding continuity of the algebra isometry. -/
theorem predual_selfAdjointBall_isCompact :
    IsCompact {φ : WeakDual ℂ X |
      IsSelfAdjoint (e (WeakDual.toStrongDual φ)).val ∧ ‖e (WeakDual.toStrongDual φ)‖ ≤ C} := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ X) C).of_isClosed_subset
    (predual_selfAdjointBall_isClosed S e C hC)
  intro φ hφ
  change dist (WeakDual.toStrongDual φ) 0 ≤ C
  rw [dist_zero_right,← e.norm_map]
  exact hφ.2

end

/-! Positive operator balls are compact in the weak-star topology of the
given Banach predual. The isometry is not assumed weak-operator continuous. -/
section
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Positivity on a bounded self-adjoint ball is one more translated norm bound. -/
theorem positive_norm_le_iff_real_shift (A : H →L[ℂ] H) (C : ℝ) (hC : 0 ≤ C) :
    (A.IsPositive ∧ ‖A‖ ≤ C) ↔
      (IsSelfAdjoint A ∧ ‖A‖ ≤ C ∧ ‖A - (C : ℂ) • 1‖ ≤ C) := by
  have hc : algebraMap ℝ (H →L[ℂ] H) C = (C : ℂ) • 1 := by
    ext x
    simp
  have hsa : IsSelfAdjoint (algebraMap ℝ (H →L[ℂ] H) C) :=
    (isSelfAdjoint_iff.mpr (star_trivial C)).algebraMap _
  constructor
  · rintro ⟨hp, hn⟩
    have ha := ContinuousLinearMap.nonneg_iff_isPositive.mpr hp
    have hupper := (CStarAlgebra.norm_le_iff_le_algebraMap A hC ha).mp hn
    have hdiff : 0 ≤ algebraMap ℝ (H →L[ℂ] H) C - A := sub_nonneg.mpr hupper
    refine ⟨IsSelfAdjoint.of_nonneg ha, hn, ?_⟩
    rw [← hc, norm_sub_rev]
    exact (CStarAlgebra.norm_le_iff_le_algebraMap _ hC hdiff).mpr
      (sub_le_self _ ha)
  · rintro ⟨ha, hn, hd⟩
    rw [← hc] at hd
    have hlo := (ha.sub hsa).neg_algebraMap_norm_le_self
    have hm := neg_le_neg (algebraMap_mono (H →L[ℂ] H) hd)
    have h : -(algebraMap ℝ (H →L[ℂ] H) C) ≤
        A - algebraMap ℝ (H →L[ℂ] H) C := hm.trans hlo
    refine ⟨ContinuousLinearMap.nonneg_iff_isPositive.mp ?_, hn⟩
    simpa only [neg_add_cancel, sub_add_cancel, add_neg_cancel,
      ← add_sub_assoc, add_sub_cancel_left] using
      add_le_add_right h (algebraMap ℝ (H →L[ℂ] H) C)

variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S) (C : ℝ) (hC : 0 ≤ C)

include hC

/-- Positive balls are weak-star closed for the actual given predual. -/
theorem predual_positiveBall_isClosed :
    IsClosed {φ : WeakDual ℂ X |
      ContinuousLinearMap.IsPositive (e (WeakDual.toStrongDual φ)).val ∧
      ‖e (WeakDual.toStrongDual φ)‖ ≤ C} := by
  have he : {φ : WeakDual ℂ X |
      ContinuousLinearMap.IsPositive (e (WeakDual.toStrongDual φ)).val ∧
      ‖e (WeakDual.toStrongDual φ)‖ ≤ C} =
      {φ : WeakDual ℂ X |
        IsSelfAdjoint (e (WeakDual.toStrongDual φ)).val ∧
        ‖e (WeakDual.toStrongDual φ)‖ ≤ C} ∩
      (WeakDual.toStrongDual ⁻¹' Metric.closedBall (e.symm ((C : ℂ) • (1 : S))) C) := by
    ext φ
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Metric.mem_closedBall, dist_eq_norm]
    rw [← e.norm_map (WeakDual.toStrongDual φ - e.symm ((C : ℂ) • (1 : S))),
      map_sub, e.apply_symm_apply]
    change (_ ∧ ‖(e (WeakDual.toStrongDual φ)).val‖ ≤ C) ↔ _
    rw [positive_norm_le_iff_real_shift _ C hC]
    exact and_assoc.symm
  rw [he]
  exact (predual_selfAdjointBall_isClosed S e C hC).inter
    (WeakDual.isClosed_closedBall _ _)

/-- Banach--Alaoglu compactness for positive operator balls in the given predual. -/
theorem predual_positiveBall_isCompact :
    IsCompact {φ : WeakDual ℂ X |
      ContinuousLinearMap.IsPositive (e (WeakDual.toStrongDual φ)).val ∧
      ‖e (WeakDual.toStrongDual φ)‖ ≤ C} := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ X) C).of_isClosed_subset
    (predual_positiveBall_isClosed S e C hC)
  intro φ hφ
  change dist (WeakDual.toStrongDual φ) 0 ≤ C
  rw [dist_zero_right, ← e.norm_map]
  exact hφ.2

end

/-! Closed and compact order intervals for the given Banach predual.
All inequalities are the concrete operator Loewner order. -/
section
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

/-- A positive order interval is the intersection of two translated positive balls. -/
theorem predual_zeroInterval_eq (b : S) :
    {φ : WeakDual ℂ X | 0 ≤ (e (WeakDual.toStrongDual φ)).val ∧
      (e (WeakDual.toStrongDual φ)).val ≤ b.val} =
    {φ : WeakDual ℂ X |
      ContinuousLinearMap.IsPositive (e (WeakDual.toStrongDual φ)).val ∧
      ‖e (WeakDual.toStrongDual φ)‖ ≤ ‖b‖} ∩
    (fun φ : WeakDual ℂ X => StrongDual.toWeakDual (e.symm b) - φ) ⁻¹'
    {φ : WeakDual ℂ X |
      ContinuousLinearMap.IsPositive (e (WeakDual.toStrongDual φ)).val ∧
      ‖e (WeakDual.toStrongDual φ)‖ ≤ ‖b‖} := by
  ext φ
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, map_sub,
    StrongDual.toStrongDual_toWeakDual, e.apply_symm_apply]
  change (0 ≤ (e (WeakDual.toStrongDual φ)).val ∧
      (e (WeakDual.toStrongDual φ)).val ≤ b.val) ↔
    ((e (WeakDual.toStrongDual φ)).val.IsPositive ∧
      ‖(e (WeakDual.toStrongDual φ)).val‖ ≤ ‖b.val‖) ∧
    (b.val - (e (WeakDual.toStrongDual φ)).val).IsPositive ∧
      ‖b.val - (e (WeakDual.toStrongDual φ)).val‖ ≤ ‖b.val‖
  simp only [← ContinuousLinearMap.nonneg_iff_isPositive]
  constructor
  · rintro ⟨ha, hab⟩
    have hd := sub_nonneg.mpr hab
    exact ⟨⟨ha, CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha⟩,
      hd, CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_le_self _ ha) hd⟩
  · rintro ⟨⟨ha, _⟩, hd, _⟩
    exact ⟨ha, sub_nonneg.mp hd⟩

theorem predual_zeroInterval_isClosed (b : S) :
    IsClosed {φ : WeakDual ℂ X | 0 ≤ (e (WeakDual.toStrongDual φ)).val ∧
      (e (WeakDual.toStrongDual φ)).val ≤ b.val} := by
  rw [predual_zeroInterval_eq S e b]
  exact (predual_positiveBall_isClosed S e ‖b‖ (norm_nonneg b)).inter
    ((predual_positiveBall_isClosed S e ‖b‖ (norm_nonneg b)).preimage
      (continuous_const.sub continuous_id))

theorem predual_zeroInterval_isCompact (b : S) :
    IsCompact {φ : WeakDual ℂ X | 0 ≤ (e (WeakDual.toStrongDual φ)).val ∧
      (e (WeakDual.toStrongDual φ)).val ≤ b.val} := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ X) ‖b‖).of_isClosed_subset
    (predual_zeroInterval_isClosed S e b)
  intro φ hφ
  change dist (WeakDual.toStrongDual φ) 0 ≤ ‖b‖
  rw [dist_zero_right, ← e.norm_map]
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg hφ.2 hφ.1

/-- Translate an arbitrary interval to one with lower endpoint zero. -/
theorem predual_orderInterval_eq (a b : S) :
    {φ : WeakDual ℂ X | a.val ≤ (e (WeakDual.toStrongDual φ)).val ∧
      (e (WeakDual.toStrongDual φ)).val ≤ b.val} =
    (fun φ : WeakDual ℂ X => φ - StrongDual.toWeakDual (e.symm a)) ⁻¹'
    {φ : WeakDual ℂ X | 0 ≤ (e (WeakDual.toStrongDual φ)).val ∧
      (e (WeakDual.toStrongDual φ)).val ≤ (b-a).val} := by
  ext φ
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, map_sub,
    StrongDual.toStrongDual_toWeakDual, e.apply_symm_apply]
  change (a.val ≤ (e (WeakDual.toStrongDual φ)).val ∧
    (e (WeakDual.toStrongDual φ)).val ≤ b.val) ↔
    (0 ≤ (e (WeakDual.toStrongDual φ)).val - a.val ∧
    (e (WeakDual.toStrongDual φ)).val - a.val ≤ b.val - a.val)
  rw [sub_nonneg, sub_le_sub_iff_right]

theorem predual_orderInterval_isClosed (a b : S) :
    IsClosed {φ : WeakDual ℂ X | a.val ≤ (e (WeakDual.toStrongDual φ)).val ∧
      (e (WeakDual.toStrongDual φ)).val ≤ b.val} := by
  rw [predual_orderInterval_eq S e a b]
  exact (predual_zeroInterval_isClosed S e (b-a)).preimage
    (continuous_id.sub continuous_const)

theorem predual_orderInterval_isCompact (a b : S) :
    IsCompact {φ : WeakDual ℂ X | a.val ≤ (e (WeakDual.toStrongDual φ)).val ∧
      (e (WeakDual.toStrongDual φ)).val ≤ b.val} := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ X)
    (‖b-a‖+‖a‖)).of_isClosed_subset (predual_orderInterval_isClosed S e a b)
  intro φ hφ
  change dist (WeakDual.toStrongDual φ) 0 ≤ ‖b-a‖+‖a‖
  rw [dist_zero_right, ← e.norm_map]
  have hd : ‖(e (WeakDual.toStrongDual φ)).val-a.val‖ ≤ ‖b.val-a.val‖ :=
    CStarAlgebra.norm_le_norm_of_le_of_nonneg (sub_le_sub_right hφ.2 a.val)
      (sub_nonneg.mpr hφ.1)
  calc
    ‖e (WeakDual.toStrongDual φ)‖ =
        ‖((e (WeakDual.toStrongDual φ)).val-a.val)+a.val‖ := by rw [sub_add_cancel]; rfl
    _ ≤ ‖(e (WeakDual.toStrongDual φ)).val-a.val‖+‖a.val‖ := norm_add_le _ _
    _ ≤ ‖b-a‖+‖a‖ := add_le_add hd le_rfl

end

/-! Monotone order limits in the algebra converge for the actual given
Banach predual. Greatest/least bounds are tested only against members of S,
not against all ambient operators. -/
section
open Filter
open scoped Topology
variable {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)
variable [Preorder I] [Nonempty I]

/-- A decreasing net converges weak-star to its greatest lower bound in S. -/
theorem predual_antitone_tendsto (a : I → S) (l : S)
    (hanti : Antitone (fun i => (a i).val))
    (hlower : ∀ i, l.val ≤ (a i).val)
    (hgreatest : ∀ b : S, (∀ i, b.val ≤ (a i).val) → b.val ≤ l.val) :
    Tendsto (fun i => StrongDual.toWeakDual (e.symm (a i))) atTop
      (𝓝 (StrongDual.toWeakDual (e.symm l))) := by
  let u : I → WeakDual ℂ X := fun i => StrongDual.toWeakDual (e.symm (a i))
  have hu (i : I) : ∀ᶠ j in atTop,
      u j ∈ {φ : WeakDual ℂ X | l.val ≤ (e (WeakDual.toStrongDual φ)).val ∧
        (e (WeakDual.toStrongDual φ)).val ≤ (a i).val} := by
    filter_upwards [eventually_ge_atTop i] with j hj
    simpa only [u, Set.mem_ofPred_eq, StrongDual.toStrongDual_toWeakDual,
      e.apply_symm_apply] using And.intro (hlower j) (hanti hj)
  inhabit I
  apply (predual_orderInterval_isCompact S e l (a default)).tendsto_nhds_of_unique_mapClusterPt
    (hu default)
  intro φ hφ hc
  have hbound (i : I) := (predual_orderInterval_isClosed S e l (a i)).mem_of_mapClusterPt
    hc (hu i)
  apply WeakDual.toStrongDual.injective
  apply e.injective
  apply Subtype.ext
  simpa only [StrongDual.toStrongDual_toWeakDual, e.apply_symm_apply] using
    le_antisymm (hgreatest (e (WeakDual.toStrongDual φ)) (fun i => (hbound i).2)) hφ.1

/-- An increasing net converges weak-star to its least upper bound in S. -/
theorem predual_monotone_tendsto (a : I → S) (l : S)
    (hmono : Monotone (fun i => (a i).val))
    (hupper : ∀ i, (a i).val ≤ l.val)
    (hleast : ∀ b : S, (∀ i, (a i).val ≤ b.val) → l.val ≤ b.val) :
    Tendsto (fun i => StrongDual.toWeakDual (e.symm (a i))) atTop
      (𝓝 (StrongDual.toWeakDual (e.symm l))) := by
  let u : I → WeakDual ℂ X := fun i => StrongDual.toWeakDual (e.symm (a i))
  have hu (i : I) : ∀ᶠ j in atTop,
      u j ∈ {φ : WeakDual ℂ X | (a i).val ≤ (e (WeakDual.toStrongDual φ)).val ∧
        (e (WeakDual.toStrongDual φ)).val ≤ l.val} := by
    filter_upwards [eventually_ge_atTop i] with j hj
    simpa only [u, Set.mem_ofPred_eq, StrongDual.toStrongDual_toWeakDual,
      e.apply_symm_apply] using And.intro (hmono hj) (hupper j)
  inhabit I
  apply (predual_orderInterval_isCompact S e (a default) l).tendsto_nhds_of_unique_mapClusterPt
    (hu default)
  intro φ hφ hc
  have hbound (i : I) := (predual_orderInterval_isClosed S e (a i) l).mem_of_mapClusterPt
    hc (hu i)
  apply WeakDual.toStrongDual.injective
  apply e.injective
  apply Subtype.ext
  simpa only [StrongDual.toStrongDual_toWeakDual, e.apply_symm_apply] using
    le_antisymm hφ.2 (hleast (e (WeakDual.toStrongDual φ)) (fun i => (hbound i).1))

/-- In particular, decreasing positive nets with infimum zero tend weak-star to zero. -/
theorem predual_antitone_tendsto_zero (a : I → S)
    (hanti : Antitone (fun i => (a i).val))
    (hpos : ∀ i, 0 ≤ (a i).val)
    (hgreatest : ∀ b : S, (∀ i, b.val ≤ (a i).val) → b.val ≤ 0) :
    Tendsto (fun i => StrongDual.toWeakDual (e.symm (a i))) atTop (𝓝 0) := by
  simpa only [map_zero] using predual_antitone_tendsto S e a 0 hanti hpos hgreatest

end

/-! The actual given predual embeds isometrically into the norm dual of S.
Conjugation accounts for the conjugate-linear predual isometry. These
functionals preserve monotone order limits. No canonical-predual membership
or weak-operator continuity is assumed. -/
section
open Filter
open scoped Topology ComplexConjugate
variable {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

/-- Evaluation by x, made complex-linear in the algebra argument. -/
def predualFunctional (x : X) : StrongDual ℂ S :=
  LinearMap.mkContinuous
    { toFun := fun a => conj (e.symm a x)
      map_add' := by intros; simp
      map_smul' := by
        intro c a
        rw [e.symm.map_smulₛₗ]
        simp }
    ‖x‖ (by
      intro a
      change ‖conj (e.symm a x)‖ ≤ ‖x‖ * ‖a‖
      simp only [Complex.norm_conj]
      exact ((e.symm a).le_opNorm x).trans_eq (by rw [e.symm.norm_map, mul_comm]))

@[simp] theorem predualFunctional_apply (x : X) (a : S) :
    predualFunctional S e x a = conj (e.symm a x) := rfl

theorem predualFunctional_norm (x : X) : ‖predualFunctional S e x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (predualFunctional S e x).opNorm_le_bound (norm_nonneg x)
    intro a
    rw [predualFunctional_apply, Complex.norm_conj]
    exact ((e.symm a).le_opNorm x).trans_eq (by rw [e.symm.norm_map, mul_comm])
  · obtain ⟨g, hg, hx⟩ := exists_dual_vector'' ℂ x
    calc
      ‖x‖ = ‖predualFunctional S e x (e g)‖ := by simp [hx]
      _ ≤ ‖predualFunctional S e x‖ * ‖e g‖ := (predualFunctional S e x).le_opNorm _
      _ ≤ ‖predualFunctional S e x‖ := by
        simpa only [e.norm_map, mul_one] using
          mul_le_mul_of_nonneg_left hg (norm_nonneg (predualFunctional S e x))

/-- A conjugate-linear isometric embedding of the actual given predual. -/
def predualFunctionalIsometry : X →ₗᵢ⋆[ℂ] StrongDual ℂ S where
  toFun := predualFunctional S e
  map_add' x y := by ext a; simp
  map_smul' c x := by ext a; simp
  norm_map' := predualFunctional_norm S e

/-- Given-predual evaluation functionals separate every two algebra elements. -/
theorem predualFunctional_separates (a b : S)
    (h : ∀ x : X, predualFunctional S e x a = predualFunctional S e x b) : a = b := by
  apply e.symm.injective
  ext x
  exact (starRingEnd ℂ).injective (h x)

variable [Preorder I] [Nonempty I]

/-- The embedded functional preserves decreasing order limits in S. -/
theorem predualFunctional_antitone_tendsto (x : X) (a : I → S) (l : S)
    (hanti : Antitone (fun i => (a i).val))
    (hlower : ∀ i, l.val ≤ (a i).val)
    (hgreatest : ∀ b : S, (∀ i, b.val ≤ (a i).val) → b.val ≤ l.val) :
    Tendsto (fun i => predualFunctional S e x (a i)) atTop
      (𝓝 (predualFunctional S e x l)) := by
  exact (Complex.continuous_conj.tendsto _).comp
    ((WeakDual.eval_continuous x).tendsto _ |>.comp
      (predual_antitone_tendsto S e a l hanti hlower hgreatest))

/-- The embedded functional preserves increasing order limits in S. -/
theorem predualFunctional_monotone_tendsto (x : X) (a : I → S) (l : S)
    (hmono : Monotone (fun i => (a i).val))
    (hupper : ∀ i, (a i).val ≤ l.val)
    (hleast : ∀ b : S, (∀ i, (a i).val ≤ b.val) → l.val ≤ b.val) :
    Tendsto (fun i => predualFunctional S e x (a i)) atTop
      (𝓝 (predualFunctional S e x l)) := by
  exact (Complex.continuous_conj.tendsto _).comp
    ((WeakDual.eval_continuous x).tendsto _ |>.comp
      (predual_monotone_tendsto S e a l hmono hupper hleast))

end

/-! An arbitrary net squeezed into shrinking operator order intervals
converges in the topology of the given Banach predual. The net itself need
not be monotone. No normal-functional decomposition is used. -/
open Filter
open scoped Topology
variable {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)
variable [Preorder I] [Nonempty I]

theorem predual_order_squeeze_tendsto_zero (a b : I → S)
    (hanti : Antitone (fun i => (b i).val))
    (hgreatest : ∀ c : S, (∀ i, c.val ≤ (b i).val) → c.val ≤ 0)
    (hlower : ∀ i, -(b i).val ≤ (a i).val)
    (hupper : ∀ i, (a i).val ≤ (b i).val) :
    Tendsto (fun i => StrongDual.toWeakDual (e.symm (a i))) atTop (𝓝 0) := by
  let u : I → WeakDual ℂ X := fun i => StrongDual.toWeakDual (e.symm (a i))
  have hu (i : I) : ∀ᶠ j in atTop,
      u j ∈ {φ : WeakDual ℂ X | -(b i).val ≤ (e (WeakDual.toStrongDual φ)).val ∧
        (e (WeakDual.toStrongDual φ)).val ≤ (b i).val} := by
    filter_upwards [eventually_ge_atTop i] with j hj
    simpa only [u, Set.mem_ofPred_eq, StrongDual.toStrongDual_toWeakDual,
      e.apply_symm_apply] using
      And.intro ((neg_le_neg (hanti hj)).trans (hlower j)) ((hupper j).trans (hanti hj))
  inhabit I
  apply (predual_orderInterval_isCompact S e (-b default) (b default)).tendsto_nhds_of_unique_mapClusterPt
    (hu default)
  intro φ _ hc
  have hb (i : I) := (predual_orderInterval_isClosed S e (-b i) (b i)).mem_of_mapClusterPt
    hc (hu i)
  have hn : (e (WeakDual.toStrongDual φ)).val ≤ 0 :=
    hgreatest _ (fun i => (hb i).2)
  have hp : 0 ≤ (e (WeakDual.toStrongDual φ)).val := by
    have h := hgreatest (-e (WeakDual.toStrongDual φ)) (fun i => by
      change -(e (WeakDual.toStrongDual φ)).val ≤ (b i).val
      have hi : -(b i).val ≤ (e (WeakDual.toStrongDual φ)).val := (hb i).1
      simpa only [neg_neg] using neg_le_neg hi)
    exact neg_nonpos.mp h
  apply WeakDual.toStrongDual.injective
  apply e.injective
  apply Subtype.ext
  simpa using le_antisymm hn hp

theorem predualFunctional_order_squeeze_tendsto_zero (x : X) (a b : I → S)
    (hanti : Antitone (fun i => (b i).val))
    (hgreatest : ∀ c : S, (∀ i, c.val ≤ (b i).val) → c.val ≤ 0)
    (hlower : ∀ i, -(b i).val ≤ (a i).val)
    (hupper : ∀ i, (a i).val ≤ (b i).val) :
    Tendsto (fun i => predualFunctional S e x (a i)) atTop (𝓝 0) := by
  have h := (Complex.continuous_conj.tendsto _).comp
    ((WeakDual.eval_continuous x).tendsto _ |>.comp
      (predual_order_squeeze_tendsto_zero S e a b hanti hgreatest hlower hupper))
  have hz : (0 : WeakDual ℂ X) x = 0 := rfl
  simpa [Function.comp_def, predualFunctional, hz] using h

end Generator

end

end OAI
