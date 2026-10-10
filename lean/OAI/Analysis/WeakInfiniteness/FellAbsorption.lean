import Mathlib
import OAI.Analysis.WeakInfiniteness.GroupRegular

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness.HilbertValued

abbrev HilbertSum (G H : Type*) [NormedAddCommGroup H] : Type _ := lp (fun _ : G => H) 2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {G K : Type*}

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma mem_l2_reindex (e : G ≃ K) (ξ : HilbertSum K H) :
    Memℓp (fun g => ξ (e g)) 2 := by
  apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mpr
  have hs : Summable (fun k => ‖ξ k‖ ^ (2 : ℝ≥0∞).toReal) :=
    Memℓp.summable (by norm_num) ξ.property
  exact e.summable_iff.mpr hs

def l2Reindex (e : G ≃ K) : HilbertSum G H ≃ₗᵢ[ℂ] HilbertSum K H where
  toFun ξ := ⟨fun k => ξ (e.symm k), mem_l2_reindex e.symm ξ⟩
  invFun ξ := ⟨fun g => ξ (e g), mem_l2_reindex e ξ⟩
  left_inv ξ := by ext g; simp
  right_inv ξ := by ext k; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' ξ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    congr 1
    exact e.symm.tsum_eq (fun g => ‖ξ g‖ ^ (2 : ℝ≥0∞).toReal)

omit [CompleteSpace H] in
@[simp]

lemma l2Reindex_apply (e : G ≃ K) (ξ : HilbertSum G H) (k : K) :
    l2Reindex e ξ k = ξ (e.symm k) := rfl

omit [CompleteSpace H] in
lemma l2Reindex_single [DecidableEq G] [DecidableEq K] (e : G ≃ K) (g : G) (c : H) :
    l2Reindex e (lp.single 2 g c) = lp.single 2 (e g) c := by
  classical
  ext k
  simp only [l2Reindex_apply, lp.single_apply, Pi.single_apply]
  have he : e.symm k = g ↔ k = e g := e.symm_apply_eq
  simp only [he]

section SchurBound

variable {X I : Type*} [Fintype I]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma l2_summable_norm_sq (ξ : HilbertSum X H) : Summable (fun x => ‖ξ x‖ ^ 2) := by
  have h := Memℓp.summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) ξ.property
  norm_num at h
  exact h

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma l2_norm_sq (ξ : HilbertSum X H) : ‖ξ‖ ^ 2 = ∑' x, ‖ξ x‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) ξ
  norm_num at h
  exact h

lemma weighted_two_mul_le (a b w : ℝ) (hw : 0 < w) :
    2 * a * b ≤ w * a ^ 2 + w⁻¹ * b ^ 2 := by
  have h := sq_nonneg (w * a - b)
  have hi : w * w⁻¹ = 1 := mul_inv_cancel₀ hw.ne'
  apply (mul_le_mul_iff_right₀ hw).mp
  nlinarith

def permutationSum (e : I → X ≃ X) : HilbertSum X H →L[ℂ] HilbertSum X H :=
  ∑ i, (l2Reindex (e i)).toContinuousLinearEquiv.toContinuousLinearMap

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma weighted_squares_summable (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (e : I → X ≃ X) (C : ℝ)
    (hrow : ∀ x, ∑ i, w ((e i).symm x) / w x ≤ C)
    (ξ : HilbertSum X H) (i : I) :
    Summable (fun x => (w ((e i).symm x) / w x) * ‖ξ x‖ ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun x => mul_nonneg (div_nonneg (hw _).le (hw _).le) (sq_nonneg _))
    (fun x => mul_le_mul_of_nonneg_right
      ((Finset.single_le_sum (fun j _ => div_nonneg (hw _).le (hw _).le)
        (Finset.mem_univ i)).trans (hrow x)) (sq_nonneg _))
    ((l2_summable_norm_sq ξ).mul_left C)

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma weighted_squares_sum_le (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (e : I → X ≃ X) (C : ℝ)
    (hrow : ∀ x, ∑ i, w ((e i).symm x) / w x ≤ C)
    (ξ : HilbertSum X H) :
    ∑ i, ∑' x, (w ((e i).symm x) / w x) * ‖ξ x‖ ^ 2 ≤ C * ‖ξ‖ ^ 2 := by
  have hs (i : I) := weighted_squares_summable w hw e C hrow ξ i
  rw [← Summable.tsum_finsetSum (fun i _ => hs i)]
  simp_rw [← Finset.sum_mul]
  rw [l2_norm_sq ξ, ← tsum_mul_left]
  apply Summable.tsum_le_tsum
    (fun x => mul_le_mul_of_nonneg_right (hrow x) (sq_nonneg _))
  · simpa only [Finset.sum_mul] using summable_sum (fun i _ => hs i)
  · exact (l2_summable_norm_sq ξ).mul_left C

omit [CompleteSpace H] in
theorem norm_permutationSum_le (w : X → ℝ) (hw : ∀ x, 0 < w x)
    (e : I → X ≃ X) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ x, ∑ i, w ((e i).symm x) / w x ≤ C)
    (hcol : ∀ x, ∑ i, w (e i x) / w x ≤ C) :
    ‖permutationSum (H := H) e‖ ≤ C := by
  classical
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
  intro ξ η hξ hη
  have hs₁ (i : I) := weighted_squares_summable w hw e C hrow η i
  have hs₂ (i : I) : Summable (fun x =>
      (w x / w ((e i).symm x)) * ‖ξ ((e i).symm x)‖ ^ 2) := by
    have h := weighted_squares_summable w hw (fun i => (e i).symm) C hcol ξ i
    convert (e i).symm.summable_iff.mpr h using 1
    ext x
    simp
  have hpoint (i : I) (x : X) :
      2 * (inner ℂ (ξ ((e i).symm x)) (η x)).re ≤
        (w ((e i).symm x) / w x) * ‖η x‖ ^ 2 +
        (w x / w ((e i).symm x)) * ‖ξ ((e i).symm x)‖ ^ 2 := by
    have hr := (Complex.re_le_norm (inner ℂ (ξ ((e i).symm x)) (η x))).trans
      (norm_inner_le_norm (ξ ((e i).symm x)) (η x))
    have he := weighted_two_mul_le ‖η x‖ ‖ξ ((e i).symm x)‖
      (w ((e i).symm x) / w x) (div_pos (hw _) (hw _))
    rw [inv_div] at he
    nlinarith
  have hi (i : I) :
      2 * (inner ℂ (l2Reindex (e i) ξ) η).re ≤
        (∑' x, (w ((e i).symm x) / w x) * ‖η x‖ ^ 2) +
        (∑' x, (w x / w ((e i).symm x)) * ‖ξ ((e i).symm x)‖ ^ 2) := by
    have hin := lp.summable_inner (𝕜 := ℂ) (l2Reindex (e i) ξ) η
    have hre := (Complex.reCLM.hasSum hin.hasSum).summable
    have hret : (inner ℂ (l2Reindex (e i) ξ) η).re =
        ∑' x, (inner ℂ (ξ ((e i).symm x)) (η x)).re := by
      exact Complex.reCLM.map_tsum hin
    rw [hret, ← tsum_mul_left, ← (hs₁ i).tsum_add (hs₂ i)]
    exact Summable.tsum_le_tsum (hpoint i) (hre.mul_left 2) ((hs₁ i).add (hs₂ i))
  have hsecond :
      (∑ i, ∑' x, (w x / w ((e i).symm x)) * ‖ξ ((e i).symm x)‖ ^ 2) =
      (∑ i, ∑' x, (w (e i x) / w x) * ‖ξ x‖ ^ 2) := by
    apply Finset.sum_congr rfl
    intro i _
    convert (e i).symm.tsum_eq (fun x => (w (e i x) / w x) * ‖ξ x‖ ^ 2) using 1
    simp
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [Finset.sum_add_distrib, hsecond] at htotal
  have hb₁ := weighted_squares_sum_le w hw e C hrow η
  have hb₂ := weighted_squares_sum_le w hw (fun i => (e i).symm) C hcol ξ
  simp only [Equiv.symm_symm] at hb₂
  have heval : (inner ℂ (permutationSum e ξ) η).re =
      ∑ i, (inner ℂ (l2Reindex (e i) ξ) η).re := by
    simp [permutationSum]
  change (inner ℂ (permutationSum e ξ) η).re ≤ C
  rw [heval]
  rw [← Finset.mul_sum] at htotal
  simp only [hξ, hη, one_pow, mul_one] at hb₁ hb₂
  nlinarith

end SchurBound

def l2Diagonal {X : Type*} (v : X → H ≃ₗᵢ[ℂ] H) :
    HilbertSum X H ≃ₗᵢ[ℂ] HilbertSum X H where
  toFun ξ := ⟨fun x => v x (ξ x), by
    apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mpr
    simpa only [LinearIsometryEquiv.norm_map] using
      (Memℓp.summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) ξ.property)⟩
  invFun ξ := ⟨fun x => (v x).symm (ξ x), by
    apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mpr
    simpa only [LinearIsometryEquiv.norm_map] using
      (Memℓp.summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) ξ.property)⟩
  left_inv ξ := by ext x; simp
  right_inv ξ := by ext x; simp
  map_add' ξ η := by ext x; exact map_add (v x) _ _
  map_smul' c ξ := by ext x; exact map_smul (v x) _ _
  norm_map' ξ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    simp

omit [CompleteSpace H] in
@[simp]

lemma l2Diagonal_apply {X : Type*} (v : X → H ≃ₗᵢ[ℂ] H)
    (ξ : HilbertSum X H) (x : X) : l2Diagonal v ξ x = v x (ξ x) := rfl

omit [CompleteSpace H] in
@[simp]

lemma l2Diagonal_symm_apply {X : Type*} (v : X → H ≃ₗᵢ[ℂ] H)
    (ξ : HilbertSum X H) (x : X) : (l2Diagonal v).symm ξ x = (v x).symm (ξ x) := rfl

variable [Group G]

def fellUnitary (π : G →* H ≃ₗᵢ[ℂ] H) : HilbertSum G H ≃ₗᵢ[ℂ] HilbertSum G H :=
  l2Diagonal π

def twistedRegular (π : G →* H ≃ₗᵢ[ℂ] H) (s : G) :
    HilbertSum G H →L[ℂ] HilbertSum G H :=
  ((l2Reindex (Equiv.mulLeft s)).trans (l2Diagonal (fun _ => π s))).toContinuousLinearEquiv
    |>.toContinuousLinearMap

omit [CompleteSpace H] in
@[simp]

lemma twistedRegular_apply (π : G →* H ≃ₗᵢ[ℂ] H) (s g : G) (ξ : HilbertSum G H) :
    twistedRegular π s ξ g = π s (ξ (s⁻¹ * g)) := rfl

theorem fell_intertwines (π : G →* H ≃ₗᵢ[ℂ] H) (s : G) :
    (fellUnitary π).conjStarAlgEquiv
      (l2Reindex (Equiv.mulLeft s)).toContinuousLinearEquiv.toContinuousLinearMap =
      twistedRegular π s := by
  ext ξ g
  change π g ((π (s⁻¹ * g)).symm (ξ (s⁻¹ * g))) = π s (ξ (s⁻¹ * g))
  have he : (π g) * (π (s⁻¹ * g))⁻¹ = π s := by
    rw [← map_inv, ← map_mul]
    simp
  exact congrArg (fun f : H ≃ₗᵢ[ℂ] H => f (ξ (s⁻¹ * g))) he

theorem norm_twistedRegular_sum {I : Type*} (s : I → G) (F : Finset I)
    (π : G →* H ≃ₗᵢ[ℂ] H) :
    ‖∑ i ∈ F, twistedRegular π (s i)‖ =
      ‖∑ i ∈ F, (l2Reindex (H := H) (Equiv.mulLeft (s i))).toContinuousLinearEquiv.toContinuousLinearMap‖ := by
  simp_rw [← fell_intertwines π]
  rw [← map_sum]
  exact NonUnitalStarAlgHom.norm_map
    ((fellUnitary π).conjStarAlgEquiv.toStarAlgHom.toNonUnitalStarAlgHom)
    (fellUnitary π).conjStarAlgEquiv.injective _

end WeakPureInfiniteness.HilbertValued
end

end OAI
