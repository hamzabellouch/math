import OAI.Combinatorics.Progressions.Estimates.RelativePatchAmplification

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativePatchBoxScore_nonpos_of_one_le
    {X : Type*} [Fintype X] [DecidableEq X] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    {target : ℝ} (htarget : 1 ≤ target) (A : PolynomialPatch X s d) :
    relativePatchBoxScore N f target A ≤ 0 := by
  unfold relativePatchBoxScore
  calc
    _ ≤ 𝔼 _x ∈ integerBox N, (0 : ℝ) := Finset.expect_le_expect (fun x hx =>
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ((hf x hx).2.trans htarget))
        (A.value_mem_Icc _).1)
    _ = 0 := Finset.expect_const_zero _

theorem relativePatchSliceScore_nonpos_of_one_le
    {X : Type*} [Fintype X] [DecidableEq X] {s d q : ℕ} {N : X → ℕ}
    (S : ResidueBoxSlice N q) (f : (X → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    {target : ℝ} (htarget : 1 ≤ target) (A : PolynomialPatch X s d) :
    relativePatchSliceScore S f target A ≤ 0 := by
  unfold relativePatchSliceScore Finset.expect
  apply smul_nonpos_of_nonneg_of_nonpos (by positivity)
  apply Finset.sum_nonpos
  intro x _
  have hx : (fun i => ((S.point x i).val : ℤ)) ∈ integerBox N :=
    (mem_integerBox _ _).mpr (fun i =>
      ⟨by positivity, by exact_mod_cast (S.point x i).isLt⟩)
  exact mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr ((hf _ hx).2.trans htarget)) (A.value_mem_Icc _).1

theorem RelativePatchSliceConclusion.target_lt_one
    {X : Type*} [Fintype X] [DecidableEq X] {s : ℕ}
    {N : X → ℕ} {f : (X → ℤ) → ℝ} {target cost : ℝ} {rankBound : ℕ}
    (h : RelativePatchSliceConclusion s N f target rankBound cost)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) : target < 1 := by
  by_contra htarget
  obtain ⟨q, _hq, S, d, A, _hlength, _hd, _hcomplexity, hscore⟩ := h
  have hnonpos := relativePatchSliceScore_nonpos_of_one_le S f hf (le_of_not_gt htarget) A
  exact (not_le_of_gt (Real.exp_pos (-cost))) (hscore.trans hnonpos)

theorem RelativePatchAbsoluteRule.mean_lt_of_one_le_target
    {s n₀ d₀ : ℕ} {p a Λ : ℝ}
    (h : RelativePatchAbsoluteRule s n₀ p a Λ d₀) (hΛ : 1 ≤ Λ)
    (N : Fin n₀ → ℕ) (hprime : ∀ i, (N i).Prime) (hinj : Function.Injective N)
    (hcomparable : ∀ i j, N i ≤ 2 ^ (n₀ + 1) * N j)
    (hlarge : ∀ i, Real.exp p ≤ (N i : ℝ))
    (f : (Fin n₀ → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2)) :
    (𝔼 x ∈ integerBox N, f x) < a := by
  by_contra hmean
  have hconclusion := h N hprime hinj hcomparable hlarge f hf hfree (le_of_not_gt hmean)
  exact (not_lt_of_ge hΛ) (hconclusion.target_lt_one hf)

end Erdos3

end

end OAI
