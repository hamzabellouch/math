import OAI.NumberTheory.JointDickman.Probability.SiteResponseConcentration

namespace OAI

/-! # Identifying a column sample after its site types are fixed -/

namespace JointDickman
open Finset Classical PublishedInputs

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

noncomputable def sampledSiteTest (E : ι → ι → A → A → ℝ) {m : ℕ}
    (s : ColumnSample (ι := ι) m) (t : ι → A) (i : ι) (a : A) : ℝ :=
  responseSign (∑ r, E i (s.1 r) a (t (s.1 r))*cutSign (s.2 r))

omit [Fintype ι] [Fintype A] [DecidableEq ι] in
theorem sampledSiteTest_bound (E : ι → ι → A → A → ℝ) {m : ℕ}
    (s : ColumnSample (ι := ι) m) (t : ι → A) (i : ι) (a : A) :
    |sampledSiteTest E s t i a| ≤ 1 := by simp [sampledSiteTest]

omit [Fintype ι] [Fintype A] in
theorem sampledSiteTest_agree (E : ι → ι → A → A → ℝ) {m : ℕ}
    (s : ColumnSample (ι := ι) m) (t x : ι → A)
    (ht : ∀ i ∈ univ.image s.1, x i = t i) :
    sampledSiteTest E s t = sampledSiteTest E s x := by
  funext i a
  unfold sampledSiteTest
  congr 1
  apply sum_congr rfl
  intro r _
  rw [ht (s.1 r) (mem_image.mpr ⟨r,mem_univ _,rfl⟩)]

omit [Fintype A] in
theorem siteColumnResponse_masked (E : ι → ι → A → A → ℝ)
    (g : ι → A → ℝ) (J : Finset ι) (x : ι → A) :
    siteColumnResponse (maskedSiteKernel J E) g x =
      residualColumnBound (realizedSiteKernel E x) J (fun i => g i (x i)) := by
  have he : univ \ J = univ.filter (fun i => i ∉ J) := by ext i; simp
  simp only [siteColumnResponse,residualColumnBound,he,sum_filter]
  apply sum_congr rfl
  intro j _
  by_cases hj : j ∈ J
  · simp [maskedSiteKernel,hj]
  · simp only [maskedSiteKernel,hj,not_false_eq_true,and_true,ite_mul,zero_mul,realizedSiteKernel]
    simp only [ite_true]

omit [Fintype A] in
theorem columnSampleNorm_eq_response (E : ι → ι → A → A → ℝ) {m : ℕ}
    (s : ColumnSample (ι := ι) m) (x : ι → A) :
    columnSampleNorm (realizedSiteKernel E x) s =
      siteColumnResponse (maskedSiteKernel (univ.image s.1) E) (sampledSiteTest E s x) x /
        Fintype.card ι := by
  rw [siteColumnResponse_masked]
  rfl

omit [Fintype A] in
theorem maskedSiteKernel_row_le (H : ι → ι → A → A → ℝ)
    (hH : ∀ i j a b, 0 ≤ H i j a b) (J : Finset ι) (x : ι → A) (i : ι) :
    siteRowSum (maskedSiteKernel J H) i x ≤ siteRowSum H i x := by
  apply sum_le_sum
  intro j _
  unfold maskedSiteKernel
  split_ifs <;> first | exact le_rfl | exact hH i j (x i) (x j)

end JointDickman

end OAI
