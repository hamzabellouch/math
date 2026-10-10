import OAI.Analysis.TriangularHilbert.IntervalMask

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def smoothKernel (a b t : ℝ) : ℝ := ∫ s in a..b, signedKernel s t / s

def selectedSum (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (a b : Matrix ι ι ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*(smoothKernel (a i j) (b i j) (u i+u j+u k):ℂ)

def maskedSigned (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (a b : Matrix ι ι ℝ) (s : ℝ) : ℂ :=
  signedCenter (maskedArray A a b s) h u s / (s:ℂ)

omit [DecidableEq ι] in
lemma maskedSigned_eq (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (a b : Matrix ι ι ℝ) (s : ℝ) :
    maskedSigned A h u a b s = ∑ i, ∑ j, ∑ k,
      (Set.Ico (a i j) (b i j)).indicator
        (fun s => (h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i)*((signedKernel s (u i+u j+u k)/s:ℝ):ℂ)) s := by
  simp only [maskedSigned,signedCenter,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  change (h^3:ℝ)*(windowMask (a i j) (b i j) s (A 0 i j)*A 1 j k*A 2 k i)*
    (signedKernel s (u i+u j+u k):ℂ)/(s:ℂ) = _
  by_cases hs : s ∈ Set.Ico (a i j) (b i j)
  · rw [Set.indicator_of_mem hs]
    simp only [Set.mem_Ico] at hs
    simp only [windowMask,ite_eq_left hs]
    push_cast
    ring
  · rw [Set.indicator_of_notMem hs]
    simp only [Set.mem_Ico] at hs
    simp only [windowMask,ite_eq_right hs]
    simp

omit [DecidableEq ι] in
lemma selectedSum_eq_integral (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (a b : Matrix ι ι ℝ)
    {L U : ℝ} (hL : 0 < L) (hLU : L ≤ U) (ha : ∀ i j, L ≤ a i j) (hab : ∀ i j, a i j ≤ b i j)
    (hb : ∀ i j, b i j ≤ U) : selectedSum A h u a b = ∫ s in L..U, maskedSigned A h u a b s := by
  have hc (i j k : ι) : IntervalIntegrable (fun s => ((signedKernel s (u i+u j+u k)/s:ℝ):ℂ)) volume L U :=
    ⟨(signedKernel_intervalIntegrable hL hLU (u i+u j+u k)).1.ofReal,
     (signedKernel_intervalIntegrable hL hLU (u i+u j+u k)).2.ofReal⟩
  have hi (i j k : ι) := intervalIntegrable_indicator
    ((hc i j k).const_mul ((h^3:ℝ)*(A 0 i j*A 1 j k*A 2 k i))) (a := a i j) (b := b i j)
  simp_rw [maskedSigned_eq]
  rw [intervalIntegral.integral_finsetSum (fun i _ => intervalIntegrable_finsetSum _ (fun j _ => intervalIntegrable_finsetSum _ (fun k _ => hi i j k)))]
  unfold selectedSum
  apply Finset.sum_congr rfl
  intro i _
  rw [intervalIntegral.integral_finsetSum (fun j _ => intervalIntegrable_finsetSum _ (fun k _ => hi i j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_finsetSum (fun k _ => hi i j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [intervalIntegral_indicator_Ico (ha i j) (hab i j) (hb i j),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal]
  rfl

lemma maskedSigned_norm_le (A : Three → Matrix ι ι ℂ) {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) (a b : Matrix ι ι ℝ) :
    ‖maskedSigned A h u a b s‖ ≤ (440/3)*∑ r, maskedCost A a b h u r s := by
  have hn (r w : Three) : 0 ≤ planeIntegral (fun p => heatCost (maskedArray A a b s) h u p
      (fun z => strictRate r z*s) w w) 0 := integral_nonneg (fun _ => heatCost_nonneg _ _ _ _ _ _ _)
  have hb : (∑ v, planeIntegral (fun p => heatCost (maskedArray A a b s) h u p
      (fun z => strictRate v z*s) v v) 0) ≤ ∑ r, maskedCost A a b h u r s := by
    apply Finset.sum_le_sum
    intro v _
    exact Finset.single_le_sum (fun w _ => hn v w) (Finset.mem_univ v)
  unfold maskedSigned
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hs.le]
  apply (div_le_div_of_nonneg_right (signedCenter_norm_le _ hh hs u) hs.le).trans
  rw [mul_assoc,mul_div_assoc,mul_div_cancel_left₀ _ hs.ne']
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

lemma maskedCost_intervalIntegrable (A : Three → Matrix ι ι ℂ) (a b : Matrix ι ι ℝ)
    (S : Finset ℝ) (hS : S.Nonempty) (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    {h : ℝ} (hh : 0 < h) (u : ι → ℝ) (hL : 0 < S.min' hS) (r : Three) :
    IntervalIntegrable (maskedCost A a b h u r) volume (S.min' hS) (S.max' hS) := by
  have ht0 : 0 < sortedTimes S hS 0 := by simpa only [sortedTimes_zero] using hL
  have hi := IntervalIntegrable.trans_iterate (n := S.card-1)
    (fun k _ => maskedCost_interval_piece A a b S hS ha hb hh u ht0 r k)
  simpa only [sortedTimes_zero,sortedTimes_last] using hi

def selectedConstant : ℝ := (440/3)*3*maskedConstant/strictConstant
lemma selectedConstant_pos : 0 < selectedConstant := by
  unfold selectedConstant
  exact div_pos (mul_pos (by norm_num) maskedConstant_pos) strictConstant_pos

lemma selectedSum_le_cubic (D : Finset ℤ) (A : Three → Matrix D D ℂ) (a b : Matrix D D ℝ)
    (hab : ∀ i j, a i j ≤ b i j) (S : Finset ℝ) (hS : S.Nonempty)
    (ha : ∀ i j, a i j ∈ S) (hb : ∀ i j, b i j ∈ S)
    {h : ℝ} (hh : 0 < h) (hl : ∀ s ∈ S, h^2 ≤ s) :
    ‖selectedSum A h (fun m => h*(m:ℤ)) a b‖ ≤ selectedConstant*arrayCubic A h := by
  have hL : 0 < S.min' hS := (sq_pos_of_pos hh).trans_le (hl _ (Finset.min'_mem S hS))
  have hLU : S.min' hS ≤ S.max' hS := Finset.min'_le S _ (Finset.max'_mem S hS)
  have hi r := maskedCost_intervalIntegrable A a b S hS ha hb hh (fun m => h*(m:ℤ)) hL r
  rw [selectedSum_eq_integral A _ _ a b hL hLU
    (fun i j => Finset.min'_le _ _ (ha i j)) hab (fun i j => Finset.le_max' _ _ (hb i j))]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le hLU
    (Filter.Eventually.of_forall (fun s hs => maskedSigned_norm_le A hh (hL.trans hs.1) _ a b))
    ((intervalIntegrable_finsetSum _ (fun r _ => hi r)).const_mul (440/3:ℝ))
  apply hbound.trans
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum (fun r _ => hi r)]
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset Three)) =>
    masked_cost_integral_le D A a b hab S hS ha hb hh hl r)
  simp only [← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Three,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hs
  have hc : (∑ r, ∫ s in S.min' hS..S.max' hS, maskedCost A a b h (fun m => h*(m:ℤ)) r s) ≤
      (3*(maskedConstant*arrayCubic A h))/strictConstant :=
    (le_div_iff₀ strictConstant_pos).mpr (by nlinarith only [hs])
  unfold selectedConstant
  calc
    _ ≤ (440/3)*((3*(maskedConstant*arrayCubic A h))/strictConstant) :=
      mul_le_mul_of_nonneg_left hc (by norm_num)
    _ = _ := by ring
end
end TriangularHilbert.Heat
end

end OAI
