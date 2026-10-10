import OAI.MeasureTheory.SelfSimilar.SuffixLaw

namespace OAI

universe uι uα

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

noncomputable def wordAverage (S : System α) (n : ℕ) (f : List α → ℝ) : ℝ :=
  ∑ w : Fin n → α, S.wordWeight w*f (List.ofFn w)

theorem wordAverage_mono (S : System α) (n : ℕ) {f g : List α → ℝ}
    (h : ∀ W, W.length=n → f W ≤ g W) : S.wordAverage n f ≤ S.wordAverage n g := by
  exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left
    (h (List.ofFn w) (List.length_ofFn ..)) (S.wordWeight_pos w).le)

theorem wordAverage_const (S : System α) (n : ℕ) (c : ℝ) : S.wordAverage n (fun _ => c)=c := by
  rw [wordAverage,← Finset.sum_mul,S.wordWeight_sum,one_mul]

theorem wordAverage_mul (S : System α) (n : ℕ) (c : ℝ) (f : List α → ℝ) :
    S.wordAverage n (fun W => c*f W)=c*S.wordAverage n f := by
  simp only [wordAverage,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem wordAverage_finset_sum {ι : Type uι} (S : System α) (n : ℕ) (s : Finset ι) (f : ι → List α → ℝ) :
    S.wordAverage n (fun W => ∑ i ∈ s, f i W)=∑ i ∈ s, S.wordAverage n (f i) := by
  simp only [wordAverage,Finset.mul_sum]
  exact Finset.sum_comm

theorem wordAverage_append (S : System α) (m n : ℕ) (f : List α → ℝ) :
    S.wordAverage (m+n) f =
      ∑ u : Fin m → α, S.wordWeight u*∑ v : Fin n → α, S.wordWeight v*f (List.ofFn u++List.ofFn v) := by
  rw [wordAverage,sum_words_append]
  simp only [wordWeight_append,List.ofFn_fin_append,Finset.mul_sum,mul_assoc]

theorem wordAverage_future_le (S : System α) (m n : ℕ) (f g : List α → ℝ)
    (h : ∀ u : Fin m → α,
      (∑ v : Fin n → α, S.wordWeight v*f (List.ofFn u++List.ofFn v)) ≤
      ∑ v : Fin n → α, S.wordWeight v*g (List.ofFn u++List.ofFn v)) :
    S.wordAverage (m+n) f ≤ S.wordAverage (m+n) g := by
  rw [wordAverage_append,wordAverage_append]
  exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (h u) (S.wordWeight_pos u).le)

theorem wordAverage_segment (S : System α) {H j n : ℕ} (hH : j+n ≤ H) (f : List α → ℝ) :
    S.wordAverage H (fun W => f ((W.drop j).take n))=S.wordAverage n f := by
  classical
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hH
  rw [wordAverage_append]
  rw [sum_words_append j n]
  simp only [wordWeight_append,List.ofFn_fin_append]
  have he (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
      (((List.ofFn u++List.ofFn w)++List.ofFn z).drop j).take n=List.ofFn w := by
    have h1 : ((List.ofFn u++List.ofFn w)++List.ofFn z).drop j=List.ofFn w++List.ofFn z := by
      rw [List.append_assoc]
      simpa only [List.length_ofFn] using (List.drop_append_length (l₁ := List.ofFn u) (l₂ := List.ofFn w++List.ofFn z))
    rw [h1]
    simpa only [List.length_ofFn] using (List.take_append_length (l₁ := List.ofFn w) (l₂ := List.ofFn z))
  simp_rw [he,← Finset.sum_mul,S.wordWeight_sum,one_mul]
  simp only [mul_assoc,← Finset.mul_sum]
  rw [← Finset.sum_mul,S.wordWeight_sum,one_mul]
  rfl

end EntropyRateDimension.System

end OAI
