import OAI.MeasureTheory.SelfSimilar.WindowGain

namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs Windows
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem total_expected_drop_le (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hc : CompactlyCarried μ)
    {M : ℕ} (hM : 0 < M) (H : ℕ) {q : ℕ} (n K : Fin q → ℕ) (a B : Fin q → ℤ) (A' : ℝ)
    (hsep : ∀ i h : Fin q, h < i → (B h : ℝ)<(a i : ℝ)-A'*n i-1) (L : ℤ) :
    (∑ i, ∑ k ∈ Finset.range (K i), S.wordAverage H (fun W =>
      retainedDrop S tag μ M A' (n i) (a i) (B i) L W (k*n i))) ≤ Real.log ((M*M : ℕ) : ℝ) := by
  classical
  have hs : 0 < (2 : ℝ)^(-L)/(M : ℝ) := div_pos (zpow_pos (by norm_num) _) (by exact_mod_cast hM)
  have hMM : 0 < M*M := Nat.mul_pos hM hM
  simp_rw [← S.wordAverage_finset_sum]
  calc
    _ ≤ S.wordAverage H (fun _ => Real.log ((M*M : ℕ) : ℝ)) := by
      apply S.wordAverage_mono
      intro W _
      have hh := retained_sum_le n K a B A' hsep (fun j => S.listDepth (W.take j))
        (S.listDepth_monotone W) L (suffixWindow S tag μ ((2 : ℝ)^(-L)/(M : ℝ)) (M*M) W)
        (suffixWindow_antitone S tag hr μ hc hs hMM W)
        (fun j => (suffixWindow_bounds S tag μ hc hs hMM W j).1)
      exact hh.trans (suffixWindow_bounds S tag μ hc hs hMM W 0).2
    _ = _ := S.wordAverage_const _ _

theorem count_pair_budget_le (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) {δ : ℝ}
    (hδ : ∀ v, 0 < v → δ ≤ deficit μ v) {M : ℕ} (hM : 4 < M)
    (he : 5/(M : ℝ)*Real.log 2 ≤ δ/2)
    {H D q : ℕ} (hD : 1 ≤ D) (hd : ∀ v, S.letterDepth v ≤ D)
    (n K : Fin q → ℕ) (a B : Fin q → ℤ) (A' : ℝ)
    (hkn : ∀ i, K i*n i=H) (ha : ∀ i, 1 ≤ a i) (hB : ∀ i, B i ≤ (H : ℤ))
    (hsep : ∀ i h : Fin q, h < i → (B h : ℝ)<(a i : ℝ)-A'*n i-1) :
    (δ/2)*(∑ i, (K i : ℝ)*pairBudget S tag A' (a i) (B i) (n i)) ≤
      (2*D*H : ℕ)*Real.log ((M*M : ℕ) : ℝ) := by
  classical
  let T : ℤ := (2*D*H : ℕ)
  have hkH (i : Fin q) (k : ℕ) (hk : k ∈ Finset.range (K i)) : k*n i+n i ≤ H := by
    rw [← Nat.succ_mul,← hkn i]
    exact Nat.mul_le_mul_right _ (Finset.mem_range.mp hk)
  have hcover (i : Fin q) (k : ℕ) (hk : k ∈ Finset.range (K i)) (W : List α) :
      0 ≤ ⌈S.listDepth (W.take (k*n i))⌉ ∧ B i+⌈S.listDepth (W.take (k*n i))⌉ ≤ T := by
    refine ⟨Int.ceil_nonneg (S.listDepth_nonneg _),?_⟩
    have hh : S.listDepth (W.take (k*n i)) ≤ ((D*H : ℕ) : ℝ) := by
      have h1 := S.listDepth_take_le (Nat.cast_nonneg D) hd W (k*n i)
      have h2 : k*n i ≤ H := (Nat.le_add_right _ _).trans (hkH i k hk)
      have h2R : ((k*n i : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h2
      exact h1.trans (by simpa only [Nat.cast_mul] using
        mul_le_mul_of_nonneg_left h2R (Nat.cast_nonneg D))
    have hh' : ⌈S.listDepth (W.take (k*n i))⌉ ≤ ((D*H : ℕ) : ℤ) := by
      apply Int.ceil_le.mpr
      exact_mod_cast hh
    have hDH : H ≤ D*H := by simpa only [one_mul] using Nat.mul_le_mul_right H hD
    dsimp only [T]
    have hDH' : (H : ℤ) ≤ ((D*H : ℕ) : ℤ) := by exact_mod_cast hDH
    have hmul : ((2*D*H : ℕ) : ℤ)=2*((D*H : ℕ) : ℤ) := by push_cast; ring
    rw [hmul]
    linarith [hB i]
  have hlocal (i : Fin q) (k : ℕ) (hk : k ∈ Finset.range (K i)) :
      (δ/2)*pairBudget S tag A' (a i) (B i) (n i) ≤
      ∑ L ∈ Finset.Icc 1 T, S.wordAverage H (fun W => retainedDrop S tag μ M A' (n i) (a i) (B i) L W (k*n i)) := by
    rw [← expected_capacity_targets S tag (hkH i k hk) A' (a i) (B i) T (ha i) (hcover i k hk),Finset.mul_sum]
    exact Finset.sum_le_sum (fun L _ => expected_retained_gain S tag hr μ hμ hc hδ hM he
      (hkH i k hk) A' (a i) (B i) L)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.range (K i)) (fun k hk => hlocal i k hk))
  have hup : (∑ i, ∑ k ∈ Finset.range (K i), ∑ L ∈ Finset.Icc 1 T,
      S.wordAverage H (fun W => retainedDrop S tag μ M A' (n i) (a i) (B i) L W (k*n i))) ≤
      (2*D*H : ℕ)*Real.log ((M*M : ℕ) : ℝ) := by
    calc
      _ = ∑ L ∈ Finset.Icc 1 T, ∑ i, ∑ k ∈ Finset.range (K i),
          S.wordAverage H (fun W => retainedDrop S tag μ M A' (n i) (a i) (B i) L W (k*n i)) := by
        simp_rw [Finset.sum_comm (s := Finset.range _) (t := Finset.Icc 1 T)]
        exact Finset.sum_comm
      _ ≤ ∑ L ∈ Finset.Icc 1 T, Real.log ((M*M : ℕ) : ℝ) := Finset.sum_le_sum (fun L _ =>
        total_expected_drop_le S tag hr μ hc (by omega) H n K a B A' hsep L)
      _ = _ := by
        have hcard : (Finset.Icc (1 : ℤ) T).card=2*D*H := by
          simp only [Int.card_Icc,add_sub_cancel_right,T,Int.toNat_natCast]
        rw [Finset.sum_const,hcard,nsmul_eq_mul]
  apply le_trans _ hup
  convert hsum using 1
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end EntropyRateDimension.Typed

end OAI
