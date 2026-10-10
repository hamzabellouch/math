import OAI.NumberTheory.JointDickman.Counting.RealPeriodicMoments

namespace OAI

/-! # Uniform periodic means under finitely many interval cutoffs -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem real_periodic_prefix_error {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ a, |f a| ≤ C) (N : ℕ) :
    |(∑ n ∈ range N, f n) - (N : ℝ)*((∑ a, f a)/(q : ℝ))| ≤ (q : ℝ)*C := by
  by_cases hN : N = 0
  · simp only [hN,range_zero,sum_empty,Nat.cast_zero,zero_mul,sub_self,abs_zero]
    positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  let fc : ZMod q → ℂ := fun a => f a
  have hfc : ‖fc‖ ≤ C := (pi_norm_le_iff_of_nonneg hC).mpr (fun a => by
    simpa only [fc,Complex.norm_real,Real.norm_eq_abs] using hf a)
  have herr := periodicAverage_error fc (Nat.pos_of_ne_zero hN)
  have heq : periodicAverage fc N-residueMean fc =
      (((∑ n ∈ range N, f n)/(N : ℝ)-(∑ a, f a)/(q : ℝ) : ℝ) : ℂ) := by
    simp [periodicAverage,residueMean,fc]
  rw [heq,Complex.norm_real,Real.norm_eq_abs] at herr
  have hh := mul_le_mul_of_nonneg_right herr hNr.le
  have halg : |(∑ n ∈ range N, f n)-(N : ℝ)*((∑ a, f a)/(q : ℝ))| =
      |(∑ n ∈ range N, f n)/(N : ℝ)-(∑ a, f a)/(q : ℝ)| * (N : ℝ) := by
    calc
      _ = |((∑ n ∈ range N, f n)/(N : ℝ)-(∑ a, f a)/(q : ℝ))*(N : ℝ)| := by
        congr 1
        field_simp
      _ = _ := by rw [abs_mul,abs_of_pos hNr]
  rw [halg]
  calc
    _ ≤ ((q : ℝ)*‖fc‖/(N : ℝ))*(N : ℝ) := hh
    _ = (q : ℝ)*‖fc‖ := div_mul_cancel₀ _ hNr.ne'
    _ ≤ (q : ℝ)*C := mul_le_mul_of_nonneg_left hfc (Nat.cast_nonneg q)

theorem real_periodic_interval_error {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ a, |f a| ≤ C)
    {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Ico a b, f n) - ((b-a : ℕ) : ℝ)*((∑ x, f x)/(q : ℝ))| ≤ 2*q*C := by
  have ha := real_periodic_prefix_error f hC hf a
  have hb := real_periodic_prefix_error f hC hf b
  rw [sum_Ico_eq_sub _ hab,Nat.cast_sub hab]
  calc
    _ = |((∑ n ∈ range b, f n)-(b : ℝ)*((∑ x, f x)/(q : ℝ)))-
        ((∑ n ∈ range a, f n)-(a : ℝ)*((∑ x, f x)/(q : ℝ)))| := by congr 1; ring
    _ ≤ |(∑ n ∈ range b, f n)-(b : ℝ)*((∑ x, f x)/(q : ℝ))|+
        |(∑ n ∈ range a, f n)-(a : ℝ)*((∑ x, f x)/(q : ℝ))| := abs_sub _ _
    _ ≤ (q : ℝ)*C+(q : ℝ)*C := add_le_add hb ha
    _ = _ := by ring

theorem finite_nat_convex_eq_interval (S : Finset ℕ)
    (hc : ∀ a ∈ S, ∀ b ∈ S, ∀ n, a ≤ n → n ≤ b → n ∈ S) :
    ∃ a b, a ≤ b ∧ S = Ico a b := by
  by_cases hs : S.Nonempty
  · refine ⟨S.min' hs,S.max' hs+1,?_,?_⟩
    · exact (min'_le S _ (max'_mem S hs)).trans (Nat.le_succ _)
    · ext n
      constructor
      · intro hn
        exact mem_Ico.mpr ⟨min'_le S n hn,Nat.lt_succ_of_le (le_max' S n hn)⟩
      · intro hn
        obtain ⟨hlo,hhi⟩ := mem_Ico.mp hn
        exact hc _ (min'_mem S hs) _ (max'_mem S hs) n hlo (Nat.le_of_lt_succ hhi)
  · exact ⟨0,0,le_rfl,by simp [not_nonempty_iff_eq_empty.mp hs]⟩

/-- Only the boundary error depends on the number of cutoff profiles.
The main term retains the uniform mean bound E. -/
theorem periodic_interval_profile_bound {q : ℕ} [NeZero q]
    {α : Type*} [Fintype α] (F : α → ZMod q → ℝ)
    {C E : ℝ} (hC : 0 ≤ C) (hF : ∀ a r, |F a r| ≤ C)
    (hmean : ∀ a, (∑ r, F a r)/(q : ℝ) ≤ E)
    (profile : ℕ → α)
    (hconv : ∀ u v w, u ≤ v → v ≤ w → profile u = profile w → profile v = profile u)
    (N : ℕ) :
    (∑ n ∈ range N, F (profile n) n) ≤
      (N : ℝ)*E+(Fintype.card α : ℝ)*(2*q*C) := by
  let S : α → Finset ℕ := fun a => (range N).filter (fun n => profile n = a)
  have hlocal (a : α) : (∑ n ∈ S a, F a n) ≤ (S a).card*E+2*q*C := by
    obtain ⟨lo,hi,hle,hI⟩ := finite_nat_convex_eq_interval (S a) (by
      intro u hu w hw v huv hvw
      obtain ⟨huN,hua⟩ := mem_filter.mp hu
      obtain ⟨hwN,hwa⟩ := mem_filter.mp hw
      exact mem_filter.mpr ⟨mem_range.mpr (hvw.trans_lt (mem_range.mp hwN)),
        (hconv u v w huv hvw (hua.trans hwa.symm)).trans hua⟩)
    rw [hI,Nat.card_Ico]
    have herr := (le_abs_self _).trans (real_periodic_interval_error (F a) hC (hF a) hle)
    have hm := mul_le_mul_of_nonneg_left (hmean a) (Nat.cast_nonneg (hi-lo))
    linarith
  have hsum : (∑ a, ∑ n ∈ S a, F a n) = ∑ n ∈ range N, F (profile n) n := by
    dsimp only [S]
    convert sum_fiberwise_of_maps_to (g := profile) (s := range N) (t := univ)
      (fun _ _ => mem_univ _) (fun n => F (profile n) n) using 1
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro n hn
    rw [(mem_filter.mp hn).2]
  have hcard : (∑ a, (S a).card) = N := by
    exact (card_eq_sum_card_fiberwise (s := range N) (t := univ) (f := profile)
      (fun _ _ => mem_univ _)).symm.trans (card_range N)
  rw [← hsum]
  calc
    _ ≤ ∑ a, ((S a).card*E+2*q*C) := sum_le_sum (fun a _ => hlocal a)
    _ = (N : ℝ)*E+(Fintype.card α : ℝ)*(2*q*C) := by
      rw [sum_add_distrib,← sum_mul,← Nat.cast_sum,hcard]
      simp

end JointDickman

end OAI
