import OAI.NumberTheory.JointDickman.Amplification.MajorArcFiniteSum

namespace OAI

/-! # Summing the coefficient approximation error over the actual reduced arcs -/

namespace JointDickman
open Finset MeasureTheory

theorem positiveDenominators_card_le (N : ℕ) : (positiveDenominators N).card ≤ N+1 := by
  exact (Finset.card_subtype (fun n : ℕ => 0 < n) (range (N+1))).trans_le
    ((card_filter_le _ _).trans_eq (card_range _))

theorem total_reducedArc_count_le (N j : ℕ) [NeZero j] :
    (∑ q ∈ positiveDenominators N,
      ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then (1 : ℝ) else 0) ≤
        (j : ℝ)*N*(N+1) := by
  simp_rw [reducedArc_lift_count]
  calc
    _ ≤ ∑ _q ∈ positiveDenominators N, (j : ℝ)*N := by
      apply sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg j)
      exact_mod_cast (Nat.totient_le (n := (q : ℕ))).trans
        ((mem_positiveDenominators N q).mp hq)
    _ = ((positiveDenominators N).card : ℝ)*((j : ℝ)*N) := by simp
    _ ≤ (N+1)*((j : ℝ)*N) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast positiveDenominators_card_le N
    _ = _ := by ring

theorem reducedArc_sum_error (N j : ℕ) [NeZero j]
    (A C : (q : ℕ+) → ZMod (j*(q : ℕ)) → ℂ) {E : ℝ} (hE : 0 ≤ E)
    (herror : ∀ q ∈ positiveDenominators N, ∀ h : ZMod (j*(q : ℕ)),
      h.val.Coprime (q : ℕ) → ‖A q h-C q h‖ ≤ E) :
    ‖(∑ q ∈ positiveDenominators N, ∑ h : ZMod (j*(q : ℕ)),
        if h.val.Coprime (q : ℕ) then A q h else 0)-
      (∑ q ∈ positiveDenominators N, ∑ h : ZMod (j*(q : ℕ)),
        if h.val.Coprime (q : ℕ) then C q h else 0)‖ ≤ (j : ℝ)*N*(N+1)*E := by
  classical
  have heq : (∑ q ∈ positiveDenominators N, ∑ h : ZMod (j*(q : ℕ)),
        if h.val.Coprime (q : ℕ) then A q h else 0)-
      (∑ q ∈ positiveDenominators N, ∑ h : ZMod (j*(q : ℕ)),
        if h.val.Coprime (q : ℕ) then C q h else 0) =
      ∑ q ∈ positiveDenominators N, ∑ h : ZMod (j*(q : ℕ)),
        if h.val.Coprime (q : ℕ) then A q h-C q h else 0 := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro q _
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro h _
    split_ifs <;> simp
  rw [heq]
  calc
    _ ≤ ∑ q ∈ positiveDenominators N,
        ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then E else 0 := by
      refine (norm_sum_le _ _).trans (sum_le_sum (fun q hq => ?_))
      refine (norm_sum_le _ _).trans (sum_le_sum (fun h _ => ?_))
      split_ifs with hh
      · exact herror q hq h hh
      · simp
    _ = (∑ q ∈ positiveDenominators N,
        ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then (1 : ℝ) else 0)*E := by
      simp only [sum_mul]
      apply sum_congr rfl
      intro q _
      apply sum_congr rfl
      intro h _
      split_ifs <;> simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (total_reducedArc_count_le N j) hE

theorem weighted_interval_error {a b M E : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    {f g h : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hbound : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M)
    (herror : ∀ x ∈ Set.Icc a b, ‖g x-h x‖ ≤ E) :
    ‖(∫ x in a..b, f x*g x)-(∫ x in a..b, f x*h x)‖ ≤ (b-a)*M*E := by
  rw [← intervalIntegral.integral_sub (f := fun x => f x*g x) (g := fun x => f x*h x)
    ((hf.mul hg).intervalIntegrable a b) ((hf.mul hh).intervalIntegrable a b)]
  have heq : (fun x => f x*g x-f x*h x) = fun x => f x*(g x-h x) := by
    funext x
    ring
  rw [heq]
  have he := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (C := M*E) (f := fun x => f x*(g x-h x)) (fun x hx => by
      have hx' : x ∈ Set.Icc a b := Set.uIcc_of_le hab ▸ Set.uIoc_subset_uIcc hx
      rw [norm_mul]
      exact mul_le_mul (hbound x hx') (herror x hx') (norm_nonneg _) hM)
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab),mul_assoc,mul_comm (M*E)] using he

end JointDickman

end OAI
