import OAI.Probability.SignedSweeps.SweepRecurrence
import OAI.Probability.SignedSweeps.BalancedErrors

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

lemma coefficient_mono_depth {η : ℝ} (hη : 0 ≤ η) {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) : coefficient η a ≤ coefficient η b := by
  have hroot : 0 < Real.sqrt a := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < a by omega))
  have hroots : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt (by exact_mod_cast hab)
  have hi := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 2*Real.sqrt a)
    (mul_le_mul_of_nonneg_left hroots (by norm_num : (0:ℝ) ≤ 2))
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left hi 1) hη

lemma signed_sweep_recurrence_depth_sum {d a b j q R : ℕ} (hab : a+b=d) (hq : 0 < q)
    {η τ κ : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1) (hκ : 0 ≤ κ) (hκτ : κ ≤ τ)
    (HA : ∀ (lam : Partition (2^a)) (u v l : ℕ) (h : u+v+l=2^a)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      SignedOccurrence h α β γ lam → weightedMoment lam (2^j) ≤
        Real.exp (η*signedEntropy α β+clippedBudget τ (2^a) l))
    (HB : ∀ (lam : Partition (2^b)) (u v l : ℕ) (h : u+v+l=2^b)
      (α : Partition u) (β : Partition v) (γ : Partition l),
      SignedOccurrence h α β γ lam → weightedMoment lam (2^j) ≤
        Real.exp (η*signedEntropy α β+clippedBudget τ (2^b) l))
    (hR : 2*max (2^a) (2^b)+2*q+1 ≤ R)
    (lam : Partition (2^d)) (u v l : ℕ) (h : u+v+l=2^d)
    (α : Partition u) (β : Partition v) (γ : Partition l)
    (hα : α.1.colLen 0 ≤ q) (hβ : β.1.colLen 0 ≤ q)
    (ho : SignedOccurrence h α β γ lam) :
    weightedMoment lam (2^j) ≤ Real.exp (η*signedEntropy α β+
      τ*l*Real.log (2^d : ℕ)-(l:ℝ)*Real.log ((2^d : ℕ)/ (l:ℝ))+6*l+
      (2^b : ℕ)*typedLineError (2^a) q R+(2^a : ℕ)*typedLineError (2^b) q R+
      holeClippingError κ (2^a) (2^b)+((2^a : ℕ)+(2^b : ℕ) : ℝ)*Real.log (l+1)) := by
  subst d
  exact signed_sweep_recurrence hq hη hη' hκ hκτ HA HB hR lam u v l h α β γ hα hβ ho

theorem signed_occurrence_moment_bound_fixed {η κ : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hκ : 0 < κ) (hsmall : κ < η/256) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ d : ℕ, 1 ≤ d →
      ∀ lam : Partition (2^d), ∀ (u v l : ℕ) (h : u+v+l=2^d)
        (α : Partition u) (β : Partition v) (γ : Partition l),
        SignedOccurrence h α β γ lam →
        logMoment (weightedMoment lam r) ≤
          ((coefficient η d*signedEntropy α β+remainderBudget κ d l : ℝ) : EReal) := by
  let ξ : ℝ := min (1/64) (κ/16)
  let δ : ℝ := ξ/4
  have hξ : 0 < ξ := lt_min (by norm_num) (by positivity)
  have hξ₁ : ξ < 1/10 := (min_le_left _ _).trans_lt (by norm_num)
  have hξ₂ : ξ < κ/6 := (min_le_right _ _).trans_lt (by nlinarith)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  have hδξ : δ < ξ := by dsimp [δ]; linarith
  obtain ⟨D₁,hD₁,herr⟩ := balanced_recurrence_error_eventually hκ hξ₁ hξ₂
  obtain ⟨D₂,_hD₂,hclose⟩ := nonsparse_closing_budget hη hκ (by norm_num : (0:ℝ) ≤ 6) hδ1 hδξ
  obtain ⟨D₃,_hD₃,hcost⟩ := truncation_coefficient_eventually hη hκ.le
    (by norm_num : (0:ℝ) < 1/64) (by nlinarith : κ < η*((1:ℝ)/64)/2)
  let D := max D₁ (max D₂ D₃)
  obtain ⟨r₀,_hr₀,hbase⟩ := signed_occurrence_moment_bound_proved_ranges D hδ hη.le κ
  have hr : r₀ ≤ 2^r₀ := Nat.lt_two_pow_self.le
  refine ⟨2^r₀, Nat.one_le_pow r₀ 2 (by decide), ?_⟩
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    by_cases hdD : d ≤ D
    · intro lam u v l h α β γ ho
      exact hbase (2^r₀) hr d hd lam (Or.inl hdD) u v l h α β γ ho
    have hlarge : D ≤ d := le_of_not_ge hdD
    have hd10 : 10 ≤ d := hD₁.trans ((le_max_left _ _).trans hlarge)
    have hd₁ : D₁ ≤ d := (le_max_left _ _).trans hlarge
    have hd₂ : D₂ ≤ d := (le_max_left D₂ D₃).trans ((le_max_right _ _).trans hlarge)
    have hd₃ : D₃ ≤ d := (le_max_right D₂ D₃).trans ((le_max_right _ _).trans hlarge)
    have hab : d/2+childDepth d=d := (balanced_depth_sizes hd10).1
    have ha1 : 1 ≤ d/2 := by omega
    have hb1 : 1 ≤ childDepth d := by unfold childDepth; omega
    have hab' : d/2 ≤ childDepth d := by unfold childDepth; omega
    have had : d/2 < d := by omega
    have hbd : childDepth d < d := by omega
    have hlocal (e : ℕ) (he1 : 1 ≤ e) (heb : e ≤ childDepth d) (hed : e < d) :
        ∀ (lam : Partition (2^e)) (u v l : ℕ) (h : u+v+l=2^e)
          (α : Partition u) (β : Partition v) (γ : Partition l),
          SignedOccurrence h α β γ lam → weightedMoment lam (2^r₀) ≤
            Real.exp (coefficient η (childDepth d)*signedEntropy α β+
              clippedBudget (coefficient κ (childDepth d)) (2^e) l) := by
      intro lam u v l h α β γ ho
      have hi := (logMoment_le_iff (weightedMoment_nonneg lam (2^r₀))).mp
        (ih e hed he1 lam u v l h α β γ ho)
      rw [remainderBudget_eq_clippedBudget] at hi
      apply hi.trans (Real.exp_le_exp.mpr _)
      exact add_le_add (mul_le_mul_of_nonneg_right (coefficient_mono_depth hη.le he1 heb)
        (signedEntropy_nonneg α β))
        (clippedBudget_mono (coefficient_mono_depth hκ.le he1 heb) (Nat.one_le_pow e 2 (by decide)))
    have HA := hlocal (d/2) ha1 hab' had
    have HB := hlocal (childDepth d) hb1 le_rfl hbd
    have hηc : 0 ≤ coefficient η (childDepth d) :=
      (by positivity : (0:ℝ) ≤ η/2).trans (coefficient_bounds hη.le hb1).1
    have hηc1 : coefficient η (childDepth d) ≤ 1 := (coefficient_bounds hη.le hb1).2.trans hη1.le
    have hκc : κ/2 ≤ coefficient κ (childDepth d) := (coefficient_bounds hκ.le hb1).1
    have hR : 2*max (2^(d/2)) (2^(childDepth d))+2*sweepColors d+1 ≤ 16*2^d := by
      have haN : 2^(d/2) ≤ 2^d := Nat.pow_le_pow_right (by decide) had.le
      have hbN : 2^(childDepth d) ≤ 2^d := Nat.pow_le_pow_right (by decide) hbd.le
      have hqN := sweepColors_le_size d
      have hn : 1 ≤ 2^d := Nat.one_le_pow d 2 (by decide)
      have hmax : max (2^(d/2)) (2^(childDepth d)) ≤ 2^d := max_le haN hbN
      omega
    apply signed_moment_of_bounded_lengths hη.le hκ.le hd (sweepColors_pos d) (hcost d hd₃)
    intro lam u v l h α β γ hα hβ ho
    by_cases hk : ((2^d-lam.1.rowLen 0 : ℕ):ℝ) ≤ ((2^d:ℕ):ℝ)^(1-δ)
    · exact hbase (2^r₀) hr d hd lam (Or.inr (Or.inl hk)) u v l h α β γ ho
    by_cases hc : 2^d/2 < lam.1.colLen 0
    · exact hbase (2^r₀) hr d hd lam (Or.inr (Or.inr (Or.inr hc))) u v l h α β γ ho
    have hcol : lam.1.colLen 0 ≤ 2^d/2 := le_of_not_gt hc
    have hlevel : ((2^d:ℕ):ℝ)^(1-δ) ≤ ((2^d-lam.1.rowLen 0 : ℕ):ℝ) := (lt_of_not_ge hk).le
    have hlengthα : α.1.colLen 0 ≤ sweepColors d := by simpa only [YoungDiagram.length_rowLens] using hα
    have hlengthβ : β.1.colLen 0 ≤ sweepColors d := by simpa only [YoungDiagram.length_rowLens] using hβ
    have hrec := signed_sweep_recurrence_depth_sum hab (sweepColors_pos d) hηc hηc1
      (by positivity : (0:ℝ) ≤ κ/2) hκc HA HB hR lam u v l h α β γ hlengthα hlengthβ ho
    have he := herr d hd₁ l (by omega)
    have hb := hclose d hd₂ lam hcol hlevel u v l h α β γ ho
    apply (logMoment_le_iff (weightedMoment_nonneg lam (2^r₀))).mpr
    apply hrec.trans (Real.exp_le_exp.mpr _)
    have hn : 0 ≤ ((2^d:ℕ):ℝ)^(1-ξ) := Real.rpow_nonneg (by positivity) _
    linarith

theorem signed_occurrence_moment_bound :
    ∃ η₀ : ℝ, 0 < η₀ ∧
      ∀ η : ℝ, 0 < η → η < η₀ →
        ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ < η / 256 ∧
          ∀ κ : ℝ, 0 < κ → κ < κ₀ →
            ∃ r : ℕ, 1 ≤ r ∧
              ∀ d : ℕ, 1 ≤ d →
                ∀ lam : Partition (2 ^ d),
                  ∀ (u v l : ℕ) (h : u + v + l = 2 ^ d)
                    (α : Partition u) (β : Partition v) (γ : Partition l),
                    SignedOccurrence h α β γ lam →
                      logMoment (weightedMoment lam r) ≤
                        ((coefficient η d * signedEntropy α β +
                            remainderBudget κ d l : ℝ) : EReal) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro η hη hη1
  refine ⟨η/512, by positivity, by linarith, ?_⟩
  intro κ hκ hκsmall
  exact signed_occurrence_moment_bound_fixed hη hη1 hκ (by linarith)

end SignedSweeps
end

end OAI
