import OAI.Probability.MatroidProphet.Maximum.Basic
import OAI.Probability.MatroidProphet.GreedyOptimal
import OAI.Probability.MatroidProphet.Algorithm.Rule

namespace OAI

namespace MatroidProphet
lemma levelWeight_mono {B : ℝ} (hB : 1 < B) :
    Monotone (fun a : WithBot ℤ => levelWeight B a) := by
  intro a b hab
  cases a with
  | bot =>
    cases b with
    | bot => exact le_rfl
    | coe j => exact (zpow_pos (zero_lt_one.trans hB) j).le
  | coe i =>
    cases b with
    | bot => exact False.elim (WithBot.not_coe_le_bot i hab)
    | coe j => exact zpow_le_zpow_right₀ hB.le (WithBot.coe_le_coe.mp hab)

namespace Priority

def asLevel (x : Option ℤ) : WithBot ℤ := x

@[simp] lemma asLevel_none : asLevel none = ⊥ := rfl
@[simp] lemma asLevel_some (i : ℤ) : asLevel (some i) = (i : WithBot ℤ) := rfl

open Finset Set

variable {n : ℕ}

def Higher (a : Fin n → Option ℤ) (e f : Fin n) : Prop :=
  Maximum.higher (K := WithBot ℤ) (e, asLevel (a e)) (f, asLevel (a f))

noncomputable def earlier (a : Fin n → Option ℤ) (e : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun f => Higher a f e

noncomputable def time (a : Fin n → Option ℤ) (e : Fin n) : ℕ := (earlier a e).card

lemma higher_trans (a : Fin n → Option ℤ) {e f g : Fin n}
    (hef : Higher a e f) (hfg : Higher a f g) : Higher a e g :=
  Maximum.higher_trans hef hfg

lemma higher_irrefl (a : Fin n → Option ℤ) (e : Fin n) : ¬ Higher a e e :=
  Maximum.higher_irrefl _

lemma higher_total (a : Fin n → Option ℤ) {e f : Fin n} (hef : e ≠ f) :
    Higher a e f ∨ Higher a f e :=
  Maximum.higher_total (fun h => hef (congrArg Prod.fst h))

lemma time_lt_of_higher (a : Fin n → Option ℤ) {e f : Fin n} (hef : Higher a e f) :
    time a e < time a f := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro g hg
    simp only [earlier, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    exact higher_trans a hg hef
  · intro heq
    have he : e ∈ earlier a f := by simp [earlier, hef]
    rw [← heq] at he
    exact higher_irrefl a e (by simpa [earlier] using he)

lemma time_lt_iff_higher (a : Fin n → Option ℤ) (e f : Fin n) :
    time a e < time a f ↔ Higher a e f := by
  constructor
  · intro h
    by_cases hef : e = f
    · subst f
      exact False.elim (Nat.lt_irrefl _ h)
    · rcases higher_total a hef with hh | hh
      · exact hh
      · exact False.elim ((time_lt_of_higher a hh).not_gt h)
  · exact time_lt_of_higher a

lemma time_injective (a : Fin n → Option ℤ) : Function.Injective (time a) := by
  intro e f h
  by_contra hef
  rcases higher_total a hef with hh | hh
  · have := time_lt_of_higher a hh
    omega
  · have := time_lt_of_higher a hh
    omega

lemma time_lt_card (a : Fin n → Option ℤ) (e : Fin n) : time a e < n := by
  classical
  have hss : earlier a e ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have he : e ∈ earlier a e := heq.symm ▸ Finset.mem_univ e
    exact higher_irrefl a e (by simpa [earlier] using he)
  simpa [time] using Finset.card_lt_card hss

noncomputable def timeEquiv (a : Fin n → Option ℤ) : Fin n ≃ Fin n :=
  Equiv.ofBijective (fun e => ⟨time a e, time_lt_card a e⟩)
    (by
      have hi : Function.Injective (fun e => (⟨time a e, time_lt_card a e⟩ : Fin n)) :=
        fun e f h => time_injective a (congrArg Fin.val h)
      exact ⟨hi, Finite.surjective_of_injective hi⟩)

noncomputable def order (a : Fin n → Option ℤ) : ArrivalOrder n := (timeEquiv a).symm

@[simp] lemma priorityTime_order (a : Fin n → Option ℤ) :
    Candidates.priorityTime (order a) = time a := rfl

lemma main_higher_iff (a : Fin n → Option ℤ) (e f : Fin n) (hf : a f ≠ none) :
    MainAlgorithm.higher e (a e) f (a f) ↔ Higher a e f := by
  cases heq : a e with
  | none => cases hfq : a f <;> simp_all [MainAlgorithm.higher, Higher, Maximum.higher]
  | some i => cases hfq : a f <;> simp_all [MainAlgorithm.higher, Higher, Maximum.higher, eq_comm]

lemma main_higher_iff_time (a : Fin n → Option ℤ) (e f : Fin n) (hf : a f ≠ none) :
    MainAlgorithm.higher e (a e) f (a f) ↔ time a e < time a f :=
  (main_higher_iff a e f hf).trans (time_lt_iff_higher a e f).symm

lemma higher_key_le (a : Fin n → Option ℤ) {e f : Fin n} (h : Higher a e f) :
    asLevel (a f) ≤ asLevel (a e) := by
  rcases h with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.symm.le

lemma order_antitone_levelWeight (a : Fin n → Option ℤ) {B : ℝ} (hB : 1 < B) :
    Antitone (fun i => levelWeight B (a (order a i))) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · apply levelWeight_mono hB
    apply higher_key_le a
    apply (time_lt_iff_higher a _ _).1
    have htime (k : Fin n) : time a (order a k) = k.val := by
      have h := congrArg Fin.val ((timeEquiv a).apply_symm_apply k)
      exact h
    simpa only [htime] using (show i.val < j.val from hij)
  · exact le_rfl

lemma rounded_greedy_optimal (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) {B : ℝ} (hB : 1 < B) :
    (∑ e ∈ Candidates.greedy M (time (fun e => roundedLevel B (w e))) Finset.univ,
      roundedWeight B (w e)) = optimum M (fun e => roundedWeight B (w e)) := by
  have h := Candidates.greedy_weight_eq_optimum M hE (fun e => roundedWeight B (w e))
    (fun e => roundedWeight_nonneg (zero_lt_one.trans hB) (w e))
    (order (fun e => roundedLevel B (w e)))
    (order_antitone_levelWeight (fun e => roundedLevel B (w e)) hB)
  simpa only [priorityTime_order] using h

end Priority
end MatroidProphet

end OAI
