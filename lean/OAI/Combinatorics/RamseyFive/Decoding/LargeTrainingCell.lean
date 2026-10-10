import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.Training

namespace OAI

namespace SharpRamseyFive.GreedyTraining
open scoped Classical
variable {A I : Type*} [DecidableEq A] [LinearOrder I]

theorem large_clipped_part (X S Y : Finset A) (hSX : S⊆X)
    (hret : X.card≤4*S.card) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (J : ℕ)
    (h : ¬∀i,(clippedPart S F hF shape Y J i).card≤(S.card:ℝ)/25) :
    ∃a∈F,(X.card:ℝ)≤100*(X∩shape a).card := by
  obtain ⟨i,hi⟩ := not_forall.mp h
  have hlarge := lt_of_not_ge hi
  cases i with
  | none =>
    simp only [clippedPart,Finset.card_empty,Nat.cast_zero] at hlarge
    have hn : (0:ℝ)≤(S.card:ℝ)/25 := by positivity
    exact False.elim (not_lt_of_ge hn hlarge)
  | some i =>
    refine ⟨chosen F hF shape Y i,chosen_mem F hF shape Y i,?_⟩
    have hsub : clippedPart S F hF shape Y J (some i)⊆X∩shape (chosen F hF shape Y i) := by
      intro a ha
      have hm := Finset.mem_inter.mp ha
      exact Finset.mem_inter.mpr ⟨hSX hm.1,(Finset.mem_inter.mp hm.2).2⟩
    have hc : ((clippedPart S F hF shape Y J (some i)).card:ℝ)≤(X∩shape (chosen F hF shape Y i)).card := by
      exact_mod_cast Finset.card_le_card hsub
    have hr : (X.card:ℝ)≤4*S.card := by exact_mod_cast hret
    nlinarith only [hc,hr,hlarge]

end SharpRamseyFive.GreedyTraining

end OAI
