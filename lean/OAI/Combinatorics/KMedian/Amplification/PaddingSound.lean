import Mathlib
import OAI.Combinatorics.KMedian.Amplification.TestSum
import OAI.Combinatorics.KMedian.Expanders.GraphExtend

namespace OAI

section Inline_PCPPaddingSound

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

lemma testSum_embedding {S T : Type} [Fintype S] [Fintype T] (e : S ↪ T)
    (p : S → Prop) (q : T → Prop) (hi : ∀ s, q (e s) ↔ p s)
    (ho : ∀ t, t ∉ Set.range e → ¬q t) : testSum q=testSum p := by
  calc
    testSum q = ∑ t ∈ univ.map e, if q t then (1:ℝ) else 0 := by
      symm
      apply sum_subset (subset_univ _)
      intro t _ ht
      have hn : t ∉ Set.range e := by
        rintro ⟨s,rfl⟩
        exact ht (mem_map.mpr ⟨s,mem_univ _,rfl⟩)
      exact ite_eq_right (ho t hn)
    _ = testSum p := by
      rw [sum_map]
      unfold testSum
      apply sum_congr rfl
      intro s _
      simp only [hi s]

namespace PortCSP
variable {V W D A : Type} [Fintype V] [Nonempty V] [Fintype W] [Nonempty W]
  [Fintype D] [Nonempty D] [DecidableEq W] [DecidableEq D] [Fintype A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) (e : V ↪ W)

omit [Nonempty V] [Fintype W] [Nonempty W] [Nonempty D] [DecidableEq A] in
lemma extend_bad_outside (a : W → A) (p : W × D) (hp : p.1 ∉ Set.range e) :
    ¬ (C.extend e).Bad a p := by
  change ¬ (_ ∉ C.extendedAllowed e p)
  rw [C.extendedAllowed_outside e p hp]
  simp

omit [DecidableEq A] in
lemma extend_failure_mass (a : W → A) :
    (Fintype.card W:ℝ)*testRate ((C.extend e).Bad a) =
      (Fintype.card V:ℝ)*testRate (C.Bad (a ∘ e)) := by
  have h := testSum_embedding (PortGraph.portEmbed e)
    (C.Bad (a ∘ e)) ((C.extend e).Bad a)
    (C.extend_bad_image e a)
    (fun p hp => C.extend_bad_outside e a p (fun hv => hp ((PortGraph.portEmbed_range e p).mpr hv)))
  rw [testSum_card_rate,testSum_card_rate,Fintype.card_prod,Fintype.card_prod,Nat.cast_mul,Nat.cast_mul] at h
  have hd : (Fintype.card D:ℝ)≠0 := by positivity
  apply (mul_right_cancel₀ hd)
  nlinarith only [h]

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPaddingSound

end OAI
