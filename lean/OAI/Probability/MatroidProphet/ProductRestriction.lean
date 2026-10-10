import OAI.Probability.MatroidProphet.FiniteBits

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

theorem bitsExpectation_restrict (q : α → ℝ) (W V : Finset α) (hV : V ⊆ W)
    (f : Finset α → ℝ)
    (hf : ∀ S S', (∀ e ∈ V, e ∈ S ↔ e ∈ S') → f S = f S') :
    bitsExpectation q W f = bitsExpectation q V f := by
  induction W using Finset.strongInductionOn with
  | _ W ih =>
    by_cases hW : W ⊆ V
    · rw [subset_antisymm hW hV]
    · obtain ⟨e, heW, heV⟩ := Finset.not_subset.mp hW
      have hVerase : V ⊆ W.erase e := by
        intro x hx
        exact mem_erase.mpr ⟨fun h => heV (h ▸ hx), hV hx⟩
      have heq : bitsExpectation q (W.erase e) (fun S => f (insert e S)) =
          bitsExpectation q (W.erase e) f := by
        apply bitsExpectation_congr
        intro S _
        apply hf
        intro x hx
        have hxe : x ≠ e := fun h => heV (h ▸ hx)
        simp [hxe]
      have hs := bitsExpectation_insert q (W.erase e) e (notMem_erase e W) f
      rw [insert_erase heW, heq, ih (W.erase e) (erase_ssubset heW) hVerase] at hs
      linarith

lemma bitsExpectation_sum {ι : Type*} (q : α → ℝ) (V : Finset α) (I : Finset ι)
    (f : ι → Finset α → ℝ) :
    bitsExpectation q V (fun S => ∑ e ∈ I, f e S) = ∑ e ∈ I, bitsExpectation q V (f e) := by
  simp only [bitsExpectation, mul_sum]
  rw [sum_comm]

lemma bitsExpectation_mem (q : α → ℝ) (V : Finset α) (e : α) (he : e ∈ V) :
    bitsExpectation q V (fun S => if e ∈ S then 1 else 0) = q e := by
  rw [bitsExpectation_restrict q V {e} (singleton_subset_iff.mpr he)
    (fun S => if e ∈ S then 1 else 0) (by
      intro S S' h
      simp only [h e (mem_singleton_self e)])]
  rw [show ({e} : Finset α) = insert e ∅ from rfl,
    bitsExpectation_insert q ∅ e (notMem_empty e)]
  simp [bitsExpectation_empty]

lemma bitsExpectation_card_inter (q : α → ℝ) (V K : Finset α) (hKV : K ⊆ V) :
    bitsExpectation q V (fun S => ((K ∩ S).card : ℝ)) = ∑ e ∈ K, q e := by
  have hsum (S : Finset α) : ((K ∩ S).card : ℝ) =
      ∑ e ∈ K, if e ∈ S then (1 : ℝ) else 0 := by
    simp
  simp_rw [hsum]
  rw [bitsExpectation_sum]
  exact sum_congr rfl (fun e he => bitsExpectation_mem q V e (hKV he))

end MatroidProphet

end OAI
