import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! The source writes the accounting sacrifice set as `D ∪ C`, whereas the
implementation retains `H ∪ D ∪ C`. Every candidate is outside H, so these
expressions agree on every actual nominal layer, before taking any rank. -/

namespace MatroidProphet.MainAlgorithm
open Set Finset
variable {n : ℕ}

lemma groupMask_not_mem_filter (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (mask : Finset (Fin n)) (h : ℕ) {e : Fin n}
    (he : e ∈ groupMask M d w mask h) : e ∉ d.H := he.2.1.2.1

lemma nominalLayer_sacrifice_eq_source (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (ε : Fin 2)
    (b : Pivots.ParityWindow (activation h) ε) :
    nominalLayerSet M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
      h (groupMask M d w univ h) ε b \ ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) =
    nominalLayerSet M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
      h (groupMask M d w univ h) ε b \ ((d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) := by
  ext e
  constructor
  · rintro ⟨he, hnot⟩
    refine ⟨he, ?_⟩
    intro heO
    exact hnot (by
      simp only [Finset.mem_coe, Finset.mem_union] at heO ⊢
      tauto)
  · rintro ⟨he, hnot⟩
    have heG := nominalLayerSet_subset M hE (2^100)
      (groupMask M d w d.D) (groupMask M d w d.C) h (groupMask M d w univ h) ε b he
    have heH := groupMask_not_mem_filter M d w univ h heG
    refine ⟨he, ?_⟩
    simp only [Finset.mem_coe, Finset.mem_union] at hnot ⊢
    tauto

end MatroidProphet.MainAlgorithm

end OAI
