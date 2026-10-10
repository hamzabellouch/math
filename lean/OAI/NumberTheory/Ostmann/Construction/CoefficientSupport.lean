import OAI.NumberTheory.Ostmann.Construction.ActualAmplitude
import OAI.NumberTheory.Ostmann.Construction.CanonicalLabels

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate FourierTransform
namespace Ostmann.Construction

theorem canonicalCoefficient_ne_zero_witness (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (outside : List ℕ) (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ)
    (l : ℕ) (a : State)
    (hA : canonicalCoefficient sources seed V outside base φ G l a≠0) :
    ∃ c : HistoryChoices sources seed V l, choicesMass sources seed V l c≠0 ∧
      (decodeHistory sources seed V l a c).Supported V outside ∧
      (decodeHistory sources seed V l a c).weight base φ G≠0 := by
  classical
  obtain ⟨c,hc,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hA
  have hm := (mul_ne_zero_iff.mp hterm).1
  have hw := (mul_ne_zero_iff.mp hterm).2
  have hs : (decodeHistory sources seed V l a c).Supported V outside := by
    by_contra hn
    exact hw (by simp only [History.supportedWeight,hn,ite_false])
  refine ⟨c,?_,hs,?_⟩
  · exact_mod_cast hm
  · simpa only [History.supportedWeight,hs,ite_true] using hw

theorem History.weight_leaf_ne_zero {l : ℕ} (h : History l)
    (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ) (hw : h.weight base φ G≠0) :
    ∀ a∈h.leafStates,base a≠0 := by
  induction h with
  | leaf b =>
    intro a ha
    have heq : a=b := by simpa only [History.leafStates,List.mem_singleton] using ha
    subst a
    exact hw
  | @node l b p u hp hm left right ihl ihr =>
    have hleft : left.weight base φ G≠0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).2
    have hright : right.weight base φ G≠0 := by
      simpa only [map_ne_zero] using (mul_ne_zero_iff.mp hw).2
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ihl hleft a ha
    · exact ihr hright a ha

theorem baseCoefficient_ne_zero_bins (X : ℝ) (ψhat : ℝ → ℂ)
    (g : (p : ℕ) → ZMod p → ℂ) (bins : List ℕ → State → ℝ)
    (outside : List ℕ) (a : State)
    (hb : baseCoefficient X ψhat g bins outside a≠0) : bins outside a≠0 := by
  intro hn
  apply hb
  simp only [baseCoefficient,hn,Complex.ofReal_zero,mul_zero,zero_mul]

theorem actualCoefficient_nonzero_leaf_bins (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (X G : ℝ) (g : (p : ℕ) → ZMod p → ℂ)
    (bins : List ℕ → State → ℝ) (outside : List ℕ) (l : ℕ) (a : State)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hA : actualCoefficient sources seed V X G g bins outside l a≠0) :
    ∃ c : HistoryChoices sources seed V l,
      choicesMass sources seed V l c≠0 ∧
      (decodeHistory sources seed V l a c).Supported V outside ∧
      ∀ b∈(decodeHistory sources seed V l a c).leafStates,
        Template.Matches seed b.small ∧ bins outside b≠0 := by
  obtain ⟨c,hm,hs,hw⟩ := canonicalCoefficient_ne_zero_witness sources seed V outside
    (baseCoefficient X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) g bins outside)
    Ostmann.smoothPartition G l a hA
  refine ⟨c,hm,hs,?_⟩
  intro b hb
  refine ⟨decoded_leaf_matches sources seed V l a c ha b hb,?_⟩
  exact baseCoefficient_ne_zero_bins _ _ _ _ _ _
    (History.weight_leaf_ne_zero _ _ _ _ hw b hb)

end Ostmann.Construction

end

end OAI
