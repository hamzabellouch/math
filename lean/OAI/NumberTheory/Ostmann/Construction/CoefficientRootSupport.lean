import OAI.NumberTheory.Ostmann.Construction.CoefficientSupport

namespace OAI

noncomputable section
open scoped FourierTransform
namespace Ostmann.Construction

theorem actualCoefficient_root_support (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (X G : ℝ) (g : (p:ℕ)→ZMod p→ℂ) (bins : List ℕ→State→ℝ)
    (outside : List ℕ) (l : ℕ) (a : State)
    (hA : actualCoefficient sources seed V X G g bins outside l a≠0) :
    a.Positive ∧ a.PrimeSmall ∧ a.TemplateAt l ∧ a.Coprime outside ∧
      a.frequency≠0 ∧ a.frequency.natAbs≤V l := by
  obtain ⟨c,hm,hs,hw⟩ := canonicalCoefficient_ne_zero_witness sources seed V outside
    (baseCoefficient X (fun ξ => 𝓕 SchwartzCutoff.psi ξ) g bins outside)
    Ostmann.smoothPartition G l a hA
  rw [History.Supported.eq_def] at hs
  have hx := And.intro hs.1 (And.intro hs.2.1 (And.intro hs.2.2.1
    (And.intro hs.2.2.2.1 (And.intro hs.2.2.2.2.1 hs.2.2.2.2.2.1))))
  simpa only [decodeHistory_root] using hx

theorem actualCoefficient_zero_of_not_coprime (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (X G : ℝ) (g : (p:ℕ)→ZMod p→ℂ) (bins : List ℕ→State→ℝ)
    (outside : List ℕ) (l : ℕ) (a : State) (ha : ¬a.Coprime outside) :
    actualCoefficient sources seed V X G g bins outside l a=0 := by
  by_contra hA
  exact ha (actualCoefficient_root_support sources seed V X G g bins outside l a hA).2.2.2.1

end Ostmann.Construction

end

end OAI
