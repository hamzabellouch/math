import OAI.Analysis.MarkovType.SmoothMarkovType
import OAI.Analysis.MarkovType.SmoothnessBounds
import OAI.Analysis.MarkovType.MarkovRenorming

namespace OAI

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem symmetricPowerSmoothWith_renormed (N : EquivalentNorm X) {q D : ℝ}
    (h : SymmetricPowerSmooth N.p q D) :
    SymmetricPowerSmoothWith q D (Renormed N) := by
  intro x y
  change N.p (Renormed.toOriginal N x + Renormed.toOriginal N y) ^ q +
      N.p (Renormed.toOriginal N x - Renormed.toOriginal N y) ^ q ≤
    2 * N.p (Renormed.toOriginal N x) ^ q +
      2 * D * N.p (Renormed.toOriginal N y) ^ q
  have hxy := h (Renormed.toOriginal N x) (Renormed.toOriginal N y)
  linarith only [hxy]

theorem normPowerSmoothWith_renormed (N : EquivalentNorm X) {q C : ℝ}
    (h : PowerSmooth N.p q C) : NormPowerSmoothWith q C (Renormed N) := by
  intro x y hx hy t ht
  change N.p (Renormed.toOriginal N x) = 1 at hx
  change N.p (Renormed.toOriginal N y) = 1 at hy
  change (N.p (Renormed.toOriginal N x + t • Renormed.toOriginal N y) +
      N.p (Renormed.toOriginal N x - t • Renormed.toOriginal N y)) / 2 ≤
    1 + C * t ^ q
  exact h (Renormed.toOriginal N x) (Renormed.toOriginal N y) hx hy t ht

theorem markovTypeWith_of_equivalent_symmetricPowerSmooth
    (N : EquivalentNorm X) {q D : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (hD : 0 ≤ D)
    (h : SymmetricPowerSmooth N.p q D) :
    MarkovTypeWith q ((N.upper / N.lower) * (64 * max 1 D)) X := by
  exact (markovTypeWith_of_symmetricPowerSmooth_nonneg hq hq₂ hD
    (symmetricPowerSmoothWith_renormed N h)).of_renormed N

theorem markovTypeWith_of_equivalent_powerSmooth
    (N : EquivalentNorm X) {q C : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (hC : 0 ≤ C)
    (h : PowerSmooth N.p q C) :
    MarkovTypeWith q ((N.upper / N.lower) * (64 * (1 + q * C))) X := by
  exact (markovTypeWith_of_normPowerSmooth hq hq₂ hC
    (normPowerSmoothWith_renormed N h)).of_renormed N

theorem hasNontrivialMarkovType_of_equivalent_symmetricPowerSmooth
    (N : EquivalentNorm X) {q D : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (hD : 0 ≤ D)
    (h : SymmetricPowerSmooth N.p q D) : HasNontrivialMarkovType X := by
  exact ⟨q, hq, (N.upper / N.lower) * (64 * max 1 D),
    markovTypeWith_of_equivalent_symmetricPowerSmooth N hq hq₂ hD h⟩

theorem hasNontrivialMarkovType_of_equivalent_powerSmooth
    (N : EquivalentNorm X) {q C : ℝ}
    (hq : 1 < q) (hq₂ : q ≤ 2) (hC : 0 ≤ C)
    (h : PowerSmooth N.p q C) : HasNontrivialMarkovType X := by
  exact ⟨q, hq, (N.upper / N.lower) * (64 * (1 + q * C)),
    markovTypeWith_of_equivalent_powerSmooth N hq hq₂ hC h⟩

end MarkovSuperreflexivity

end OAI
