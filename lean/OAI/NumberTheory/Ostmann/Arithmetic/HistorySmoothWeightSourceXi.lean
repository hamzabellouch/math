import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightArchimedeanDeriv
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceTree

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open Construction Characters.RationalHistory HistoryOccurrenceVariables

def sourceXiConstant (l k : ℕ) (E : ℝ) : ℝ :=
  (2^l : ℕ) * (E+12+4*(k:ℝ)+2*Real.log leafFourierBound)

theorem sourceLeafAmplitude_pair (l k : ℕ) (Δ E : ℝ) :
    (sourceLeafAmplitude k Δ E)^(2^l) * (sourceLeafAmplitude k Δ E)^(2^l) =
      Real.exp (-((2^l : ℕ):ℝ)*Δ + sourceXiConstant l k E) := by
  have hC := Real.exp_log leafFourierBound_pos
  have hA : sourceLeafAmplitude k Δ E =
      Real.exp (Real.log leafFourierBound + (-Δ+(E+12+4*(k:ℝ)))/2) := by
    rw [Real.exp_add,hC]
    rfl
  rw [hA,← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  dsimp only [sourceXiConstant]
  ring

namespace HistorySymbolicEncoding
open HistorySymbolicState InitialCoordinatesTemplate

structure SourceDomain (b k : ℕ) (G : ℝ) (center : ℕ → ℝ)
    {l : ℕ} (h : History l) (x : Key h → ℝ) : Prop where
  positive : ∀ i, 0 < x i
  source : IndependentSourceCells (independentSlot h) center x
  giant : ∀ j : Bool, |Real.log (x (Sum.inl j))-G| ≤ 1
  leaves : ∀ a ∈ h.leafStates, Template.Matches (Template.initial (2*b) k) a.small

def actualRealXi (b s : ℕ) (X tb td G : ℝ) (outside : List ℕ)
    {l : ℕ} {V : ℕ → ℕ} (h₁ h₂ : History l)
    (hs₁ : h₁.Supported V outside) (hs₂ : h₂.Supported V outside)
    (x₁ : Key h₁ → ℝ) (x₂ : Key h₂ → ℝ) : ℂ :=
  actualRealHistoryScalar b s X tb td G outside h₁ hs₁ x₁ *
    star (actualRealHistoryScalar b s X tb td G outside h₂ hs₂ x₂)

theorem actualRealXi_norm_le (b s k : ℕ) (X tb td G Δ E : ℝ)
    (center : ℕ → ℝ) (outside : List ℕ)
    (hX : 0 < X) (houtside : ∀ q ∈ outside, 0 < q) (hout : outside.length=2*s)
    {l : ℕ} {V : ℕ → ℕ} (h₁ h₂ : History l)
    (hs₁ : h₁.Supported V outside) (hs₂ : h₂.Supported V outside)
    (x₁ : Key h₁ → ℝ) (x₂ : Key h₂ → ℝ)
    (hx₁ : SourceDomain b k G center h₁ x₁) (hx₂ : SourceDomain b k G center h₂ x₂)
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ h,∑ i,topCenters b center h i)+
      (∑ h,∑ j : Fin k,∑ i,compensationCenters b center h j i)) :
    ‖actualRealXi b s X tb td G outside h₁ h₂ hs₁ hs₂ x₁ x₂‖ ≤
      Real.exp (-((2^l : ℕ):ℝ)*Δ + sourceXiConstant l k E) := by
  rw [actualRealXi,norm_mul,norm_star,← sourceLeafAmplitude_pair]
  exact mul_le_mul
    (actualRealHistoryScalar_norm_le_sourceRanges b s k X tb td G Δ E center outside hX houtside hout
      h₁ hs₁ hx₁.leaves x₁ hx₁.positive hx₁.source hx₁.giant hcenter)
    (actualRealHistoryScalar_norm_le_sourceRanges b s k X tb td G Δ E center outside hX houtside hout
      h₂ hs₂ hx₂.leaves x₂ hx₂.positive hx₂.source hx₂.giant hcenter)
    (norm_nonneg _) (pow_nonneg (sourceLeafAmplitude_pos k Δ E).le _)

theorem actualRealXi_counterpart_norm_le (b s k : ℕ) (X tb td G Δ E : ℝ)
    (center : ℕ → ℝ) (outside : List ℕ)
    (hX : 0 < X) (houtside : ∀ q ∈ outside, 0 < q) (hout : outside.length=2*s)
    {l : ℕ} {V : ℕ → ℕ} (h₁ h₂ : History l)
    (hs₁ : h₁.Supported V outside) (hs₂ : h₂.Supported V outside)
    (x₁ : Key h₁ → ℝ) (x₂ : Key h₂ → ℝ)
    (hx₁ : SourceDomain b k G center h₁ x₁) (hx₂ : SourceDomain b k G center h₂ x₂)
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ h,∑ i,topCenters b center h i)+
      (∑ h,∑ j : Fin k,∑ i,compensationCenters b center h j i))
    {ι : Type*} (S : Finset ι) (cellCenter p : ι → ℝ) (T U H u WH Wu : ℝ)
    (hH : 0 < H) (hu : 0 < u) (hlogH : T-WH ≤ Real.log H) (hlogu : Real.log u ≤ U+Wu) :
    ‖(counterpartArchimedean T U H u S cellCenter p:ℂ) *
      actualRealXi b s X tb td G outside h₁ h₂ hs₁ hs₂ x₁ x₂‖ ≤
      Real.exp (-((2^l : ℕ):ℝ)*Δ + sourceXiConstant l k E + WH+Wu) := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (counterpartArchimedean_nonneg T U H u S cellCenter p hH.le hu.le)]
  calc
    _ ≤ Real.exp (WH+Wu) * Real.exp (-((2^l : ℕ):ℝ)*Δ + sourceXiConstant l k E) :=
      mul_le_mul (counterpartArchimedean_le T U H u WH Wu S cellCenter p hH hu hlogH hlogu)
        (actualRealXi_norm_le b s k X tb td G Δ E center outside hX houtside hout h₁ h₂ hs₁ hs₂
          x₁ x₂ hx₁ hx₂ hcenter) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end HistorySymbolicEncoding
end Ostmann.Arithmetic

end

end OAI
