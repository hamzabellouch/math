import OAI.Analysis.IrrationalRotation.Model.OneCoordinateCoupling

namespace OAI

open MeasureTheory

namespace Invariant233.OrderedProductCoupling

open OneCoordinateCoupling

structure Parameters where
  κ : ℕ → ℝ
  m : ℕ → ℝ
  a : ℕ → ℝ
  b : ℕ → ℝ
  t : ℕ → ℝ
  κ_nonneg : ∀ i, 0 ≤ κ i
  κ_le : ∀ i, κ i ≤ 1 / 100
  m_ge : ∀ i, 100 ≤ m i
  a_lower : ∀ i, 1 / m i ≤ a i
  a_upper : ∀ i, a i ≤ 1 / 4
  b_lower : ∀ i, 1 / m i ≤ b i
  b_upper : ∀ i, b i ≤ 1 / 4
  t_nonneg : ∀ i, 0 ≤ t i
  t_le : ∀ i, t i ≤ 1

abbrev CoordinateSample := Option (Fin 5) × (ℝ × ℝ)
abbrev Sample := ℕ → CoordinateSample
abbrev Endpoint := ℕ → ℝ

noncomputable def coordinateLaw (P : Parameters) (i : ℕ) : Measure CoordinateSample :=
  labelledLaw (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)

noncomputable def law (P : Parameters) : Measure Sample :=
  Measure.infinitePi (coordinateLaw P)

noncomputable def baseMeasure : Measure Endpoint :=
  Measure.infinitePi (fun _ : ℕ => baseLaw)

def leftEndpoint (ω : Sample) (i : ℕ) : ℝ := (ω i).2.1

def rightEndpoint (ω : Sample) (i : ℕ) : ℝ := (ω i).2.2

def hybridEndpoint (ε : ℕ → Bool) (ω : Sample) (i : ℕ) : ℝ :=
  if ε i then rightEndpoint ω i else leftEndpoint ω i

noncomputable def marginalDensity (P : Parameters) (side : Bool) (i : ℕ) : ℝ → ℝ :=
  if side then rightMarginalDensity (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)
  else leftMarginalDensity (P.κ i) (P.m i) (P.a i) (P.b i) (P.t i)

noncomputable def energyBound (P : Parameters) (i : ℕ) : ℝ :=
  20 * (2 * (P.κ i) ^ 2 / P.m i + P.t i / P.m i)

end Invariant233.OrderedProductCoupling

end OAI
