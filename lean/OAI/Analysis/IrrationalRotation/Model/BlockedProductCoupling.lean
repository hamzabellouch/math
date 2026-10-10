import OAI.Analysis.IrrationalRotation.Model.OneCoordinateCoupling
import OAI.Analysis.IrrationalRotation.Model.ProductCoupling
import OAI.Analysis.IrrationalRotation.Model.ProductBase
import Mathlib.Probability.ProductMeasure

namespace OAI

open MeasureTheory

namespace Invariant233.BlockedProductCoupling

abbrev Coordinate := Option (Fin 5) × (ℝ × ℝ)

abbrev Sample (m : ℕ → ℕ) := (s : ℕ) → Fin (m s) → Coordinate

def flatten {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s)) (z : Sample m) :
    OrderedProductCoupling.Sample := fun i => z (e i).1 (e i).2

def leftEndpoint {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s))
    (z : Sample m) : OrderedProductCoupling.Endpoint :=
  OrderedProductCoupling.leftEndpoint (flatten e z)

def rightEndpoint {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s))
    (z : Sample m) : OrderedProductCoupling.Endpoint :=
  OrderedProductCoupling.rightEndpoint (flatten e z)

def toCircle (x : OrderedProductCoupling.Endpoint) : ProductModel.Base :=
  fun i => (x i : Circle)

def circleLeftEndpoint {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s)) :
    Sample m → ProductModel.Base := toCircle ∘ leftEndpoint e

def circleRightEndpoint {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s)) :
    Sample m → ProductModel.Base := toCircle ∘ rightEndpoint e

def parameters {m : ℕ → ℕ} {κ : ℕ → ℝ}
    {a b : (s : ℕ) → Fin (m s) → ℝ}
    (hm : ∀ s, 100 ≤ m s) (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
    (ha : ∀ s i, 1 / (m s : ℝ) ≤ a s i) (ha' : ∀ s i, a s i ≤ 1 / 4)
    (hb : ∀ s i, 1 / (m s : ℝ) ≤ b s i) (hb' : ∀ s i, b s i ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) : OrderedProductCoupling.Parameters where
  κ i := κ (e i).1
  m i := m (e i).1
  a i := a (e i).1 (e i).2
  b i := b (e i).1 (e i).2
  t i := if (e i).1 = j then 1 else 0
  κ_nonneg i := hκ0 _
  κ_le i := hκ _
  m_ge i := Nat.cast_le.mpr (hm _)
  a_lower i := ha _ _
  a_upper i := ha' _ _
  b_lower i := hb _ _
  b_upper i := hb' _ _
  t_nonneg i := by split_ifs <;> norm_num
  t_le i := by split_ifs <;> norm_num

noncomputable def blockLaw (m : ℕ → ℕ) (κ : ℕ → ℝ)
    (a b : (s : ℕ) → Fin (m s) → ℝ) (j s : ℕ) :
    Measure (Fin (m s) → Coordinate) :=
  Measure.pi (fun i => OneCoordinateCoupling.labelledLaw (κ s) (m s)
    (a s i) (b s i) (if s = j then 1 else 0))

noncomputable def law (m : ℕ → ℕ) (κ : ℕ → ℝ)
    (a b : (s : ℕ) → Fin (m s) → ℝ) (j : ℕ) : Measure (Sample m) :=
  Measure.infinitePi (blockLaw m κ a b j)

def currentEvent (m : ℕ → ℕ) (j : ℕ) : Set (Sample m) :=
  {z | (∃ i, (z j i).1 = some (4 : Fin 5)) ∧
    ∀ i, (z j i).2.1 < 1 - 2 / (m j : ℝ) ∧
      2 / (m j : ℝ) < (z j i).2.2}

def futureBad (m : ℕ → ℕ) (K : ℕ → ℝ) (j : ℕ) : Set (Sample m) :=
  ⋃ n : ℕ, ⋃ i : Fin (m (j + 1 + n)),
    {z | 1 - 2 * K j / ((m (j + 1 + n) : ℝ) * K (j + 1 + n)) ≤
        (z (j + 1 + n) i).2.1 ∨
      (z (j + 1 + n) i).2.2 ≤
        2 * K j / ((m (j + 1 + n) : ℝ) * K (j + 1 + n))}

def retainedEvent {X : Type*} (m : ℕ → ℕ) (K : ℕ → ℝ)
    (r : X → ℝ) (x y : Sample m → X) (j : ℕ) : Set (Sample m) :=
  currentEvent m j \ (futureBad m K j ∪
    ({z | r (x z) < 1 / (j : ℝ)} ∪ {z | 1 - r (y z) < 1 / (j : ℝ)}))

end Invariant233.BlockedProductCoupling

end OAI
