import OAI.Combinatorics.KMedianRecovery.Model

namespace OAI

/-! Normalized metric inputs, hidden comparison certificates, and the refined recovery claim. -/

namespace MetricKMedianRecovery.RefinedRecovery

structure Input where
  metric : RationalMetricInput
  disjoint : Disjoint metric.clients metric.facilities
  integral : ∀ x y, ∃ z : ℕ, metric.distance x y = (z : ℚ)
  positive : ∀ x y, x ≠ y → 0 < metric.distance x y
  anchor : Finset (Fin metric.pointCount)
  anchor_subset : anchor ⊆ metric.facilities
  anchor_card : anchor.card = metric.budget

namespace Input
abbrev Point (I : Input) := Fin I.metric.pointCount

def size (I : Input) : ℕ := I.metric.size

def Bounded (I : Input) (bound : Polynomial ℕ) : Prop :=
  ∀ x y, I.metric.distance x y ≤ ((bound.eval I.size : ℕ) : ℚ)

lemma anchor_nonempty (I : Input) : I.anchor.Nonempty :=
  Finset.card_pos.mp (I.anchor_card.symm ▸ I.metric.budget_pos)

noncomputable def assign (I : Input) (O : Finset I.Point) (p : I.Point) : I.Point :=
  if h : O.Nonempty then
    Classical.choose (Finset.exists_min_image O
      (fun i => toLex (I.metric.distance p i, i)) h)
  else p

noncomputable def cluster (I : Input) (O : Finset I.Point) (i : I.Point) : Finset I.Point :=
  I.metric.clients.filter (fun p => I.assign O p = i)

noncomputable def clusterCost (I : Input) (O : Finset I.Point) (i : I.Point) : ℝ :=
  ∑ p ∈ I.cluster O i, (I.metric.distance p i : ℝ)

def anchorBits (I : Input) : List Bool :=
  List.ofFn (fun i : I.Point => decide (i ∈ I.anchor))

end Input

structure Certificate (I : Input) (μ : ℚ) (L₀ : ℝ) where
  centers : Finset I.Point
  centers_subset : centers ⊆ I.metric.facilities
  same_card : centers.card = I.anchor.card
  positive_cost : 0 < (I.metric.cost centers : ℝ)
  good : Finset I.Point
  good_subset : good ⊆ centers
  proxy : I.Point → I.Point
  proxy_mem : ∀ i ∈ good, proxy i ∈ I.anchor
  proxy_inj : Set.InjOn proxy (↑good)
  proxy_cost : (∑ i ∈ good, ∑ p ∈ I.cluster centers i,
      (I.metric.distance p (proxy i) : ℝ)) ≤
    (∑ i ∈ good, I.clusterCost centers i) + (μ : ℝ) * (I.metric.cost centers : ℝ)
  few_bad : (((centers \ good).card : ℕ) : ℝ) ≤ L₀ * Real.log (I.size : ℝ)

namespace Certificate
variable {I : Input} {μ : ℚ} {L₀ : ℝ}
def bad (C : Certificate I μ L₀) : Finset I.Point := C.centers \ C.good
noncomputable def nonproxy (C : Certificate I μ L₀) : Finset I.Point :=
  I.anchor \ C.good.image C.proxy
end Certificate

noncomputable def precision (ζ : ℝ) : ℕ :=
  ⌈Real.log (1 / ζ) / Real.log 2⌉₊

noncomputable def queryBits (I : Input) (ζ : ℝ) : List Bool :=
  pairBits (I.metric.bits, I.anchorBits ++ List.replicate (precision ζ) true)

noncomputable def seedLength (A : BinaryRandomizedAlgorithm) (I : Input) (ζ : ℝ) : ℕ :=
  A.randomBits.eval (queryBits I ζ).length

abbrev Seed (A : BinaryRandomizedAlgorithm) (I : Input) (ζ : ℝ) :=
  Fin (seedLength A I ζ) → Bool

noncomputable def output (A : BinaryRandomizedAlgorithm) (I : Input) (ζ : ℝ)
    (s : Seed A I ζ) : Finset I.Point :=
  I.metric.decodeOutput (A.run (queryBits I ζ, List.ofFn s))

noncomputable def successProbability (A : BinaryRandomizedAlgorithm) (I : Input)
    (ζ target : ℝ) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun s : Seed A I ζ =>
    (I.metric.cost (output A I ζ s) : ℝ) ≤ target)).card : ℝ) /
    2 ^ seedLength A I ζ

noncomputable def workBound (A : BinaryRandomizedAlgorithm) (I : Input) (ζ : ℝ) : ℕ :=
  (queryBits I ζ).length + seedLength A I ζ +
    A.computation.time.eval (pairBits
      (queryBits I ζ, List.replicate (seedLength A I ζ) false)).length

def PolynomialWork (A : BinaryRandomizedAlgorithm) (bound : Polynomial ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ d : ℕ,
    ∀ I : Input, I.Bounded bound → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
      (workBound A I ζ : ℝ) ≤
        c * ((I.size : ℝ) + 1) ^ d * (1 + Real.log (1 / ζ)) ^ d

def refinedRecoveryClaim : Prop :=
  ∀ (bound : Polynomial ℕ) (ε L₀ : ℝ) (μ : ℚ),
    0 < ε → 0 < L₀ → 0 < μ → μ ≤ 1/4 → (μ : ℝ) ≤ ε/12 →
    ∃ A : BinaryRandomizedAlgorithm,
      PolynomialWork A bound ∧
      ∀ I : Input, I.Bounded bound → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
        (∀ s : Seed A I ζ, I.metric.Feasible (output A I ζ s)) ∧
        (∀ C : Certificate I μ L₀,
          1 - ζ ≤ successProbability A I ζ
            ((1 + 2 / Real.exp 1 + ε) * (I.metric.cost C.centers : ℝ)))

end MetricKMedianRecovery.RefinedRecovery

end OAI
