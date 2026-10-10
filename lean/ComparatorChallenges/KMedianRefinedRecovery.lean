import Mathlib

namespace OAI

namespace MetricKMedianRecovery

structure RationalMetricInput where
  pointCount : ℕ
  distance : Fin pointCount → Fin pointCount → ℚ
  clients : Finset (Fin pointCount)
  facilities : Finset (Fin pointCount)
  budget : ℕ
  facilities_nonempty : facilities.Nonempty
  budget_pos : 0 < budget
  covered : clients ∪ facilities = Finset.univ
  distance_nonneg : ∀ x y, 0 ≤ distance x y
  distance_self : ∀ x, distance x x = 0
  distance_symm : ∀ x y, distance x y = distance y x
  distance_triangle : ∀ x y z, distance x z ≤ distance x y + distance y z

namespace RationalMetricInput

def size (I : RationalMetricInput) : ℕ := I.clients.card + I.facilities.card

def Feasible (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) : Prop :=
  S ⊆ I.facilities ∧ S.card ≤ I.budget ∧ (I.clients.Nonempty → S.Nonempty)

def cost (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) : ℚ :=
  if hS : S.Nonempty then ∑ p ∈ I.clients, S.inf' hS (I.distance p) else 0

def natBits (n : ℕ) : List Bool :=
  List.replicate (Nat.bits n).length true ++ [false] ++ Nat.bits n

def rationalBits (r : ℚ) : List Bool :=
  [decide (r < 0)] ++ natBits r.num.natAbs ++ natBits r.den

def bits (I : RationalMetricInput) : List Bool :=
  natBits I.pointCount ++ natBits I.budget ++
    List.ofFn (fun i : Fin I.pointCount => decide (i ∈ I.clients)) ++
    List.ofFn (fun i : Fin I.pointCount => decide (i ∈ I.facilities)) ++
    (List.ofFn (fun i : Fin I.pointCount =>
      (List.ofFn (fun j : Fin I.pointCount => rationalBits (I.distance i j))).flatten)).flatten

def decodeOutput (I : RationalMetricInput) (out : List Bool) : Finset (Fin I.pointCount) :=
  I.facilities.filter (fun i => out[i.val]?.getD false = true)

end RationalMetricInput

def pairBits (p : List Bool × List Bool) : List Bool :=
  p.1.flatMap (fun b => [true, b]) ++ [false] ++ p.2

structure BinaryRandomizedAlgorithm where
  randomBits : Polynomial ℕ
  run : List Bool × List Bool → List Bool
  computation : Turing.TM2ComputableInPolyTime pairBits id run
  finiteWorkAlphabet : ∀ k : computation.tm.K, Finite (computation.tm.Γ k)


end MetricKMedianRecovery

run_elab Lean.modifyEnv fun environment => Lean.Meta.auxLemmasExt.setState environment {}

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


end MetricKMedianRecovery.RefinedRecovery

namespace MetricKMedianRecovery.RefinedRecovery

theorem refined_recovery :
    ∀ (bound : Polynomial ℕ) (ε L₀ : ℝ) (μ : ℚ),
      0 < ε → 0 < L₀ → 0 < μ → μ ≤ 1/4 → (μ : ℝ) ≤ ε/12 →
      ∃ A : BinaryRandomizedAlgorithm,
        PolynomialWork A bound ∧
        ∀ I : Input, I.Bounded bound → ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
          (∀ s : Seed A I ζ, I.metric.Feasible (output A I ζ s)) ∧
          (∀ C : Certificate I μ L₀,
            1 - ζ ≤ successProbability A I ζ
              ((1 + 2 / Real.exp 1 + ε) * (I.metric.cost C.centers : ℝ))) := by
  sorry

end MetricKMedianRecovery.RefinedRecovery

end OAI
