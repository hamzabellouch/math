import Mathlib
import OAI.Probability.JammingConcavity.RowRankTerminalStability

namespace OAI

/-! Family Cascade Log. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def familyLeafTotal {E : Type} [MeasurableSpace E] [Add E] :
    (ms : List ℝ) → (E → ℝ) → E → FamilyCascadeTree E ms.length → ℝ≥0∞
  | [], u, x, _ => ENNReal.ofReal (Real.exp (u x))
  | m::ms, u, x, ω => pointCloudFunctional
      (fun z : ℝ × (E × FamilyCascadeTree E ms.length) =>
        ENNReal.ofReal (z.1^(-1/m))*familyLeafTotal ms u (x+z.2.1) z.2.2) ω

def familyLogPartition {E : Type} [MeasurableSpace E] [Add E]
    (ms : List ℝ) (u : E → ℝ) (x : E) (ω : FamilyCascadeTree E ms.length) : ℝ :=
  Real.log ((familyLeafTotal ms u x ω).toReal/(familyLeafTotal ms (fun _ => 0) x ω).toReal)

def FamilyCascadeLogStatement : Prop :=
  ∀ (E : Type) (_ : MeasurableSpace E) (_ : Add E) (_ : MeasurableAdd₂ E),
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ ν : ℕ → Measure E, (∀ j, IsProbabilityMeasure (ν j)) →
  ∀ u : E → ℝ, Measurable u → FamilyMomentsFinite ms ν u → ∀ x : E,
    (∀ᵐ ω ∂familyCascadeLaw ms.length ν,
      0 < familyLeafTotal ms u x ω ∧ familyLeafTotal ms u x ω < ∞) ∧
    Integrable (fun ω => |Real.log (familyLeafTotal ms u x ω).toReal|^2)
      (familyCascadeLaw ms.length ν) ∧
    Integrable (familyLogPartition ms u x) (familyCascadeLaw ms.length ν) ∧
    (∫ ω, familyLogPartition ms u x ω ∂familyCascadeLaw ms.length ν) =
      familyRecursion ms ν u x
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def decoratedTreeSpace (E : Type) [MeasurableSpace E] : ℕ → (Σ T : Type, MeasurableSpace T)
  | 0 => ⟨Unit, inferInstanceAs (MeasurableSpace Unit)⟩
  | k+1 => by
    letI := (decoratedTreeSpace E k).2
    exact ⟨Measure (ℝ × (E × (decoratedTreeSpace E k).1)), inferInstance⟩

abbrev DecoratedTree (E : Type) [MeasurableSpace E] (k : ℕ) := (decoratedTreeSpace E k).1
instance decoratedTreeMeasurable (E : Type) [MeasurableSpace E] (k : ℕ) :
    MeasurableSpace (DecoratedTree E k) := (decoratedTreeSpace E k).2

def transformedDecoratedTree {E : Type} [MeasurableSpace E] [Add E] :
    (ms : List ℝ) → (ℕ → Measure E) → (E → ℝ) → E → FamilyCascadeTree E ms.length → DecoratedTree E ms.length
  | [], _, _, _, _ => ()
  | m::ms, ν, u, x, ω => (pointCloudMeasure ω).map
      (fun z : ℝ × (E × FamilyCascadeTree E ms.length) =>
        (z.1/(familyEdgeMultiplier m ms ν u x z.2.1)^m,
          (z.2.1, transformedDecoratedTree ms (fun j => ν (j+1)) u (x+z.2.1) z.2.2)))

def decoratedTransition {E : Type} [MeasurableSpace E] [Add E]
    (m : ℝ) (ms : List ℝ) (ν : ℕ → Measure E) (u : E → ℝ) (x : E) : Measure E :=
  pointCloudTilt m (familyEdgeMultiplier m ms ν u x) (ν 0)

def decoratedCascadeLaw {E : Type} [MeasurableSpace E] [Add E] :
    (ms : List ℝ) → (ℕ → Measure E) → (E → ℝ) → E → Measure (DecoratedTree E ms.length)
  | [], _, _, _ => Measure.dirac ()
  | m::ms, ν, u, x =>
      (pointCloudLaw ((decoratedTransition m ms ν u x).bind fun a =>
        (decoratedCascadeLaw ms (fun j => ν (j+1)) u (x+a)).map (fun t => (a,t)))).map pointCloudMeasure

def DecoratedCascadeStatement : Prop :=
  ∀ (E : Type) (_ : MeasurableSpace E) (_ : Add E) (_ : MeasurableAdd₂ E),
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ ν : ℕ → Measure E, (∀ j, IsProbabilityMeasure (ν j)) →
  ∀ u : E → ℝ, Measurable u → FamilyMomentsFinite ms ν u → ∀ x : E,
    (familyCascadeLaw ms.length ν).map (transformedDecoratedTree ms ν u x) =
      decoratedCascadeLaw ms ν u x
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MicroscopicJamming
 
def rowGaussianBlocks : List ℝ → (ℕ → ℝ≥0) → List (ℝ × ℝ)
  | [], _ => []
  | m::ms, d => (m,(d 0:ℝ))::rowGaussianBlocks ms (fun j => d (j+1))
def rowGaussianLaw (d : ℕ → ℝ≥0) (j : ℕ) : Measure ℝ := gaussianReal 0 (d j)
 

def RowGaussianCascadeStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (d : ℕ → ℝ≥0) (Δ p₀ : ℝ≥0),
    let v := gaussianRowOperator 1 Δ u
    FamilyMomentsFinite ms (rowGaussianLaw d) v ∧
    (∀ x, familyRecursion ms (rowGaussianLaw d) v x =
      gaussianRowComposition (rowGaussianBlocks ms d ++ [(1,(Δ:ℝ))]) u x) ∧
    (∀ x, Integrable (familyLogPartition ms v x) (familyCascadeLaw ms.length (rowGaussianLaw d))) ∧
    (∫ z, ∫ ω, familyLogPartition ms v z ω ∂familyCascadeLaw ms.length (rowGaussianLaw d)
      ∂gaussianReal 0 p₀) =
      gaussianRowComposition ((0,(p₀:ℝ))::(rowGaussianBlocks ms d ++ [(1,(Δ:ℝ))])) u 0
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def familyPathGibbs {E : Type} [MeasurableSpace E] [Add E] :
    (ms : List ℝ) → (E → ℝ) → (E → ℝ≥0∞) → E → FamilyCascadeTree E ms.length → ℝ≥0∞
  | [], _, φ, x, _ => φ x
  | m::ms, u, φ, x, ω =>
      pointCloudFunctional (fun z : ℝ × (E × FamilyCascadeTree E ms.length) =>
        ENNReal.ofReal (z.1^(-1/m))*familyLeafTotal ms u (x+z.2.1) z.2.2 *
          familyPathGibbs ms u φ (x+z.2.1) z.2.2) ω / familyLeafTotal (m::ms) u x ω

def familyPathMean {E : Type} [MeasurableSpace E] [Add E] :
    (ms : List ℝ) → (ℕ → Measure E) → (E → ℝ) → (E → ℝ≥0∞) → E → ℝ≥0∞
  | [], _, _, φ, x => φ x
  | m::ms, ν, u, φ, x => ∫⁻ a, familyPathMean ms (fun j => ν (j+1)) u φ (x+a)
      ∂decoratedTransition m ms ν u x

def FamilyPathStatement : Prop :=
  ∀ (E : Type) (_ : MeasurableSpace E) (_ : MeasurableEq E) (_ : Add E) (_ : MeasurableAdd₂ E),
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ ν : ℕ → Measure E, (∀ j, IsProbabilityMeasure (ν j)) →
  ∀ u : E → ℝ, Measurable u → FamilyMomentsFinite ms ν u →
  ∀ φ : E → ℝ≥0∞, Measurable φ → (∀ x, φ x ≤ 1) →
  ∀ η : ℝ, 0 ≤ η → (∀ m ∈ ms, η < m) → ∀ x : E,
    (∫⁻ ω, ENNReal.ofReal ((familyLeafTotal ms u x ω).toReal^η)*familyPathGibbs ms u φ x ω
      ∂familyCascadeLaw ms.length ν) /
      ENNReal.ofReal (∫ ω, (familyLeafTotal ms u x ω).toReal^η ∂familyCascadeLaw ms.length ν) =
      familyPathMean ms ν u φ x
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def PointCloudCampbellStatement : Prop :=
  ∀ (A : Type) (_ : MeasurableSpace A) (ν : Measure A), IsProbabilityMeasure ν →
  ∀ F : (ℝ × A) × Measure (ℝ × A) → ℝ≥0∞, Measurable F →
    (∫⁻ ω, ∫⁻ z, F (z, pointCloudMeasure ω) ∂pointCloudMeasure ω ∂pointCloudLaw ν) =
      ∫⁻ z, ∫⁻ ω, F (z, Measure.dirac z + pointCloudMeasure ω) ∂pointCloudLaw ν
        ∂(volume.restrict (Set.Ioi 0)).prod ν
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def distinctCloudIntegral {X : Type*} [MeasurableSpace X] :
    List (X → ℝ≥0∞) → Measure X → List X → ℝ≥0∞
  | [], _, _ => 1
  | f::fs, μ, xs => by
      classical
      exact ∫⁻ x, if x ∈ xs then 0 else f x * distinctCloudIntegral fs μ (x::xs) ∂μ

def FactorialCloudStatement : Prop :=
  ∀ g : ℝ × Unit → ℝ≥0∞, Measurable g →
  ∀ fs : List ((ℝ × Unit) → ℝ≥0∞), (∀ f ∈ fs, Measurable f) →
    (∫⁻ ω, ENNReal.ofReal (expNeg (∫⁻ z, g z ∂pointCloudMeasure ω)) *
      distinctCloudIntegral fs (pointCloudMeasure ω) [] ∂pointCloudLaw (Measure.dirac ())) =
    (∫⁻ ω, ENNReal.ofReal (expNeg (∫⁻ z, g z ∂pointCloudMeasure ω))
      ∂pointCloudLaw (Measure.dirac ())) *
    (fs.map (fun f => ∫⁻ z, f z * ENNReal.ofReal (expNeg (g z))
      ∂(volume.restrict (Set.Ioi 0)).prod (Measure.dirac ()))).prod
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def stableJump (m c : ℝ) (z : ℝ × Unit) : ℝ≥0∞ :=
  ENNReal.ofReal (c^(1/m)*z.1^(-1/m))

def stableTotal (m c : ℝ) (ω : PointCloud Unit) : ℝ≥0∞ :=
  pointCloudFunctional (stableJump m c) ω

def poissonPartitionNumerator (m c η : ℝ) (ns : List ℕ) (ω : PointCloud Unit) : ℝ≥0∞ :=
  ENNReal.ofReal ((stableTotal m c ω).toReal^(η-(ns.sum:ℝ))) *
    distinctCloudIntegral (ns.map (fun n z => stableJump m c z ^ n)) (pointCloudMeasure ω) []

def partitionProduct (m η : ℝ) (ns : List ℕ) : ℝ :=
  (∏ a ∈ Finset.Ico 1 ns.length, ((a:ℝ)*m-η)) /
    (∏ a ∈ Finset.Ico 1 ns.sum, ((a:ℝ)-η)) *
    (ns.map (fun n : ℕ => ∏ a ∈ Finset.Ico 1 n, ((a:ℝ)-m))).prod

def CascadeEPPFStatement : Prop :=
  ∀ m c η : ℝ, 0 < m → m < 1 → 0 < c → 0 ≤ η → η < m →
  ∀ ns : List ℕ, ns ≠ [] → (∀ n ∈ ns, 0 < n) →
    (∫⁻ ω, poissonPartitionNumerator m c η ns ω ∂pointCloudLaw (Measure.dirac ())) /
      ENNReal.ofReal (∫ ω, (stableTotal m c ω).toReal^η ∂pointCloudLaw (Measure.dirac ())) =
      ENNReal.ofReal (partitionProduct m η ns)
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def expMarkedTotal {A : Type*} (m : ℝ) (X : A → ℝ) (ω : PointCloud A) : ℝ≥0∞ :=
  coloredStableSum m (fun a => ⟨Real.exp (X a), (Real.exp_pos _).le⟩) ω

def unmarkedTotal {A : Type*} (m : ℝ) (ω : PointCloud A) : ℝ≥0∞ :=
  coloredStableSum m (fun _ => 1) ω

def cascadeLogIncrement {A : Type*} (m : ℝ) (X : A → ℝ) (ω : PointCloud A) : ℝ :=
  Real.log ((expMarkedTotal m X ω).toReal/(unmarkedTotal m ω).toReal)

def CascadeLogStatement : Prop :=
  ∀ (A : Type) (_ : MeasurableSpace A) (ν : Measure A), IsProbabilityMeasure ν →
  ∀ m : ℝ, 0 < m → m < 1 → ∀ X : A → ℝ, Measurable X →
    Integrable (fun a => Real.exp (m*X a)) ν →
    Integrable (cascadeLogIncrement m X) (pointCloudLaw ν) ∧
    (∫ ω, cascadeLogIncrement m X ω ∂pointCloudLaw ν) =
      (1/m)*Real.log (∫ a, Real.exp (m*X a) ∂ν)
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def expMarkedJump {A : Type*} (m : ℝ) (X : A → ℝ) (z : ℝ × A) : ℝ≥0∞ :=
  ENNReal.ofReal (z.1^(-1/m))*ENNReal.ofReal (Real.exp (X z.2))

def expMarkedBlock {A : Type*} (m : ℝ) (X : A → ℝ) (n : ℕ) (s : Set A)
    (z : ℝ × A) : ℝ≥0∞ := s.indicator (fun _ => expMarkedJump m X z^n) z.2

def markedPartitionNumerator {A : Type*} [MeasurableSpace A] (m η : ℝ)
    (X : A → ℝ) (bs : List (ℕ × Set A)) (ω : PointCloud A) : ℝ≥0∞ :=
  ENNReal.ofReal ((expMarkedTotal m X ω).toReal^(η-((bs.map Prod.fst).sum:ℝ))) *
    distinctCloudIntegral (bs.map (fun b => expMarkedBlock m X b.1 b.2)) (pointCloudMeasure ω) []

def tiltedChildProbability {A : Type*} [MeasurableSpace A] (ν : Measure A)
    (m : ℝ) (X : A → ℝ) (s : Set A) : ℝ≥0∞ :=
  (∫⁻ a in s, ENNReal.ofReal (Real.exp (m*X a)) ∂ν) /
    ENNReal.ofReal (∫ a, Real.exp (m*X a) ∂ν)

def MarkedEPPFStatement : Prop :=
  ∀ (A : Type) (_ : MeasurableSpace A) (_ : MeasurableEq A)
    (ν : Measure A), IsProbabilityMeasure ν →
  ∀ m η : ℝ, 0 < m → m < 1 → 0 ≤ η → η < m →
  ∀ X : A → ℝ, Measurable X → Integrable (fun a => Real.exp (m*X a)) ν →
  ∀ bs : List (ℕ × Set A), bs ≠ [] → (∀ b ∈ bs, 0 < b.1 ∧ MeasurableSet b.2) →
    (∫⁻ ω, markedPartitionNumerator m η X bs ω ∂pointCloudLaw ν) /
      ENNReal.ofReal (∫ ω, (expMarkedTotal m X ω).toReal^η ∂pointCloudLaw ν) =
      ENNReal.ofReal (partitionProduct m η (bs.map Prod.fst)) *
        (bs.map (fun b => tiltedChildProbability ν m X b.2)).prod
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def ReplicaPattern : ℕ → Type
  | 0 => ℕ
  | k+1 => List (ReplicaPattern k)

def replicaPatternSize : (k : ℕ) → ReplicaPattern k → ℕ
  | 0, n => n
  | k+1, bs => (bs.map (replicaPatternSize k)).sum

def ValidReplicaPattern : (k : ℕ) → ReplicaPattern k → Prop
  | 0, n => Nat.lt 0 n
  | k+1, bs => bs ≠ (List.nil : List (ReplicaPattern k)) ∧ ∀ b, List.Mem b bs → ValidReplicaPattern k b

 
def rpcPatternWeight : (ms : List ℝ) → ReplicaPattern ms.length → CascadeTree ms.length → ℝ≥0∞
  | [], _, _ => 1
  | m::ms, bs, ω => ENNReal.ofReal ((cascadeTotal (m::ms) ω).toReal ^
      (-(replicaPatternSize (ms.length+1) bs : ℝ))) *
      distinctCloudIntegral (bs.map (fun b (z : ℝ × CascadeTree ms.length) =>
        (ENNReal.ofReal (z.1^(-1/m))*cascadeTotal ms z.2)^(replicaPatternSize ms.length b) *
          rpcPatternWeight ms b z.2)) (pointCloudMeasure ω) []

def rpcPatternProduct : (ms : List ℝ) → ℝ → ReplicaPattern ms.length → ℝ
  | [], _, _ => 1
  | m::ms, η, bs => partitionProduct m η (bs.map (replicaPatternSize ms.length)) *
      (bs.map (rpcPatternProduct ms m)).prod

def RPCPartitionStatement : Prop :=
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ η : ℝ, 0 ≤ η → (∀ m ∈ ms, η < m) →
  ∀ b : ReplicaPattern ms.length, ValidReplicaPattern ms.length b →
    (∫⁻ ω, ENNReal.ofReal ((cascadeTotal ms ω).toReal^η)*rpcPatternWeight ms b ω ∂cascadeLaw ms) /
      ENNReal.ofReal (∫ ω, (cascadeTotal ms ω).toReal^η ∂cascadeLaw ms) =
      ENNReal.ofReal (rpcPatternProduct ms η b)
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

 

def MarkedReplicaPattern (E : Type) : ℕ → Type
  | 0 => ℕ × (E → ℝ≥0∞)
  | k+1 => List (MarkedReplicaPattern E k)

def markedReplicaShape {E : Type} : (k : ℕ) → MarkedReplicaPattern E k → ReplicaPattern k
  | 0, b => b.1
  | k+1, bs => bs.map (markedReplicaShape k)

def ValidMarkedReplicaPattern {E : Type} [MeasurableSpace E] :
    (k : ℕ) → MarkedReplicaPattern E k → Prop
  | 0, b => 0 < b.1 ∧ Measurable b.2 ∧ ∀ x, b.2 x ≤ 1
  | k+1, bs => bs ≠ (List.nil : List (MarkedReplicaPattern E k)) ∧
      ∀ b, List.Mem b bs → ValidMarkedReplicaPattern k b

def familyReplicaWeight {E : Type} [MeasurableSpace E] [Add E] :
    (ms : List ℝ) → MarkedReplicaPattern E ms.length → (E → ℝ) → E →
      FamilyCascadeTree E ms.length → ℝ≥0∞
  | [], b, _, x, _ => b.2 x
  | m::ms, bs, u, x, ω =>
      ENNReal.ofReal ((familyLeafTotal (m::ms) u x ω).toReal ^
        (-(replicaPatternSize (ms.length+1) (markedReplicaShape (ms.length+1) bs) : ℝ))) *
      distinctCloudIntegral (bs.map (fun b (z : ℝ × (E × FamilyCascadeTree E ms.length)) =>
        (ENNReal.ofReal (z.1^(-1/m))*familyLeafTotal ms u (x+z.2.1) z.2.2)^
          (replicaPatternSize ms.length (markedReplicaShape ms.length b)) *
          familyReplicaWeight ms b u (x+z.2.1) z.2.2)) (pointCloudMeasure ω) []

def familyReplicaMean {E : Type} [MeasurableSpace E] [Add E] :
    (ms : List ℝ) → MarkedReplicaPattern E ms.length → (ℕ → Measure E) → (E → ℝ) → E → ℝ≥0∞
  | [], b, _, _, x => b.2 x
  | m::ms, bs, ν, u, x => (bs.map (fun b => ∫⁻ a,
      familyReplicaMean ms b (fun j => ν (j+1)) u (x+a)
        ∂decoratedTransition m ms ν u x)).prod

def FamilyReplicaStatement : Prop :=
  ∀ (E : Type) (_ : MeasurableSpace E) (_ : MeasurableEq E) (_ : Add E) (_ : MeasurableAdd₂ E),
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ ν : ℕ → Measure E, (∀ j, IsProbabilityMeasure (ν j)) →
  ∀ u : E → ℝ, Measurable u → FamilyMomentsFinite ms ν u →
  ∀ b : MarkedReplicaPattern E ms.length, ValidMarkedReplicaPattern ms.length b →
  ∀ η : ℝ, 0 ≤ η → (∀ m ∈ ms, η < m) → ∀ x : E,
    (∫⁻ ω, ENNReal.ofReal ((familyLeafTotal ms u x ω).toReal^η)*familyReplicaWeight ms b u x ω
      ∂familyCascadeLaw ms.length ν) /
      ENNReal.ofReal (∫ ω, (familyLeafTotal ms u x ω).toReal^η ∂familyCascadeLaw ms.length ν) =
      ENNReal.ofReal (rpcPatternProduct ms η (markedReplicaShape ms.length b)) *
        familyReplicaMean ms b ν u x
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma infinitePi_pair {I A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : I → Measure A) (ν : I → Measure B)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p i => (p.1 i,p.2 i)) = Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  let F : ((I → A) × (I → B)) → I → A × B := fun p i => (p.1 i,p.2 i)
  have hF : Measurable F := by fun_prop
  symm
  apply (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique
  intro s
  let R : ((I → A) × (I → B)) → (s → A) × (s → B) :=
    Prod.map s.restrict s.restrict
  let G : ((s → A) × (s → B)) → s → A × B := fun p i => (p.1 i,p.2 i)
  have hR : Measurable R := by fun_prop
  have hG : Measurable G := by fun_prop
  have he : s.restrict ∘ F = G ∘ R := rfl
  change (((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map F).map s.restrict = _
  have hrs : Measurable (s.restrict : (I → A × B) → s → A × B) := by fun_prop
  rw [Measure.map_map hrs hF, he, ← Measure.map_map hG hR]
  change (((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
    (Prod.map s.restrict s.restrict)).map G = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
  simpa only [G, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
    MeasurableEquiv.coe_mk, MeasurableEquiv.symm, Equiv.symm, Equiv.coe_fn_mk] using
    (measurePreserving_arrowProdEquivProdArrow A B s (fun i => μ i) (fun i => ν i)).symm.map_eq
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def zipPoissonBin {A B : Type*} (p : PoissonBin A × (ℕ → B)) : PoissonBin (A × B) :=
  (p.1.1, fun j => (p.1.2 j,p.2 j))

lemma measurable_zipPoissonBin {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] :
    Measurable (zipPoissonBin (A := A) (B := B)) := by
  fun_prop [zipPoissonBin]

lemma poissonBin_independent_marks {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((poissonBinLaw μ).prod (Measure.infinitePi fun _ : ℕ => ν)).map zipPoissonBin =
      poissonBinLaw (μ.prod ν) := by
  let ρ := Measure.infinitePi fun _ : ℕ => μ
  let η := Measure.infinitePi fun _ : ℕ => ν
  have hp : MeasurePreserving (fun p : (ℕ → A) × (ℕ → B) => fun j => (p.1 j,p.2 j))
      (ρ.prod η) (Measure.infinitePi fun _ : ℕ => μ.prod ν) :=
    ⟨by fun_prop, infinitePi_pair (fun _ : ℕ => μ) (fun _ : ℕ => ν)⟩
  have H := ((MeasurePreserving.id (poissonMeasure 1)).prod hp).comp
    (measurePreserving_prodAssoc (poissonMeasure 1) ρ η)
  exact H.map_eq

def zipPointCloud {A B : Type*} (p : PointCloud A × (ℕ → ℕ → B)) : PointCloud (A × B) :=
  fun n => ((p.1 n).1, fun j => (((p.1 n).2 j).1, (((p.1 n).2 j).2,p.2 n j)))

lemma measurable_zipPointCloud {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] :
    Measurable (zipPointCloud (A := A) (B := B)) := by
  fun_prop [zipPointCloud]

lemma pointCloud_independent_marks {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((pointCloudLaw μ).prod (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => ν)).map
      zipPointCloud = pointCloudLaw (μ.prod ν) := by
  let ρ := poissonBinLaw (cloudUniform.prod μ)
  let η := Measure.infinitePi fun _ : ℕ => ν
  let F : PoissonBin (ℝ × A) × (ℕ → B) → PoissonBin (ℝ × (A × B)) :=
    fun p => mapPoissonBin (fun z => (z.1.1,(z.1.2,z.2))) (zipPoissonBin p)
  have hF : Measurable F := (measurable_mapPoissonBin (by fun_prop)).comp measurable_zipPoissonBin
  have hFlaw : (ρ.prod η).map F = poissonBinLaw (cloudUniform.prod (μ.prod ν)) := by
    rw [show F = (mapPoissonBin (fun z : (ℝ × A) × B => (z.1.1,(z.1.2,z.2)))) ∘ zipPoissonBin from rfl,
      ← Measure.map_map (measurable_mapPoissonBin (by fun_prop)) measurable_zipPoissonBin]
    rw [poissonBin_independent_marks, poissonBinLaw_map _ (by fun_prop)]
    congr 1
    exact (measurePreserving_prodAssoc cloudUniform μ ν).map_eq
  have hpair := infinitePi_pair (fun _ : ℕ => ρ) (fun _ : ℕ => η)
  have hmap := congrArg (fun ζ : Measure (ℕ → (PoissonBin (ℝ × A) × (ℕ → B))) =>
    ζ.map (fun p n => F (p n))) hpair
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_pi _ (fun _ => hF)] at hmap
  simp_rw [hFlaw] at hmap
  exact hmap
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma measurable_coloredStableSum {A : Type*} [MeasurableSpace A] (m : ℝ)
    {Y : A → ℝ≥0} (hY : Measurable Y) : Measurable (coloredStableSum m Y) := by
  apply measurable_pointCloudFunctional
  fun_prop

lemma coloredStable_laplace {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {Y : A → ℝ≥0} (hY : Measurable Y)
    (hi : Integrable (fun a => (Y a:ℝ)^m) ν) (hp : 0 < ∫ a, (Y a:ℝ)^m ∂ν)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, Real.exp (-t*(coloredStableSum m Y ω).toReal) ∂pointCloudLaw ν) =
      Real.exp (-(Real.Gamma (1-m)*(∫ a, (Y a:ℝ)^m ∂ν))*t^m) := by
  let η := ν.map Y
  have : IsProbabilityMeasure η := inferInstance
  have hpow : Measurable (fun y : ℝ≥0 => (y:ℝ)^m) := by fun_prop
  have hiη : Integrable (fun y : ℝ≥0 => (y:ℝ)^m) η :=
    (integrable_map_measure hpow.aestronglyMeasurable hY.aemeasurable).mpr hi
  have hpη : 0 < ∫ y : ℝ≥0, (y:ℝ)^m ∂η := by
    rwa [integral_map hY.aemeasurable hpow.aestronglyMeasurable]
  have hs := stableCloud m hm hm1 η inferInstance hiη hpη
  have hmap : MeasurePreserving (mapPointCloud Y) (pointCloudLaw ν) (markedCloudLaw η) :=
    ⟨measurable_mapPointCloud hY, pointCloudLaw_map ν hY⟩
  have hF : Measurable (fun ω : MarkedCloud => Real.exp (-t*(stableCloudSum m ω).toReal)) := by
    have := measurable_stableCloudSum m
    fun_prop
  have hv := integral_map (μ := pointCloudLaw ν) hmap.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hmap.map_eq] at hv
  simp only [stableCloudSum_mapPointCloud] at hv
  rw [← hv, hs.2.1 t ht, integral_map hY.aemeasurable hpow.aestronglyMeasurable]
  congr 1; ring

lemma integrable_log_of_square {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsFiniteMeasure ν] {X : A → ℝ≥0∞} (hX : Measurable X)
    (hi : Integrable (fun a => |Real.log (X a).toReal|^2) ν) :
    Integrable (fun a => Real.log (X a).toReal) ν := by
  apply ((integrable_const (1:ℝ)).add hi).mono'
    (Real.measurable_log.comp hX.ennreal_toReal).aestronglyMeasurable
  filter_upwards [] with a
  simp only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply]
  nlinarith [sq_nonneg (|Real.log (X a).toReal|-1)]

lemma coloredStable_log_integrable {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {Y : A → ℝ≥0} (hY : Measurable Y)
    (hi : Integrable (fun a => (Y a:ℝ)^m) ν) (hp : 0 < ∫ a, (Y a:ℝ)^m ∂ν) :
    Integrable (fun ω => Real.log (coloredStableSum m Y ω).toReal) (pointCloudLaw ν) :=
  integrable_log_of_square _ (measurable_coloredStableSum m hY)
    (coloredStable_properties ν hm hm1 hY hi hp).2.2
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma probability_eq_of_scalar_laplace (μ ν : Measure ℝ≥0∞)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ n : ℕ, (∫ x, expNeg (n • x) ∂μ) = ∫ x, expNeg (n • x) ∂ν) : μ = ν := by
  let f : ℝ≥0∞ → Unit → ℝ≥0∞ := fun x _ => x
  have hf : Measurable f := Measurable.of_eval (fun _ => measurable_id)
  have : IsProbabilityMeasure (μ.map f) := inferInstance
  have : IsProbabilityMeasure (ν.map f) := inferInstance
  have he : μ.map f = ν.map f := by
    apply probability_eq_of_laplace
    intro d
    have hm : Measurable (fun x : Unit → ℝ≥0∞ => expNeg (d.sum (fun i n => n • x i))) := by
      apply continuous_expNeg.measurable.comp
      apply Finset.measurable_sum
      intro i hi
      simp only [nsmul_eq_mul]
      exact (measurable_pi_apply i : Measurable (fun x : Unit → ℝ≥0∞ => x i)).const_mul (d i : ℝ≥0∞)
    rw [integral_map hf.aemeasurable hm.aestronglyMeasurable,
      integral_map hf.aemeasurable hm.aestronglyMeasurable]
    simpa [f, Finsupp.sum_fintype] using h (d ())
  have hv := congrArg (fun ρ => ρ.map (fun x : Unit → ℝ≥0∞ => x ())) he
  simpa only [Measure.map_map (measurable_pi_apply ()) hf, Function.comp_def, f, Measure.map_id'] using hv

lemma law_eq_of_real_laplace {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : A → ℝ≥0∞} {Y : B → ℝ≥0∞} (hX : Measurable X) (hY : Measurable Y)
    (hXfin : ∀ᵐ a ∂μ, X a ≠ ∞) (hYfin : ∀ᵐ b ∂ν, Y b ≠ ∞)
    (h : ∀ t : ℝ, 0 ≤ t → (∫ a, Real.exp (-t*(X a).toReal) ∂μ) =
      ∫ b, Real.exp (-t*(Y b).toReal) ∂ν) : μ.map X = ν.map Y := by
  have : IsProbabilityMeasure (μ.map X) := inferInstance
  have : IsProbabilityMeasure (ν.map Y) := inferInstance
  apply probability_eq_of_scalar_laplace
  intro n
  have hn : Measurable (fun x : ℝ≥0∞ => expNeg (n • x)) := by
    simpa only [nsmul_eq_mul, Pi.mul_apply, Function.comp_def] using
      (continuous_expNeg.measurable.comp (measurable_const.mul measurable_id) :
        Measurable (fun x : ℝ≥0∞ => expNeg ((n:ℝ≥0∞)*x)))
  rw [integral_map hX.aemeasurable hn.aestronglyMeasurable,
    integral_map hY.aemeasurable hn.aestronglyMeasurable]
  have hx : (fun a => expNeg (n • X a)) =ᵐ[μ] (fun a => Real.exp (-(n:ℝ)*(X a).toReal)) := by
    filter_upwards [hXfin] with a ha
    rw [nsmul_eq_mul, expNeg_eq_of_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) ha),
      ENNReal.toReal_mul, ENNReal.toReal_natCast]
    congr 1; ring
  have hy : (fun b => expNeg (n • Y b)) =ᵐ[ν] (fun b => Real.exp (-(n:ℝ)*(Y b).toReal)) := by
    filter_upwards [hYfin] with b hb
    rw [nsmul_eq_mul, expNeg_eq_of_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hb),
      ENNReal.toReal_mul, ENNReal.toReal_natCast]
    congr 1; ring
  rw [integral_congr_ae hx, integral_congr_ae hy, h n (Nat.cast_nonneg _)]
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma coloredStable_log_shift {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {Y : A → ℝ≥0} (hY : Measurable Y)
    (hi : Integrable (fun a => (Y a:ℝ)^m) ν) (hp : 0 < ∫ a, (Y a:ℝ)^m ∂ν) :
    (∫ ω, Real.log (coloredStableSum m Y ω).toReal ∂pointCloudLaw ν) =
      (1/m)*Real.log (∫ a, (Y a:ℝ)^m ∂ν) +
      ∫ ω, Real.log (coloredStableSum m (fun _ : A => 1) ω).toReal ∂pointCloudLaw ν := by
  let M := ∫ a, (Y a:ℝ)^m ∂ν
  let d := M^(1/m)
  have hd : 0 < d := Real.rpow_pos_of_pos hp _
  have hdm : d^m = M := by
    dsimp [d]
    rw [← Real.rpow_mul hp.le, one_div_mul_cancel hm.ne', Real.rpow_one]
  let S : PointCloud A → ℝ≥0∞ := coloredStableSum m (fun _ : A => 1)
  have hS : Measurable S := measurable_coloredStableSum m measurable_const
  have hi1 : Integrable (fun _ : A => (1:ℝ)^m) ν := by simp
  have hp1 : 0 < ∫ _ : A, (1:ℝ)^m ∂ν := by simp
  have hprop := coloredStable_properties ν hm hm1 (Y := fun _ : A => 1) measurable_const hi1 hp1
  have hX := coloredStable_properties ν hm hm1 hY hi hp
  have hSf : ∀ᵐ ω ∂pointCloudLaw ν, S ω ≠ ∞ := by
    filter_upwards [hprop.1] with ω hω
    exact hω.2.ne
  have hXf : ∀ᵐ ω ∂pointCloudLaw ν, coloredStableSum m Y ω ≠ ∞ := by
    filter_upwards [hX.1] with ω hω
    exact hω.2.ne
  let Z : PointCloud A → ℝ≥0∞ := fun ω => ENNReal.ofReal d*S ω
  have hZ : Measurable Z := measurable_const.mul hS
  have hZf : ∀ᵐ ω ∂pointCloudLaw ν, Z ω ≠ ∞ := by
    filter_upwards [hSf] with ω hω
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω
  have hL (t : ℝ) (ht : 0 ≤ t) :
      (∫ ω, Real.exp (-t*(coloredStableSum m Y ω).toReal) ∂pointCloudLaw ν) =
        ∫ ω, Real.exp (-t*(Z ω).toReal) ∂pointCloudLaw ν := by
    have he (ω : PointCloud A) : Real.exp (-t*(Z ω).toReal) =
        Real.exp (-(t*d)*(S ω).toReal) := by
      dsimp [Z]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le]
      congr 1; ring
    simp_rw [he]
    rw [coloredStable_laplace ν hm hm1 hY hi hp ht,
      coloredStable_laplace ν hm hm1 (Y := fun _ : A => 1) measurable_const hi1 hp1
        (mul_nonneg ht hd.le)]
    simp only [NNReal.coe_one, Real.one_rpow, integral_const, probReal_univ, smul_eq_mul, mul_one]
    rw [Real.mul_rpow ht hd.le, hdm]
    congr 1; dsimp [M]; ring
  have hlaw := law_eq_of_real_laplace (pointCloudLaw ν) (pointCloudLaw ν)
    (measurable_coloredStableSum m hY) hZ hXf hZf hL
  have hlog : Measurable (fun x : ℝ≥0∞ => Real.log x.toReal) :=
    Real.measurable_log.comp measurable_id.ennreal_toReal
  have hv : (∫ ω, Real.log (coloredStableSum m Y ω).toReal ∂pointCloudLaw ν) =
      ∫ ω, Real.log (Z ω).toReal ∂pointCloudLaw ν := by
    rw [← integral_map (measurable_coloredStableSum m hY).aemeasurable hlog.aestronglyMeasurable,
      hlaw, integral_map hZ.aemeasurable hlog.aestronglyMeasurable]
  have he : (fun ω => Real.log (Z ω).toReal) =ᵐ[pointCloudLaw ν]
      (fun ω => Real.log d+Real.log (S ω).toReal) := by
    filter_upwards [hprop.1] with ω hω
    have hs : 0 < (S ω).toReal := ENNReal.toReal_pos hω.1.ne' hω.2.ne
    dsimp [Z]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le, Real.log_mul hd.ne' hs.ne']
  rw [hv, integral_congr_ae he, integral_add (integrable_const _)
    (coloredStable_log_integrable ν hm hm1 (Y := fun _ : A => 1) measurable_const hi1 hp1)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [show Real.log d = (1/m)*Real.log M by exact Real.log_rpow hp _]
end MicroscopicJamming

end

end OAI
