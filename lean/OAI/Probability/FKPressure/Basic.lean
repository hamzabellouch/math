import Mathlib

namespace OAI

 

 
section

 

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace BelowOne

abbrev Time := Set.Icc (0 : ℝ) 1
abbrev Curve := C(Time, ℂ)
abbrev GridPoint := ℤ × ℤ

instance : MeasurableSpace Curve := borel Curve
instance : BorelSpace Curve := ⟨rfl⟩

 
structure IncreasingReparam where
  homeomorph : Time ≃ₜ Time
  increasing : StrictMono homeomorph

instance : Inhabited IncreasingReparam :=
  ⟨⟨Homeomorph.refl _, fun _ _ h => h⟩⟩

 
def curveDistance (α β : Curve) : ℝ :=
  sInf {r : ℝ | ∃ φ ψ : IncreasingReparam,
    r = sSup (Set.range fun t : Time => dist (α (φ.homeomorph t)) (β (ψ.homeomorph t)))}

 

def IsCurveTest (f : Curve → ℝ) : Prop :=
  (∃ C : ℝ, ∀ α, |f α| ≤ C) ∧
  ∀ α, ∀ ε > 0, ∃ r > 0, ∀ β, curveDistance α β < r → |f α - f β| < ε

def gridEmbed (δ : ℝ) (v : GridPoint) : ℂ :=
  ⟨δ * v.1, δ * v.2⟩

def gridNeighbor (v w : GridPoint) : Prop :=
  (v.1 = w.1 ∧ |v.2 - w.2| = 1) ∨
  (v.2 = w.2 ∧ |v.1 - w.1| = 1)

 
def interpolate (points : List ℂ) (t : Time) : ℂ :=
  if (t : ℝ) = 1 then points.getLast?.getD 0 else
    let s := (t : ℝ) * (points.length - 1)
    let j := Nat.floor s
    let θ : ℂ := ((s - j : ℝ) : ℂ)
    (1 - θ) * points[j]?.getD 0 + θ * points[j + 1]?.getD 0

def cycleNext {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

def cyclePrev {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn⟩

 

structure SmoothMarkedJordan where
  domain : Set ℂ
  isOpen : IsOpen domain
  isConnected : IsConnected domain
  bounded : Bornology.IsBounded domain
  boundary : ℝ → ℂ
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) boundary
  periodic : Function.Periodic boundary 1
  simple : Set.InjOn boundary (Set.Ico 0 1)
  regular : ∀ t, deriv boundary t ≠ 0
  frontier : frontier domain = boundary '' Set.Icc 0 1
  positive_orientation :
    0 < ∫ t in (0 : ℝ)..1,
      (boundary t).re * (deriv boundary t).im -
        (boundary t).im * (deriv boundary t).re
  secondMark : ℝ
  secondMark_pos : 0 < secondMark
  secondMark_lt : secondMark < 1

def SmoothMarkedJordan.a (D : SmoothMarkedJordan) := D.boundary 0
def SmoothMarkedJordan.b (D : SmoothMarkedJordan) := D.boundary D.secondMark

 

structure LatticePolygon (δ : ℝ) where
  domain : Set ℂ
  isOpen : IsOpen domain
  isConnected : IsConnected domain
  bounded : Bornology.IsBounded domain
  nVertices : ℕ
  vertices : Fin nVertices → GridPoint
  vertices_injective : Function.Injective vertices
  all_vertices : ∀ v : GridPoint,
    (∃ i, vertices i = v) ↔ gridEmbed δ v ∈ closure domain
  nBoundary : ℕ
  boundary_pos : 0 < nBoundary
  boundary_three : 3 ≤ nBoundary
  boundaryVertex : Fin nBoundary → Fin nVertices
  boundary_injective : Function.Injective boundaryVertex
  boundary_neighbor : ∀ i,
    gridNeighbor (vertices (boundaryVertex i))
      (vertices (boundaryVertex (cycleNext boundary_pos i)))
  boundary_segment : ∀ i,
    segment ℝ (gridEmbed δ (vertices (boundaryVertex i)))
      (gridEmbed δ (vertices (boundaryVertex (cycleNext boundary_pos i)))) ⊆
      closure domain
  boundaryCurve : Curve
  boundary_interpolation : ∀ t,
    boundaryCurve t = interpolate
      ((List.ofFn fun i => gridEmbed δ (vertices (boundaryVertex i))) ++
        [gridEmbed δ (vertices (boundaryVertex ⟨0, boundary_pos⟩))]) t
  boundary_simple : ∀ s t : Time,
    (s : ℝ) < 1 → (t : ℝ) < 1 → boundaryCurve s = boundaryCurve t → s = t
  frontier : frontier domain = Set.range boundaryCurve
  positive_orientation :
    0 < ∑ i : Fin nBoundary,
      ((gridEmbed δ (vertices (boundaryVertex i))).re *
        (gridEmbed δ (vertices (boundaryVertex (cycleNext boundary_pos i)))).im -
      (gridEmbed δ (vertices (boundaryVertex i))).im *
        (gridEmbed δ (vertices (boundaryVertex (cycleNext boundary_pos i)))).re)
  secondMark : Fin nBoundary
  secondMark_ne : secondMark.val ≠ 0
  wiredForward : Bool

namespace LatticePolygon

variable {δ : ℝ} (P : LatticePolygon δ)

abbrev Vertex := Fin P.nVertices

def position (v : P.Vertex) : ℂ := gridEmbed δ (P.vertices v)

def graph : SimpleGraph P.Vertex :=
  SimpleGraph.fromRel fun v w =>
    gridNeighbor (P.vertices v) (P.vertices w) ∧
      segment ℝ (P.position v) (P.position w) ⊆ closure P.domain

def edges : Finset (Sym2 P.Vertex) := P.graph.edgeSet.toFinite.toFinset

def first : Fin P.nBoundary := ⟨0, P.boundary_pos⟩

def aVertex : P.Vertex := P.boundaryVertex P.first
def bVertex : P.Vertex := P.boundaryVertex P.secondMark

def wiredVertices : Finset P.Vertex :=
  Finset.univ.filter fun v => ∃ i : Fin P.nBoundary,
    P.boundaryVertex i = v ∧
      if P.wiredForward then i.val ≤ P.secondMark.val
      else P.secondMark.val ≤ i.val ∨ i.val = 0

 

def wiredEdges : Finset (Sym2 P.Vertex) :=
  ((Finset.univ : Finset (Fin P.nBoundary)).filter fun i =>
    if P.wiredForward then i.val < P.secondMark.val
    else P.secondMark.val ≤ i.val).image fun i =>
      s(P.boundaryVertex i, P.boundaryVertex (cycleNext P.boundary_pos i))

 

def wiredConfiguration (A : Finset (Sym2 P.Vertex)) : SimpleGraph P.Vertex :=
  SimpleGraph.fromRel fun v w =>
    (s(v,w) ∈ A) ∨ (v ∈ P.wiredVertices ∧ w ∈ P.wiredVertices)

def componentCount (A : Finset (Sym2 P.Vertex)) : ℕ :=
  Nat.card (P.wiredConfiguration A).ConnectedComponent

 
def configurationWeight (q : ℝ) (A : Finset (Sym2 P.Vertex)) : ℝ :=
  let p := Real.sqrt q / (1 + Real.sqrt q)
  p ^ A.card * (1 - p) ^ (P.edges.card - A.card) * q ^ P.componentCount A

def partitionFunction (q : ℝ) : ℝ :=
  ∑ A ∈ P.edges.powerset, P.configurationWeight q A

 
structure Dart where
  source : P.Vertex
  target : P.Vertex
  adjacent : P.graph.Adj source target

instance : Finite P.Dart :=
  Finite.of_injective (fun e : P.Dart => (e.source, e.target)) (by
    rintro ⟨s, t, h⟩ ⟨s', t', h'⟩ he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    rfl)

instance : Fintype P.Dart := Fintype.ofFinite _
instance : DecidableEq P.Dart := Classical.decEq _

def Dart.reverse (e : P.Dart) : P.Dart :=
  ⟨e.target, e.source, P.graph.adj_symm e.adjacent⟩

def dartPosition (e : P.Dart) : ℂ :=
  (P.position e.source + P.position e.target) / 2

 
def dartDirection (e : P.Dart) : ℕ :=
  if (P.vertices e.source).1 < (P.vertices e.target).1 then 0 else
  if (P.vertices e.source).2 < (P.vertices e.target).2 then 1 else
  if (P.vertices e.target).1 < (P.vertices e.source).1 then 2 else 3

def angularSteps (clockwise : Bool) (e f : P.Dart) : ℕ :=
  let k := if clockwise then
    (P.dartDirection e + 4 - P.dartDirection f) % 4 else
    (P.dartDirection f + 4 - P.dartDirection e) % 4
  if k = 0 then 4 else k

 
def IsNextDart (clockwise : Bool) (e f : P.Dart) : Prop :=
  e.source = f.source ∧ ∀ g : P.Dart, e.source = g.source →
    P.angularSteps clockwise e f ≤ P.angularSteps clockwise e g

 

def IsSwitched (A : Finset (Sym2 P.Vertex)) (e f : P.Dart) : Prop :=
  if s(e.source, e.target) ∈ A ∪ P.wiredEdges then f = e.reverse P else f = e

def IsContourSuccessor (A : Finset (Sym2 P.Vertex)) (e f : P.Dart) : Prop :=
  if P.wiredForward then ∃ h, P.IsNextDart true e h ∧ P.IsSwitched A h f
  else ∃ h, P.IsSwitched A e h ∧ P.IsNextDart false h f

 
def IsInitialDart (A : Finset (Sym2 P.Vertex)) (e : P.Dart) : Prop :=
  if P.wiredForward then ∃ h : P.Dart,
    h.source = P.aVertex ∧
    h.target = P.boundaryVertex (cyclePrev P.boundary_pos P.first) ∧
    P.IsSwitched A h e
  else e.source = P.aVertex ∧
    e.target = P.boundaryVertex (cycleNext P.boundary_pos P.first)

def IsFinalDart (A : Finset (Sym2 P.Vertex)) (e : P.Dart) : Prop :=
  if P.wiredForward then e.source = P.bVertex ∧
    e.target = P.boundaryVertex (cycleNext P.boundary_pos P.secondMark)
  else ∃ h : P.Dart,
    h.source = P.bVertex ∧
    h.target = P.boundaryVertex (cyclePrev P.boundary_pos P.secondMark) ∧
    P.IsSwitched A h e

 

def IsInterface (A : Finset (Sym2 P.Vertex)) (η : Curve) : Prop :=
  ∃ walk : List P.Dart,
    walk ≠ [] ∧ walk.Nodup ∧
    (∃ e, walk.head? = some e ∧ P.IsInitialDart A e) ∧
    (∃ e, walk.getLast? = some e ∧ P.IsFinalDart A e) ∧
    walk.IsChain (P.IsContourSuccessor A) ∧
    ∀ t, η t = interpolate
      (P.position P.aVertex :: walk.map P.dartPosition ++ [P.position P.bVertex]) t

end LatticePolygon

 

structure MarkedApproximation (D : SmoothMarkedJordan) where
  mesh : ℕ → ℝ
  mesh_pos : ∀ n, 0 < mesh n
  mesh_zero : Tendsto mesh atTop (𝓝 0)
  polygon : ∀ n, LatticePolygon (mesh n)
  boundaryReparam : ℕ → IncreasingReparam
  boundary_uniform :
    Tendsto (fun n => sSup (Set.range fun t : Time =>
      dist ((polygon n).boundaryCurve ((boundaryReparam n).homeomorph t))
        (D.boundary t))) atTop (𝓝 0)
  marked_uniform :
    Tendsto (fun n =>
      (((boundaryReparam n).homeomorph.symm
        ⟨((polygon n).secondMark.val : ℝ) / (polygon n).nBoundary,
          by
            have hn : (0 : ℝ) < (polygon n).nBoundary := by
              exact_mod_cast (polygon n).boundary_pos
            constructor
            · exact div_nonneg (Nat.cast_nonneg _) hn.le
            · exact (div_le_one hn).2 (by exact_mod_cast (polygon n).secondMark.isLt.le)⟩ : Time) : ℝ))
      atTop (𝓝 D.secondMark)
  interface : ∀ n, Finset (Sym2 (polygon n).Vertex) → Curve
  interface_drawing : ∀ n A, A ⊆ (polygon n).edges →
    (polygon n).IsInterface A (interface n A)

 
def interfaceExpectation {D : SmoothMarkedJordan} (M : MarkedApproximation D)
    (q : ℝ) (n : ℕ) (f : Curve → ℝ) : ℝ :=
  (∑ A ∈ (M.polygon n).edges.powerset,
    (M.polygon n).configurationWeight q A * f (M.interface n A)) /
      (M.polygon n).partitionFunction q

 
def kappa (q : ℝ) : ℝ := 4 * Real.pi / Real.arccos (-Real.sqrt q / 2)

def upperHalfPlane : Set ℂ := {z | 0 < z.im}

def pastTrace (γ : ℝ≥0 → ℂ) (t : ℝ≥0) : Set ℂ := γ '' Set.Iic t

 
def loewnerDomain (γ : ℝ≥0 → ℂ) (t : ℝ≥0) : Set ℂ :=
  {z ∈ upperHalfPlane \ pastTrace γ t |
    ¬ Bornology.IsBounded
      (connectedComponentIn (upperHalfPlane \ pastTrace γ t) z)}

 
def inverseOn (g : ℂ → ℂ) (U : Set ℂ) (w : ℂ) : ℂ := by
  classical
  exact if h : ∃ z ∈ U, g z = w then h.choose else 0

 

def IsLoewnerTrace (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (g : ℝ≥0 → ℂ → ℂ) : Prop :=
  Continuous γ ∧ γ 0 = 0 ∧
  (∀ t, 0 ≤ (γ t).im) ∧
  (∀ R : ℝ, ∃ T : ℝ≥0, ∀ t ≥ T, R ≤ ‖γ t‖) ∧
  (∀ z ∈ upperHalfPlane, g 0 z = z) ∧
  (∀ t, DifferentiableOn ℂ (g t) (loewnerDomain γ t)) ∧
  (∀ t, Set.BijOn (g t) (loewnerDomain γ t) upperHalfPlane) ∧
  (∀ t,
    Tendsto (fun z => g t z - z)
      (Filter.cocompact ℂ ⊓ Filter.principal (loewnerDomain γ t)) (𝓝 0)) ∧
  (∀ t,
    Tendsto (fun z => z * (g t z - z))
      (Filter.cocompact ℂ ⊓ Filter.principal (loewnerDomain γ t)) (𝓝 (2 * (t : ℝ) : ℂ))) ∧
  (∀ t z, z ∈ loewnerDomain γ t →
    HasDerivWithinAt (fun s : ℝ => g (Real.toNNReal s) z)
      (2 / (g t z - (W t : ℂ))) (Set.Ici 0) (t : ℝ)) ∧
  (∀ t,
    Tendsto (fun y : ℝ => inverseOn (g t) (loewnerDomain γ t)
      ((W t : ℂ) + Complex.I * y)) (𝓝[>] 0) (𝓝 (γ t)))

def cayley (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)

 

def IsDomainCoordinate (D : SmoothMarkedJordan) (φ : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ φ (Metric.ball 0 1) ∧
  Set.BijOn φ (Metric.ball 0 1) D.domain ∧
  ContinuousOn φ (Metric.closedBall 0 1) ∧
  Set.BijOn φ (Metric.closedBall 0 1) (closure D.domain) ∧
  φ (-1) = D.a ∧ φ 1 = D.b

 
abbrev BrownianSample := C(ℝ≥0, ℝ)

instance : MeasurableSpace BrownianSample := borel BrownianSample
instance : BorelSpace BrownianSample := ⟨rfl⟩

 

def IsChordalSLE (κ : ℝ) (D : SmoothMarkedJordan) (μ : Measure Curve) : Prop :=
  IsProbabilityMeasure μ ∧
  ∃ (P : Measure BrownianSample) (φ : ℂ → ℂ)
      (γ : BrownianSample → ℝ≥0 → ℂ)
      (g : BrownianSample → ℝ≥0 → ℂ → ℂ)
      (η : BrownianSample → Curve),
    IsProbabilityMeasure P ∧
    IsBrownianReal (fun t ω => ω t) P ∧
    IsDomainCoordinate D φ ∧
    Measurable η ∧ μ = Measure.map η P ∧
    (∀ᵐ ω ∂P,
      IsLoewnerTrace (fun t => Real.sqrt κ * ω t) (γ ω) (g ω) ∧
      (∀ u : Time, (u : ℝ) < 1 →
        η ω u = φ (cayley (γ ω (Real.toNNReal ((u : ℝ) / (1 - (u : ℝ))))))) ∧
      η ω ⟨1, by simp⟩ = D.b)

end BelowOne

 

noncomputable section
open SimpleGraph Function
namespace BelowOne.FKComponents

variable {V : Type*} {G : SimpleGraph V}

lemma eq_of_walk {β : Sort*} {f : V → β}
    (hf : ∀ ⦃v w⦄, G.Adj v w → f v = f w) {v w : V} (p : G.Walk v w) :
    f v = f w := by
  induction p with
  | nil => rfl
  | cons h p ih => exact (hf h).trans ih

lemma component_card_sup_edge_of_reachable [Finite V] {a b : V}
    (hab : G.Reachable a b) :
    Nat.card (G ⊔ edge a b).ConnectedComponent = Nat.card G.ConnectedComponent := by
  classical
  let H := G ⊔ edge a b
  have hconst : ∀ ⦃v w⦄, H.Adj v w → G.connectedComponentMk v = G.connectedComponentMk w := by
    intro v w hvw
    rcases hvw with hG | he
    · exact ConnectedComponent.sound hG.reachable
    · rcases (edge_adj _ _ _ _).mp he with ⟨⟨rfl,rfl⟩ | ⟨rfl,rfl⟩,_⟩
      · exact ConnectedComponent.sound hab
      · exact ConnectedComponent.sound hab.symm
  let f : H.ConnectedComponent → G.ConnectedComponent :=
    ConnectedComponent.lift G.connectedComponentMk (fun _ _ p _ => eq_of_walk hconst p)
  let g : G.ConnectedComponent → H.ConnectedComponent :=
    ConnectedComponent.map (Hom.ofLE le_sup_left)
  let e : H.ConnectedComponent ≃ G.ConnectedComponent :=
    { toFun := f
      invFun := g
      left_inv := fun c => c.ind fun v => rfl
      right_inv := fun c => c.ind fun v => rfl }
  exact Nat.card_congr e

lemma component_card_sup_edge_of_not_reachable [Finite V] {a b : V}
    (hab : ¬ G.Reachable a b) :
    Nat.card (G ⊔ edge a b).ConnectedComponent + 1 = Nat.card G.ConnectedComponent := by
  classical
  let H := G ⊔ edge a b
  let A := G.connectedComponentMk a
  let B := G.connectedComponentMk b
  have hAB : A ≠ B := fun h => hab (ConnectedComponent.exact h)
  let collapse : G.ConnectedComponent → {c : G.ConnectedComponent // c ≠ B} :=
    fun c => ⟨if c = B then A else c, by split_ifs with h; exact hAB; exact h⟩
  have hcollapse : collapse A = collapse B := by
    apply Subtype.ext
    simp [collapse,hAB]
  have hconst : ∀ ⦃v w⦄, H.Adj v w →
      collapse (G.connectedComponentMk v) = collapse (G.connectedComponentMk w) := by
    intro v w hvw
    rcases hvw with hG | he
    · exact congrArg collapse (ConnectedComponent.sound hG.reachable)
    · rcases (edge_adj _ _ _ _).mp he with ⟨⟨rfl,rfl⟩ | ⟨rfl,rfl⟩,_⟩
      · exact hcollapse
      · exact hcollapse.symm
  let f : H.ConnectedComponent → {c : G.ConnectedComponent // c ≠ B} :=
    ConnectedComponent.lift (fun v => collapse (G.connectedComponentMk v))
      (fun _ _ p _ => eq_of_walk hconst p)
  let g : G.ConnectedComponent → H.ConnectedComponent :=
    ConnectedComponent.map (Hom.ofLE le_sup_left)
  have hgab : g A = g B := by
    apply ConnectedComponent.sound
    apply SimpleGraph.Adj.reachable
    exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,fun h => hAB (congrArg G.connectedComponentMk h)⟩)
  have hfg (c : G.ConnectedComponent) : f (g c) = collapse c := by
    exact c.ind fun v => rfl
  let e : H.ConnectedComponent ≃ {c : G.ConnectedComponent // c ≠ B} :=
    { toFun := f
      invFun := fun c => g c.val
      left_inv := by
        intro c
        induction c using ConnectedComponent.ind with
        | h v =>
          change g (if G.connectedComponentMk v = B then A else G.connectedComponentMk v) = g (G.connectedComponentMk v)
          split_ifs with hv
          · rw [hv]; exact hgab
          · rfl
      right_inv := by
        intro c
        rw [hfg]
        apply Subtype.ext
        simp [collapse,c.property] }
  have hcard := Nat.card_congr e
  let := Fintype.ofFinite G.ConnectedComponent
  let := Fintype.ofFinite H.ConnectedComponent
  simp only [Nat.card_eq_fintype_card] at hcard ⊢
  rw [hcard]
  have hsub := Fintype.card_subtype_compl (fun c : G.ConnectedComponent => c = B)
  have hpos : 0 < Fintype.card G.ConnectedComponent := Fintype.card_pos_iff.mpr ⟨A⟩
  simp only [Fintype.card_unique] at hsub
  change Fintype.card {c : G.ConnectedComponent // c ≠ B} =
    Fintype.card G.ConnectedComponent - 1 at hsub
  omega

lemma component_card_sup_edge [Finite V] (a b : V) :
    Nat.card (G ⊔ edge a b).ConnectedComponent = Nat.card G.ConnectedComponent ∨
      Nat.card (G ⊔ edge a b).ConnectedComponent + 1 = Nat.card G.ConnectedComponent := by
  by_cases h : G.Reachable a b
  · exact Or.inl (component_card_sup_edge_of_reachable h)
  · exact Or.inr (component_card_sup_edge_of_not_reachable h)

end BelowOne.FKComponents

namespace BelowOne.FKFinite
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*}

 
def configuration (G : SimpleGraph V) (A : Finset (Sym2 V)) : SimpleGraph V :=
  G ⊔ fromEdgeSet (A : Set (Sym2 V))

def count (G : SimpleGraph V) (A : Finset (Sym2 V)) : ℕ :=
  Nat.card (configuration G A).ConnectedComponent

def weight (G : SimpleGraph V) (q v : ℝ) (A : Finset (Sym2 V)) : ℝ :=
  v ^ A.card * q ^ count G A

def partition (G : SimpleGraph V) (q v : ℝ) (E : Finset (Sym2 V)) : ℝ :=
  ∑ A ∈ E.powerset, weight G q v A

lemma weight_pos (G : SimpleGraph V) {q v : ℝ} (hq : 0 < q) (hv : 0 < v)
    (A : Finset (Sym2 V)) : 0 < weight G q v A := by
  exact mul_pos (pow_pos hv _) (pow_pos hq _)

lemma partition_pos (G : SimpleGraph V) {q v : ℝ} (hq : 0 < q) (hv : 0 < v)
    (E : Finset (Sym2 V)) : 0 < partition G q v E := by
  apply sum_pos
  · intro A hA
    exact weight_pos G hq hv A
  · exact ⟨∅,by simp⟩

lemma configuration_insert (G : SimpleGraph V) (A : Finset (Sym2 V)) (a b : V) :
    configuration G (insert s(a,b) A) = configuration G A ⊔ edge a b := by
  classical
  ext u w
  simp only [configuration, sup_adj, fromEdgeSet_adj, mem_coe, Finset.mem_insert,
    edge, Set.mem_singleton_iff]
  tauto

lemma configuration_union (G : SimpleGraph V) (A F : Finset (Sym2 V)) :
    configuration G (A ∪ F) = configuration (configuration G F) A := by
  classical
  ext u w
  simp only [configuration,sup_adj,fromEdgeSet_adj,mem_coe,Finset.mem_union]
  tauto

lemma weight_union (G : SimpleGraph V) (q v : ℝ) {A F : Finset (Sym2 V)}
    (hAF : Disjoint A F) :
    weight G q v (A ∪ F) = v ^ F.card * weight (configuration G F) q v A := by
  classical
  simp only [weight,count,configuration_union,card_union_of_disjoint hAF,pow_add]
  ring

 

theorem domain_markov (G : SimpleGraph V) {q v : ℝ} (hv : 0 < v)
    {S F : Finset (Sym2 V)} (hSF : Disjoint S F) (f : Finset (Sym2 V) → ℝ) :
    (∑ A ∈ S.powerset, weight G q v (A ∪ F) * f A) /
        (∑ A ∈ S.powerset, weight G q v (A ∪ F)) =
      (∑ A ∈ S.powerset, weight (configuration G F) q v A * f A) /
        partition (configuration G F) q v S := by
  classical
  have hx : ∀ A ∈ S.powerset, weight G q v (A ∪ F) =
      v ^ F.card * weight (configuration G F) q v A := by
    intro A hA
    exact weight_union G q v (hSF.mono_left (mem_powerset.mp hA))
  simp_rw [sum_congr rfl hx]
  have hn : (∑ A ∈ S.powerset, weight G q v (A ∪ F) * f A) =
      v ^ F.card * (∑ A ∈ S.powerset, weight (configuration G F) q v A * f A) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro A hA
    rw [hx A hA]
    ring
  rw [hn,← mul_sum]
  change _ / (v ^ F.card * partition (configuration G F) q v S) = _
  exact mul_div_mul_left _ _ (ne_of_gt (pow_pos hv _))

variable [Finite V]

lemma weight_insert_connected (G : SimpleGraph V) (q v : ℝ) (A : Finset (Sym2 V))
    {a b : V} (he : s(a,b) ∉ A) (hab : (configuration G A).Reachable a b) :
    weight G q v (insert s(a,b) A) = v * weight G q v A := by
  classical
  have hc := FKComponents.component_card_sup_edge_of_reachable hab
  simp only [weight,count,configuration_insert,card_insert_of_notMem he,pow_succ]
  rw [hc]
  ring

lemma weight_insert_separated (G : SimpleGraph V) (q v : ℝ) (A : Finset (Sym2 V))
    {a b : V} (he : s(a,b) ∉ A) (hab : ¬(configuration G A).Reachable a b) :
    q * weight G q v (insert s(a,b) A) = v * weight G q v A := by
  classical
  have hc := FKComponents.component_card_sup_edge_of_not_reachable hab
  unfold weight count
  rw [configuration_insert,card_insert_of_notMem he,← hc,pow_succ,pow_succ]
  ring

 

theorem edge_conditional_probability (G : SimpleGraph V) {q v : ℝ}
    (hq : 0 < q) (hv : 0 < v) (A : Finset (Sym2 V)) {a b : V}
    (he : s(a,b) ∉ A) :
    weight G q v (insert s(a,b) A) /
        (weight G q v A + weight G q v (insert s(a,b) A)) =
      if (configuration G A).Reachable a b then v/(1+v) else v/(q+v) := by
  classical
  have hw := weight_pos G hq hv A
  split_ifs with hab
  · rw [weight_insert_connected G q v A he hab]
    apply (div_eq_div_iff (ne_of_gt (add_pos hw (mul_pos hv hw)))
      (ne_of_gt (add_pos zero_lt_one hv))).mpr
    ring
  · have hc := weight_insert_separated G q v A he hab
    have hi := weight_pos G hq hv (insert s(a,b) A)
    apply (div_eq_div_iff (ne_of_gt (add_pos hw hi)) (ne_of_gt (add_pos hq hv))).mpr
    nlinarith

end BelowOne.FKFinite

namespace BelowOne.LatticePolygon
open Finset SimpleGraph
variable {δ : ℝ} (P : LatticePolygon δ)

def wireGraph : SimpleGraph P.Vertex :=
  fromRel fun v w => v ∈ P.wiredVertices ∧ w ∈ P.wiredVertices

lemma wiredConfiguration_eq (A : Finset (Sym2 P.Vertex)) :
    P.wiredConfiguration A = FKFinite.configuration P.wireGraph A := by
  classical
  ext v w
  simp only [wiredConfiguration,wireGraph,FKFinite.configuration,fromRel_adj,
    sup_adj,fromEdgeSet_adj,mem_coe,Sym2.eq_swap]
  tauto

lemma componentCount_eq (A : Finset (Sym2 P.Vertex)) :
    P.componentCount A = FKFinite.count P.wireGraph A := by
  unfold componentCount FKFinite.count
  rw [P.wiredConfiguration_eq]

lemma configurationWeight_odds {q : ℝ} (hq : 0 < q) (A : Finset (Sym2 P.Vertex))
    (hA : A ⊆ P.edges) :
    P.configurationWeight q A =
      (1 / (1 + Real.sqrt q)) ^ P.edges.card *
        FKFinite.weight P.wireGraph q (Real.sqrt q) A := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hd : 1 + Real.sqrt q ≠ 0 := ne_of_gt (by linarith)
  have hp : 1 - Real.sqrt q / (1 + Real.sqrt q) = 1/(1+Real.sqrt q) := by
    field_simp
    ring
  have hc : A.card + (P.edges.card - A.card) = P.edges.card :=
    Nat.add_sub_of_le (card_le_card hA)
  unfold configurationWeight FKFinite.weight
  dsimp only
  rw [P.componentCount_eq,hp]
  rw [div_eq_mul_one_div, mul_pow, ← hc, pow_add, Nat.add_sub_cancel_left]
  ring

lemma partitionFunction_odds {q : ℝ} (hq : 0 < q) :
    P.partitionFunction q = (1 / (1 + Real.sqrt q)) ^ P.edges.card *
      FKFinite.partition P.wireGraph q (Real.sqrt q) P.edges := by
  unfold partitionFunction FKFinite.partition
  rw [mul_sum]
  apply sum_congr rfl
  intro A hA
  exact P.configurationWeight_odds hq A (mem_powerset.mp hA)

 
theorem normalized_configurationWeight_odds {q : ℝ} (hq : 0 < q)
    (A : Finset (Sym2 P.Vertex)) (hA : A ⊆ P.edges) :
    P.configurationWeight q A / P.partitionFunction q =
      FKFinite.weight P.wireGraph q (Real.sqrt q) A /
        FKFinite.partition P.wireGraph q (Real.sqrt q) P.edges := by
  rw [P.configurationWeight_odds hq A hA,P.partitionFunction_odds hq]
  exact mul_div_mul_left _ _ (ne_of_gt (pow_pos (one_div_pos.mpr
    (by have := Real.sqrt_nonneg q; linarith)) _))

end BelowOne.LatticePolygon

end
end
end

 
section

 

noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
namespace BelowOne.FKPressure
variable {V I : Type*} [Finite V]

 
def graph (G : SimpleGraph V) (ends : I → V × V) (A : Finset I) : SimpleGraph V :=
  G ⊔ A.sup (fun e => edge (ends e).1 (ends e).2)

def components (G : SimpleGraph V) (ends : I → V × V) (A : Finset I) : ℕ :=
  Nat.card (graph G ends A).ConnectedComponent

 
def partition (G : SimpleGraph V) (ends : I → V × V) (s : ℝ) (w : I → ℝ)
    (E : Finset I) : ℝ :=
  ∑ A ∈ E.powerset, (∏ e ∈ A, w e) * s ^ components G ends A

omit [Finite V] in
@[simp] lemma graph_empty (G : SimpleGraph V) (ends : I → V × V) :
    graph G ends ∅ = G := by simp [graph]

omit [Finite V] in
lemma graph_mono (G : SimpleGraph V) (ends : I → V × V) {A B : Finset I}
    (h : A ⊆ B) : graph G ends A ≤ graph G ends B := by
  exact sup_le_sup_left (Finset.sup_mono h) _

omit [Finite V] in
lemma graph_insert (G : SimpleGraph V) (ends : I → V × V) (e : I) (A : Finset I) :
    graph G ends (insert e A) = graph G ends A ⊔ edge (ends e).1 (ends e).2 := by
  classical
  simp [graph, sup_left_comm, sup_comm]

omit [Finite V] in
lemma graph_contracted (G : SimpleGraph V) (ends : I → V × V) (e : I) (A : Finset I) :
    graph (G ⊔ edge (ends e).1 (ends e).2) ends A =
      graph G ends A ⊔ edge (ends e).1 (ends e).2 := by
  simp [graph, sup_assoc, sup_left_comm, sup_comm]

omit [Finite V] in
@[simp] lemma partition_empty (G : SimpleGraph V) (ends : I → V × V)
    (s : ℝ) (w : I → ℝ) : partition G ends s w ∅ = s ^ Nat.card G.ConnectedComponent := by
  simp [partition, components]

 
omit [Finite V] in
lemma deletion_contraction (G : SimpleGraph V) (ends : I → V × V)
    (s : ℝ) (w : I → ℝ) {e : I} {E : Finset I} (he : e ∉ E) :
    partition G ends s w (insert e E) = partition G ends s w E +
      w e * partition (G ⊔ edge (ends e).1 (ends e).2) ends s w E := by
  classical
  unfold partition
  rw [sum_powerset_insert he, mul_sum]
  congr 1
  apply sum_congr rfl
  intro A hA
  have heA : e ∉ A := fun h => he (mem_powerset.mp hA h)
  rw [prod_insert heA]
  simp only [components,graph_insert,graph_contracted]
  ring

 
lemma separating_edge_count (G : SimpleGraph V) (ends : I → V × V)
    {e : I} {E A : Finset I} (h : ¬(graph G ends E).Reachable (ends e).1 (ends e).2)
    (hA : A ⊆ E) :
    components (G ⊔ edge (ends e).1 (ends e).2) ends A + 1 = components G ends A := by
  unfold components
  rw [graph_contracted]
  apply FKComponents.component_card_sup_edge_of_not_reachable
  exact fun hr => h (hr.mono (graph_mono G ends hA))

 
lemma separating_edge_partition (G : SimpleGraph V) (ends : I → V × V)
    (s : ℝ) (w : I → ℝ) {e : I} {E : Finset I}
    (h : ¬(graph G ends E).Reachable (ends e).1 (ends e).2) :
    partition G ends s w E =
      s * partition (G ⊔ edge (ends e).1 (ends e).2) ends s w E := by
  unfold partition
  rw [mul_sum]
  apply sum_congr rfl
  intro A hA
  rw [← separating_edge_count G ends h (mem_powerset.mp hA),pow_succ]
  ring

 

theorem negative_partition (G : SimpleGraph V) (ends : I → V × V)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (w : I → ℝ) (E : Finset I)
    (hw : ∀ e ∈ E, 1 ≤ w e) (hc : components G ends E = 1) :
    partition G ends (-u) w E < 0 := by
  classical
  induction E using Finset.induction_on generalizing G with
  | empty =>
    simp only [components,graph_empty] at hc
    simpa [hc] using neg_neg_of_pos hu
  | @insert e E he ih =>
    have hwE : ∀ f ∈ E, 1 ≤ w f := fun f hf => hw f (mem_insert_of_mem hf)
    have hwe : 1 ≤ w e := hw e (mem_insert_self _ _)
    let G' := G ⊔ edge (ends e).1 (ends e).2
    have hc' : components G' ends E = 1 := by
      simpa only [components,G',graph_contracted,graph_insert] using hc
    have hp' : partition G' ends (-u) w E < 0 := ih G' hwE hc'
    rw [deletion_contraction G ends (-u) w he]
    by_cases hE : components G ends E = 1
    · exact add_neg (ih G hwE hE) (mul_neg_of_pos_of_neg (by linarith) hp')
    · have hsep : ¬(graph G ends E).Reachable (ends e).1 (ends e).2 := by
        intro hr
        have hcards := FKComponents.component_card_sup_edge_of_reachable hr
        apply hE
        apply hcards.symm.trans
        simpa only [components,graph_insert] using hc
      rw [separating_edge_partition G ends (-u) w hsep]
      change (-u) * partition G' ends (-u) w E + w e * partition G' ends (-u) w E < 0
      rw [← add_mul]
      exact mul_neg_of_pos_of_neg (by linarith) hp'

 

theorem signed_partition_pos (G : SimpleGraph V) (ends : I → V × V)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (w : I → ℝ) (E : Finset I)
    (hw : ∀ e ∈ E, 1 ≤ w e) :
    0 < (-1 : ℝ) ^ components G ends E * partition G ends (-u) w E := by
  classical
  induction E using Finset.induction_on generalizing G with
  | empty =>
    simp only [components, graph_empty, partition_empty, ← mul_pow, neg_mul_neg,
      one_mul]
    exact pow_pos hu _
  | @insert e E he ih =>
    have hwE : ∀ f ∈ E, 1 ≤ w f := fun f hf => hw f (mem_insert_of_mem hf)
    have hwe : 1 ≤ w e := hw e (mem_insert_self _ _)
    let G' := G ⊔ edge (ends e).1 (ends e).2
    have hc' : components G ends (insert e E) = components G' ends E := by
      simp only [components,G',graph_contracted,graph_insert]
    have hp' := ih G' hwE
    rw [hc', deletion_contraction G ends (-u) w he, mul_add]
    by_cases hr : (graph G ends E).Reachable (ends e).1 (ends e).2
    · have hc : components G' ends E = components G ends E := by
        simp only [components,G',graph_contracted]
        exact FKComponents.component_card_sup_edge_of_reachable hr
      have hp := ih G hwE
      rw [← hc] at hp
      have hpw := mul_pos (lt_of_lt_of_le zero_lt_one hwe) hp'
      nlinarith
    · rw [separating_edge_partition G ends (-u) w hr]
      change 0 < (-1 : ℝ) ^ components G' ends E *
        ((-u) * partition G' ends (-u) w E) +
        (-1 : ℝ) ^ components G' ends E * (w e * partition G' ends (-u) w E)
      have hpw := mul_pos (show 0 < w e - u by linarith) hp'
      nlinarith

 
def hardSum (G : SimpleGraph V) (ends : I → V × V) (E : Finset I) : ℝ :=
  ∑ A ∈ E.powerset, if components G ends A = 1 then (-1 : ℝ)^A.card else 0

lemma components_contracted_of_reachable (G : SimpleGraph V) (ends : I → V × V)
    {e : I} (hr : G.Reachable (ends e).1 (ends e).2) (A : Finset I) :
    components (G ⊔ edge (ends e).1 (ends e).2) ends A = components G ends A := by
  unfold components
  rw [graph_contracted]
  exact FKComponents.component_card_sup_edge_of_reachable (hr.mono le_sup_left)

omit [Finite V] in
lemma hardSum_deletion_contraction (G : SimpleGraph V) (ends : I → V × V)
    {e : I} {E : Finset I} (he : e ∉ E) :
    hardSum G ends (insert e E) = hardSum G ends E -
      hardSum (G ⊔ edge (ends e).1 (ends e).2) ends E := by
  unfold hardSum
  rw [sum_powerset_insert he,sub_eq_add_neg,← sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro A hA
  have heA : e ∉ A := fun h => he (mem_powerset.mp hA h)
  simp only [components,graph_insert,graph_contracted,card_insert_of_notMem heA,pow_succ]
  split_ifs <;> ring

 
lemma hardSum_eq_zero_of_reachable (G : SimpleGraph V) (ends : I → V × V)
    {e : I} {E : Finset I} (he : e ∉ E) (hr : G.Reachable (ends e).1 (ends e).2) :
    hardSum G ends (insert e E) = 0 := by
  rw [hardSum_deletion_contraction G ends he]
  have h : hardSum (G ⊔ edge (ends e).1 (ends e).2) ends E = hardSum G ends E := by
    unfold hardSum
    congr 1
    funext A
    rw [components_contracted_of_reachable G ends hr]
  rw [h,sub_self]

 

theorem hardSum_sign (G : SimpleGraph V) (ends : I → V × V) (E : Finset I) :
    (-1 : ℝ) ^ Nat.card G.ConnectedComponent * hardSum G ends E ≤ 0 := by
  induction E using Finset.induction_on generalizing G with
  | empty =>
    simp only [hardSum,powerset_empty,sum_singleton,components,graph_empty,card_empty,pow_zero]
    split_ifs with h
    · simp [h]
    · simp
  | @insert e E he ih =>
    by_cases hr : G.Reachable (ends e).1 (ends e).2
    · rw [hardSum_eq_zero_of_reachable G ends he hr,mul_zero]
    · have hc := FKComponents.component_card_sup_edge_of_not_reachable hr
      have h0 := ih G
      have h1 := ih (G ⊔ edge (ends e).1 (ends e).2)
      rw [hardSum_deletion_contraction G ends he,mul_sub]
      have hsign : (-1 : ℝ) ^ Nat.card G.ConnectedComponent =
          - (-1 : ℝ) ^ Nat.card (G ⊔ edge (ends e).1 (ends e).2).ConnectedComponent := by
        rw [← hc,pow_succ]
        ring
      rw [hsign] at h0 ⊢
      nlinarith

 

lemma union_constrained_sum (v : I → ℝ) {A D : Finset I} (hA : A ⊆ D) :
    (∑ B ∈ D.powerset with A ∪ B = D, ∏ e ∈ B, v e) =
      (∏ e ∈ D \ A, v e) * ∏ e ∈ A, (1 + v e) := by
  classical
  rw [prod_one_add, mul_sum]
  apply sum_bij' (fun B _ => B ∩ A) (fun C _ => (D \ A) ∪ C)
  · intro B hB
    exact mem_powerset.mpr inter_subset_right
  · intro C hC
    have hc := mem_powerset.mp hC
    apply mem_filter.mpr
    constructor
    · exact mem_powerset.mpr (union_subset sdiff_subset (hc.trans hA))
    · ext e
      simp only [mem_union, mem_sdiff]
      constructor
      · rintro (he | ⟨he, _⟩ | he)
        · exact hA he
        · exact he
        · exact hA (hc he)
      · intro he
        by_cases ha : e ∈ A
        · exact Or.inl ha
        · exact Or.inr (Or.inl ⟨he, ha⟩)
  · intro B hB
    obtain ⟨hb, hab⟩ := mem_filter.mp hB
    have hbD := mem_powerset.mp hb
    ext e
    simp only [mem_union, mem_sdiff, mem_inter]
    constructor
    · rintro (⟨hd, ha⟩ | ⟨hb, _⟩)
      · have he : e ∈ A ∪ B := by rw [hab]; exact hd
        exact (mem_union.mp he).resolve_left ha
      · exact hb
    · intro hb
      by_cases ha : e ∈ A
      · exact Or.inr ⟨hb, ha⟩
      · exact Or.inl ⟨hbD hb, ha⟩
  · intro C hC
    have hc := mem_powerset.mp hC
    ext e
    simp only [mem_inter, mem_union, mem_sdiff]
    constructor
    · rintro ⟨(⟨_, hn⟩ | he), ha⟩
      · exact (hn ha).elim
      · exact he
    · intro he
      exact ⟨Or.inr he, hc he⟩
  · intro B hB
    obtain ⟨hb, hab⟩ := mem_filter.mp hB
    have hbD := mem_powerset.mp hb
    have heq : B = (D \ A) ∪ (B ∩ A) := by
      ext e
      simp only [mem_union,mem_sdiff,mem_inter]
      constructor
      · intro he
        by_cases ha : e ∈ A
        · exact Or.inr ⟨he,ha⟩
        · exact Or.inl ⟨hbD he,ha⟩
      · rintro (⟨hd,hn⟩ | ⟨he,_⟩)
        · have he : e ∈ A ∪ B := by rw [hab]; exact hd
          exact (mem_union.mp he).resolve_left hn
        · exact he
    conv_lhs => rw [heq,prod_union (show Disjoint (D \ A) (B ∩ A) from
      disjoint_left.mpr fun e he he' => (mem_sdiff.mp he).2 (mem_inter.mp he').2)]

omit [Finite V] in
lemma fixed_union (G : SimpleGraph V) (ends : I → V × V) (v : I → ℝ)
    (s : ℝ) (D : Finset I) :
    (∑ A ∈ D.powerset, (∏ e ∈ A, v e) * s ^ components G ends A *
      ∑ B ∈ D.powerset with A ∪ B = D, ∏ e ∈ B, v e) =
      (∏ e ∈ D, v e) * partition G ends s (fun e => 1 + v e) D := by
  unfold partition
  rw [mul_sum]
  apply sum_congr rfl
  intro A hA
  have ha := mem_powerset.mp hA
  rw [union_constrained_sum v ha]
  have hp := prod_sdiff (f := v) ha
  calc
    _ = ((∏ e ∈ D \ A, v e) * ∏ e ∈ A, v e) *
      ((∏ e ∈ A, (1 + v e)) * s ^ components G ends A) := by ring
    _ = _ := by rw [hp]

 

theorem fixed_union_hard_nonpos {J : Type*} (G : SimpleGraph V)
    (ends : I → V × V) (hardEnds : J → V × V) (v : I → ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (D : Finset I) (H : Finset J)
    (hv : ∀ e ∈ D, 0 ≤ v e) :
    (∏ e ∈ D, v e) * partition G ends (-u) (fun e => 1 + v e) D *
      hardSum (graph G ends D) hardEnds H ≤ 0 := by
  have hp := signed_partition_pos G ends hu hu1 (fun e => 1 + v e) D
    (fun e he => by linarith [hv e he])
  have hh := hardSum_sign (graph G ends D) hardEnds H
  change (-1 : ℝ) ^ components G ends D * hardSum (graph G ends D) hardEnds H ≤ 0 at hh
  have hs : ((-1 : ℝ) ^ components G ends D) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    simp
  have hph := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hp) hh
  have hprod : partition G ends (-u) (fun e => 1 + v e) D *
      hardSum (graph G ends D) hardEnds H ≤ 0 := by
    nlinarith [sq_nonneg ((-1 : ℝ) ^ components G ends D)]
  exact (by simpa only [mul_assoc] using
    mul_nonpos_of_nonneg_of_nonpos (prod_nonneg hv) hprod)

end BelowOne.FKPressure
end
end

 
section

 
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
namespace BelowOne.FKPressure
variable {V I J : Type*} [Finite V]

lemma regroup_union (E : Finset I) (f : Finset I → Finset I → ℝ) :
    (∑ A ∈ E.powerset, ∑ B ∈ E.powerset, f A B) =
      ∑ D ∈ E.powerset, ∑ A ∈ D.powerset,
        ∑ B ∈ D.powerset with A ∪ B = D, f A B := by
  classical
  rw [← sum_product']
  have hmap : ∀ p ∈ E.powerset ×ˢ E.powerset, p.1 ∪ p.2 ∈ E.powerset := by
    intro p hp
    obtain ⟨ha,hb⟩ := mem_product.mp hp
    exact mem_powerset.mpr (union_subset (mem_powerset.mp ha) (mem_powerset.mp hb))
  rw [← sum_fiberwise_of_maps_to hmap]
  apply sum_congr rfl
  intro D hD
  have hd := mem_powerset.mp hD
  apply sum_finset_product'
  intro p
  simp only [mem_filter,mem_product,mem_powerset]
  constructor
  · rintro ⟨⟨ha,hb⟩, hab⟩
    refine ⟨?_, ?_, hab⟩
    · rw [← hab]
      exact subset_union_left
    · rw [← hab]
      exact subset_union_right
  · rintro ⟨ha,hb, hab⟩
    exact ⟨⟨ha.trans hd, hb.trans hd⟩,hab⟩

 

def connectedSum (G : SimpleGraph V) (ends : I → V × V)
    (hardEnds : J → V × V) (E : Finset I) (H : Finset J)
    (s : ℝ) (v : I → ℝ) : ℝ :=
  ∑ A ∈ E.powerset, ∑ B ∈ E.powerset,
    (∏ e ∈ A, v e) * (∏ e ∈ B, v e) * s ^ components G ends A *
      hardSum (graph G ends (A ∪ B)) hardEnds H

omit [Finite V] in
lemma connectedSum_grouped (G : SimpleGraph V) (ends : I → V × V)
    (hardEnds : J → V × V) (E : Finset I) (H : Finset J)
    (s : ℝ) (v : I → ℝ) :
    connectedSum G ends hardEnds E H s v =
      ∑ D ∈ E.powerset, (∏ e ∈ D, v e) *
        partition G ends s (fun e => 1 + v e) D *
          hardSum (graph G ends D) hardEnds H := by
  unfold connectedSum
  rw [regroup_union]
  apply sum_congr rfl
  intro D hD
  rw [← fixed_union, sum_mul]
  apply sum_congr rfl
  intro A hA
  rw [mul_sum, sum_mul]
  apply sum_congr rfl
  intro B hB
  have hab := (mem_filter.mp hB).2
  rw [hab]
  ring

 

theorem connectedSum_nonpos (G : SimpleGraph V) (ends : I → V × V)
    (hardEnds : J → V × V) (E : Finset I) (H : Finset J)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (v : I → ℝ)
    (hv : ∀ e ∈ E, 0 ≤ v e) :
    connectedSum G ends hardEnds E H (-u) v ≤ 0 := by
  rw [connectedSum_grouped]
  apply sum_nonpos
  intro D hD
  exact fixed_union_hard_nonpos G ends hardEnds v hu hu1 D H
    (fun e he => hv e (mem_powerset.mp hD he))

end BelowOne.FKPressure
end
end

 
section

 

noncomputable section
open Finset
attribute [local instance] Classical.propDecidable
namespace BelowOne.PartitionCumulant

instance finiteSetoid (α : Type*) [Finite α] : Finite (Setoid α) :=
  Finite.of_injective (fun r : Setoid α => r.r) (fun _ _ h => Setoid.ext (by simp [h]))

instance fintypeSetoid (α : Type*) [Finite α] : Fintype (Setoid α) := Fintype.ofFinite _

variable {α : Type*}

def extendMap (r : Setoid α) (o : Option (Quotient r)) : Option α → Option (Quotient r)
  | none => o
  | some a => some (Quotient.mk r a)

def extend (r : Setoid α) (o : Option (Quotient r)) : Setoid (Option α) :=
  Setoid.ker (extendMap r o)

@[simp] lemma extend_some (r : Setoid α) (o : Option (Quotient r)) (a b : α) :
    extend r o (some a) (some b) ↔ r a b := by
  change some (Quotient.mk r a) = some (Quotient.mk r b) ↔ r a b
  rw [Option.some.injEq, Quotient.eq]

@[simp] lemma extend_none_some (r : Setoid α) (o : Option (Quotient r)) (a : α) :
    extend r o none (some a) ↔ o = some (Quotient.mk r a) := Iff.rfl

@[simp] lemma restrict_extend (r : Setoid α) (o : Option (Quotient r)) :
    (extend r o).comap some = r := by
  ext a b
  exact extend_some r o a b

lemma extend_injective (r : Setoid α) : Function.Injective (extend r) := by
  intro o p h
  have hh (a : α) : (o = some (Quotient.mk r a)) ↔ (p = some (Quotient.mk r a)) := by
    simpa only [extend_none_some] using Setoid.ext_iff.mp h none (some a)
  cases o with
  | none =>
    cases p with
    | none => rfl
    | some q =>
      obtain ⟨a,rfl⟩ := q.exists_rep
      simpa using (hh a).mpr rfl
  | some q =>
    obtain ⟨a,rfl⟩ := q.exists_rep
    exact ((hh a).mp rfl).symm

lemma extend_bijective : Function.Bijective
    (fun p : Σ r : Setoid α, Option (Quotient r) => extend p.1 p.2) := by
  constructor
  · rintro ⟨r,o⟩ ⟨s,p⟩ h
    have hrs : r = s := by
      simpa using congrArg (Setoid.comap (some : α → Option α)) h
    subst s
    have hop : o = p := extend_injective r h
    subst p
    rfl
  · intro s
    let r := s.comap (some : α → Option α)
    by_cases h : ∃ a, s none (some a)
    · obtain ⟨a,ha⟩ := h
      refine ⟨⟨r,some (Quotient.mk r a)⟩, ?_⟩
      apply Setoid.ext
      intro x y
      cases x with
      | none =>
        cases y with
        | none => simp
        | some b =>
          simp only [extend_none_some, Option.some.injEq, Quotient.eq]
          change s (some a) (some b) ↔ s none (some b)
          exact ⟨fun h => s.trans ha h, fun h => s.trans (s.symm ha) h⟩
      | some a' =>
        cases y with
        | none =>
          change some (Quotient.mk r a') = some (Quotient.mk r a) ↔ s (some a') none
          rw [Option.some.injEq, Quotient.eq]
          change s (some a') (some a) ↔ s (some a') none
          exact ⟨fun h => s.trans h (s.symm ha), fun h => s.trans h ha⟩
        | some b => exact extend_some r _ _ _
    · refine ⟨⟨r,none⟩, ?_⟩
      apply Setoid.ext
      intro x y
      cases x with
      | none =>
        cases y with
        | none => simp
        | some b =>
          rw [extend_none_some]
          exact iff_of_false (by simp) (fun hb => h ⟨b,hb⟩)
      | some a =>
        cases y with
        | none =>
          change some (Quotient.mk r a) = none ↔ s (some a) none
          exact iff_of_false (by simp) (fun ha => h ⟨a,s.symm ha⟩)
        | some b => exact extend_some r _ _ _

def extensionEquiv : (Σ r : Setoid α, Option (Quotient r)) ≃ Setoid (Option α) :=
  Equiv.ofBijective _ extend_bijective

lemma card_extend_none [Finite α] (r : Setoid α) :
    Nat.card (Quotient (extend r none)) = Nat.card (Quotient r) + 1 := by
  have hs : Function.Surjective (extendMap r none) := by
    intro x
    cases x with
    | none => exact ⟨none,rfl⟩
    | some q =>
      obtain ⟨a,rfl⟩ := q.exists_rep
      exact ⟨some a,rfl⟩
  change Nat.card (Quotient (Setoid.ker (extendMap r none))) = _
  rw [Nat.card_congr (Setoid.quotientKerEquivOfSurjective (extendMap r none) hs)]
  let := Fintype.ofFinite (Quotient r)
  simp only [Nat.card_eq_fintype_card, Fintype.card_option]

lemma card_extend_some [Finite α] (r : Setoid α) (q : Quotient r) :
    Nat.card (Quotient (extend r (some q))) = Nat.card (Quotient r) := by
  let f : Option α → Quotient r := Option.elim' q (Quotient.mk r)
  have he : extend r (some q) = Setoid.ker f := by
    apply Setoid.ext
    intro x y
    change extendMap r (some q) x = extendMap r (some q) y ↔ f x = f y
    cases x <;> cases y <;> simp [extendMap, f]
  have hs : Function.Surjective f := by
    intro p
    obtain ⟨a,rfl⟩ := p.exists_rep
    exact ⟨some a,rfl⟩
  rw [he]
  exact Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hs)

 

theorem sum_option [Finite α] (f : ℕ → ℝ) :
    (∑ s : Setoid (Option α), f (Nat.card (Quotient s))) =
      ∑ r : Setoid α, (f (Nat.card (Quotient r) + 1) +
        (Nat.card (Quotient r) : ℝ) * f (Nat.card (Quotient r))) := by
  classical
  let := Fintype.ofFinite α
  let (r : Setoid α) := Fintype.ofFinite (Quotient r)
  rw [← extensionEquiv.sum_comp, Fintype.sum_sigma]
  apply sum_congr rfl
  intro r _
  rw [Fintype.sum_option]
  change f (Nat.card (Quotient (extend r none))) +
    (∑ x : Quotient r, f (Nat.card (Quotient (extend r (some x))))) = _
  simp only [card_extend_none, card_extend_some]
  simp only [sum_const, card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

 
def coefficient (n : ℕ) : ℝ := (-1) ^ (n - 1) * (n - 1).factorial

lemma coefficient_recurrence {n : ℕ} (hn : 0 < n) :
    coefficient (n+1) + (n : ℝ) * coefficient n = 0 := by
  have hn' : n = (n-1)+1 := by omega
  simp only [coefficient, Nat.add_sub_cancel]
  conv_lhs => arg 1; arg 1; rw [hn',pow_succ]
  have hf : n.factorial = n * (n-1).factorial := by
    conv_lhs => rw [hn', Nat.factorial_succ]
    rw [← hn']
  rw [hf]
  push_cast
  ring

 

theorem sum_coefficient_option [Finite α] [Nonempty α] :
    (∑ r : Setoid (Option α), coefficient (Nat.card (Quotient r))) = 0 := by
  rw [sum_option]
  apply sum_eq_zero
  intro r _
  let : Nonempty (Quotient r) := ⟨Quotient.mk r (Classical.arbitrary α)⟩
  exact coefficient_recurrence Nat.card_pos

 
def setoidEquiv {β : Type*} (e : α ≃ β) : Setoid α ≃ Setoid β where
  toFun r := r.comap e.symm
  invFun s := s.comap e
  left_inv r := by
    apply Setoid.ext
    intro a b
    change r (e.symm (e a)) (e.symm (e b)) ↔ r a b
    simp only [e.symm_apply_apply]
  right_inv s := by
    apply Setoid.ext
    intro a b
    change s (e (e.symm a)) (e (e.symm b)) ↔ s a b
    simp only [e.apply_symm_apply]

lemma card_relabel {β : Type*} (e : α ≃ β) (r : Setoid α) :
    Nat.card (Quotient (setoidEquiv e r)) = Nat.card (Quotient r) := by
  apply Nat.card_congr
  exact Quotient.congr e.symm (fun _ _ => Iff.rfl)

lemma sum_relabel {β : Type*} [Finite α] [Finite β] (e : α ≃ β) (f : ℕ → ℝ) :
    (∑ r : Setoid α, f (Nat.card (Quotient r))) =
      ∑ s : Setoid β, f (Nat.card (Quotient s)) := by
  exact Fintype.sum_equiv (setoidEquiv e) _ _ (fun r => by rw [card_relabel])

lemma sum_coefficient_nontrivial [Finite α] [Nontrivial α] :
    (∑ r : Setoid α, coefficient (Nat.card (Quotient r))) = 0 := by
  classical
  obtain ⟨a,b,hab⟩ := exists_pair_ne α
  let : Nonempty {x : α // x ≠ a} := ⟨⟨b,hab.symm⟩⟩
  rw [← sum_relabel (Equiv.optionSubtypeNe a)]
  exact sum_coefficient_option

lemma sum_coefficient_subsingleton [Finite α] [Subsingleton α] [Nonempty α] :
    (∑ r : Setoid α, coefficient (Nat.card (Quotient r))) = 1 := by
  let : Unique (Setoid α) :=
    { default := ⊤
      uniq := fun r => Setoid.ext (fun a b => by
        rw [Subsingleton.elim b a]
        simp) }
  rw [Fintype.sum_unique]
  have hcard : Nat.card (Quotient (default : Setoid α)) = 1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨?_, ⟨Quotient.mk _ (Classical.arbitrary α)⟩⟩
    refine ⟨fun x y => ?_⟩
    induction x using Quotient.inductionOn with | h a =>
      induction y using Quotient.inductionOn with | h b =>
        rw [Subsingleton.elim b a]
  rw [hcard]
  norm_num [coefficient]

lemma sum_coefficient [Finite α] [Nonempty α] :
    (∑ r : Setoid α, coefficient (Nat.card (Quotient r))) =
      if Nat.card α = 1 then 1 else 0 := by
  classical
  cases subsingleton_or_nontrivial α with
  | inl h =>
    let := h
    rw [sum_coefficient_subsingleton, ite_eq_left (Nat.card_eq_one_iff_unique.mpr ⟨h,inferInstance⟩)]
  | inr h =>
    let := h
    rw [sum_coefficient_nontrivial, ite_eq_right]
    exact fun he => not_subsingleton α (Nat.card_eq_one_iff_unique.mp he).1

 

def coarseningQuotientEquiv (r s : Setoid α) (h : r ≤ s) :
    Quotient (Setoid.correspondence r ⟨s,h⟩) ≃ Quotient s := by
  apply Equiv.trans _ (Setoid.quotientQuotientEquivQuotient r s h)
  apply Quotient.congrRight
  intro a b
  induction a using Quotient.inductionOn with | h x =>
    induction b using Quotient.inductionOn with | h y =>
      change s x y ↔ Quotient.mk s x = Quotient.mk s y
      exact Quotient.eq.symm

 

theorem sum_coarsenings [Finite α] [Nonempty α] (r : Setoid α) :
    (∑ s : {s : Setoid α // r ≤ s}, coefficient (Nat.card (Quotient s.1))) =
      if Nat.card (Quotient r) = 1 then 1 else 0 := by
  classical
  let := Fintype.ofFinite (Quotient r)
  let : Nonempty (Quotient r) := ⟨Quotient.mk r (Classical.arbitrary α)⟩
  rw [← sum_coefficient (α := Quotient r)]
  apply Fintype.sum_equiv (Setoid.correspondence r).toEquiv
  intro s
  exact congrArg coefficient (Nat.card_congr (coarseningQuotientEquiv r s.1 s.2)).symm

 

theorem connected_cancellation [Finite α] [Nonempty α]
    {Ω : Type*} [Fintype Ω] (component : Ω → Setoid α) (weight : Ω → ℝ) :
    (∑ r : Setoid α, coefficient (Nat.card (Quotient r)) *
      ∑ ω : Ω, if component ω ≤ r then weight ω else 0) =
      ∑ ω : Ω, if Nat.card (Quotient (component ω)) = 1 then weight ω else 0 := by
  classical
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  have he : (∑ r : Setoid α, coefficient (Nat.card (Quotient r)) *
      (if component ω ≤ r then weight ω else 0)) =
      (∑ r : {r : Setoid α // component ω ≤ r},
        coefficient (Nat.card (Quotient r.1))) * weight ω := by
    rw [sum_mul, ← Finset.sum_subtype (univ.filter (fun r => component ω ≤ r))
      (by simp) (fun r => coefficient (Nat.card (Quotient r)) * weight ω), sum_filter]
    apply sum_congr rfl
    intro r _
    split_ifs <;> simp_all
  rw [he, sum_coarsenings]
  split_ifs <;> simp

end BelowOne.PartitionCumulant
end
end

 
section

 

noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
namespace BelowOne.FKPressure
variable {V I J : Type*} [Finite V]

 

def blockStructureSum (G : SimpleGraph V) (ends : I → V × V)
    (hardEnds : J → V × V) (E : Finset I) (H : Finset J)
    (s : ℝ) (v : I → ℝ) (r : Setoid V) : ℝ :=
  ∑ A ∈ E.powerset, ∑ B ∈ E.powerset, ∑ L ∈ H.powerset,
    if (graph (graph G ends (A ∪ B)) hardEnds L).reachableSetoid ≤ r then
      (∏ e ∈ A, v e) * (∏ e ∈ B, v e) * s ^ components G ends A * (-1 : ℝ)^L.card
    else 0

 

theorem exponential_cancellation [Nonempty V] (G : SimpleGraph V) (ends : I → V × V)
    (hardEnds : J → V × V) (E : Finset I) (H : Finset J)
    (s : ℝ) (v : I → ℝ) :
    (∑ r : Setoid V, PartitionCumulant.coefficient (Nat.card (Quotient r)) *
      blockStructureSum G ends hardEnds E H s v r) =
      connectedSum G ends hardEnds E H s v := by
  classical
  let Ω := (E.powerset ×ˢ E.powerset) ×ˢ H.powerset
  let component (ω : ((Finset I × Finset I) × Finset J)) : Setoid V :=
    (graph (graph G ends (ω.1.1 ∪ ω.1.2)) hardEnds ω.2).reachableSetoid
  let weight (ω : ((Finset I × Finset I) × Finset J)) : ℝ :=
    (∏ e ∈ ω.1.1, v e) * (∏ e ∈ ω.1.2, v e) *
      s ^ components G ends ω.1.1 * (-1 : ℝ)^ω.2.card
  have hsum (f : ((Finset I × Finset I) × Finset J) → ℝ) :
      (∑ ω : Ω, f ω.1) = ∑ A ∈ E.powerset, ∑ B ∈ E.powerset,
        ∑ L ∈ H.powerset, f ((A,B),L) := by
    rw [Finset.sum_coe_sort Ω f]
    simp only [Ω, sum_product]
  have h := PartitionCumulant.connected_cancellation
    (fun ω : Ω => component ω.1) (fun ω : Ω => weight ω.1)
  have hs (r : Setoid V) :
      (∑ ω : Ω, if component ω.1 ≤ r then weight ω.1 else 0) =
        blockStructureSum G ends hardEnds E H s v r := by
    exact hsum (fun ω => if component ω ≤ r then weight ω else 0)
  have hc : (∑ ω : Ω, if Nat.card (Quotient (component ω.1)) = 1 then weight ω.1 else 0) =
      connectedSum G ends hardEnds E H s v := by
    rw [hsum (fun ω => if Nat.card (Quotient (component ω)) = 1 then weight ω else 0)]
    unfold connectedSum hardSum
    apply sum_congr rfl
    intro A hA
    apply sum_congr rfl
    intro B hB
    rw [mul_sum]
    apply sum_congr rfl
    intro L hL
    change (if components (graph G ends (A ∪ B)) hardEnds L = 1 then _ else _) = _
    split_ifs <;> simp [weight]
  simpa only [hs, hc] using h

 

theorem logarithmic_structure_nonpos [Nonempty V]
    (G : SimpleGraph V) (ends : I → V × V) (hardEnds : J → V × V)
    (E : Finset I) (H : Finset J) {u : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e) :
    (∑ r : Setoid V, PartitionCumulant.coefficient (Nat.card (Quotient r)) *
      blockStructureSum G ends hardEnds E H (-u) v r) ≤ 0 := by
  rw [exponential_cancellation]
  exact connectedSum_nonpos G ends hardEnds E H hu hu1 v hv

end BelowOne.FKPressure
end
end

 
section

 

noncomputable section
open Finset SimpleGraph Set
namespace BelowOne.FKPressure
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

lemma component_card_block_sum (G : SimpleGraph V) (r : Setoid V)
    (h : G.reachableSetoid ≤ r) :
    Nat.card G.ConnectedComponent =
      ∑ q : Quotient r, Nat.card
        (Quotient (G.reachableSetoid.comap
          (Subtype.val : Quotient.mk r ⁻¹' {q} → V))) := by
  classical
  change Nat.card (Quotient G.reachableSetoid) = _
  rw [← Nat.card_congr (Setoid.sigmaQuotientEquivOfLe h)]
  exact Nat.card_sigma

omit [Fintype V] in
lemma reachable_induce_block (G : SimpleGraph V) (r : Setoid V)
    (h : G.reachableSetoid ≤ r) (q : Quotient r)
    (x y : Quotient.mk r ⁻¹' {q}) :
    (G.induce (Quotient.mk r ⁻¹' {q})).Reachable x y ↔ G.Reachable x.1 y.1 := by
  constructor
  · intro hxy
    exact hxy.map (SimpleGraph.Embedding.induce _).toHom
  · rintro ⟨p⟩
    have hp : ∀ z ∈ p.support, z ∈ Quotient.mk r ⁻¹' {q} := by
      intro z hz
      have hr : r x.1 z := h ⟨p.takeUntil z hz⟩
      change Quotient.mk r z = q
      exact (Quotient.sound hr).symm.trans x.property
    exact ⟨p.induce _ hp⟩

lemma components_induce_block_sum (G : SimpleGraph V) (r : Setoid V)
    (h : G.reachableSetoid ≤ r) :
    Nat.card G.ConnectedComponent =
      ∑ q : Quotient r, Nat.card (G.induce (Quotient.mk r ⁻¹' {q})).ConnectedComponent := by
  classical
  rw [component_card_block_sum G r h]
  apply sum_congr rfl
  intro q hq
  have he : G.reachableSetoid.comap (Subtype.val : Quotient.mk r ⁻¹' {q} → V) =
      (G.induce (Quotient.mk r ⁻¹' {q})).reachableSetoid := by
    apply Setoid.ext
    intro x y
    exact (reachable_induce_block G r h q x y).symm
  rw [he]
  rfl

lemma component_weight_block_prod (G : SimpleGraph V) (r : Setoid V)
    (h : G.reachableSetoid ≤ r) (s : ℝ) :
    s ^ Nat.card G.ConnectedComponent =
      ∏ q : Quotient r, s ^ Nat.card (G.induce (Quotient.mk r ⁻¹' {q})).ConnectedComponent := by
  classical
  rw [components_induce_block_sum G r h,← Finset.prod_pow_eq_pow_sum]

variable {I : Type*}

omit [Fintype V] in
lemma graph_adj_iff (G : SimpleGraph V) (ends : I → V × V) (A : Finset I) (x y : V) :
    (graph G ends A).Adj x y ↔ G.Adj x y ∨ ∃ e ∈ A, (edge (ends e).1 (ends e).2).Adj x y := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert e A he ih =>
    simp only [graph_insert,SimpleGraph.sup_adj,ih]
    aesop

omit [Fintype V] in
lemma endpoints_reachable (G : SimpleGraph V) (ends : I → V × V) {A : Finset I} {e : I}
    (he : e ∈ A) : (graph G ends A).Reachable (ends e).1 (ends e).2 := by
  by_cases h : (ends e).1 = (ends e).2
  · rw [h]
  · apply SimpleGraph.Adj.reachable
    apply (graph_adj_iff G ends A _ _).mpr
    exact Or.inr ⟨e,he,(edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,h⟩⟩

omit [Fintype V] in
lemma graph_reachable_le_iff (G : SimpleGraph V) (ends : I → V × V) (A : Finset I)
    (r : Setoid V) : (graph G ends A).reachableSetoid ≤ r ↔
      G.reachableSetoid ≤ r ∧ ∀ e ∈ A, r (ends e).1 (ends e).2 := by
  constructor
  · intro h
    exact ⟨fun x y hxy => h (hxy.mono le_sup_left),fun e he => h (endpoints_reachable G ends he)⟩
  · rintro ⟨hG,hA⟩ x y ⟨p⟩
    apply Quotient.exact
    apply FKComponents.eq_of_walk (f := Quotient.mk r) (p := p)
    intro x y hxy
    apply Quotient.sound
    rcases (graph_adj_iff G ends A x y).mp hxy with hxy | ⟨e,he,hexy⟩
    · exact hG hxy.reachable
    · rcases (edge_adj _ _ _ _).mp hexy with ⟨⟨rfl,rfl⟩ | ⟨rfl,rfl⟩,_⟩
      · exact hA e he
      · exact r.symm (hA e he)

def edgeBlock (r : Setoid V) (ends : I → V × V) (e : I) : Quotient r := Quotient.mk r (ends e).1

omit [Fintype V] in
lemma graph_induce_filter (G : SimpleGraph V) (r : Setoid V) (ends : I → V × V)
    (A : Finset I) (q : Quotient r) :
    (graph G ends (A.filter (edgeBlock r ends · = q))).induce (Quotient.mk r ⁻¹' {q}) =
      (graph G ends A).induce (Quotient.mk r ⁻¹' {q}) := by
  classical
  ext x y
  simp only [SimpleGraph.induce_adj,graph_adj_iff,mem_filter]
  constructor
  · rintro (h | ⟨e,⟨he,_⟩,hxy⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e,he,hxy⟩
  · rintro (h | ⟨e,he,hxy⟩)
    · exact Or.inl h
    · refine Or.inr ⟨e,⟨he,?_⟩,hxy⟩
      rcases (edge_adj _ _ _ _).mp hxy with ⟨h | h,_⟩
      · change Quotient.mk r (ends e).1 = q
        rw [← h.1]
        exact x.2
      · change Quotient.mk r (ends e).1 = q
        rw [← h.2]
        exact y.2

end BelowOne.FKPressure
end
end

 
section

 
noncomputable section
open Finset
namespace BelowOne.SubsetSplitting
variable {I Q : Type*} [Fintype Q]
attribute [local instance] Classical.propDecidable

abbrev Selection (E : Finset I) := ↥E.powerset

def fiber (E : Finset I) (f : I → Q) (q : Q) : Finset I := E.filter (f · = q)

def split (E : Finset I) (f : I → Q) (A : Selection E) (q : Q) : Selection (fiber E f q) :=
  ⟨A.1.filter (f · = q), mem_powerset.mpr (by
    intro e he
    have h := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_powerset.mp A.2 h.1,h.2⟩)⟩

def join (E : Finset I) (f : I → Q) (B : ∀ q, Selection (fiber E f q)) : Selection E :=
  ⟨univ.biUnion (fun q => (B q).1),mem_powerset.mpr (by
    intro e he
    obtain ⟨q,_,hq⟩ := mem_biUnion.mp he
    exact mem_filter.mp (mem_powerset.mp (B q).2 hq) |>.1)⟩

lemma join_split (E : Finset I) (f : I → Q) (A : Selection E) :
    join E f (split E f A) = A := by
  classical
  apply Subtype.ext
  ext e
  simp only [join,split,mem_biUnion,mem_univ,true_and,mem_filter]
  constructor
  · rintro ⟨q,he,_⟩
    exact he
  · intro he
    exact ⟨f e,he,rfl⟩

lemma split_join (E : Finset I) (f : I → Q) (B : ∀ q, Selection (fiber E f q)) :
    split E f (join E f B) = B := by
  classical
  funext q
  apply Subtype.ext
  ext e
  simp only [split,join,mem_filter,mem_biUnion,mem_univ,true_and]
  constructor
  · rintro ⟨⟨r,he⟩,hq⟩
    have hr := mem_filter.mp (mem_powerset.mp (B r).2 he) |>.2
    have hqr : q = r := hq.symm.trans hr
    cases hqr
    exact he
  · intro he
    exact ⟨⟨q,he⟩,mem_filter.mp (mem_powerset.mp (B q).2 he) |>.2⟩

def selectionEquiv (E : Finset I) (f : I → Q) : Selection E ≃ (∀ q, Selection (fiber E f q)) where
  toFun := split E f
  invFun := join E f
  left_inv := join_split E f
  right_inv := split_join E f

lemma sum_factorization (E : Finset I) (f : I → Q) (W : Finset I → ℝ)
    (w : Q → Finset I → ℝ)
    (hW : ∀ A ⊆ E, W A = ∏ q, w q (A.filter (f · = q))) :
    (∑ A ∈ E.powerset, W A) = ∏ q, ∑ A ∈ (fiber E f q).powerset, w q A := by
  classical
  have hs : (∑ A : Selection E, W A.1) =
      ∑ B : (∀ q, Selection (fiber E f q)), ∏ q, w q (B q).1 := by
    apply Fintype.sum_equiv (selectionEquiv E f)
    intro A
    exact hW A.1 (mem_powerset.mp A.2)
  have hp := Fintype.prod_sum (fun q (A : Selection (fiber E f q)) => w q A.1)
  simpa only [Selection,Finset.sum_coe_sort] using hs.trans hp.symm

def piTripleEquiv {Q : Type*} (A B C : Q → Type*) :
    ((∀ q, A q) × (∀ q, B q) × (∀ q, C q)) ≃ (∀ q, A q × B q × C q) where
  toFun p q := (p.1 q,p.2.1 q,p.2.2 q)
  invFun p := (fun q => (p q).1, fun q => (p q).2.1, fun q => (p q).2.2)
  left_inv p := rfl
  right_inv p := by funext q; rfl

lemma sum_triple_coe {I J K : Type*} (E : Finset I) (F : Finset J) (H : Finset K)
    (W : I → J → K → ℝ) :
    (∑ p : E × F × H, W p.1.1 p.2.1.1 p.2.2.1) =
      ∑ a ∈ E, ∑ b ∈ F, ∑ c ∈ H, W a b c := by
  simp only [Fintype.sum_prod_type]
  rw [show (∑ a : E, ∑ b : F, ∑ c : H, W a.1 b.1 c.1) =
      ∑ a ∈ E, ∑ b : F, ∑ c : H, W a b.1 c.1 from Finset.sum_coe_sort E (fun a => ∑ b : F, ∑ c : H, W a b.1 c.1)]
  apply sum_congr rfl
  intro a ha
  rw [show (∑ b : F, ∑ c : H, W a b.1 c.1) =
      ∑ b ∈ F, ∑ c : H, W a b c.1 from Finset.sum_coe_sort F (fun b => ∑ c : H, W a b c.1)]
  simp only [Finset.sum_coe_sort]

lemma sum_factorization_three {J K : Type*}
    (E : Finset I) (F : Finset J) (H : Finset K)
    (f : I → Q) (g : J → Q) (h : K → Q)
    (W : Finset I → Finset J → Finset K → ℝ)
    (w : Q → Finset I → Finset J → Finset K → ℝ)
    (hW : ∀ A ⊆ E, ∀ B ⊆ F, ∀ C ⊆ H,
      W A B C = ∏ q, w q (A.filter (f · = q)) (B.filter (g · = q)) (C.filter (h · = q))) :
    (∑ A ∈ E.powerset, ∑ B ∈ F.powerset, ∑ C ∈ H.powerset, W A B C) =
      ∏ q, ∑ A ∈ (fiber E f q).powerset, ∑ B ∈ (fiber F g q).powerset,
        ∑ C ∈ (fiber H h q).powerset, w q A B C := by
  classical
  let e := (Equiv.prodCongr (selectionEquiv E f)
    (Equiv.prodCongr (selectionEquiv F g) (selectionEquiv H h))).trans
      (piTripleEquiv _ _ _)
  have hs : (∑ p : Selection E × Selection F × Selection H, W p.1.1 p.2.1.1 p.2.2.1) =
      ∑ p : (∀ q, Selection (fiber E f q) × Selection (fiber F g q) × Selection (fiber H h q)),
        ∏ q, w q (p q).1.1 (p q).2.1.1 (p q).2.2.1 := by
    apply Fintype.sum_equiv e
    intro p
    exact hW p.1.1 (mem_powerset.mp p.1.2) p.2.1.1 (mem_powerset.mp p.2.1.2)
      p.2.2.1 (mem_powerset.mp p.2.2.2)
  have hp := Fintype.prod_sum (fun q
    (p : Selection (fiber E f q) × Selection (fiber F g q) × Selection (fiber H h q)) =>
      w q p.1.1 p.2.1.1 p.2.2.1)
  have hh := hs.trans hp.symm
  change (∑ p : E.powerset × F.powerset × H.powerset, _) =
    ∏ q, ∑ p : (fiber E f q).powerset × (fiber F g q).powerset × (fiber H h q).powerset, _ at hh
  rw [sum_triple_coe] at hh
  simpa only [sum_triple_coe] using hh

end BelowOne.SubsetSplitting
end
end

 
section

 
noncomputable section
open Finset SimpleGraph
namespace BelowOne.FKPressure
attribute [local instance] Classical.propDecidable
variable {V I J : Type*} [Fintype V]

lemma filter_classical (E : Finset I) (p : I → Prop) (d : DecidablePred p) :
    @Finset.filter I p d E = @Finset.filter I p (fun e => Classical.propDecidable (p e)) E := by
  exact @Finset.filter_congr_decidable I E p d (fun e => Classical.propDecidable (p e))

lemma powerset_filter_eq (E : Finset I) (p : I → Prop) :
    (E.filter p).powerset = E.powerset.filter (fun A => ∀ e ∈ A, p e) := by
  classical
  ext A
  simp only [mem_powerset,mem_filter]
  constructor
  · intro h
    exact ⟨fun e he => (mem_filter.mp (h he)).1,fun e he => (mem_filter.mp (h he)).2⟩
  · rintro ⟨h₁,h₂⟩ e he
    exact mem_filter.mpr ⟨h₁ he,h₂ e he⟩

lemma sum_powerset_filter (E : Finset I) (p : I → Prop) (W : Finset I → ℝ) :
    (∑ A ∈ E.powerset, if ∀ e ∈ A, p e then W A else 0) =
      ∑ A ∈ (E.filter p).powerset, W A := by
  rw [powerset_filter_eq,sum_filter]

omit [Fintype V] in
lemma confinement_iff (G : SimpleGraph V) (ends : I → V × V)
    (hardEnds : J → V × V) (A B : Finset I) (L : Finset J) (r : Setoid V)
    (hG : G.reachableSetoid ≤ r) :
    (graph (graph G ends (A ∪ B)) hardEnds L).reachableSetoid ≤ r ↔
      (∀ e ∈ A, r (ends e).1 (ends e).2) ∧
      (∀ e ∈ B, r (ends e).1 (ends e).2) ∧
      (∀ e ∈ L, r (hardEnds e).1 (hardEnds e).2) := by
  rw [graph_reachable_le_iff,graph_reachable_le_iff]
  simp only [hG,true_and,mem_union,or_imp,forall_and,and_assoc]

omit [Fintype V] in
lemma blockStructureSum_restrict (G : SimpleGraph V) (ends : I → V × V)
    (hardEnds : J → V × V) (E : Finset I) (H : Finset J)
    (s : ℝ) (v : I → ℝ) (r : Setoid V) (hG : G.reachableSetoid ≤ r) :
    blockStructureSum G ends hardEnds E H s v r =
      ∑ A ∈ (E.filter (fun e => r (ends e).1 (ends e).2)).powerset,
      ∑ B ∈ (E.filter (fun e => r (ends e).1 (ends e).2)).powerset,
      ∑ L ∈ (H.filter (fun e => r (hardEnds e).1 (hardEnds e).2)).powerset,
        (∏ e ∈ A, v e) * (∏ e ∈ B, v e) * s ^ components G ends A * (-1 : ℝ)^L.card := by
  unfold blockStructureSum
  simp_rw [confinement_iff G ends hardEnds _ _ _ r hG]
  rw [← sum_powerset_filter E (fun e => r (ends e).1 (ends e).2)]
  apply sum_congr rfl
  intro A hA
  by_cases ha : ∀ e ∈ A, r (ends e).1 (ends e).2
  · have eqa : (∀ e ∈ A, r (ends e).1 (ends e).2) = True := propext (iff_true_intro ha)
    simp only [eqa,true_and,ite_true]
    rw [← sum_powerset_filter E (fun e => r (ends e).1 (ends e).2)]
    apply sum_congr rfl
    intro B hB
    by_cases hb : ∀ e ∈ B, r (ends e).1 (ends e).2
    · have eqb : (∀ e ∈ B, r (ends e).1 (ends e).2) = True := propext (iff_true_intro hb)
      simp only [eqb,true_and,ite_true]
      rw [sum_powerset_filter]
    · simp [hb]
  · simp [ha]

 

def inducedBlockMoment (G : SimpleGraph V) (ends : I → V × V)
    (hardEnds : J → V × V) (E : Finset I) (H : Finset J)
    (s : ℝ) (v : I → ℝ) (r : Setoid V) (q : Quotient r) : ℝ :=
  ∑ A ∈ (E.filter (fun e => r (ends e).1 (ends e).2 ∧ edgeBlock r ends e = q)).powerset,
  ∑ B ∈ (E.filter (fun e => r (ends e).1 (ends e).2 ∧ edgeBlock r ends e = q)).powerset,
  ∑ L ∈ (H.filter (fun e => r (hardEnds e).1 (hardEnds e).2 ∧ edgeBlock r hardEnds e = q)).powerset,
    (∏ e ∈ A, v e) * (∏ e ∈ B, v e) *
      s ^ Nat.card ((graph G ends A).induce (Quotient.mk r ⁻¹' {q})).ConnectedComponent * (-1 : ℝ)^L.card

lemma structure_weight_factor (G : SimpleGraph V) (ends : I → V × V)
    (hardEnds : J → V × V) (A B : Finset I) (L : Finset J)
    (s : ℝ) (v : I → ℝ) (r : Setoid V) (hA : (graph G ends A).reachableSetoid ≤ r) :
    (∏ e ∈ A, v e) * (∏ e ∈ B, v e) * s ^ components G ends A * (-1 : ℝ)^L.card =
      ∏ q : Quotient r,
        (∏ e ∈ A.filter (edgeBlock r ends · = q), v e) *
        (∏ e ∈ B.filter (edgeBlock r ends · = q), v e) *
        s ^ Nat.card ((graph G ends (A.filter (edgeBlock r ends · = q))).induce
          (Quotient.mk r ⁻¹' {q})).ConnectedComponent *
        (-1 : ℝ)^(L.filter (edgeBlock r hardEnds · = q)).card := by
  classical
  simp_rw [graph_induce_filter,Finset.prod_mul_distrib]
  rw [prod_fiberwise,prod_fiberwise]
  congr 1
  · congr 1
    exact component_weight_block_prod (graph G ends A) r hA s
  · simpa only [prod_const] using
      (prod_fiberwise L (edgeBlock r hardEnds) (fun _ => (-1:ℝ))).symm

lemma blockStructureSum_factorization (G : SimpleGraph V) (ends : I → V × V)
    (hardEnds : J → V × V) (E : Finset I) (H : Finset J)
    (s : ℝ) (v : I → ℝ) (r : Setoid V) (hG : G.reachableSetoid ≤ r) :
    blockStructureSum G ends hardEnds E H s v r =
      ∏ q : Quotient r, inducedBlockMoment G ends hardEnds E H s v r q := by
  rw [blockStructureSum_restrict G ends hardEnds E H s v r hG]
  have hf := SubsetSplitting.sum_factorization_three
    (E.filter (fun e => r (ends e).1 (ends e).2))
    (E.filter (fun e => r (ends e).1 (ends e).2))
    (H.filter (fun e => r (hardEnds e).1 (hardEnds e).2))
    (edgeBlock r ends) (edgeBlock r ends) (edgeBlock r hardEnds)
    (fun A B L => (∏ e ∈ A, v e) * (∏ e ∈ B, v e) * s ^ components G ends A * (-1 : ℝ)^L.card)
    (fun q A B L => (∏ e ∈ A, v e) * (∏ e ∈ B, v e) *
      s ^ Nat.card ((graph G ends A).induce (Quotient.mk r ⁻¹' {q})).ConnectedComponent * (-1 : ℝ)^L.card)
    (by
      intro A hA B hB L hL
      simpa only [filter_classical] using structure_weight_factor G ends hardEnds A B L s v r
        ((graph_reachable_le_iff G ends A r).mpr ⟨hG,fun e he => (mem_filter.mp (hA he)).2⟩))
  simpa only [SubsetSplitting.fiber,filter_filter,inducedBlockMoment,filter_classical] using hf

end BelowOne.FKPressure
end
end

 
section

 
noncomputable section
open Finset
open scoped Classical
namespace BelowOne.MultiaffineDerivative
variable {V : Type*} [Fintype V]

abbrev coordinate (i : V) : (V → ℝ) := Pi.single i 1

def restrict (T : Finset V) : (V → ℝ) →L[ℝ] (T → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i.1)

omit [Fintype V] in
lemma restrict_apply (T : Finset V) (x : V → ℝ) (i : T) : restrict T x i = x i.1 := rfl

def Matches {n : ℕ} (τ : Fin n → V) {T : Finset V} (e : Fin n ↪ T) : Prop :=
  ∀ t : T, ∃ i, e i = t ∧ τ i = t.1

omit [Fintype V] in
lemma matches_iff {n : ℕ} (τ : Fin n → V) {T : Finset V} (e : Fin n ↪ T) :
    Matches τ e ↔ (∀ i, τ i = (e i).1) ∧ Function.Surjective e := by
  constructor
  · intro h
    constructor
    · intro i
      obtain ⟨j,hj,hτ⟩ := h (e i)
      have hji := e.injective hj
      simpa [hji] using hτ
    · intro t
      obtain ⟨i,hi,_⟩ := h t
      exact ⟨i,hi⟩
  · rintro ⟨hτ,he⟩ t
    obtain ⟨i,rfl⟩ := he t
    exact ⟨i,rfl,hτ i⟩

omit [Fintype V] in
lemma matches_data {n : ℕ} {τ : Fin n → V} {T : Finset V} {e : Fin n ↪ T}
    (h : Matches τ e) : Function.Injective τ ∧ univ.image τ = T := by
  obtain ⟨hτ,he⟩ := (matches_iff τ e).mp h
  constructor
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    rw [←hτ i,←hτ j,hij]
  · ext t
    simp only [mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩
      rw [hτ i]
      exact (e i).2
    · intro ht
      obtain ⟨i,hi⟩ := he ⟨t,ht⟩
      exact ⟨i,(hτ i).trans (congrArg Subtype.val hi)⟩

omit [Fintype V] in
lemma matches_unique {n : ℕ} {τ : Fin n → V} {T : Finset V} {e f : Fin n ↪ T}
    (he : Matches τ e) (hf : Matches τ f) : e = f := by
  ext i
  exact ((matches_iff τ e).mp he).1 i |>.symm.trans (((matches_iff τ f).mp hf).1 i)

def matchingEmbedding {n : ℕ} (τ : Fin n → V) (T : Finset V)
    (h : Function.Injective τ ∧ univ.image τ = T) : Fin n ↪ T where
  toFun i := ⟨τ i,by rw [←h.2]; exact mem_image_of_mem τ (mem_univ i)⟩
  inj' := fun i j hij => h.1 (congrArg Subtype.val hij)

omit [Fintype V] in
lemma matchingEmbedding_matches {n : ℕ} (τ : Fin n → V) (T : Finset V)
    (h : Function.Injective τ ∧ univ.image τ = T) : Matches τ (matchingEmbedding τ T h) := by
  intro t
  have ht : t.1 ∈ univ.image τ := by rw [h.2]; exact t.2
  obtain ⟨i,_,hi⟩ := mem_image.mp ht
  refine ⟨i,?_,hi⟩
  exact Subtype.ext hi

omit [Fintype V] in
lemma sum_matches {n : ℕ} (τ : Fin n → V) (T : Finset V) :
    (∑ e : Fin n ↪ T, if Matches τ e then (1:ℝ) else 0) =
      if Function.Injective τ ∧ univ.image τ = T then 1 else 0 := by
  by_cases h : Function.Injective τ ∧ univ.image τ = T
  · rw [ite_eq_left h]
    let e := matchingEmbedding τ T h
    have he := matchingEmbedding_matches τ T h
    rw [Fintype.sum_eq_single e]
    · exact ite_eq_left he
    · intro f hf
      exact ite_eq_right (fun hh => hf (matches_unique hh he))
  · rw [ite_eq_right h]
    apply sum_eq_zero
    intro e he
    exact ite_eq_right (fun hh => h (matches_data hh))

omit [Fintype V] in
lemma factor_indicator {n : ℕ} (τ : Fin n → V) (T : Finset V) (e : Fin n ↪ T) (t : T) :
    (if ht : t ∈ Set.range e then
      coordinate (τ (e.toEquivRange.symm ⟨t,ht⟩)) t.1 else 0) =
      if ∃ i, e i = t ∧ τ i = t.1 then (1:ℝ) else 0 := by
  by_cases ht : t ∈ Set.range e
  · obtain ⟨i,rfl⟩ := ht
    rw [dite_eq_left (Set.mem_range_self i)]
    have hi : e.toEquivRange.symm ⟨e i, Set.mem_range_self i⟩ = i :=
      e.toEquivRange.symm_apply_apply i
    rw [hi]
    simp [coordinate,Pi.single_apply,e.injective.eq_iff,eq_comm]
  · rw [dite_eq_right ht,ite_eq_right]
    rintro ⟨i,hi,_⟩
    exact ht ⟨i,hi⟩

lemma prod_indicator {T : Type*} [Fintype T] (p : T → Prop) :
    (∏ t : T, if p t then (1:ℝ) else 0) = if ∀ t, p t then 1 else 0 := by
  by_cases h : ∀ t, p t
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨t,ht⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (mem_univ t) (ite_eq_right ht)

lemma ite_classical {α : Sort*} (p : Prop) (d : Decidable p) (a b : α) :
    @ite α p d a b = @ite α p (Classical.propDecidable p) a b := by
  cases d <;> simp_all

lemma dite_classical {α : Sort*} (p : Prop) (d : Decidable p) (a : p → α) (b : ¬p → α) :
    @dite α p d a b = @dite α p (Classical.propDecidable p) a b := by
  cases d <;> simp_all

lemma range_equiv_classical {α β : Type*} [Fintype α] (d : DecidableEq β) (e : α ↪ β) :
    @Function.Embedding.toEquivRange α β _ d e =
      @Function.Embedding.toEquivRange α β _ (fun a b => Classical.propDecidable (a = b)) e := by
  ext i
  rfl

lemma monomial_derivative {n : ℕ} (τ : Fin n → V) (T : Finset V) :
    iteratedFDeriv ℝ n (fun x : V → ℝ => ∏ i ∈ T, x i) 0 (coordinate ∘ τ) =
      if Function.Injective τ ∧ univ.image τ = T then 1 else 0 := by
  let f := ContinuousMultilinearMap.mkPiAlgebra ℝ T ℝ
  have hf : (fun x : V → ℝ => ∏ i ∈ T, x i) = f ∘ restrict T := by
    funext x
    simp only [Function.comp_apply,f,ContinuousMultilinearMap.mkPiAlgebra_apply,restrict_apply]
    exact (Finset.prod_coe_sort T x).symm
  rw [hf,ContinuousLinearMap.iteratedFDeriv_comp_right _ f.contDiff _ le_rfl]
  rw [f.iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.iteratedFDeriv,_root_.sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply,
    ContinuousLinearMap.map_zero,Pi.zero_apply,
    Function.comp_apply,restrict_apply,f,ContinuousMultilinearMap.mkPiAlgebra_apply]
  trans ∑ e : Fin n ↪ T, if Matches τ e then (1:ℝ) else 0
  · apply sum_congr rfl
    intro e he
    trans ∏ t : T, if ∃ i, e i = t ∧ τ i = t.1 then (1:ℝ) else 0
    · apply prod_congr rfl
      intro t ht
      simpa only [range_equiv_classical,ite_classical,dite_classical] using factor_indicator τ T e t
    · by_cases hm : Matches τ e
      · rw [ite_eq_left hm]
        apply prod_eq_one
        intro t ht
        exact ite_eq_left (hm t)
      · rw [ite_eq_right hm]
        obtain ⟨t,ht⟩ := not_forall.mp hm
        exact prod_eq_zero (mem_univ t) (ite_eq_right ht)
  · exact sum_matches τ T

end BelowOne.MultiaffineDerivative
end
end

 
section

 

noncomputable section
open Finset
open scoped Classical ContDiff
namespace BelowOne.MultiaffineDerivative
variable {V : Type*} [Fintype V]

lemma contDiff_monomial (T : Finset V) (n : ℕ∞ω) :
    ContDiff ℝ n (fun x : V → ℝ => ∏ i ∈ T, x i) := by
  fun_prop

lemma weighted_monomial_derivative {n : ℕ} (τ : Fin n → V) (T : Finset V) (c : ℝ) :
    iteratedFDeriv ℝ n (fun x : V → ℝ => c * ∏ i ∈ T, x i) 0 (coordinate ∘ τ) =
      if Function.Injective τ ∧ univ.image τ = T then c else 0 := by
  change iteratedFDeriv ℝ n (fun x : V → ℝ => c • ∏ i ∈ T, x i) 0 (coordinate ∘ τ) = _
  rw [iteratedFDeriv_const_smul_apply' (contDiff_monomial T n).contDiffAt]
  simp only [_root_.smul_apply,smul_eq_mul,monomial_derivative]
  split_ifs <;> simp

def polynomial (W : Finset V → ℝ) (x : V → ℝ) : ℝ :=
  ∑ T : Finset V, W T * ∏ i ∈ T, x i

lemma contDiff_polynomial (W : Finset V → ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (polynomial W) := by
  unfold polynomial
  fun_prop

lemma polynomial_derivative (W : Finset V → ℝ) {n : ℕ} (τ : Fin n → V) :
    iteratedFDeriv ℝ n (polynomial W) 0 (coordinate ∘ τ) =
      if Function.Injective τ then W (univ.image τ) else 0 := by
  unfold polynomial
  rw [iteratedFDeriv_fun_sum_apply
    (fun T hT => (contDiff_const.mul (contDiff_monomial T n)).contDiffAt)]
  simp only [_root_.sum_apply,weighted_monomial_derivative]
  by_cases hτ : Function.Injective τ
  · simp only [hτ,true_and,ite_true]
    simp [eq_comm]
  · simp [hτ]

lemma polynomial_zero (W : Finset V → ℝ) : polynomial W 0 = W ∅ := by
  have h := polynomial_derivative W (fun i : Fin 0 => i.elim0)
  simpa only [iteratedFDeriv_zero_apply,Finset.univ_eq_empty,Finset.image_empty,
    Function.injective_of_subsingleton,ite_true] using h

end BelowOne.MultiaffineDerivative
end
end

 
section

 

noncomputable section
open Finset Function Set
namespace BelowOne.OrderedPartitionBridge

variable {n : ℕ}

def partition (c : OrderedFinpartition n) : Setoid (Fin n) := Setoid.ker c.index

lemma index_emb (c : OrderedFinpartition n) (i : Fin c.length) (j : Fin (c.partSize i)) :
    c.index (c.emb i j) = i := by
  exact congrArg Sigma.fst (c.equivSigma.left_inv ⟨i,j⟩)

lemma index_surjective (c : OrderedFinpartition n) : Surjective c.index := by
  intro i
  exact ⟨c.emb i ⟨0,c.partSize_pos i⟩,index_emb c i _⟩

lemma card_partition (c : OrderedFinpartition n) : Nat.card (Quotient (partition c)) = c.length := by
  unfold partition
  rw [Nat.card_congr (Setoid.quotientKerEquivOfSurjective c.index (index_surjective c)),Nat.card_fin]

def maximum (c : OrderedFinpartition n) (i : Fin c.length) : Fin n :=
  c.emb i ⟨c.partSize i - 1, Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩

lemma index_maximum (c : OrderedFinpartition n) (i : Fin c.length) :
    c.index (maximum c i) = i := index_emb c _ _

lemma le_maximum (c : OrderedFinpartition n) (x : Fin n) :
    x ≤ maximum c (c.index x) := by
  nth_rw 1 [← c.emb_invEmbedding x]
  exact (c.emb_strictMono _).monotone (Fin.le_iff_val_le_val.mpr (Nat.le_sub_one_of_lt (c.invEmbedding x).isLt))

lemma relation_iff_range (c : OrderedFinpartition n) (i : Fin c.length) (x : Fin n) :
    c.index x = i ↔ x ∈ Set.range (c.emb i) := by
  constructor
  · intro h
    subst i
    exact ⟨c.invEmbedding x,c.emb_invEmbedding x⟩
  · rintro ⟨j,rfl⟩
    exact index_emb c _ _

lemma maximum_eq_of_partition_eq (c d : OrderedFinpartition n)
    (h : partition c = partition d) (x : Fin n) :
    maximum c (c.index x) = maximum d (d.index x) := by
  apply le_antisymm
  · have hr : d.index (maximum c (c.index x)) = d.index x := by
      apply (Setoid.ext_iff.mp h _ _).mp
      exact index_maximum c _
    simpa only [hr] using le_maximum d (maximum c (c.index x))
  · have hr : c.index (maximum d (d.index x)) = c.index x := by
      apply (Setoid.ext_iff.mp h _ _).mpr
      exact index_maximum d _
    simpa only [hr] using le_maximum c (maximum d (d.index x))

lemma partition_injective : Injective (partition (n := n)) := by
  intro c d h
  have hl : c.length = d.length := (card_partition c).symm.trans
    ((congrArg (fun r : Setoid (Fin n) => Nat.card (Quotient r)) h).trans (card_partition d))
  have hm : Set.range (maximum c) = Set.range (maximum d) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      refine ⟨d.index (maximum c i),?_⟩
      simpa only [index_maximum] using (maximum_eq_of_partition_eq c d h (maximum c i)).symm
    · rintro ⟨i,rfl⟩
      refine ⟨c.index (maximum d i),?_⟩
      simpa only [index_maximum] using maximum_eq_of_partition_eq c d h (maximum d i)
  cases c with | mk cl cs cp ce cm co cd cc =>
    cases d with | mk dl ds dp de dm do' dd dc =>
      dsimp only at hl
      subst dl
      have hmax : (fun i => ce i ⟨cs i - 1,Nat.sub_one_lt_of_lt (cp i)⟩) =
          (fun i => de i ⟨ds i - 1,Nat.sub_one_lt_of_lt (dp i)⟩) :=
        co.range_inj_of_wellFoundedLT do' |>.mp hm
      have hr (i : Fin cl) : Set.range (ce i) = Set.range (de i) := by
        ext x
        let c' : OrderedFinpartition n := ⟨cl,cs,cp,ce,cm,co,cd,cc⟩
        let d' : OrderedFinpartition n := ⟨cl,ds,dp,de,dm,do',dd,dc⟩
        rw [← relation_iff_range c' i x,← relation_iff_range d' i x]
        have hx := Setoid.ext_iff.mp h x (ce i ⟨cs i-1,Nat.sub_one_lt_of_lt (cp i)⟩)
        change (c'.index x = c'.index (ce i ⟨cs i-1,Nat.sub_one_lt_of_lt (cp i)⟩)) ↔
          (d'.index x = d'.index (ce i ⟨cs i-1,Nat.sub_one_lt_of_lt (cp i)⟩)) at hx
        have hci : c'.index (ce i ⟨cs i-1,Nat.sub_one_lt_of_lt (cp i)⟩) = i :=
          index_emb c' _ _
        have hdi : d'.index (ce i ⟨cs i-1,Nat.sub_one_lt_of_lt (cp i)⟩) = i := by
          rw [congrFun hmax i]
          exact index_emb d' _ _
        simpa only [hci,hdi] using hx
      have hs : cs = ds := by
        funext i
        have hh := Nat.card_congr (Set.equivOfEq (hr i))
        simpa only [Nat.card_range_of_injective (cm i).injective,
          Nat.card_range_of_injective (dm i).injective, Nat.card_fin] using hh
      subst ds
      have he : ce = de := by
        funext i
        exact ((cm i).range_inj_of_wellFoundedLT (dm i)).mp (hr i)
      subst de
      rfl

def block (r : Setoid (Fin n)) (x : Fin n) : Finset (Fin n) := by
  classical
  exact univ.filter (r x)

@[simp] lemma mem_block (r : Setoid (Fin n)) (x y : Fin n) : y ∈ block r x ↔ r x y := by
  classical
  simp [block]

lemma block_nonempty (r : Setoid (Fin n)) (x : Fin n) : (block r x).Nonempty :=
  ⟨x,(mem_block r x x).mpr (r.refl x)⟩

lemma block_eq (r : Setoid (Fin n)) {x y : Fin n} (h : r x y) : block r x = block r y := by
  ext z
  simp only [mem_block]
  exact ⟨fun hx => r.trans (r.symm h) hx,fun hy => r.trans h hy⟩

def blockMax (r : Setoid (Fin n)) (x : Fin n) : Fin n :=
  (block r x).max' (block_nonempty r x)

lemma blockMax_related (r : Setoid (Fin n)) (x : Fin n) : r x (blockMax r x) :=
  (mem_block r x _).mp (max'_mem _ _)

lemma blockMax_eq (r : Setoid (Fin n)) {x y : Fin n} (h : r x y) : blockMax r x = blockMax r y := by
  simp only [blockMax,block_eq r h]

def maxima (r : Setoid (Fin n)) : Finset (Fin n) := by
  classical
  exact univ.image (blockMax r)

lemma maximum_fixed (r : Setoid (Fin n)) {x : Fin n} (h : x ∈ maxima r) : blockMax r x = x := by
  classical
  obtain ⟨y,_,rfl⟩ := mem_image.mp h
  exact (blockMax_eq r (blockMax_related r y)).symm

lemma blockMax_mem (r : Setoid (Fin n)) (x : Fin n) : blockMax r x ∈ maxima r := by
  classical
  exact mem_image_of_mem _ (mem_univ x)

def ofSetoid (r : Setoid (Fin n)) : OrderedFinpartition n where
  length := (maxima r).card
  partSize i := (block r ((maxima r).orderEmbOfFin rfl i)).card
  partSize_pos i := card_pos.mpr (block_nonempty r _)
  emb i := (block r ((maxima r).orderEmbOfFin rfl i)).orderEmbOfFin rfl
  emb_strictMono i := OrderEmbedding.strictMono _
  parts_strictMono := by
    have hm (i : Fin (maxima r).card) :
        (block r ((maxima r).orderEmbOfFin rfl i)).orderEmbOfFin rfl
          ⟨(block r ((maxima r).orderEmbOfFin rfl i)).card-1,
            Nat.sub_one_lt_of_lt (card_pos.mpr (block_nonempty r _))⟩ =
            (maxima r).orderEmbOfFin rfl i := by
      rw [orderEmbOfFin_last rfl (card_pos.mpr (block_nonempty r _))]
      exact maximum_fixed r (orderEmbOfFin_mem _ _ _)
    simpa only [hm] using (maxima r).orderEmbOfFin rfl |>.strictMono
  disjoint := by
    intro i _ j _ hij
    dsimp only [Function.onFun]
    rw [range_orderEmbOfFin,range_orderEmbOfFin]
    apply Set.disjoint_left.mpr
    intro x hi hj
    have hr := r.trans (mem_block r _ x |>.mp hi) (r.symm (mem_block r _ x |>.mp hj))
    have he := blockMax_eq r hr
    rw [maximum_fixed r (orderEmbOfFin_mem _ _ _),
      maximum_fixed r (orderEmbOfFin_mem _ _ _)] at he
    exact hij ((maxima r).orderEmbOfFin rfl |>.injective he)
  cover := by
    intro x
    obtain ⟨i,hi⟩ : ∃ i : Fin (maxima r).card,
        (maxima r).orderEmbOfFin rfl i = blockMax r x := by
      apply Set.mem_range.mp
      rw [range_orderEmbOfFin]
      exact blockMax_mem r x
    refine ⟨i,?_⟩
    rw [range_orderEmbOfFin]
    apply (mem_block r _ x).mpr
    rw [hi]
    exact r.symm (blockMax_related r x)

lemma range_ofSetoid (r : Setoid (Fin n)) (i : Fin (ofSetoid r).length) :
    Set.range ((ofSetoid r).emb i) = block r ((maxima r).orderEmbOfFin rfl i) :=
  range_orderEmbOfFin _ _

@[simp] lemma partition_ofSetoid (r : Setoid (Fin n)) : partition (ofSetoid r) = r := by
  apply Setoid.ext
  intro x y
  change (ofSetoid r).index x = (ofSetoid r).index y ↔ r x y
  have hx := (relation_iff_range (ofSetoid r) ((ofSetoid r).index x) x).mp rfl
  rw [range_ofSetoid] at hx
  have hy := (relation_iff_range (ofSetoid r) ((ofSetoid r).index y) y).mp rfl
  rw [range_ofSetoid] at hy
  constructor
  · intro h
    rw [← h] at hy
    exact r.trans (r.symm ((mem_block r _ _).mp hx)) ((mem_block r _ _).mp hy)
  · intro h
    apply Eq.symm
    apply (relation_iff_range (ofSetoid r) ((ofSetoid r).index x) y).mpr
    rw [range_ofSetoid]
    exact (mem_block r _ _).mpr (r.trans ((mem_block r _ _).mp hx) h)

def partitionEquiv (n : ℕ) : OrderedFinpartition n ≃ Setoid (Fin n) :=
  Equiv.ofBijective partition ⟨partition_injective,fun r => ⟨ofSetoid r,partition_ofSetoid r⟩⟩

end BelowOne.OrderedPartitionBridge
end
end

 
section

 
noncomputable section
open Finset Filter
open scoped Topology
namespace BelowOne.PartitionCumulant

lemma iteratedDeriv_succ_log {n : ℕ} {x : ℝ} (hx : x ≠ 0) :
    iteratedDeriv (n+1) Real.log x = (-1 : ℝ)^n * n.factorial * x^(-(n:ℤ)-1) := by
  have heq : deriv Real.log =ᶠ[𝓝 x] Inv.inv := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [Real.deriv_log]
  rw [iteratedDeriv_succ',heq.iteratedDeriv_eq,iteratedDeriv_eq_iterate,iter_deriv_inv]
  grind

lemma iteratedDeriv_log_one {n : ℕ} (hn : 0 < n) :
    iteratedDeriv n Real.log 1 = coefficient n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  simp [iteratedDeriv_succ_log (by norm_num : (1:ℝ) ≠ 0),coefficient]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma iteratedFDeriv_log_comp {f : E → ℝ} {x : E} {n : ℕ}
    (hf : ContDiffAt ℝ n f x) (hx : f x = 1) (hn : 0 < n) (v : Fin n → E) :
    iteratedFDeriv ℝ n (Real.log ∘ f) x v =
      ∑ c : OrderedFinpartition n, coefficient c.length *
        ∏ i : Fin c.length, iteratedFDeriv ℝ (c.partSize i) f x (v ∘ c.emb i) := by
  have hg : ContDiffAt ℝ n Real.log (f x) := by
    rw [hx]
    exact Real.contDiffAt_log.mpr (by norm_num)
  rw [iteratedFDeriv_comp hg hf (le_refl _)]
  simp only [FormalMultilinearSeries.taylorComp,_root_.sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,ftaylorSeries]
  apply sum_congr rfl
  intro c hc
  have hcl : 0 < c.length := Nat.pos_of_ne_zero (fun h => by
    have hi := (c.index ⟨0,hn⟩).isLt
    omega)
  rw [hx,iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    iteratedDeriv_log_one hcl]
  simp only [smul_eq_mul,mul_comm]
  rfl

 
def blockDerivative {n : ℕ} (f : E → ℝ) (x : E) (v : Fin n → E)
    (r : Setoid (Fin n)) : ℝ :=
  let c := OrderedPartitionBridge.ofSetoid r
  ∏ i : Fin c.length, iteratedFDeriv ℝ (c.partSize i) f x (v ∘ c.emb i)

lemma logarithmic_derivative_partition_sum {f : E → ℝ} {x : E} {n : ℕ}
    (hf : ContDiffAt ℝ n f x) (hx : f x = 1) (hn : 0 < n) (v : Fin n → E) :
    iteratedFDeriv ℝ n (Real.log ∘ f) x v =
      ∑ r : Setoid (Fin n), coefficient (Nat.card (Quotient r)) * blockDerivative f x v r := by
  rw [iteratedFDeriv_log_comp hf hx hn]
  apply Fintype.sum_equiv (OrderedPartitionBridge.partitionEquiv n)
  intro c
  have hc : OrderedPartitionBridge.ofSetoid (OrderedPartitionBridge.partition c) = c := by
    apply OrderedPartitionBridge.partition_injective
    simp
  change coefficient c.length * _ = coefficient
    (Nat.card (Quotient (OrderedPartitionBridge.partition c))) * _
  rw [OrderedPartitionBridge.card_partition]
  change _ = coefficient c.length * blockDerivative f x v (OrderedPartitionBridge.partition c)
  unfold blockDerivative
  rw [hc]

end BelowOne.PartitionCumulant
end
end

 
section

 

noncomputable section
open Finset SimpleGraph
open scoped Classical ContDiff
namespace BelowOne.FKPressure
variable {V I J : Type*} [Fintype V]

 

def siteMoment (ends : I → V × V) (hardEnds : J → V × V)
    (E : Finset I) (H : Finset J) (s : ℝ) (v : I → ℝ) (T : Set V) : ℝ :=
  ∑ A ∈ (E.filter (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T)).powerset,
  ∑ B ∈ (E.filter (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T)).powerset,
  ∑ L ∈ (H.filter (fun e => (hardEnds e).1 ∈ T ∧ (hardEnds e).2 ∈ T)).powerset,
    (∏ e ∈ A, v e) * (∏ e ∈ B, v e) *
      s ^ Nat.card ((graph (⊥ : SimpleGraph V) ends A).induce T).ConnectedComponent * (-1 : ℝ)^L.card

omit [Fintype V] in
lemma siteMoment_empty (ends : I → V × V) (hardEnds : J → V × V)
    (E : Finset I) (H : Finset J) (s : ℝ) (v : I → ℝ) :
    siteMoment ends hardEnds E H s v ∅ = 1 := by
  simp [siteMoment,Nat.card_eq_fintype_card]

omit [Fintype V] in
lemma block_edge_iff (r : Setoid V) (ends : I → V × V) (q : Quotient r) (e : I) :
    r (ends e).1 (ends e).2 ∧ edgeBlock r ends e = q ↔
      (ends e).1 ∈ Quotient.mk r ⁻¹' {q} ∧ (ends e).2 ∈ Quotient.mk r ⁻¹' {q} := by
  change (r (ends e).1 (ends e).2 ∧ Quotient.mk r (ends e).1 = q) ↔
    Quotient.mk r (ends e).1 = q ∧ Quotient.mk r (ends e).2 = q
  constructor
  · rintro ⟨h,e⟩
    exact ⟨e,(Quotient.sound h).symm.trans e⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨Quotient.exact (h₁.trans h₂.symm),h₁⟩

omit [Fintype V] in
lemma inducedBlockMoment_eq_siteMoment (ends : I → V × V) (hardEnds : J → V × V)
    (E : Finset I) (H : Finset J) (s : ℝ) (v : I → ℝ) (r : Setoid V) (q : Quotient r) :
    inducedBlockMoment ⊥ ends hardEnds E H s v r q =
      siteMoment ends hardEnds E H s v (Quotient.mk r ⁻¹' {q}) := by
  unfold inducedBlockMoment siteMoment
  simp_rw [block_edge_iff]

omit [Fintype V] in
lemma bot_reachable_le (r : Setoid V) : (⊥ : SimpleGraph V).reachableSetoid ≤ r := by
  intro x y h
  have hx := SimpleGraph.reachable_bot.mp h
  exact hx ▸ r.refl x

lemma blockStructureSum_siteMoment (ends : I → V × V) (hardEnds : J → V × V)
    (E : Finset I) (H : Finset J) (s : ℝ) (v : I → ℝ) (r : Setoid V) :
    blockStructureSum ⊥ ends hardEnds E H s v r =
      ∏ q : Quotient r, siteMoment ends hardEnds E H s v (Quotient.mk r ⁻¹' {q}) := by
  rw [blockStructureSum_factorization _ ends hardEnds E H s v r (bot_reachable_le r)]
  simp_rw [inducedBlockMoment_eq_siteMoment]

def sitePolynomial (ends : I → V × V) (hardEnds : J → V × V)
    (E : Finset I) (H : Finset J) (s : ℝ) (v : I → ℝ) : (V → ℝ) → ℝ :=
  MultiaffineDerivative.polynomial (fun T : Finset V => siteMoment ends hardEnds E H s v T)

lemma sitePolynomial_zero (ends : I → V × V) (hardEnds : J → V × V)
    (E : Finset I) (H : Finset J) (s : ℝ) (v : I → ℝ) :
    sitePolynomial ends hardEnds E H s v 0 = 1 := by
  rw [sitePolynomial,MultiaffineDerivative.polynomial_zero]
  simpa only [Finset.coe_empty] using siteMoment_empty ends hardEnds E H s v

lemma coe_image_emb {n : ℕ} (c : OrderedFinpartition n) (i : Fin c.length) :
    ((univ.image (c.emb i) : Finset (Fin n)) : Set (Fin n)) = Set.range (c.emb i) := by
  ext x
  simp

lemma product_moments_partition {n : ℕ}
    (W : Set (Fin n) → ℝ) (c : OrderedFinpartition n) :
    (∏ q : Quotient (OrderedPartitionBridge.partition c),
      W (Quotient.mk (OrderedPartitionBridge.partition c) ⁻¹' {q})) =
        ∏ i : Fin c.length, W (Set.range (c.emb i)) := by
  unfold OrderedPartitionBridge.partition
  let e := Setoid.quotientKerEquivOfSurjective c.index
    (OrderedPartitionBridge.index_surjective c)
  apply Fintype.prod_equiv e
  intro q
  congr 1
  ext x
  change Quotient.mk (Setoid.ker c.index) x = q ↔ _
  constructor
  · intro hx
    exact (OrderedPartitionBridge.relation_iff_range c (e q) x).mp (congrArg e hx)
  · intro hx
    apply e.injective
    exact (OrderedPartitionBridge.relation_iff_range c (e q) x).mpr hx

lemma blockDerivative_sitePolynomial {n : ℕ}
    (ends : I → Fin n × Fin n) (hardEnds : J → Fin n × Fin n)
    (E : Finset I) (H : Finset J) (s : ℝ) (v : I → ℝ) (r : Setoid (Fin n)) :
    PartitionCumulant.blockDerivative (sitePolynomial ends hardEnds E H s v) 0
      MultiaffineDerivative.coordinate r =
        blockStructureSum ⊥ ends hardEnds E H s v r := by
  unfold PartitionCumulant.blockDerivative
  let c := OrderedPartitionBridge.ofSetoid r
  have hp : OrderedPartitionBridge.partition c = r := OrderedPartitionBridge.partition_ofSetoid r
  have heq : (∏ q : Quotient r, siteMoment ends hardEnds E H s v (Quotient.mk r ⁻¹' {q})) =
      ∏ i : Fin c.length, siteMoment ends hardEnds E H s v (Set.range (c.emb i)) := by
    rw [← hp]
    exact product_moments_partition _ c
  rw [blockStructureSum_siteMoment,heq]
  change (∏ i : Fin c.length, _) = _
  apply prod_congr rfl
  intro i hi
  rw [sitePolynomial,MultiaffineDerivative.polynomial_derivative,
    ite_eq_left (c.emb_strictMono i).injective]
  simp only [Finset.coe_image,Finset.coe_univ,Set.image_univ,c]

 

theorem sitePolynomial_log_derivative {n : ℕ} (hn : 0 < n)
    (ends : I → Fin n × Fin n) (hardEnds : J → Fin n × Fin n)
    (E : Finset I) (H : Finset J) (s : ℝ) (v : I → ℝ) :
    iteratedFDeriv ℝ n (Real.log ∘ sitePolynomial ends hardEnds E H s v) 0
      MultiaffineDerivative.coordinate = connectedSum ⊥ ends hardEnds E H s v := by
  have : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have hf : ContDiffAt ℝ n (sitePolynomial ends hardEnds E H s v) 0 :=
    (MultiaffineDerivative.contDiff_polynomial _ n).contDiffAt
  rw [PartitionCumulant.logarithmic_derivative_partition_sum hf
    (sitePolynomial_zero ends hardEnds E H s v) hn]
  simp_rw [blockDerivative_sitePolynomial]
  exact exponential_cancellation ⊥ ends hardEnds E H s v

theorem sitePolynomial_log_derivative_nonpos {n : ℕ} (hn : 0 < n)
    (ends : I → Fin n × Fin n) (hardEnds : J → Fin n × Fin n)
    (E : Finset I) (H : Finset J) {u : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e) :
    iteratedFDeriv ℝ n (Real.log ∘ sitePolynomial ends hardEnds E H (-u) v) 0
      MultiaffineDerivative.coordinate ≤ 0 := by
  rw [sitePolynomial_log_derivative hn]
  exact connectedSum_nonpos ⊥ ends hardEnds E H hu hu1 v hv

end BelowOne.FKPressure
end
end

 
section

 

noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace BelowOne.FKPressure
variable {V I J : Type*} [Fintype V]

def inducedPartition (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) (T : Set V) : ℝ :=
  ∑ A ∈ (E.filter (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T)).powerset,
    (∏ e ∈ A, v e) *
      s ^ Nat.card ((graph (⊥ : SimpleGraph V) ends A).induce T).ConnectedComponent

lemma alternating_powerset (H : Finset J) :
    (∑ L ∈ H.powerset, (-1 : ℝ)^L.card) = if H = ∅ then 1 else 0 := by
  have hh : (∑ L ∈ H.powerset, (-1 : ℝ)^L.card) = ∏ h ∈ H, (1 + (-1 : ℝ)) := by
    simpa only [prod_const] using (prod_one_add (f := fun _ : J => (-1:ℝ)) H).symm
  rw [hh]
  by_cases h : H = ∅
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨e,he⟩ := nonempty_iff_ne_empty.mpr h
    exact prod_eq_zero he (by norm_num)

omit [Fintype V] in
lemma siteMoment_separate (ends : I → V × V) (hardEnds : J → V × V)
    (E : Finset I) (H : Finset J) (s : ℝ) (v : I → ℝ) (T : Set V) :
    siteMoment ends hardEnds E H s v T =
      inducedPartition ends E s v T *
        (∑ B ∈ (E.filter (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T)).powerset,
          ∏ e ∈ B, v e) *
        (∑ L ∈ (H.filter (fun e => (hardEnds e).1 ∈ T ∧ (hardEnds e).2 ∈ T)).powerset,
          (-1:ℝ)^L.card) := by
  unfold siteMoment inducedPartition
  rw [sum_mul,sum_mul]
  apply sum_congr rfl
  intro A hA
  rw [show (∏ e ∈ A, v e) * s ^ Nat.card (induce T (graph ⊥ ends A)).ConnectedComponent *
      (∑ B ∈ (E.filter (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T)).powerset, ∏ e ∈ B, v e) =
      ∑ B ∈ (E.filter (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T)).powerset,
        (∏ e ∈ A, v e) * s ^ Nat.card (induce T (graph ⊥ ends A)).ConnectedComponent * (∏ e ∈ B, v e) from mul_sum _ _ _]
  rw [sum_mul]
  apply sum_congr rfl
  intro B hB
  rw [mul_sum]
  apply sum_congr rfl
  intro L hL
  ring

omit [Fintype V] in
lemma siteMoment_squarefree (ends : I → V × V) (hardEnds : J → V × V)
    (E : Finset I) (H : Finset J) (s : ℝ) (v : I → ℝ) (T : Set V) :
    siteMoment ends hardEnds E H s v T =
      if (H.filter (fun e => (hardEnds e).1 ∈ T ∧ (hardEnds e).2 ∈ T)) = ∅ then
        (∏ e ∈ E.filter (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T), (1 + v e)) *
          inducedPartition ends E s v T else 0 := by
  rw [siteMoment_separate,alternating_powerset,← prod_one_add]
  split_ifs <;> ring

omit [Fintype V] in
lemma siteMoment_collision_zero (ends : I → V × V) (hardEnds : J → V × V)
    (E : Finset I) (H : Finset J) (s : ℝ) (v : I → ℝ) (T : Set V)
    {e : J} (he : e ∈ H) (h₁ : (hardEnds e).1 ∈ T) (h₂ : (hardEnds e).2 ∈ T) :
    siteMoment ends hardEnds E H s v T = 0 := by
  rw [siteMoment_squarefree,ite_eq_right]
  exact nonempty_iff_ne_empty.mp ⟨e,mem_filter.mpr ⟨he,h₁,h₂⟩⟩

end BelowOne.FKPressure
end
end

 
section

 

noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace BelowOne.FKPressure
variable {V W I J : Type*} [Fintype V] [Fintype W]

def imageEquiv (f : V → W) (T : Set V) (hf : Set.InjOn f T) : T ≃ f '' T :=
  Equiv.ofBijective (fun x => ⟨f x, Set.mem_image_of_mem f x.property⟩) (by
    constructor
    · intro x y h
      exact Subtype.ext (hf x.property y.property (congrArg Subtype.val h))
    · rintro ⟨y,x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩)

omit [Fintype V] [Fintype W] in
lemma induced_graph_image_iso (f : V → W) (T : Set V) (hf : Set.InjOn f T)
    (ends : I → V × V) (ends' : J → W × W) (g : I → J) (A : Finset I)
    (hT : ∀ e ∈ A, (ends e).1 ∈ T ∧ (ends e).2 ∈ T)
    (he : ∀ e ∈ A, ends' (g e) = (f (ends e).1, f (ends e).2)) :
    Nonempty ((graph ⊥ ends A).induce T ≃g
      (graph ⊥ ends' (A.image g)).induce (f '' T)) := by
  refine ⟨{ toEquiv := imageEquiv f T hf, map_rel_iff' := ?_ }⟩
  intro x y
  change (graph ⊥ ends' (A.image g)).Adj (f x) (f y) ↔ (graph ⊥ ends A).Adj x y
  simp only [graph_adj_iff,SimpleGraph.bot_adj,false_or]
  constructor
  · rintro ⟨j,hj,hxy⟩
    obtain ⟨e,heA,rfl⟩ := mem_image.mp hj
    rw [he e heA] at hxy
    obtain ⟨h,hne⟩ := (edge_adj _ _ _ _).mp hxy
    refine ⟨e,heA,(edge_adj _ _ _ _).mpr ⟨?_,?_⟩⟩
    · rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · exact Or.inl ⟨hf x.property (hT e heA).1 hx,hf y.property (hT e heA).2 hy⟩
      · exact Or.inr ⟨hf x.property (hT e heA).2 hx,hf y.property (hT e heA).1 hy⟩
    · intro h
      exact hne (congrArg f h)
  · rintro ⟨e,heA,hxy⟩
    refine ⟨g e,mem_image_of_mem g heA,?_⟩
    rw [he e heA]
    obtain ⟨h,hne⟩ := (edge_adj _ _ _ _).mp hxy
    apply (edge_adj _ _ _ _).mpr
    constructor
    · rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · exact Or.inl ⟨congrArg f hx,congrArg f hy⟩
      · exact Or.inr ⟨congrArg f hx,congrArg f hy⟩
    · exact fun h => hne (hf x.property y.property h)

omit [Fintype V] [Fintype W] in
lemma induced_component_image (f : V → W) (T : Set V) (hf : Set.InjOn f T)
    (ends : I → V × V) (ends' : J → W × W) (g : I → J) (A : Finset I)
    (hT : ∀ e ∈ A, (ends e).1 ∈ T ∧ (ends e).2 ∈ T)
    (he : ∀ e ∈ A, ends' (g e) = (f (ends e).1, f (ends e).2)) :
    Nat.card ((graph ⊥ ends A).induce T).ConnectedComponent =
      Nat.card ((graph ⊥ ends' (A.image g)).induce (f '' T)).ConnectedComponent := by
  obtain ⟨e⟩ := induced_graph_image_iso f T hf ends ends' g A hT he
  exact Nat.card_congr e.connectedComponentEquiv

omit [Fintype V] [Fintype W] in
lemma inducedPartition_reindex (f : V → W) (T : Set V) (hf : Set.InjOn f T)
    (ends : I → V × V) (ends' : J → W × W) (g : I → J) (E : Finset I)
    (s : ℝ) (v : J → ℝ)
    (hT : ∀ e ∈ E, (ends e).1 ∈ T ∧ (ends e).2 ∈ T)
    (he : ∀ e ∈ E, ends' (g e) = (f (ends e).1, f (ends e).2))
    (hg : Set.InjOn g E) :
    inducedPartition ends E s (v ∘ g) T =
      inducedPartition ends' (E.image g) s v (f '' T) := by
  have hfilter : E.filter (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T) = E := by
    exact filter_eq_self.mpr hT
  have hfilter' : (E.image g).filter (fun e => (ends' e).1 ∈ f '' T ∧
      (ends' e).2 ∈ f '' T) = E.image g := by
    apply filter_eq_self.mpr
    intro j hj
    obtain ⟨e,heE,rfl⟩ := mem_image.mp hj
    rw [he e heE]
    exact ⟨Set.mem_image_of_mem f (hT e heE).1,Set.mem_image_of_mem f (hT e heE).2⟩
  unfold inducedPartition
  rw [hfilter,hfilter',powerset_image,sum_image]
  · apply sum_congr rfl
    intro A hA
    have hAE := mem_powerset.mp hA
    rw [induced_component_image f T hf ends ends' g A
      (fun e heA => hT e (hAE heA)) (fun e heA => he e (hAE heA)),prod_image]
    · rfl
    · intro a ha b hb hab
      exact hg (hAE ha) (hAE hb) hab
  · intro A hA B hB hAB
    exact (Finset.image_eq_image_iff_of_injOn hg
      (mem_powerset.mp hA) (mem_powerset.mp hB)).mp hAB

end BelowOne.FKPressure
end
end

 
section

 

noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace BelowOne.FKPressure
attribute [local instance] Classical.propDecidable
variable {V U I : Type*} [Fintype V] [Fintype U] [LinearOrder U]

def liftEdges (τ : U → V) (ends : I → V × V) (E : Finset I) : Finset (I × U × U) :=
  (E ×ˢ (univ ×ˢ univ)).filter (fun e => τ e.2.1 = (ends e.1).1 ∧ τ e.2.2 = (ends e.1).2)

def hardEdges (τ : U → V) : Finset (U × U) :=
  univ.filter (fun e => e.1 < e.2 ∧ τ e.1 = τ e.2)

def squarefreeMoment (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) (T : Set V) : ℝ :=
  (∏ e ∈ E.filter (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T), (1 + v e)) *
    inducedPartition ends E s v T

omit [Fintype V] [LinearOrder U] in
lemma mem_liftEdges (τ : U → V) (ends : I → V × V) (E : Finset I) (e : I × U × U) :
    e ∈ liftEdges τ ends E ↔ e.1 ∈ E ∧ τ e.2.1 = (ends e.1).1 ∧ τ e.2.2 = (ends e.1).2 := by
  simp [liftEdges]

omit [Fintype V] [LinearOrder U] in
lemma liftEdges_filter_image (τ : U → V) (ends : I → V × V) (E : Finset I) (T : Set U) :
    ((liftEdges τ ends E).filter (fun e => e.2.1 ∈ T ∧ e.2.2 ∈ T)).image Prod.fst =
      E.filter (fun e => (ends e).1 ∈ τ '' T ∧ (ends e).2 ∈ τ '' T) := by
  ext e
  constructor
  · intro h
    obtain ⟨⟨d,i,j⟩,hlift,heq⟩ := mem_image.mp h
    change d = e at heq
    subst e
    obtain ⟨he,hij⟩ := mem_filter.mp hlift
    obtain ⟨hd,hi,hj⟩ := (mem_liftEdges _ _ _ _).mp he
    exact mem_filter.mpr ⟨hd,⟨i,hij.1,hi⟩,⟨j,hij.2,hj⟩⟩
  · intro h
    obtain ⟨he,⟨i,hi,hei⟩,⟨j,hj,hej⟩⟩ := mem_filter.mp h
    exact mem_image.mpr ⟨(e,i,j),mem_filter.mpr
      ⟨(mem_liftEdges _ _ _ _).mpr ⟨he,hei,hej⟩,hi,hj⟩,rfl⟩

omit [Fintype V] [LinearOrder U] in
lemma liftEdges_filter_inj (τ : U → V) (ends : I → V × V) (E : Finset I)
    (T : Set U) (hτ : Set.InjOn τ T) :
    Set.InjOn Prod.fst (↑((liftEdges τ ends E).filter (fun e => e.2.1 ∈ T ∧ e.2.2 ∈ T)) : Set (I × U × U)) := by
  rintro ⟨e,i,j⟩ h ⟨e',i',j'⟩ h' he
  obtain ⟨hm,hi,hj⟩ := mem_filter.mp h
  obtain ⟨hm',hi',hj'⟩ := mem_filter.mp h'
  obtain ⟨_,hei,hej⟩ := (mem_liftEdges _ _ _ _).mp hm
  obtain ⟨_,hei',hej'⟩ := (mem_liftEdges _ _ _ _).mp hm'
  change e = e' at he
  subst e'
  have hii := hτ hi hi' (hei.trans hei'.symm)
  have hjj := hτ hj hj' (hej.trans hej'.symm)
  exact Prod.ext rfl (Prod.ext hii hjj)

omit [Fintype V] in
lemma hardEdges_filter_empty_iff (τ : U → V) (T : Set U) :
    (hardEdges τ).filter (fun e => e.1 ∈ T ∧ e.2 ∈ T) = ∅ ↔ Set.InjOn τ T := by
  rw [Finset.eq_empty_iff_forall_notMem]
  simp only [mem_filter,hardEdges,mem_univ,true_and]
  constructor
  · intro h a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab' | hba'
    · exact h (a,b) ⟨⟨hab',hab⟩,ha,hb⟩
    · exact h (b,a) ⟨⟨hba',hab.symm⟩,hb,ha⟩
  · intro h e he
    exact (ne_of_lt he.1.1) (h he.2.1 he.2.2 he.1.2)

omit [Fintype V] in
lemma inducedPartition_filter (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) (T : Set V) :
    inducedPartition ends (E.filter (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T)) s v T =
      inducedPartition ends E s v T := by
  unfold inducedPartition
  rw [filter_filter]
  simp only [and_self]

omit [Fintype V] in
lemma siteMoment_lift (τ : U → V) (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) (T : Set U) :
    siteMoment Prod.snd id (liftEdges τ ends E) (hardEdges τ) s (v ∘ Prod.fst) T =
      if Set.InjOn τ T then squarefreeMoment ends E s v (τ '' T) else 0 := by
  rw [siteMoment_squarefree]
  simp only [id_eq]
  simp only [hardEdges_filter_empty_iff]
  split_ifs with hτ
  · let F := (liftEdges τ ends E).filter (fun e => e.2.1 ∈ T ∧ e.2.2 ∈ T)
    have hF : ∀ e ∈ F, e.2.1 ∈ T ∧ e.2.2 ∈ T := fun e he => (mem_filter.mp he).2
    have he : ∀ e ∈ F, ends (Prod.fst e) = (τ e.2.1,τ e.2.2) := by
      intro e he
      have h := (mem_liftEdges _ _ _ _).mp (mem_filter.mp he).1
      exact Prod.ext h.2.1.symm h.2.2.symm
    have hpart := inducedPartition_reindex τ T hτ Prod.snd ends Prod.fst F s v hF he
      (liftEdges_filter_inj τ ends E T hτ)
    rw [inducedPartition_filter] at hpart
    rw [liftEdges_filter_image] at hpart
    rw [inducedPartition_filter] at hpart
    unfold squarefreeMoment
    rw [hpart]
    congr 1
    rw [← liftEdges_filter_image τ ends E T,prod_image]
    · rfl
    · exact liftEdges_filter_inj τ ends E T hτ
  · rfl

end BelowOne.FKPressure
end
end

 
section

 

noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace BelowOne.FKPressure
variable {V I : Type*} [Fintype V]

def unscaledSitePolynomial (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) : (V → ℝ) → ℝ :=
  MultiaffineDerivative.polynomial (fun T => squarefreeMoment ends E s v (T : Set V))

lemma unscaledSitePolynomial_zero (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) : unscaledSitePolynomial ends E s v 0 = 1 := by
  rw [unscaledSitePolynomial,MultiaffineDerivative.polynomial_zero]
  simp [squarefreeMoment,inducedPartition,Nat.card_eq_fintype_card]

lemma injOn_range_iff {X Y Z : Type*} (f : Y → Z) (e : X ↪ Y) :
    Set.InjOn f (Set.range e) ↔ Function.Injective (f ∘ e) := by
  constructor
  · intro h x y hxy
    exact e.injective (h ⟨x,rfl⟩ ⟨y,rfl⟩ hxy)
  · intro h x hx y hy hxy
    obtain ⟨a,rfl⟩ := hx
    obtain ⟨b,rfl⟩ := hy
    exact congrArg e (h hxy)

lemma lifted_derivative {n k : ℕ} (τ : Fin n → V) (e : Fin k ↪ Fin n)
    (ends : I → V × V) (E : Finset I) (s : ℝ) (v : I → ℝ) :
    iteratedFDeriv ℝ k (unscaledSitePolynomial ends E s v) 0
      (MultiaffineDerivative.coordinate ∘ (τ ∘ e)) =
        siteMoment Prod.snd id (liftEdges τ ends E) (hardEdges τ) s
          (v ∘ Prod.fst) (Set.range e) := by
  rw [unscaledSitePolynomial,MultiaffineDerivative.polynomial_derivative,
    siteMoment_lift,injOn_range_iff]
  simp only [Finset.coe_image,Finset.coe_univ,Set.image_univ,Set.range_comp]
  split_ifs <;> rfl

lemma blockDerivative_lift {n : ℕ} (τ : Fin n → V)
    (ends : I → V × V) (E : Finset I) (s : ℝ) (v : I → ℝ) (r : Setoid (Fin n)) :
    PartitionCumulant.blockDerivative (unscaledSitePolynomial ends E s v) 0
      (MultiaffineDerivative.coordinate ∘ τ) r =
        PartitionCumulant.blockDerivative
          (sitePolynomial Prod.snd id (liftEdges τ ends E) (hardEdges τ) s (v ∘ Prod.fst)) 0
          MultiaffineDerivative.coordinate r := by
  unfold PartitionCumulant.blockDerivative
  apply prod_congr rfl
  intro i hi
  let c := OrderedPartitionBridge.ofSetoid r
  let e : Fin (c.partSize i) ↪ Fin n := ⟨c.emb i,(c.emb_strictMono i).injective⟩
  change iteratedFDeriv ℝ _ (unscaledSitePolynomial ends E s v) 0
    (MultiaffineDerivative.coordinate ∘ (τ ∘ e)) = _
  rw [lifted_derivative]
  rw [sitePolynomial,MultiaffineDerivative.polynomial_derivative,
    ite_eq_left (c.emb_strictMono i).injective]
  simp only [Finset.coe_image,Finset.coe_univ,Set.image_univ]
  rfl

theorem unscaledSitePolynomial_log_derivative {n : ℕ} (hn : 0 < n)
    (τ : Fin n → V) (ends : I → V × V) (E : Finset I) (s : ℝ) (v : I → ℝ) :
    iteratedFDeriv ℝ n (Real.log ∘ unscaledSitePolynomial ends E s v) 0
      (MultiaffineDerivative.coordinate ∘ τ) =
        connectedSum ⊥ Prod.snd id (liftEdges τ ends E) (hardEdges τ) s (v ∘ Prod.fst) := by
  rw [← sitePolynomial_log_derivative hn]
  have hf : ContDiffAt ℝ n (unscaledSitePolynomial ends E s v) 0 :=
    (MultiaffineDerivative.contDiff_polynomial _ n).contDiffAt
  have hg : ContDiffAt ℝ n (sitePolynomial Prod.snd id (liftEdges τ ends E)
      (hardEdges τ) s (v ∘ Prod.fst)) 0 :=
    (MultiaffineDerivative.contDiff_polynomial _ n).contDiffAt
  rw [PartitionCumulant.logarithmic_derivative_partition_sum hf
    (unscaledSitePolynomial_zero ends E s v) hn,
    PartitionCumulant.logarithmic_derivative_partition_sum hg
    (sitePolynomial_zero _ _ _ _ _ _) hn]
  simp_rw [blockDerivative_lift]

theorem unscaledSitePolynomial_log_derivative_nonpos {n : ℕ} (hn : 0 < n)
    (τ : Fin n → V) (ends : I → V × V) (E : Finset I)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e) :
    iteratedFDeriv ℝ n (Real.log ∘ unscaledSitePolynomial ends E (-u) v) 0
      (MultiaffineDerivative.coordinate ∘ τ) ≤ 0 := by
  have : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  rw [unscaledSitePolynomial_log_derivative hn]
  apply connectedSum_nonpos ⊥ Prod.snd id _ _ hu hu1
  intro e he
  exact hv e.1 ((mem_liftEdges _ _ _ _).mp he).1

end BelowOne.FKPressure
end
end

 
section

 

noncomputable section
open Finset
namespace BelowOne.ComponentProduct
attribute [local instance] Classical.propDecidable
variable {V Q : Type*} [Fintype V] [Fintype Q]

def saturated (f : V → Q) (T : Finset V) : Prop :=
  ∀ a b, f a = f b → (a ∈ T ↔ b ∈ T)

def preimage (f : V → Q) (J : Finset Q) : Finset V := univ.filter (fun v => f v ∈ J)

omit [Fintype Q] in
lemma mem_preimage (f : V → Q) (J : Finset Q) (v : V) :
    v ∈ preimage f J ↔ f v ∈ J := by simp [preimage]

omit [Fintype Q] in
lemma preimage_saturated (f : V → Q) (J : Finset Q) : saturated f (preimage f J) := by
  intro a b hab
  simp only [mem_preimage,hab]

omit [Fintype Q] in
lemma image_preimage (f : V → Q) (hf : Function.Surjective f) (J : Finset Q) :
    (preimage f J).image f = J := by
  ext q
  simp only [mem_image,mem_preimage]
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact hv
  · intro hq
    obtain ⟨v,rfl⟩ := hf q
    exact ⟨v,hq,rfl⟩

omit [Fintype Q] in
lemma preimage_image (f : V → Q) (T : Finset V) (hT : saturated f T) :
    preimage f (T.image f) = T := by
  ext v
  simp only [mem_preimage,mem_image]
  constructor
  · rintro ⟨w,hw,hwv⟩
    exact (hT w v hwv).mp hw
  · intro hv
    exact ⟨v,hv,rfl⟩

omit [Fintype Q] in
lemma selected_product (f : V → Q) (J : Finset Q) (s : ℝ) (x : V → ℝ) :
    (∏ q ∈ J, s * ∏ v ∈ univ.filter (fun v => f v = q), x v) =
      s ^ J.card * ∏ v ∈ preimage f J, x v := by
  rw [prod_mul_distrib,prod_const]
  congr 1
  exact Finset.prod_fiberwise_eq_prod_filter univ J f x

lemma expansion (f : V → Q) (hf : Function.Surjective f) (s : ℝ) (x : V → ℝ) :
    (∏ q : Q, (1 + s * ∏ v ∈ univ.filter (fun v => f v = q), x v)) =
      ∑ T : Finset V, if saturated f T then
        s ^ (T.image f).card * ∏ v ∈ T, x v else 0 := by
  rw [prod_one_add]
  symm
  rw [← sum_filter]
  symm
  apply sum_bij (fun J hJ => preimage f J)
  · intro J hJ
    exact mem_filter.mpr ⟨mem_univ _,preimage_saturated f J⟩
  · intro J hJ K hK hJK
    have h := congrArg (Finset.image f) hJK
    simpa only [image_preimage f hf] using h
  · intro T hT
    refine ⟨T.image f,mem_powerset.mpr (subset_univ _),?_⟩
    exact preimage_image f T (mem_filter.mp hT).2
  · intro J hJ
    rw [selected_product,image_preimage f hf]

end BelowOne.ComponentProduct
end
end

 
section

 

noncomputable section
open Finset SimpleGraph
namespace BelowOne.FKPressure
attribute [local instance] Classical.propDecidable
variable {V I : Type*} [Fintype V]

omit [Fintype V] in
lemma reachable_induce_saturated (G : SimpleGraph V) (T : Finset V)
    (hT : ComponentProduct.saturated G.connectedComponentMk T) (x y : (T : Set V)) :
    (G.induce T).Reachable x y ↔ G.Reachable x.1 y.1 := by
  constructor
  · exact fun h => h.map (SimpleGraph.Embedding.induce _).toHom
  · rintro ⟨p⟩
    have hp : ∀ z ∈ p.support, z ∈ (T : Set V) := by
      intro z hz
      have he : G.connectedComponentMk x = G.connectedComponentMk z :=
        ConnectedComponent.sound ⟨p.takeUntil z hz⟩
      exact (hT x z he).mp x.property
    exact ⟨p.induce (T : Set V) hp⟩

omit [Fintype V] in
lemma component_card_induce_saturated (G : SimpleGraph V) (T : Finset V)
    (hT : ComponentProduct.saturated G.connectedComponentMk T) :
    Nat.card (G.induce T).ConnectedComponent = (T.image G.connectedComponentMk).card := by
  let f : ↥(T : Set V) → G.ConnectedComponent := fun x => G.connectedComponentMk x
  have hr : (G.induce T).reachableSetoid = Setoid.ker f := by
    apply Setoid.ext
    intro x y
    change (G.induce T).Reachable x y ↔ G.connectedComponentMk x = G.connectedComponentMk y
    rw [reachable_induce_saturated G T hT]
    exact ⟨ConnectedComponent.sound,ConnectedComponent.exact⟩
  have him : Set.range f = (↑(T.image G.connectedComponentMk) : Set G.ConnectedComponent) := by
    ext q
    simp only [Set.mem_range,Finset.mem_coe,mem_image,f]
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  change Nat.card (Quotient (G.induce T).reachableSetoid) = _
  rw [hr,Nat.card_congr (Setoid.quotientKerEquivRange f),him,Nat.card_eq_fintype_card]
  exact Fintype.card_coe _

omit [Fintype V] in
lemma saturated_graph_iff (ends : I → V × V) (A : Finset I) (T : Finset V) :
    ComponentProduct.saturated (graph ⊥ ends A).connectedComponentMk T ↔
      ∀ e ∈ A, ((ends e).1 ∈ T ↔ (ends e).2 ∈ T) := by
  constructor
  · intro h e he
    exact h _ _ (ConnectedComponent.sound (endpoints_reachable ⊥ ends he))
  · intro h a b hab
    have hr : (graph ⊥ ends A).Reachable a b := ConnectedComponent.exact hab
    obtain ⟨p⟩ := hr
    clear hab
    induction p with
    | nil => rfl
    | @cons a b c hab p ih =>
      have heq : a ∈ T ↔ b ∈ T := by
        obtain hfalse | ⟨e,he,hxy⟩ := (graph_adj_iff ⊥ ends A a b).mp hab
        · exact False.elim hfalse
        obtain ⟨hxy,_⟩ := (edge_adj _ _ _ _).mp hxy
        rcases hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact h e he
        · exact (h e he).symm
      exact heq.trans ih

def componentProduct (G : SimpleGraph V) (s : ℝ) (x : V → ℝ) : ℝ :=
  ∏ c : G.ConnectedComponent, (1 + s *
    ∏ v ∈ univ.filter (fun v => G.connectedComponentMk v = c), x v)

lemma componentProduct_expansion (ends : I → V × V) (A : Finset I)
    (s : ℝ) (x : V → ℝ) :
    componentProduct (graph ⊥ ends A) s x =
      ∑ T : Finset V, if ∀ e ∈ A, ((ends e).1 ∈ T ↔ (ends e).2 ∈ T) then
        s ^ Nat.card ((graph ⊥ ends A).induce T).ConnectedComponent * ∏ v ∈ T, x v else 0 := by
  rw [componentProduct,ComponentProduct.expansion
    (graph ⊥ ends A).connectedComponentMk (fun q => Quot.mk_surjective q)]
  apply sum_congr rfl
  intro T hT
  by_cases h : ComponentProduct.saturated (graph ⊥ ends A).connectedComponentMk T
  · rw [ite_eq_left h,ite_eq_left ((saturated_graph_iff ends A T).mp h),component_card_induce_saturated _ T h]
  · rw [ite_eq_right h,ite_eq_right (fun hh => h ((saturated_graph_iff ends A T).mpr hh))]

end BelowOne.FKPressure
end
end

 
section

 
noncomputable section
open Finset
namespace BelowOne.SubsetSplitting
attribute [local instance] Classical.propDecidable
variable {I : Type*}

lemma sum_factorization_binary (E : Finset I) (p : I → Prop) (W W₁ W₂ : Finset I → ℝ)
    (hW : ∀ A ⊆ E, W A = W₁ (A.filter p) * W₂ (A.filter (fun e => ¬p e))) :
    (∑ A ∈ E.powerset, W A) =
      (∑ A ∈ (E.filter p).powerset, W₁ A) *
        (∑ A ∈ (E.filter (fun e => ¬p e)).powerset, W₂ A) := by
  have h := sum_factorization E (fun e => decide (p e)) W
    (fun b A => if b then W₁ A else W₂ A) (by
      intro A hA
      rw [Fintype.prod_bool]
      simpa only [Bool.false_eq_true,ite_false,ite_true,decide_eq_false_iff_not,
        decide_eq_true_eq] using hW A hA)
  simpa only [Fintype.prod_bool,fiber,Bool.false_eq_true,ite_false,ite_true,
    decide_eq_false_iff_not,decide_eq_true_eq,mul_comm] using h

end BelowOne.SubsetSplitting
end
end

 
section

 

noncomputable section
open Finset SimpleGraph
namespace BelowOne.FKPressure
attribute [local instance] Classical.propDecidable
variable {V I : Type*} [Fintype V]

omit [Fintype V] in
lemma graph_induce_inside_filter (G : SimpleGraph V) (ends : I → V × V)
    (A : Finset I) (T : Set V) :
    (graph G ends (A.filter (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T))).induce T =
      (graph G ends A).induce T := by
  ext x y
  simp only [SimpleGraph.induce_adj,graph_adj_iff,mem_filter]
  constructor
  · rintro (h | ⟨e,⟨he,_⟩,hxy⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e,he,hxy⟩
  · rintro (h | ⟨e,he,hxy⟩)
    · exact Or.inl h
    · refine Or.inr ⟨e,⟨he,?_⟩,hxy⟩
      rcases (edge_adj _ _ _ _).mp hxy with ⟨⟨hx,hy⟩ | ⟨hx,hy⟩,_⟩
      · exact ⟨hx ▸ x.property,hy ▸ y.property⟩
      · exact ⟨hy ▸ y.property,hx ▸ x.property⟩

omit [Fintype V] in
lemma confined_edge_sum (ends : I → V × V) (E : Finset I) (T : Set V)
    (s : ℝ) (v : I → ℝ) :
    (∑ A ∈ E.powerset, if ∀ e ∈ A, ((ends e).1 ∈ T ↔ (ends e).2 ∈ T) then
      (∏ e ∈ A, v e) * s ^ Nat.card ((graph ⊥ ends A).induce T).ConnectedComponent else 0) =
      inducedPartition ends E s v T *
        ∏ e ∈ E.filter (fun e => (ends e).1 ∉ T ∧ (ends e).2 ∉ T), (1 + v e) := by
  trans ∑ A ∈ (E.filter (fun e => (ends e).1 ∈ T ↔ (ends e).2 ∈ T)).powerset,
    (∏ e ∈ A, v e) * s ^ Nat.card ((graph ⊥ ends A).induce T).ConnectedComponent
  · have hh := sum_powerset_filter E (fun e => (ends e).1 ∈ T ↔ (ends e).2 ∈ T)
      (fun A => (∏ e ∈ A, v e) * s ^ Nat.card ((graph ⊥ ends A).induce T).ConnectedComponent)
    simpa only [MultiaffineDerivative.ite_classical,filter_classical] using hh
  let F := E.filter (fun e => (ends e).1 ∈ T ↔ (ends e).2 ∈ T)
  have h := SubsetSplitting.sum_factorization_binary F
    (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T)
    (fun A => (∏ e ∈ A, v e) * s ^ Nat.card ((graph ⊥ ends A).induce T).ConnectedComponent)
    (fun A => (∏ e ∈ A, v e) * s ^ Nat.card ((graph ⊥ ends A).induce T).ConnectedComponent)
    (fun A => ∏ e ∈ A, v e) (by
      intro A hA
      simp only [filter_classical]
      have hg := graph_induce_inside_filter (⊥ : SimpleGraph V) ends A T
      simp only [filter_classical] at hg
      rw [hg]
      rw [← Finset.prod_filter_mul_prod_filter_not A
        (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T) v]
      simp only [filter_classical]
      ring)
  have hi : F.filter (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T) =
      E.filter (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T) := by
    ext e
    simp only [F,mem_filter]
    tauto
  have ho : F.filter (fun e => ¬((ends e).1 ∈ T ∧ (ends e).2 ∈ T)) =
      E.filter (fun e => (ends e).1 ∉ T ∧ (ends e).2 ∉ T) := by
    ext e
    simp only [F,mem_filter]
    tauto
  simp only [filter_classical] at h hi ho ⊢
  rw [hi,ho,← prod_one_add] at h
  simpa only [F,inducedPartition,filter_classical] using h

def percolationSitePolynomial (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) (x : V → ℝ) : ℝ :=
  (∑ A ∈ E.powerset, (∏ e ∈ A, v e) * componentProduct (graph ⊥ ends A) s x) /
    ∏ e ∈ E, (1 + v e)

def percolationCoefficient (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) (T : Finset V) : ℝ :=
  (inducedPartition ends E s v T *
    ∏ e ∈ E.filter (fun e => (ends e).1 ∉ T ∧ (ends e).2 ∉ T), (1 + v e)) /
      ∏ e ∈ E, (1 + v e)

lemma percolationSitePolynomial_eq (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) :
    percolationSitePolynomial ends E s v =
      MultiaffineDerivative.polynomial (percolationCoefficient ends E s v) := by
  funext x
  unfold percolationSitePolynomial
  simp_rw [componentProduct_expansion,mul_sum]
  rw [sum_comm]
  unfold MultiaffineDerivative.polynomial percolationCoefficient
  rw [sum_div]
  apply sum_congr rfl
  intro T hT
  rw [div_mul_eq_mul_div]
  congr 1
  have hh := confined_edge_sum ends E (T : Set V) s v
  simp only [Finset.mem_coe,filter_classical] at hh ⊢
  rw [← hh,sum_mul]
  apply sum_congr rfl
  intro A hA
  split_ifs <;> ring

end BelowOne.FKPressure
end
end

 
section

 

noncomputable section
open Finset
namespace BelowOne.FKPressure
attribute [local instance] Classical.propDecidable
variable {V I : Type*} [Fintype V]

def incidentProduct (ends : I → V × V) (E : Finset I) (v : I → ℝ) (i : V) : ℝ :=
  ∏ e ∈ E, (if (ends e).1 = i then 1 + v e else 1) *
    (if (ends e).2 = i then 1 + v e else 1)

def incidentScale (ends : I → V × V) (E : Finset I) (v : I → ℝ) (i : V) : ℝ :=
  (incidentProduct ends E v i)⁻¹

omit [Fintype V] in
lemma incidentProduct_pos (ends : I → V × V) (E : Finset I) (v : I → ℝ)
    (hv : ∀ e ∈ E, 0 ≤ v e) (i : V) : 0 < incidentProduct ends E v i := by
  unfold incidentProduct
  apply prod_pos
  intro e he
  apply mul_pos <;> split_ifs <;> linarith [hv e he]

omit [Fintype V] in
lemma incidentProduct_subprod (ends : I → V × V) (E : Finset I)
    (v : I → ℝ) (T : Finset V) :
    (∏ i ∈ T, incidentProduct ends E v i) =
      ∏ e ∈ E, (if (ends e).1 ∈ T then 1 + v e else 1) *
        (if (ends e).2 ∈ T then 1 + v e else 1) := by
  unfold incidentProduct
  rw [prod_comm]
  apply prod_congr rfl
  intro e he
  rw [prod_mul_distrib]
  simp only [prod_ite_eq]

omit [Fintype V] in
lemma incident_product_identity (ends : I → V × V) (E : Finset I)
    (v : I → ℝ) (T : Finset V) :
    (∏ e ∈ E, (1 + v e)) *
        (∏ e ∈ E.filter (fun e => (ends e).1 ∈ T ∧ (ends e).2 ∈ T), (1 + v e)) =
      (∏ i ∈ T, incidentProduct ends E v i) *
        (∏ e ∈ E.filter (fun e => (ends e).1 ∉ T ∧ (ends e).2 ∉ T), (1 + v e)) := by
  rw [incidentProduct_subprod]
  simp only [prod_filter]
  rw [← prod_mul_distrib,← prod_mul_distrib]
  apply prod_congr rfl
  intro e he
  split_ifs <;> simp_all

omit [Fintype V] in
lemma percolationCoefficient_rescale (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e) (T : Finset V) :
    percolationCoefficient ends E s v T =
      (∏ i ∈ T, incidentScale ends E v i) * squarefreeMoment ends E s v T := by
  have hP : (∏ e ∈ E, (1 + v e)) ≠ 0 := ne_of_gt (prod_pos (fun e he => by linarith [hv e he]))
  have hD : (∏ i ∈ T, incidentProduct ends E v i) ≠ 0 :=
    ne_of_gt (prod_pos (fun i hi => incidentProduct_pos ends E v hv i))
  have hid := incident_product_identity ends E v T
  unfold percolationCoefficient squarefreeMoment incidentScale
  rw [prod_inv_distrib]
  simp only [Finset.mem_coe,filter_classical] at hid ⊢
  field_simp
  nlinarith [congrArg (fun r : ℝ => r * inducedPartition ends E s v T) hid]

lemma percolationSitePolynomial_rescale (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e) (x : V → ℝ) :
    percolationSitePolynomial ends E s v x =
      unscaledSitePolynomial ends E s v (fun i => incidentScale ends E v i * x i) := by
  rw [percolationSitePolynomial_eq]
  unfold unscaledSitePolynomial MultiaffineDerivative.polynomial
  apply sum_congr rfl
  intro T hT
  rw [percolationCoefficient_rescale ends E s v hv T,prod_mul_distrib]
  ring

end BelowOne.FKPressure
end
end

 
section

 
noncomputable section
open Finset
open scoped Classical
namespace BelowOne.MultiaffineDerivative
variable {V : Type*} [Fintype V]

def diagonalEquiv (c : V → ℝ) (hc : ∀ i, c i ≠ 0) : (V → ℝ) ≃L[ℝ] (V → ℝ) where
  toFun x i := c i * x i
  invFun x i := (c i)⁻¹ * x i
  left_inv x := by ext i; simp [hc i]
  right_inv x := by ext i; simp [hc i]
  map_add' x y := by ext i; exact mul_add _ _ _
  map_smul' a x := by ext i; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [Fintype V] in
lemma diagonalEquiv_coordinate (c : V → ℝ) (hc : ∀ i, c i ≠ 0) (i : V) :
    diagonalEquiv c hc (coordinate i) = c i • coordinate i := by
  ext j
  by_cases h : i = j
  · subst j; simp [diagonalEquiv,coordinate]
  · simp [diagonalEquiv,coordinate,h]

lemma iteratedFDeriv_diagonal (f : (V → ℝ) → ℝ) (c : V → ℝ)
    (hc : ∀ i, c i ≠ 0) (n : ℕ) (τ : Fin n → V) :
    iteratedFDeriv ℝ n (fun x => f (fun i => c i * x i)) 0 (coordinate ∘ τ) =
      (∏ j, c (τ j)) * iteratedFDeriv ℝ n f 0 (coordinate ∘ τ) := by
  have h := (diagonalEquiv c hc).iteratedFDerivWithin_comp_right f
    (s := Set.univ) uniqueDiffOn_univ (x := 0) (Set.mem_univ _) n
  simp only [Set.preimage_univ,iteratedFDerivWithin_univ,map_zero] at h
  change iteratedFDeriv ℝ n (f ∘ diagonalEquiv c hc) 0 (coordinate ∘ τ) = _
  rw [h,ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change iteratedFDeriv ℝ n f 0 (fun j => diagonalEquiv c hc (coordinate (τ j))) = _
  simp_rw [diagonalEquiv_coordinate]
  rw [ContinuousMultilinearMap.map_smul_univ]
  rfl

end BelowOne.MultiaffineDerivative
end
end

 
section

 

noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace BelowOne.FKPressure
variable {V I : Type*} [Fintype V]

lemma percolationSitePolynomial_zero (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e) :
    percolationSitePolynomial ends E s v 0 = 1 := by
  rw [percolationSitePolynomial_rescale ends E s v hv]
  simp only [Pi.zero_apply,mul_zero]
  exact unscaledSitePolynomial_zero ends E s v

lemma percolationSitePolynomial_log_derivative_nonpos {n : ℕ} (hn : 0 < n)
    (τ : Fin n → V) (ends : I → V × V) (E : Finset I)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e) :
    iteratedFDeriv ℝ n (Real.log ∘ percolationSitePolynomial ends E (-u) v) 0
      (MultiaffineDerivative.coordinate ∘ τ) ≤ 0 := by
  have heq : Real.log ∘ percolationSitePolynomial ends E (-u) v =
      fun x => (Real.log ∘ unscaledSitePolynomial ends E (-u) v)
        (fun i => incidentScale ends E v i * x i) := by
    funext x
    simp only [Function.comp_apply,percolationSitePolynomial_rescale ends E (-u) v hv]
  rw [heq,MultiaffineDerivative.iteratedFDeriv_diagonal]
  · apply mul_nonpos_of_nonneg_of_nonpos
    · exact prod_nonneg (fun i _ => (inv_pos.mpr (incidentProduct_pos ends E v hv (τ i))).le)
    · exact unscaledSitePolynomial_log_derivative_nonpos hn τ ends E hu hu1 v hv
  · intro i
    exact ne_of_gt (inv_pos.mpr (incidentProduct_pos ends E v hv i))

lemma componentProduct_pos (G : SimpleGraph V) {u : ℝ} (hu : 0 ≤ u)
    (hu1 : u < 1) (x : V → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 1) :
    0 < componentProduct G (-u) x := by
  unfold componentProduct
  apply prod_pos
  intro c hc
  have hb : (∏ i ∈ univ.filter (fun i => G.connectedComponentMk i = c), x i) ≤ 1 :=
    prod_le_one₀ (fun i _ => (hx i).1) (fun i _ => (hx i).2)
  nlinarith

lemma percolationSitePolynomial_pos (ends : I → V × V) (E : Finset I)
    {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e)
    (x : V → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 1) :
    0 < percolationSitePolynomial ends E (-u) v x := by
  unfold percolationSitePolynomial
  apply div_pos
  · apply sum_pos'
    · intro A hA
      exact mul_nonneg (prod_nonneg (fun e he => hv e ((mem_powerset.mp hA) he)))
        (componentProduct_pos _ hu hu1 x hx).le
    · refine ⟨∅,mem_powerset.mpr (empty_subset E),?_⟩
      simpa only [prod_empty,one_mul] using componentProduct_pos (graph ⊥ ends ∅) hu hu1 x hx
  · exact prod_pos (fun e he => by linarith [hv e he])

end BelowOne.FKPressure
end
end

 
section

 

noncomputable section
open Finset
open scoped Classical
namespace BelowOne.PositiveMultilinear
open MultiaffineDerivative
variable {V : Type*} [Fintype V] {n : ℕ}

lemma sum_coordinates (x : V → ℝ) : ∑ i, x i • coordinate i = x := by
  ext j
  simp [coordinate,Pi.single_apply]

lemma expansion (F : ContinuousMultilinearMap ℝ (fun _ : Fin n => V → ℝ) ℝ)
    (x : Fin n → V → ℝ) :
    F x = ∑ τ : Fin n → V, (∏ j, x j (τ j)) * F (coordinate ∘ τ) := by
  conv_lhs => rw [show x = fun j => ∑ i, x j i • coordinate i by simp only [sum_coordinates]]
  rw [F.map_sum]
  apply sum_congr rfl
  intro τ hτ
  rw [F.map_smul_univ]
  rfl

lemma nonneg (F : ContinuousMultilinearMap ℝ (fun _ : Fin n => V → ℝ) ℝ)
    (hF : ∀ τ : Fin n → V, 0 ≤ F (coordinate ∘ τ)) (x : Fin n → V → ℝ)
    (hx : ∀ j i, 0 ≤ x j i) : 0 ≤ F x := by
  rw [expansion]
  exact sum_nonneg (fun τ _ => mul_nonneg (prod_nonneg (fun j _ => hx j (τ j))) (hF τ))

lemma ones_eq_sum (F : ContinuousMultilinearMap ℝ (fun _ : Fin n => V → ℝ) ℝ) :
    F (fun _ _ => 1) = ∑ τ : Fin n → V, F (coordinate ∘ τ) := by
  rw [expansion]
  simp only [prod_const_one,one_mul]

lemma norm_le_ones (F : ContinuousMultilinearMap ℝ (fun _ : Fin n => V → ℝ) ℝ)
    (hF : ∀ τ : Fin n → V, 0 ≤ F (coordinate ∘ τ)) : ‖F‖ ≤ F (fun _ _ => 1) := by
  apply F.opNorm_le_bound (nonneg F hF _ (fun _ _ => zero_le_one))
  intro x
  rw [expansion,ones_eq_sum,sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro τ hτ
  rw [norm_mul,Real.norm_of_nonneg (hF τ),mul_comm]
  apply mul_le_mul_of_nonneg_left _ (hF τ)
  rw [norm_prod]
  apply prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => ?_)
  exact norm_le_pi_norm (x j) (τ j)

end BelowOne.PositiveMultilinear
end
end

 
section

 

noncomputable section
open scoped Topology NNReal ENNReal
open Filter Set FormalMultilinearSeries
namespace BelowOne.PositiveSeries

lemma scalar_apply_nonneg (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (n : ℕ) (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    0 ≤ ofScalars ℝ c n v := by
  simp only [ofScalars, _root_.smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, smul_eq_mul, List.prod_ofFn]
  exact mul_nonneg (hc n) (Finset.prod_nonneg (fun i _ => hv i))

 

lemma summable_add_of_shift (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxr : (‖x‖₊ : ℝ≥0∞) < (ofScalars ℝ c).radius)
    (hshift : Summable fun k => (ofScalars ℝ c).changeOrigin x k (fun _ => y)) :
    Summable fun n => ofScalars ℝ c n (fun _ => x+y) := by
  let p := ofScalars ℝ c
  let f : (Σ k l : ℕ, {s : Finset (Fin (k+l)) // s.card = l}) → ℝ :=
    fun s => p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ => x) (fun _ => y)
  have fnonneg : ∀ s, 0 ≤ f s := by
    intro s
    dsimp [f]
    rw [changeOriginSeriesTerm_apply]
    apply scalar_apply_nonneg c hc
    intro i
    dsimp only [Finset.piecewise]
    split_ifs <;> assumption
  have hinner (k : ℕ) : HasSum (fun s => f ⟨k,s⟩) (p.changeOrigin x k (fun _ => y)) := by
    apply ContinuousMultilinearMap.hasSum_eval
    have ht := (p.hasFPowerSeriesOnBall_changeOrigin k hxr.pos).hasSum
      (mem_eball_zero_iff.mpr hxr)
    rw [zero_add] at ht
    refine HasSum.sigma_of_hasSum ht (fun l => ?_) ?_
    · simp only [changeOriginSeries, sum_apply]
      exact hasSum_fintype _
    · refine .of_nnnorm_bounded (p.changeOriginSeries_summable_aux₂ hxr k) ?_
      intro s
      refine (ContinuousMultilinearMap.le_opNNNorm _ _).trans_eq ?_
      simp
  have hsf : Summable f := (summable_sigma_of_nonneg fnonneg).mpr
    ⟨fun k => (hinner k).summable, by simpa only [(hinner _).tsum_eq] using hshift⟩
  have hs := (changeOriginIndexEquiv.symm.summable_iff.mpr hsf).sigma
  apply hs.congr
  intro n
  change (∑' s : Finset (Fin n), f (changeOriginIndexEquiv.symm ⟨n,s⟩)) =
    p n (fun _ => x+y)
  rw [tsum_fintype, ← Pi.add_def, (p n).map_add_univ (fun _ => x) (fun _ => y)]
  simp_rw [← changeOriginSeriesTerm_changeOriginIndexEquiv_symm]
  rfl

lemma radius_add_le (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (x y : ℝ≥0) (hx : (x : ℝ≥0∞) < (ofScalars ℝ c).radius)
    (hy : (y : ℝ≥0∞) < ((ofScalars ℝ c).changeOrigin (x : ℝ)).radius) :
    ((x+y : ℝ≥0) : ℝ≥0∞) ≤ (ofScalars ℝ c).radius := by
  have hs := summable_add_of_shift c hc x.coe_nonneg y.coe_nonneg
    (by simpa using hx) (((ofScalars ℝ c).changeOrigin (x : ℝ)).summable
      (by simpa only [mem_eball_zero_iff, enorm_eq_nnnorm, NNReal.nnnorm_eq] using hy))
  apply (ofScalars ℝ c).le_radius_of_summable (r := x+y)
  simpa only [ofScalars_norm, Real.norm_eq_abs, abs_of_nonneg (hc _),
    NNReal.coe_add, ofScalars_apply_eq, smul_eq_mul] using hs

 

theorem not_analytic_at_radius (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (R : ℝ≥0) (hR : 0 < R) (hr : (ofScalars ℝ c).radius = R)
    (f : ℝ → ℝ) (heq : EqOn f (ofScalars ℝ c).sum (Ioo 0 (R : ℝ))) :
    ¬ AnalyticAt ℝ f (R : ℝ) := by
  intro ha
  obtain ⟨q,r,hq⟩ := ha
  obtain ⟨e,he0,he⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp
    (show (0 : ℝ≥0∞) < min (R : ℝ≥0∞) r from lt_min (by exact_mod_cast hR) hq.r_pos)
  have hepos : 0 < e := by exact_mod_cast he0
  have heR : e < R := by exact_mod_cast (lt_min_iff.mp he).1
  have her : (e : ℝ≥0∞) < r := (lt_min_iff.mp he).2
  let d : ℝ≥0 := e/4
  have hdpos : 0 < d := div_pos hepos (by norm_num)
  have hdR : d < R := by dsimp [d]; linarith
  have hde : 3*d < e := by dsimp [d]; linarith
  have hd_le_e : d ≤ e := by dsimp [d]; linarith
  let x : ℝ≥0 := R-d
  have hdx : x+d=R := tsub_add_cancel_of_le hdR.le
  have hxpos : 0 < x := tsub_pos_iff_lt.mpr hdR
  have hxR : x < R := by linarith
  have hxr : (x : ℝ≥0∞) < (ofScalars ℝ c).radius := by rw [hr]; exact_mod_cast hxR
  have hdr : (‖-(d : ℝ)‖₊ : ℝ≥0∞) < r := by
    simpa using (show (d : ℝ≥0∞) < r from (show (d : ℝ≥0∞) ≤ (e : ℝ≥0∞) by exact_mod_cast hd_le_e).trans_lt her)
  have hsright := hq.changeOrigin hdr
  have hcenter : (R : ℝ) + -(d : ℝ) = (x : ℝ) := by
    have hh : (x : ℝ)+(d : ℝ)=(R : ℝ) := by exact_mod_cast hdx
    linarith
  rw [hcenter] at hsright
  have hsleft := ((ofScalars ℝ c).hasFPowerSeriesOnBall hxr.pos).changeOrigin
    (show (‖(x : ℝ)‖₊ : ℝ≥0∞) < (ofScalars ℝ c).radius by simpa using hxr)
  rw [zero_add] at hsleft
  have hloc : (ofScalars ℝ c).sum =ᶠ[𝓝 (x : ℝ)] f := by
    filter_upwards [Ioo_mem_nhds (by exact_mod_cast hxpos) (by exact_mod_cast hxR)] with z hz
    exact (heq hz).symm
  have hseries := (hsleft.hasFPowerSeriesAt.congr hloc).eq_formalMultilinearSeries
    hsright.hasFPowerSeriesAt
  have hy : ((2*d : ℝ≥0) : ℝ≥0∞) < ((ofScalars ℝ c).changeOrigin (x : ℝ)).radius := by
    rw [hseries]
    apply lt_of_lt_of_le _ hsright.r_le
    simp only [nnnorm_neg, NNReal.nnnorm_eq]
    rw [lt_tsub_iff_right]
    calc
      ((2*d : ℝ≥0) : ℝ≥0∞) + (d : ℝ≥0∞) = ((3*d : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
      _ < (e : ℝ≥0∞) := by exact_mod_cast hde
      _ < r := her
  have hh := radius_add_le c hc x (2*d) hxr hy
  rw [hr] at hh
  have hcast : x+2*d ≤ R := by exact_mod_cast hh
  linarith

 

theorem radius_gt_of_analytic_interval (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (B : ℝ≥0) (f : ℝ → ℝ)
    (hp : HasFPowerSeriesAt f (ofScalars ℝ c) 0)
    (hf : AnalyticOnNhd ℝ f (Icc 0 (B : ℝ))) :
    (B : ℝ≥0∞) < (ofScalars ℝ c).radius := by
  by_contra hb
  have hle : (ofScalars ℝ c).radius ≤ B := le_of_not_gt hb
  have hfin : (ofScalars ℝ c).radius ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  let R := (ofScalars ℝ c).radius.toNNReal
  have hr : (ofScalars ℝ c).radius = (R : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin).symm
  have hR : 0 < R := by
    have hh := hp.radius_pos
    rw [hr] at hh
    exact_mod_cast hh
  have hRB : R ≤ B := by rw [hr] at hle; exact_mod_cast hle
  have hloc : f =ᶠ[𝓝 0] (ofScalars ℝ c).sum := by
    filter_upwards [hp.eventually_hasSum] with z hz
    simpa only [zero_add, FormalMultilinearSeries.sum] using hz.tsum_eq.symm
  have hfs : AnalyticOnNhd ℝ f (Ico 0 (R : ℝ)) :=
    hf.mono (fun z hz => ⟨hz.1, hz.2.le.trans (by exact_mod_cast hRB)⟩)
  have hps : AnalyticOnNhd ℝ (ofScalars ℝ c).sum (Ico 0 (R : ℝ)) := by
    apply (ofScalars ℝ c).analyticOnNhd.mono
    intro z hz
    rw [mem_eball_zero_iff, hr, enorm_eq_nnnorm, ENNReal.coe_lt_coe]
    exact_mod_cast (show ‖z‖ < (R : ℝ) by simpa [Real.norm_eq_abs, abs_of_nonneg hz.1] using hz.2)
  have heq := hfs.eqOn_of_preconnected_of_eventuallyEq hps isPreconnected_Ico
    (show (0 : ℝ) ∈ Ico 0 (R : ℝ) from ⟨le_rfl, by exact_mod_cast hR⟩) hloc
  exact not_analytic_at_radius c hc R hR hr f
    (heq.mono Ioo_subset_Ico_self) (hf R ⟨R.coe_nonneg, by exact_mod_cast hRB⟩)

end BelowOne.PositiveSeries
end
end

 
section

 

noncomputable section
open Finset Filter Set FormalMultilinearSeries
open scoped Topology NNReal ENNReal Classical
namespace BelowOne.PositiveAnalyticCube
open MultiaffineDerivative
variable {V : Type*} [Fintype V]

def cube : Set (V → ℝ) := {x | ∀ i, x i ∈ Set.Icc 0 1}
def diagonal : ℝ →L[ℝ] (V → ℝ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ

def taylor (f : (V → ℝ) → ℝ) : FormalMultilinearSeries ℝ (V → ℝ) ℝ :=
  fun n => (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n f 0

def diagonalCoefficient (f : (V → ℝ) → ℝ) (n : ℕ) : ℝ :=
  taylor f n (fun _ _ => 1)

lemma taylor_diagonal_eq {f : (V → ℝ) → ℝ} {p : FormalMultilinearSeries ℝ (V → ℝ) ℝ}
    {r : ℝ≥0∞} (hp : HasFPowerSeriesOnBall f p 0 r) (x : V → ℝ) (n : ℕ) :
    taylor f n (fun _ => x) = p n (fun _ => x) := by
  have h := hp.factorial_smul x n
  simp only [nsmul_eq_mul] at h
  rw [taylor,_root_.smul_apply,smul_eq_mul,←h]
  rw [←mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero),one_mul]

lemma diagonal_hasFPowerSeriesAt {f : (V → ℝ) → ℝ} (hf : AnalyticAt ℝ f 0) :
    HasFPowerSeriesAt (f ∘ diagonal) (ofScalars ℝ (diagonalCoefficient f)) 0 := by
  obtain ⟨p,r,hp⟩ := hf
  have hs : HasFPowerSeriesAt (f ∘ diagonal) (p.compContinuousLinearMap diagonal) 0 :=
    (show HasFPowerSeriesAt f p (diagonal (V := V) 0) by simpa using hp.hasFPowerSeriesAt).compContinuousLinearMap
  convert hs using 1
  ext n
  rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    coeff_ofScalars]
  congr 1
  rw [diagonalCoefficient,taylor_diagonal_eq hp]
  rfl

lemma taylor_coordinate_nonneg (f : (V → ℝ) → ℝ) (hf0 : 0 ≤ f 0)
    (hf : ∀ n, 0 < n → ∀ τ : Fin n → V,
      0 ≤ iteratedFDeriv ℝ n f 0 (coordinate ∘ τ)) (n : ℕ) (τ : Fin n → V) :
    0 ≤ taylor f n (coordinate ∘ τ) := by
  rw [taylor,_root_.smul_apply,smul_eq_mul]
  apply mul_nonneg (by positivity)
  by_cases hn : n = 0
  · subst n
    simpa only [iteratedFDeriv_zero_apply] using hf0
  · exact hf n (Nat.pos_of_ne_zero hn) τ

lemma diagonalCoefficient_nonneg (f : (V → ℝ) → ℝ) (hf0 : 0 ≤ f 0)
    (hf : ∀ n, 0 < n → ∀ τ : Fin n → V,
      0 ≤ iteratedFDeriv ℝ n f 0 (coordinate ∘ τ)) (n : ℕ) :
    0 ≤ diagonalCoefficient f n :=
  PositiveMultilinear.nonneg _ (taylor_coordinate_nonneg f hf0 hf n) _ (fun _ _ => zero_le_one)

lemma radius_le_of_norm_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : FormalMultilinearSeries ℝ E ℝ) (q : FormalMultilinearSeries ℝ F ℝ)
    (h : ∀ n, ‖q n‖ ≤ ‖p n‖) : p.radius ≤ q.radius := by
  unfold FormalMultilinearSeries.radius
  apply iSup_le
  intro r
  apply iSup_le
  intro C
  apply iSup_le
  intro hC
  apply q.le_radius_of_bound C
  intro n
  exact (mul_le_mul_of_nonneg_right (h n) (by positivity)).trans (hC n)

lemma taylor_radius_gt_one (f : (V → ℝ) → ℝ) (hf0 : 0 ≤ f 0)
    (hf : ∀ n, 0 < n → ∀ τ : Fin n → V,
      0 ≤ iteratedFDeriv ℝ n f 0 (coordinate ∘ τ))
    (ha : AnalyticOnNhd ℝ f cube) : 1 < (taylor f).radius := by
  have ha0 : AnalyticAt ℝ f 0 := ha 0 (fun i => by simp)
  have hd : AnalyticOnNhd ℝ (f ∘ diagonal) (Set.Icc (0:ℝ) 1) := by
    intro x hx
    exact (ha (diagonal x) (fun _ => hx)).compContinuousLinearMap
  have hR := PositiveSeries.radius_gt_of_analytic_interval (diagonalCoefficient f)
    (diagonalCoefficient_nonneg f hf0 hf) 1 (f ∘ diagonal) (diagonal_hasFPowerSeriesAt ha0) hd
  apply hR.trans_le
  apply radius_le_of_norm_le
  intro n
  rw [ofScalars_norm,Real.norm_of_nonneg (diagonalCoefficient_nonneg f hf0 hf n)]
  exact PositiveMultilinear.norm_le_ones _ (taylor_coordinate_nonneg f hf0 hf n)

lemma hasFPowerSeriesAt_taylor {f : (V → ℝ) → ℝ} (hf : AnalyticAt ℝ f 0)
    (hR : 0 < (taylor f).radius) : HasFPowerSeriesAt f (taylor f) 0 := by
  obtain ⟨p,r,hp⟩ := hf
  refine ⟨min r (taylor f).radius, ?_⟩
  refine ⟨min_le_right _ _,lt_min hp.r_pos hR,?_⟩
  intro x hx
  have hx' : x ∈ Metric.eball 0 r := by
    exact mem_eball_zero_iff.mpr ((mem_eball_zero_iff.mp hx).trans_le (min_le_left _ _))
  simpa only [taylor,_root_.smul_apply] using hp.hasSum_iteratedFDeriv hx'

omit [Fintype V] in
lemma cube_convex : Convex ℝ (cube (V := V)) := by
  have hc : cube (V := V) = Set.pi Set.univ (fun _ : V => Set.Icc (0:ℝ) 1) := by
    ext x
    change (∀ i, x i ∈ Set.Icc 0 1) ↔ ∀ i ∈ Set.univ, x i ∈ Set.Icc 0 1
    simp only [Set.mem_univ, forall_true_left]
  rw [hc]
  exact convex_pi (fun _ _ => convex_Icc 0 1)

lemma cube_subset_eball {r : ℝ≥0∞} (hr : 1 < r) : cube (V := V) ⊆ Metric.eball 0 r := by
  intro x hx
  have hn : ‖x‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    exact (Real.norm_of_nonneg (hx i).1).trans_le (hx i).2
  apply mem_eball_zero_iff.mpr
  exact (show ‖x‖ₑ ≤ (1:ℝ≥0∞) by
    rw [enorm_eq_nnnorm,← ENNReal.coe_one,ENNReal.coe_le_coe]
    exact_mod_cast hn).trans_lt hr

lemma taylor_sum_eq_on_cube (f : (V → ℝ) → ℝ) (hf0 : 0 ≤ f 0)
    (hf : ∀ n, 0 < n → ∀ τ : Fin n → V,
      0 ≤ iteratedFDeriv ℝ n f 0 (coordinate ∘ τ))
    (ha : AnalyticOnNhd ℝ f cube) : Set.EqOn f (taylor f).sum cube := by
  have hR := taylor_radius_gt_one f hf0 hf ha
  have hp := hasFPowerSeriesAt_taylor (ha 0 (fun i => by simp)) (zero_lt_one.trans hR)
  have heq : f =ᶠ[𝓝 0] (taylor f).sum := by
    filter_upwards [hp.eventually_hasSum] with x hx
    simpa only [zero_add,FormalMultilinearSeries.sum] using hx.tsum_eq.symm
  exact ha.eqOn_of_preconnected_of_eventuallyEq
    ((taylor f).analyticOnNhd.mono (cube_subset_eball hR)) cube_convex.isPreconnected
      (fun i => by simp) heq

end BelowOne.PositiveAnalyticCube
end
end

 
section

 

noncomputable section
open Finset Filter Set FormalMultilinearSeries
open scoped Topology NNReal ENNReal Classical
namespace BelowOne.FKPressure
variable {V I : Type*} [Fintype V]

def pressure (ends : I → V × V) (E : Finset I) (u : ℝ) (v : I → ℝ)
    (x : V → ℝ) : ℝ := -Real.log (percolationSitePolynomial ends E (-u) v x)

lemma analyticAt_percolationSitePolynomial (ends : I → V × V) (E : Finset I)
    (s : ℝ) (v : I → ℝ) (x : V → ℝ) :
    AnalyticAt ℝ (percolationSitePolynomial ends E s v) x := by
  rw [percolationSitePolynomial_eq]
  unfold MultiaffineDerivative.polynomial
  apply Finset.analyticAt_fun_sum
  intro T hT
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i hi
  exact (ContinuousLinearMap.proj i : (V → ℝ) →L[ℝ] ℝ).analyticAt x

lemma pressure_zero (ends : I → V × V) (E : Finset I)
    (u : ℝ) (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e) : pressure ends E u v 0 = 0 := by
  simp only [pressure,percolationSitePolynomial_zero ends E (-u) v hv,Real.log_one,neg_zero]

lemma pressure_derivative_nonneg (ends : I → V × V) (E : Finset I)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e)
    (n : ℕ) (hn : 0 < n) (τ : Fin n → V) :
    0 ≤ iteratedFDeriv ℝ n (pressure ends E u v) 0
      (MultiaffineDerivative.coordinate ∘ τ) := by
  change 0 ≤ iteratedFDeriv ℝ n (-(fun x => Real.log (percolationSitePolynomial ends E (-u) v x))) 0
    (MultiaffineDerivative.coordinate ∘ τ)
  rw [iteratedFDeriv_neg_apply,_root_.neg_apply]
  exact neg_nonneg.mpr (percolationSitePolynomial_log_derivative_nonpos hn τ ends E hu hu1 v hv)

lemma pressure_analyticOn_cube (ends : I → V × V) (E : Finset I)
    {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e) :
    AnalyticOnNhd ℝ (pressure ends E u v) PositiveAnalyticCube.cube := by
  intro x hx
  exact ((analyticAt_log (percolationSitePolynomial_pos ends E hu hu1 v hv x hx)).comp
    (analyticAt_percolationSitePolynomial ends E (-u) v x)).neg

theorem pressure_expansion (ends : I → V × V) (E : Finset I)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) (v : I → ℝ) (hv : ∀ e ∈ E, 0 ≤ v e) :
    let p := PositiveAnalyticCube.taylor (pressure ends E u v)
    1 < p.radius ∧
    (∀ n (τ : Fin n → V), 0 ≤ p n (MultiaffineDerivative.coordinate ∘ τ)) ∧
    (∀ x ∈ PositiveAnalyticCube.cube, HasSum (fun n => p n (fun _ => x)) (pressure ends E u v x)) := by
  dsimp only
  have hf0 : 0 ≤ pressure ends E u v 0 := (pressure_zero ends E u v hv).ge
  have hf := pressure_derivative_nonneg ends E hu hu1 v hv
  have ha := pressure_analyticOn_cube ends E hu.le hu1 v hv
  have hR := PositiveAnalyticCube.taylor_radius_gt_one _ hf0 hf ha
  refine ⟨hR,PositiveAnalyticCube.taylor_coordinate_nonneg _ hf0 hf,?_⟩
  intro x hx
  rw [PositiveAnalyticCube.taylor_sum_eq_on_cube _ hf0 hf ha hx]
  exact (PositiveAnalyticCube.taylor (pressure ends E u v)).summable
    (PositiveAnalyticCube.cube_subset_eball hR hx) |>.hasSum

end BelowOne.FKPressure
end
end

end OAI
