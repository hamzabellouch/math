import Mathlib

namespace OAI

/-! # Quasi-isometric recognition and uniform bounded height

A polycyclic group has a finite subnormal series with cyclic factors. The
height quotient below is the quotient of the Lie algebra by the common
kernel of the diagonal adjoint characters.
-/

noncomputable section

namespace ChromaticCyclic

structure CyclicStep {G : Type*} [Group G] (H K : Subgroup G) : Prop where
  le : H ≤ K
  normal : (H.subgroupOf K).Normal
  cyclic : letI := normal; IsCyclic (K ⧸ H.subgroupOf K)

structure CyclicSeries {G : Type*} [Group G] (H K : Subgroup G) (n : ℕ) where
  group : ℕ → Subgroup G
  first : group 0 = H
  last : group n = K
  step : ∀ i < n, CyclicStep (group i) (group (i + 1))

end ChromaticCyclic

namespace PolycyclicRecognition

open Module LieAlgebra MeasureTheory
open scoped Manifold NNReal

section Coarse

variable {G H J : Type*} [Group G] [Group H] [Group J]

/-- Uniform control of finite sets of group differences. -/
def GroupBornologous (f : G → H) : Prop :=
  ∀ S : Set G, S.Finite → ∃ T : Set H, T.Finite ∧
    ∀ x y, x⁻¹ * y ∈ S → (f x)⁻¹ * f y ∈ T

/-- Coarse inverse maps with errors contained in fixed finite sets. -/
structure GroupCoarseEquivalence (G H : Type*) [Group G] [Group H] where
  toFun : G → H
  invFun : H → G
  bornologous_toFun : GroupBornologous toFun
  bornologous_invFun : GroupBornologous invFun
  left_error : (Set.range fun x => x⁻¹ * invFun (toFun x)).Finite
  right_error : (Set.range fun y => y⁻¹ * toFun (invFun y)).Finite

end Coarse

section Polycyclic

open ChromaticCyclic

variable (G : Type*) [Group G]

/-- Polycyclicity expressed by an actual cyclic subnormal series. -/
def IsPolycyclic : Prop :=
  ∃ n : ℕ, Nonempty (CyclicSeries (⊥ : Subgroup G) ⊤ n)

/-- Virtual polycyclicity means a polycyclic subgroup of finite index. -/
def IsVirtuallyPolycyclic : Prop :=
  ∃ H : Subgroup G, H.FiniteIndex ∧ IsPolycyclic H

end Polycyclic

section UniformLattice

variable {G : Type*} [Group G]

/-- A uniform lattice is discrete and has a compact fundamental cover. -/
def IsUniformLattice [TopologicalSpace G] (Λ : Subgroup G) : Prop :=
  DiscreteTopology Λ ∧ ∃ K : Set G, IsCompact K ∧
    ∀ g : G, ∃ (γ : Λ) (k : G), k ∈ K ∧ (γ : G) * k = g

end UniformLattice

/-- A connected simply connected finite-dimensional real solvable Lie group. -/
structure SimplyConnectedSolvableLieModel where
  modelSpace : Type
  [normedAddCommGroup : NormedAddCommGroup modelSpace]
  [normedSpace : NormedSpace ℝ modelSpace]
  [finiteDimensional : FiniteDimensional ℝ modelSpace]
  carrier : Type
  [topologicalSpace : TopologicalSpace carrier]
  [chartedSpace : ChartedSpace modelSpace carrier]
  [group : Group carrier]
  [lieGroup : LieGroup (𝓘(ℝ, modelSpace)) ⊤ carrier]
  [t2Space : T2Space carrier]
  [secondCountableTopology : SecondCountableTopology carrier]
  [simplyConnectedSpace : SimplyConnectedSpace carrier]
  [solvable : Group.IsSolvable carrier]

attribute [instance] SimplyConnectedSolvableLieModel.normedAddCommGroup
  SimplyConnectedSolvableLieModel.normedSpace SimplyConnectedSolvableLieModel.finiteDimensional
  SimplyConnectedSolvableLieModel.topologicalSpace SimplyConnectedSolvableLieModel.chartedSpace
  SimplyConnectedSolvableLieModel.group SimplyConnectedSolvableLieModel.lieGroup
  SimplyConnectedSolvableLieModel.t2Space SimplyConnectedSolvableLieModel.simplyConnectedSpace
  SimplyConnectedSolvableLieModel.secondCountableTopology
  SimplyConnectedSolvableLieModel.solvable

/-- A discrete subgroup with a normalized invariant measure on its coset space. -/
def IsFiniteCovolumeLattice {G : Type} [Group G] [TopologicalSpace G]
    (Λ : Subgroup G) : Prop :=
  letI : MeasurableSpace (G ⧸ Λ) := borel _
  DiscreteTopology Λ ∧ ∃ μ : Measure (G ⧸ Λ),
    IsProbabilityMeasure μ ∧ SMulInvariantMeasure G (G ⧸ Λ) μ

/-- Explicit chains with bounded steps and a linear bound on their length. -/
structure LinearMetricChains (X : Type*) [PseudoMetricSpace X] where
  step : ℝ
  step_pos : 0 < step
  slope : ℝ
  slope_nonneg : 0 ≤ slope
  error : ℝ
  error_nonneg : 0 ≤ error
  chain : ∀ x y : X, ∃ (n : ℕ) (p : ℕ → X),
    p 0 = x ∧ p n = y ∧ (n : ℝ) ≤ slope * dist x y + error ∧
      ∀ i < n, dist (p i) (p (i + 1)) ≤ step

/-- A compatible proper left-invariant metric with large-scale-geodesic chains. -/
structure ProperChainMetric (G : Type*) [Group G] [TopologicalSpace G] where
  metric : MetricSpace G
  topology_eq : metric.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace G›
  proper : letI := metric; ProperSpace G
  leftInvariant : letI := metric; IsIsometricSMul G G
  chains : letI := metric; LinearMetricChains G

/-- The compatible metric retains the original topology definitionally. -/
abbrev ProperChainMetric.compatibleMetric
    {G : Type*} [Group G] [TopologicalSpace G] (d : ProperChainMetric G) : MetricSpace G :=
  d.metric.replaceTopology d.topology_eq.symm

section Height

variable {L I : Type*} [AddCommGroup L] [Module ℝ L]

/-- The common kernel, including the empty family of characters. -/
def heightKernel (χ : I → L →ₗ[ℝ] ℝ) : Submodule ℝ L := ⨅ i, (χ i).ker

/-- The canonical linear height quotient. -/
abbrev HeightSpace (χ : I → L →ₗ[ℝ] ℝ) := L ⧸ heightKernel χ

/-- The quotient map defining infinitesimal height. -/
def heightProjection (χ : I → L →ₗ[ℝ] ℝ) : L →ₗ[ℝ] HeightSpace χ :=
  (heightKernel χ).mkQ

end Height

/-- A simultaneous real upper triangular basis for the adjoint representation. -/
structure TriangularAdjoint (L : Type*) [LieRing L] [LieAlgebra ℝ L] (n : ℕ) where
  basis : Basis (Fin n) ℝ L
  upper : ∀ x : L, (LinearMap.toMatrix basis basis (LieAlgebra.ad ℝ L x)).IsUpperTriangular

namespace TriangularAdjoint

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
variable (T : TriangularAdjoint L n)

/-- The diagonal entries of the adjoint representation. -/
noncomputable def character (i : Fin n) : L →ₗ[ℝ] ℝ where
  toFun x := T.basis.repr ⁅x, T.basis i⁆ i
  map_add' x y := by simp [add_lie]
  map_smul' r x := (by simp [smul_lie] : _ = r * T.basis.repr ⁅x, T.basis i⁆ i)

end TriangularAdjoint

section Exponential

attribute [local instance 10000] NormedField.toNormedSpace

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

/-- The exponential is characterized by its one-parameter subgroups and
by their tangent vectors at the identity. -/
structure IsGroupExponential (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) : Prop where
  map_zero : Exp 0 = 1
  map_add_smul : ∀ (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (s t : ℝ),
    Exp ((s + t) • v) = Exp (s • v) * Exp (t • v)
  hasMFDerivAt_zero : ∀ v : GroupLieAlgebra (𝓘(ℝ, E)) G,
    HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t : ℝ => Exp (t • v)) 0
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v)

end Exponential

/-- Unimodularity for the canonical Borel Haar measure of the Lie group. -/
def ModelIsUnimodular (R : SimplyConnectedSolvableLieModel) : Prop :=
  letI : IsTopologicalGroup R.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, R.modelSpace)) ⊤
  letI : LocallyCompactSpace R.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, R.modelSpace))
  letI : MeasurableSpace R.carrier := borel _
  letI : BorelSpace R.carrier := ⟨rfl⟩
  (Measure.haar : Measure R.carrier).IsMulRightInvariant

/-- The upper, lower, and coarse-surjectivity bounds of a self quasi-isometry. -/
structure SelfQuasiIsometry (G : Type*) [PseudoMetricSpace G] (K C : ℝ) where
  toFun : G → G
  upper : ∀ x y, dist (toFun x) (toFun y) ≤ K * dist x y + C
  lower : ∀ x y, dist x y ≤ K * dist (toFun x) (toFun y) + K * C
  surjective : ∀ y, ∃ x, dist y (toFun x) ≤ C

/-- Quasi-isometric recognition, including the finite-index uniform-lattice realization. -/
theorem group_recognition
    {P J : Type} [Group P] [Group J] [Group.FG P] [Group.FG J]
    (e : GroupCoarseEquivalence P J) (hP : IsVirtuallyPolycyclic P) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  sorry

/-- One finite slope group controls the height of every self quasi-isometry. -/
theorem main_uniform_bounded_height
    (R : SimplyConnectedSolvableLieModel) (d : ProperChainMetric R.carrier)
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) a)
    (huni : ModelIsUnimodular R)
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier → R.carrier)
    (hExp : IsGroupExponential Exp) (π : R.carrier →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) :
    letI := d.compatibleMetric
    ∃ A : Subgroup (W ≃ₗ[ℝ] W), Set.Finite (A : Set (W ≃ₗ[ℝ] W)) ∧
      ∀ K C : ℝ, 1 ≤ K → 0 ≤ C → ∃ B : ℝ, 0 ≤ B ∧
        ∀ F : SelfQuasiIsometry R.carrier K C, ∃ AF : A, ∀ g,
          ‖(π (F.toFun g)).toAdd - ((π (F.toFun 1)).toAdd + AF.val (π g).toAdd)‖ ≤ B := by
  sorry

/-- Finite-covolume lattice recognition, allowing a different ambient Lie group. -/
theorem lattice_recognition
    (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier)
    (hΛ : IsFiniteCovolumeLattice Λ)
    {J : Type} [Group J] [Group.FG J] (e : GroupCoarseEquivalence Λ J) :
    ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
      ∃ (R : SimplyConnectedSolvableLieModel) (Δ : Subgroup R.carrier),
        IsUniformLattice Δ ∧ Nonempty (Γ ≃* Δ) := by
  sorry

end PolycyclicRecognition

end

end OAI
