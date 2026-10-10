import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.SparseClusters
import OAI.Probability.LatticeSurface.Convexity.ProductData
import OAI.Probability.LatticeSurface.Convexity.ProductGraph
import OAI.Probability.LatticeSurface.Convexity.ProductVolume
import OAI.Probability.LatticeSurface.Dynamics.ClusterShift
import OAI.Probability.LatticeSurface.Dynamics.JacobianIdentity
import OAI.Probability.LatticeSurface.Dynamics.LogDet
import OAI.Probability.LatticeSurface.Dynamics.MatrixJacobi
import OAI.Probability.LatticeSurface.Dynamics.ShiftAnalysis
import OAI.Probability.LatticeSurface.Dynamics.ShiftAssembly
import OAI.Probability.LatticeSurface.Dynamics.ShiftAsymptotics
import OAI.Probability.LatticeSurface.Dynamics.ShiftData
import OAI.Probability.LatticeSurface.Dynamics.ShiftProduct
import OAI.Probability.LatticeSurface.Geometry.TriangularCover

namespace OAI

section

open Set MeasureTheory intervalIntegral

namespace FeasibleShift

variable {V : Type*} [Fintype V] [DecidableEq V]

end FeasibleShift

open Matrix Polynomial

open scoped Topology

namespace TangentialJacobian

variable {V : Type*} [Fintype V] [DecidableEq V]

open MeasureTheory

end TangentialJacobian

open Set MeasureTheory Filter

open scoped Topology

namespace TangentialJacobian

variable {V : Type*} [Fintype V] [DecidableEq V]

end TangentialJacobian

namespace TangentialJacobian

open Matrix

open scoped Topology

variable {V : Type*} [Fintype V] [DecidableEq V]

end TangentialJacobian

namespace TangentialJacobian

variable {V : Type*} [Fintype V] [DecidableEq V]

end TangentialJacobian

namespace FeasibleShift

open TangentialJacobian

variable {V : Type*} [Fintype V] [DecidableEq V]

end FeasibleShift

namespace FeasibleShift

open TangentialJacobian

variable {V : Type*} [Fintype V] [DecidableEq V]

end FeasibleShift

namespace TangentialJacobian

variable {V : Type*} [Fintype V] [DecidableEq V]

end TangentialJacobian

namespace TangentialJacobian

variable {V : Type*} [Fintype V] [DecidableEq V]

end TangentialJacobian

end

section

open Set MeasureTheory

namespace SparseClusters

variable {V : Type*} [Fintype V] [DecidableEq V]

end SparseClusters

namespace SparseClusters

variable {V : Type*} [Fintype V] [DecidableEq V]

end SparseClusters

namespace SparseClusters

end SparseClusters

namespace SparseClusters

end SparseClusters

namespace SparseClusters

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

end SparseClusters

end

universe u v

open Set MeasureTheory

namespace FeasibleShift

variable {V : Type u} [Fintype V] [DecidableEq V]

namespace ShiftData

variable {W : Type v} [Fintype W] [DecidableEq W]

variable {n D Db B : ℕ} {ρ : ENNReal} {sstar L M N : ℝ}

variable (S : ShiftData (V := V) W n D Db B ρ sstar L M N)

end ShiftData

end FeasibleShift

namespace FeasibleShift.ShiftData

open SparseClusters

variable {V : Type u} [Fintype V] [DecidableEq V]

variable {W : Type v} [Fintype W] [DecidableEq W]

variable {n D Db B : ℕ} {ρ : ENNReal} {sstar L M N : ℝ}

variable (S : ShiftData (V := V) W n D Db B ρ sstar L M N)

open TangentialJacobian

end FeasibleShift.ShiftData

open Filter

namespace FeasibleShift

end FeasibleShift

namespace FeasibleShift

open Filter

end FeasibleShift

section

namespace FeasibleShift

namespace DisjointUnion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {V : ι → Type u} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

end DisjointUnion

end FeasibleShift

section

open Set MeasureTheory

namespace ProductVolume

variable {ι : Type u} [Fintype ι] {J : ι → Type v} [∀ i, Fintype (J i)]

end ProductVolume

end

namespace FeasibleShift.DisjointUnion

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {V : ι → Type u} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

variable {W : ι → Type v} [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)]

variable {n D Db B : ℕ} {ρ : ENNReal} {sstar L M N : ℝ}

variable (S : ∀ i, ShiftData (V := V i) (W i) n D Db B ρ sstar L M N)

end FeasibleShift.DisjointUnion

end

namespace FeasibleShift

open Filter

end FeasibleShift

open Set MeasureTheory

noncomputable section

namespace TriangularLipschitz

variable {V : Type*} [Fintype V] [DecidableEq V]

end TriangularLipschitz

namespace FeasibleShift

open Set MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma localSites_card_bound (G : SimpleGraph V) (ground active : Finset V)
    (hactive : ∀ x, x ∉ ground → x ∈ active) (D : ℕ)
    (hD : ∀ x, (neighbors G x).card ≤ D) :
    (localSites G ground).card ≤ (D+1)*active.card := by
  classical
  have hs : localSites G ground ⊆ active ∪ active.biUnion (neighbors G) := by
    intro x hx
    rcases (Finset.mem_filter.mp hx).2 with hx | ⟨y, hy, hxy⟩
    · exact Finset.mem_union_left _ (hactive x hx)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨y,hactive y hy,by simp [neighbors, hxy.symm]⟩)
  calc
    (localSites G ground).card ≤ (active ∪ active.biUnion (neighbors G)).card := Finset.card_le_card hs
    _ ≤ active.card + (active.biUnion (neighbors G)).card := Finset.card_union_le _ _
    _ ≤ active.card + ∑ x ∈ active, (neighbors G x).card :=
      Nat.add_le_add_left (Finset.card_biUnion_le) _
    _ ≤ active.card + ∑ x ∈ active, D :=
      Nat.add_le_add_left (Finset.sum_le_sum fun x _ => hD x) _
    _ = (D+1)*active.card := by simp; ring

structure LatticeData (n ℓ : ℕ) (ρ : ENNReal) (sstar L M C : ℝ) where
  location : V ↪ TriangularLipschitz.Vertex
  graph : SimpleGraph V
  lattice_edges : ∀ x y, graph.Adj x y → TriangularLipschitz.Adj (location x) (location y)
  ground : Finset V
  active : Finset V
  active_contains : ∀ x, x ∉ ground → x ∈ active
  active_count : (active.card : ℝ) ≤ C * (n:ℝ)^2
  pins : Finset V
  walls : Finset V
  pins_ground : pins ⊆ ground
  walls_ground : walls ⊆ ground
  boundary : V → ℝ
  intervals : V → Set ℝ
  prescribed : V → ℝ
  prescribed_ground : ∀ x ∈ ground, prescribed x = 0
  prescribed_bound : ∀ x, |prescribed x| ≤ M
  prescribed_gradient : ∀ x y, graph.Adj x y → |prescribed x - prescribed y| ≤ L / n
  polytope_measurable : MeasurableSet (heightPolytope graph pins walls boundary intervals)
  polytope_positive : volume (heightPolytope graph pins walls boundary intervals) ≠ 0
  polytope_finite : volume (heightPolytope graph pins walls boundary intervals) ≠ ⊤
  bad : (FreeSites pins → ℝ) → Set TriangularLipschitz.Vertex
  contact_bad : ∀ h x y, (contactGraph (shiftGraph graph ground)
    (extendHeight pins boundary h) sstar).Adj x y →
      TriangularLipschitz.boxIndex ℓ (location x) ∈ bad h ∧
      TriangularLipschitz.boxIndex ℓ (location y) ∈ bad h
  sparse : ∀ A : Finset TriangularLipschitz.Vertex, (ProbabilityTheory.cond volume
    (heightPolytope graph pins walls boundary intervals)) {h | ∀ w ∈ A, w ∈ bad h} ≤ ρ^A.card

namespace LatticeData

variable {n ℓ : ℕ} {ρ : ENNReal} {sstar L M C : ℝ}

variable (S : LatticeData (V := V) n ℓ ρ sstar L M C)

noncomputable def toShiftData (hℓ : 0 < ℓ) :
    ShiftData (V := V) (TriangularLipschitz.Boxes S.location ℓ) n 6 8 (ℓ^2)
      ρ sstar L M (7*C) where
  graph := S.graph
  ground := S.ground
  pins := S.pins
  walls := S.walls
  pins_ground := S.pins_ground
  walls_ground := S.walls_ground
  boundary := S.boundary
  intervals := S.intervals
  prescribed := S.prescribed
  prescribed_ground := S.prescribed_ground
  prescribed_bound := S.prescribed_bound
  prescribed_gradient := S.prescribed_gradient
  vertex_count := by
    classical
    have hd : ∀ x, (neighbors S.graph x).card ≤ 6 := by
      intro x
      exact TriangularLipschitz.finite_graph_degree S.location S.graph S.lattice_edges
        x _ (by intro y hy; exact (Finset.mem_filter.mp hy).2)
    have hc := localSites_card_bound S.graph S.ground S.active S.active_contains 6 hd
    have hc' : ((localSites S.graph S.ground).card : ℝ) ≤ 7 * (S.active.card : ℝ) := by
      exact_mod_cast hc
    nlinarith [S.active_count]
  degree := by
    classical
    intro x
    exact TriangularLipschitz.finite_graph_degree S.location S.graph S.lattice_edges
      x _ (by intro y hy; exact (Finset.mem_filter.mp hy).2)
  polytope_measurable := S.polytope_measurable
  polytope_positive := S.polytope_positive
  polytope_finite := S.polytope_finite
  boxGraph := TriangularLipschitz.coverGraph S.location ℓ
  box_degree := TriangularLipschitz.coverGraph_degree S.location ℓ
  boxMap := TriangularLipschitz.boxMap S.location ℓ
  box_fiber := TriangularLipschitz.boxMap_fiber S.location ℓ hℓ
  box_adjacent := by
    intro x y hxy
    exact TriangularLipschitz.boxMap_adjacent S.location ℓ hℓ (S.lattice_edges x y hxy)
  badBoxes := fun h => Subtype.val ⁻¹' S.bad h
  contact_bad := S.contact_bad
  sparse := by
    classical
    intro A
    have hs := S.sparse (A.image Subtype.val)
    have he : {h | ∀ w ∈ A.image Subtype.val, w ∈ S.bad h} =
        {h | ∀ w ∈ A, w ∈ Subtype.val ⁻¹' S.bad h} := by
      ext h
      simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        Set.mem_ofPred_eq, Set.mem_preimage]
    rw [he, Finset.card_image_of_injective _ Subtype.val_injective] at hs
    exact hs

end LatticeData

end FeasibleShift

namespace FeasibleShift

open Set MeasureTheory Filter

universe uI uV

namespace LatticeData

variable {V : Type uV} [Fintype V] [DecidableEq V]

variable {n ℓ : ℕ} {ρ : ENNReal} {sstar L M C : ℝ}

variable (S : LatticeData (V := V) n ℓ ρ sstar L M C)

noncomputable def polytope := heightPolytope S.graph S.pins S.walls S.boundary S.intervals

noncomputable def law := ProbabilityTheory.cond volume S.polytope

noncomputable def map (s₀ s₁ : ℝ) (h : FreeSites S.pins → ℝ) := h +
  freeShift (shiftGraph S.graph S.ground) S.ground S.pins S.boundary S.prescribed s₀ s₁ h

end LatticeData

theorem feasible_lattice_shifts_product {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (ℓ : ℕ) (ρ : ENNReal) (s₀ s₁ s₂ sstar L M C p : ℝ)
    (hℓ : 0 < ℓ) (hρ : ρ ≤ 1) (hsparse : (8 : ENNReal)^2 * ρ ≤ 1/2)
    (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hss : s₁ < s₂) (hstar : s₂ < sstar)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hC : 0 ≤ C) (hp : 0 < p) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
      Tendsto (fun n : ℕ => (L / n) * (n : ℝ)^(1/8 : ℝ)) atTop (nhds 0) ∧
      ∀ (n : ℕ), n₀ ≤ n → ∀ (V : ι → Type uV)
        [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
        (S : ∀ i, LatticeData (V := V i) n ℓ ρ sstar L M C)
        (E : Set (∀ i, FreeSites (S i).pins → ℝ)), MeasurableSet E →
        p ≤ (MeasureTheory.Measure.pi (fun i => (S i).law)).real E →
        ∃ E' : Set (∀ i, FreeSites (S i).pins → ℝ), MeasurableSet E' ∧ E' ⊆ E ∧
          p/2 ≤ (MeasureTheory.Measure.pi (fun i => (S i).law)).real E' ∧
          Set.InjOn (fun h i => (S i).map s₀ s₁ (h i)) E' ∧
          (fun h i => (S i).map s₀ s₁ (h i)) '' E' ⊆ Set.pi Set.univ (fun i => (S i).polytope) ∧
          MeasurableSet ((fun h i => (S i).map s₀ s₁ (h i)) '' E') ∧
          (∀ h ∈ E', ‖(fun i => (S i).map s₀ s₁ (h i) - h i -
            (fun x : FreeSites (S i).pins => (S i).prescribed x))‖ ≤
            (L / n) * (n : ℝ)^(1/8 : ℝ)) ∧
          c ≤ (MeasureTheory.Measure.pi (fun i => (S i).law)).real
            ((fun h i => (S i).map s₀ s₁ (h i)) '' E') := by
  classical
  obtain ⟨c,hc,n₀,ht,hn₀⟩ := feasible_shifts_product (ι := ι) 6 8 (ℓ^2) ρ s₀ s₁ s₂ sstar L M
    (7*C) p (by positivity) hρ hsparse hs₀ hs hss hstar hL hM (by positivity) hp
  refine ⟨c,hc,n₀,ht,?_⟩
  intro n hn V iV dV S E hE hpE
  exact hn₀ n hn V (fun i => TriangularLipschitz.Boxes (S i).location ℓ)
    (fun i => (S i).toShiftData hℓ) E hE hpE

end FeasibleShift

end

end OAI
