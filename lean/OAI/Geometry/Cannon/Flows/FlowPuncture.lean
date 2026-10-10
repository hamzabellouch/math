import Mathlib
import OAI.Geometry.Cannon.Flows.FlowSetup
import OAI.Geometry.Cannon.Boundary.BoundaryBasedRay
import OAI.Geometry.Cannon.Boundary.VisualSynchronousPrefix
import OAI.Geometry.Cannon.Flows.NearProbabilityBound

namespace OAI

section
section
section
noncomputable section
section
namespace CannonRelease

open CannonGraph CannonVisual CannonApprox CannonNode CannonPairs Set Metric Filter Topology Finset

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance flowPunctureSetoid : Setoid (BasedRay D) := raySetoid D

local instance flowPunctureMeasurableSpace : MeasurableSpace (Boundary D) := borel (Boundary D)

local instance flowPunctureBorelSpace : BorelSpace (Boundary D) := ⟨rfl⟩

variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] {p : ∀ n, ι n → Boundary D} {r : ℕ → ℝ}

lemma flow_scale_visual :
    let _ := visualMetricSpace D hδ
    ∀ (T : RecordData (boundaryHomeomorph D ⟨δ,hδ⟩) ι p r)
      {L CE LE : ℝ} {Q : ℕ} (F : FlowSetup T (2*visualExponent δ) L CE LE Q), ∀ g : ℕ,
    F.S.scale g=visualScale δ (F.S.kmin+160*(Q+1)*F.n*g) := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  intro T L CE LE Q F g
  dsimp [CannonNode.SourceConstruction.scale,CannonNode.radius,CannonVisual.visualScale]
  congr 1
  push_cast
  ring

lemma flow_center_z₀ :
    let _ := visualMetricSpace D hδ
    ∀ (T : RecordData (boundaryHomeomorph D ⟨δ,hδ⟩) ι p r)
      {L CE LE : ℝ} {Q : ℕ} (F : FlowSetup T (2*visualExponent δ) L CE LE Q),
    0 ≤ F.B+1 → ∀ (g : ℕ) (i : Fin (F.S.flow.size g)),
    F.ε ≤ dist (F.S.center g i) T.z₀ := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  intro T L CE LE Q F hB g i
  by_contra hn
  have hi := mem_closedBall.mp (F.S.center_mem hB g i)
  apply T.z₀not (F.local_domain ?_)
  rw [mem_closedBall]
  have ht := dist_triangle T.z₀ (F.S.center g i) T.x₀
  rw [dist_comm T.z₀ (F.S.center g i)] at ht
  linarith only [ht,hi,lt_of_not_ge hn]

def flowPuncture :
    let _ := visualMetricSpace D hδ
    ∀ (T : RecordData (boundaryHomeomorph D ⟨δ,hδ⟩) ι p r)
      {L CE LE : ℝ} {Q : ℕ} (F : FlowSetup T (2*visualExponent δ) L CE LE Q),
    ∀ (g : ℕ), Fin (F.S.flow.size g) → Boundary D := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  intro T L CE LE Q F g i
  exact boundaryExpansion D hδ (F.S.center g i) (F.S.kmin+160*(Q+1)*F.n*g) T.z₀

theorem flow_puncture_multiplicity :
    let _ := visualMetricSpace D hδ
    ∀ (T : RecordData (boundaryHomeomorph D ⟨δ,hδ⟩) ι p r)
      {L CE LE : ℝ} {Q : ℕ} (F : FlowSetup T (2*visualExponent δ) L CE LE Q),
    0 ≤ F.B+1 → 4*(F.B+1) < F.H → ∀ C : ℝ, 0 ≤ C →
    ∃ N : ℕ, ∀ g b, ((univ : Finset (Fin (F.S.flow.size g))).filter
      (fun i => dist (flowPuncture D hδ T F g i) b ≤ C*F.S.scale g)).card ≤ N := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  intro T L CE LE Q F hB hH C hC
  have hep (g : ℕ) (i : Fin (F.S.flow.size g)) : flowPuncture D hδ T F g i =
      boundaryTranslate D ⟨δ,hδ⟩ ((boundaryBasedRay D (F.S.center g i)).val
        (F.S.kmin+160*(Q+1)*F.n*g))⁻¹ T.z₀ := rfl
  have hdistance (x y : Boundary D) : dist x y=boundaryDist D hδ x y := rfl
  have hHp : 0 < F.H := by linarith only [hB,hH]
  obtain ⟨N,hN⟩ := puncture_ball_multiplicity D hδ F.εpos hHp hC
  refine ⟨N,fun g b => ?_⟩
  have hh := hN (univ : Finset (Fin (F.S.flow.size g)))
    (fun i => boundaryBasedRay D (F.S.center g i)) (boundaryBasedRay D T.z₀)
    (F.S.kmin+160*(Q+1)*F.n*g)
    (fun i _ => by simpa only [boundaryBasedRay_rep] using flow_center_z₀ D hδ T F hB g i)
    (fun i _ j _ hij => by simpa only [boundaryBasedRay_rep,← flow_scale_visual D hδ T F g]
      using F.S.centers_separated F.decay hB hH g i j hij) b
  simpa only [boundaryBasedRay_rep,← flow_scale_visual D hδ T F g,hep,hdistance] using hh

theorem flow_near_probability :
    let _ := visualMetricSpace D hδ
    ∀ (T : RecordData (boundaryHomeomorph D ⟨δ,hδ⟩) ι p r)
      {L CE LE : ℝ} {Q : ℕ} (F : FlowSetup T (2*visualExponent δ) L CE LE Q),
    0 ≤ F.B+1 → 4*(F.B+1) < F.H →
    ∃ N : ℕ, ∀ g m (b : Boundary D),
      ∑ i ∈ (univ : Finset (Fin (F.S.flow.size (g+m)))).filter
        (fun i => dist (flowPuncture D hδ T F (g+m) i) b ≤ visualScale δ (160*(Q+1)*F.n*m)),
        F.S.flow.weight (g+m) i ≤ (N:ℝ)*(Real.exp (-(2*visualExponent δ)*F.n))^m := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  intro T L CE LE Q F hB hH
  have hep (g : ℕ) (i : Fin (F.S.flow.size g)) : flowPuncture D hδ T F g i =
      boundaryTranslate D ⟨δ,hδ⟩ ((boundaryBasedRay D (F.S.center g i)).val
        (F.S.kmin+160*(Q+1)*F.n*g))⁻¹ T.z₀ := rfl
  have hdistance (x y : Boundary D) : dist x y=boundaryDist D hδ x y := rfl
  have hHp : 0 < F.H := by linarith only [hB,hH]
  obtain ⟨N,hN⟩ := near_puncture_descendant_count D hδ F.εpos hHp (by positivity : 0 ≤ 2*(F.B+1))
  refine ⟨N,fun g m b => ?_⟩
  let S := (univ : Finset (Fin (F.S.flow.size (g+m)))).filter
    (fun i => dist (flowPuncture D hδ T F (g+m) i) b ≤ visualScale δ (160*(Q+1)*F.n*m))
  have hcount (a : Fin (F.S.flow.size g)) :
      (S.filter (fun i => F.S.flow.ancestor g m i=a)).card ≤ N := by
    let V := S.filter (fun i => F.S.flow.ancestor g m i=a)
    have hd : F.S.kmin+160*(Q+1)*F.n*(g+m)-160*(Q+1)*F.n*m =
        F.S.kmin+160*(Q+1)*F.n*g := by simp only [Nat.mul_add]; omega
    apply hN V (fun i => boundaryBasedRay D (F.S.center (g+m) i))
      (boundaryBasedRay D T.z₀) (boundaryBasedRay D (F.S.center g a)) (boundaryBasedRay D b)
      (F.S.kmin+160*(Q+1)*F.n*(g+m)) (160*(Q+1)*F.n*m) (by simp only [Nat.mul_add]; omega)
    · intro i _
      simpa only [boundaryBasedRay_rep] using flow_center_z₀ D hδ T F hB (g+m) i
    · intro i _ j _ hij
      simpa only [boundaryBasedRay_rep,← flow_scale_visual D hδ T F (g+m)]
        using F.S.centers_separated F.decay hB hH (g+m) i j hij
    · intro i hi
      have hia := (mem_filter.mp hi).2
      have hx := F.S.descendant_displacement F.decay hB g m i
      rw [hia,flow_scale_visual D hδ T F g] at hx
      simpa only [boundaryBasedRay_rep,hd] using hx
    · intro i hi
      have hip := (mem_filter.mp (mem_filter.mp hi).1).2
      simpa only [boundaryBasedRay_rep,hep,hdistance] using hip
  have hh := near_probability_bound S (F.S.flow.ancestor g m) (F.S.flow.weight (g+m))
    (F.S.flow.weight g) N ((Real.exp (-(2*visualExponent δ)*F.n))^m)
    (pow_nonneg (Real.exp_pos _).le _) (F.S.flow.nonneg g) (fun a => by
      convert hcount a using 1
      congr 1
      ext i
      simp only [mem_filter])
    (fun i _ => F.S.weight_conditional g m i)
  simpa only [F.S.flow.total_mass,mul_one] using hh

end CannonRelease

end

section
section

section

section

section

section

section

section

section

section

section

section

section

section

namespace CannonCapacity

open Finset Set

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

open Finset

namespace CannonCapacity

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

namespace CannonCapacity

open Set Metric Finset CannonAnnular

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

namespace CannonCapacity

open Set Metric Finset CannonAnnular CannonPacking

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset CannonAnnular

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

namespace CannonCapacity

open Set Metric Finset CannonAnnular CannonPacking

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

section

open Set Metric Finset

namespace CannonCapacity

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset CannonPacking CannonAnnular Filter Topology

attribute [local instance] Classical.propDecidable

end CannonCapacity

end

namespace CannonCapacity

open Set Finset

attribute [local instance] Classical.propDecidable

end CannonCapacity

namespace CannonCapacity

open Set Metric Finset

attribute [local instance] Classical.propDecidable

end CannonCapacity

namespace CannonNode

open Set Metric Finset CannonCapacity CannonFlow

attribute [local instance] Classical.propDecidable

end CannonNode

namespace CannonNode

open Set Metric Finset CannonCapacity CannonFlow CannonPacking CannonAnnular Filter Topology

attribute [local instance] Classical.propDecidable

end CannonNode

end

namespace CannonNode

open Set Metric Finset Filter Topology CannonPacking CannonAnnular CannonMagnification

attribute [local instance] Classical.propDecidable

end CannonNode

end

section

section

open Set Filter Finset

namespace CannonFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

end CannonFlow

namespace CannonFlow

open Finset

attribute [local instance] Classical.propDecidable

end CannonFlow

end

namespace CannonNode

open Set Metric Finset CannonFlow

attribute [local instance] Classical.propDecidable

end CannonNode

end

namespace CannonNode

open Set Metric Finset Filter Topology CannonPacking CannonAnnular CannonMagnification CannonFlow

attribute [local instance] Classical.propDecidable

end CannonNode

end

section

open Set Filter Finset

namespace CannonFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

namespace FiniteFlow

attribute [local instance] Classical.propDecidable

variable (T : FiniteFlow)

end FiniteFlow

end CannonFlow

namespace CannonFlow

open Finset

attribute [local instance] Classical.propDecidable

end CannonFlow

end

section

open Set Finset MeasureTheory Filter

namespace CannonPairCost

attribute [local instance] Classical.propDecidable

end CannonPairCost

end

namespace CannonNode.SourceConstruction

open Set Metric Finset Filter Topology CannonFlow

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

end CannonNode.SourceConstruction

namespace CannonNode.SourceConstruction

open Set Metric Finset MeasureTheory CannonFlow

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

end CannonNode.SourceConstruction

end

namespace CannonNode

open Set Metric CannonCapacity CannonMagnification

namespace SourceConstruction

attribute [local instance] Classical.propDecidable

variable {X : Type*} [MetricSpace X] [ProperSpace X] {f : X → ℝ} {x₀ : X}
  {ε ell c₀ A B H ρ : ℝ} {qdim n : ℕ}

variable (S : SourceConstruction f x₀ ε ell c₀ A B H ρ qdim n)

end SourceConstruction

end CannonNode

end

end

end
end
end
end
end
end
end
end

end OAI
