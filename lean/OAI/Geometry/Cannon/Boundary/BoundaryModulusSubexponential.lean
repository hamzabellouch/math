import Mathlib
import OAI.Geometry.Cannon.ScalarLimits.CompactVariationRegion

namespace OAI

section
section
section
noncomputable section
section
section
section
section
namespace CannonRelease

open CannonGraph CannonVisual CannonCells CannonCharts Set Metric

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

theorem boundary_modulus_subexponential (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    let a := Real.exp (2*visualExponent δ)
    let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
    ∀ d : ℝ, 0 < d → d < diam (univ : Set (Boundary D)) → d ≤ 1/(LE*3^2) →
    ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → Boundary D),
    (∀ n i j, i ≠ j → (a^n)⁻¹ ≤ dist (p n i) (p n j)) →
    (∀ n x, ∃ i, dist (p n i) x ≤ (a^n)⁻¹) →
    ∀ lam : ℝ, 1 < lam → ∃ B : ℝ, 0 < B ∧ ∀ n,
      modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d) ≤ B*lam^n := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  intro d hd hdia hdc ι hι p hsep hnet lam hlam
  have hn := boundary_exponential_records_impossible D hδ φ d hd hdia hdc ι p hsep hnet lam hlam
  have hbnd : ∃ B : ℝ, ∀ n,
      modulus (fun i => ball (p n i) (2*(Real.exp (2*visualExponent δ)^n)⁻¹))
        (macroFamily d)/lam^n ≤ B := by
    by_contra h
    apply hn
    intro B
    by_contra hB
    apply h
    refine ⟨B,fun n => ?_⟩
    exact le_of_not_gt (fun hh => hB ⟨n,hh⟩)
  obtain ⟨B,hB⟩ := hbnd
  refine ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right ..),fun n => ?_⟩
  have hh := hB n
  have hl : 0 < lam^n := pow_pos (lt_trans zero_lt_one hlam) n
  exact (div_le_iff₀ hl).mp (hh.trans (le_max_left ..))

end CannonRelease

end

section

open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonScalarLocal

open CannonGrid CannonCells CannonRegularization CannonChart

variable {X ι : Type*} [MetricSpace X] [Fintype ι]

local instance : LocallyPathConnectedSpace unitInterval :=
  (isQuotientMap_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).locallyPathConnectedSpace

local instance : PathConnectedSpace Square :=
  pathConnectedSpace_iff_connectedSpace.mpr inferInstance

end CannonScalarLocal

namespace CannonApprox

open CannonGrid CannonRegularization CannonLevel CannonCells CannonBands

variable {ι : Type*} [Fintype ι]

local instance : PathConnectedSpace (Strip height (1 / 3) (2 / 3)) :=
  strip_pathConnected _ _ (by norm_num) (by norm_num) (by norm_num)

end CannonApprox

open Set Metric Topology
open Set Topology unitInterval
open Set Filter Topology
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open scoped NNReal ENNReal

namespace CannonAtomic

attribute [local instance] Classical.propDecidable

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

end CannonAtomic

namespace CannonAtomic

open Set MeasureTheory

attribute [local instance] Classical.propDecidable

end CannonAtomic

open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace CannonScalarLimit

open CannonAtomic CannonAnnularCompactness CannonScales Set Filter Metric Topology MeasureTheory

attribute [local instance] Classical.propDecidable

end CannonScalarLimit

namespace CannonScalarLimit

open CannonAtomic CannonAnnularCompactness Set Filter Metric Topology MeasureTheory
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

end CannonScalarLimit

open Set Filter Topology TopologicalSpace Metric

end

end
end
end
end
end
end
end

end OAI
