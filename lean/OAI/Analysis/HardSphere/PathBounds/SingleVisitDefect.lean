import Mathlib
import OAI.Analysis.HardSphere.Geometry.FreePathExpectation
import OAI.Analysis.HardSphere.PathBounds.FreeVisitTravel

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.FreeVisits
open HardSphere.Wiener HardSphere.BathSlice HardSphere.Lattice HardSphere.CellOrbital
attribute [local irreducible] freeTrajectory pathVisitedSites torusDistance

def singleVisitDefect {K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    (η : ℝ) (D : Set (ConfigurationPath 1 L)) (ω : ConfigurationPath 1 L) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal (Real.exp (η*(if ω∈D then ((pathVisitedSites L (siteCenter L) A 0 ω).card:ℝ) else 0))-1)

lemma singleVisitDefect_measurable {K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    (η : ℝ) {D : Set (ConfigurationPath 1 L)} (hD : MeasurableSet D) :
    Measurable (singleVisitDefect L A η D) := by
  classical
  exact ((measurable_const.mul ((pathVisitedSites_measurable L (siteCenter L) A 0).ite hD measurable_const)).exp.sub
    measurable_const).ennreal_ofReal

lemma singleVisitDefect_reverse {K : ℕ} (L : Length) (A : Finset (DiscreteTorus K))
    (η : ℝ) {D : Set (ConfigurationPath 1 L)}
    (hD : ∀ω,reverseConfigurationPath 1 L ω∈D ↔ ω∈D) (ω : ConfigurationPath 1 L) :
    singleVisitDefect L A η D (reverseConfigurationPath 1 L ω)=singleVisitDefect L A η D ω := by
  classical
  simp only [singleVisitDefect,hD,pathVisitedSites_reverse]

lemma free_single_defect_bound {η₀ : ℝ} (hη₀ : 0≤η₀) : ∃ C : ℝ, 0<C ∧
    ∀ {K : ℕ} [NeZero K] (L : Length), L.val=(K:ℝ) → ∀ A : Finset (DiscreteTorus K),
    ∀ {t η ε : ℝ}, 0<t → t≤2 → 0≤η → η≤η₀ → 0≤ε →
    ∀ D : Set (ConfigurationPath 1 L), MeasurableSet D →
    (∀ y : Torus L, coordinateWiener 1 {w | freeTrajectory 1 L t w (oneConfiguration y)∈D}≤ENNReal.ofReal ε) →
    ∀ y : Torus L,
      oneFreeExpectation t (singleVisitDefect L A η D) y ≤
      ENNReal.ofReal (C*η*ε^(1/3:ℝ)*Real.exp (-spatialSiteDistance L (A.image (siteCenter L)) y)) := by
  classical
  obtain ⟨C,hC,hbound⟩ := free_visit_bound hη₀
  refine ⟨C.toReal+1,by positivity,?_⟩
  intro K _ L hL A t η ε ht ht2 hη hηη hε D hD hprob y
  let E := {w : CoordinatePaths 1 | freeTrajectory 1 L t w (oneConfiguration y)∈D}
  have hE : MeasurableSet E := hD.preimage
    ((freeTrajectory_continuous 1 L t).measurable.comp (measurable_id.prodMk measurable_const))
  have H := hbound L hL A 0 ht ht2 hη hηη (oneConfiguration y) E hE (ENNReal.ofReal ε) (hprob y)
  have heq : oneFreeExpectation t (singleVisitDefect L A η D) y =
      ∫⁻ w,visitDefect L A 0 t η (oneConfiguration y) E w ∂coordinateWiener 1 := by
    rfl
  rw [heq]
  apply H.trans
  have hC' : C≤ENNReal.ofReal (C.toReal+1) := by
    calc
      C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC.ne).symm
      _ ≤ ENNReal.ofReal (C.toReal+1) := ENNReal.ofReal_le_ofReal (by linarith)
  calc
    C*ENNReal.ofReal η*ENNReal.ofReal ε^(1/3:ℝ)*
        ENNReal.ofReal (Real.exp (-visitStartDistance L A 0 (oneConfiguration y))) ≤
      ENNReal.ofReal (C.toReal+1)*ENNReal.ofReal η*ENNReal.ofReal ε^(1/3:ℝ)*
        ENNReal.ofReal (Real.exp (-visitStartDistance L A 0 (oneConfiguration y))) := by gcongr
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg hε (show 0≤(1/3:ℝ) by norm_num),
        ←ENNReal.ofReal_mul (show 0≤C.toReal+1 by positivity),
        ←ENNReal.ofReal_mul (show 0≤(C.toReal+1)*η by positivity),
        ←ENNReal.ofReal_mul (show 0≤(C.toReal+1)*η*ε^(1/3:ℝ) by positivity)]
      rfl

end HardSphere.FreeVisits

end
end

end

end OAI
