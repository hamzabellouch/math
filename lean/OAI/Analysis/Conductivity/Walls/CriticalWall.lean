import Mathlib
import OAI.Analysis.Conductivity.Walls.CriticalWallBounds

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

lemma coordinateDivergence_tsupport (F : Coord3 → Coord3) :
    tsupport (coordinateDivergence F)⊆tsupport F := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have he : F =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hn
  apply hx
  unfold coordinateDivergence
  apply Finset.sum_eq_zero
  intro i _
  have hei : (fun y => F y i) =ᶠ[𝓝 x] (fun _ => 0) := he.mono (fun y hy => congrFun hy i)
  rw [hei.fderiv_eq]
  simp

lemma symmetricSource_tsupport (H : Coord3 → Mat3) (u : Coord3 → Fin 2 → ℝ) (j : Fin 2) :
    tsupport (symmetricSource H u j)⊆tsupport H :=
  (coordinateDivergence_tsupport _).trans (tensorColumn_tsupport H _ j)

lemma wallHomogeneousQuotient_zero_off_surface {v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a)
    {p : Box3} (hp : p.1∉tsupport a) :
    wallQuotient (wallHomogeneousNumerator (1,0) v a) p=0 := by
  unfold wallQuotient
  have haz : a p.1=0 := image_eq_zero_of_notMem_tsupport hp
  have had : fderiv ℝ a p.1=0 := fderiv_of_notMem_tsupport ℝ hp
  have hz (t : ℝ) : wallDerivative (wallHomogeneousNumerator (1,0) v a) (p.1,t*p.2)=0 := by
    rw [wallHomogeneousNumerator_derivative hv ha,wallAlong_pullback_box (ha.differentiable (by simp))]
    simp only [haz,had,_root_.zero_apply,mul_zero,zero_mul,sub_zero]
  simp only [hz,integral_zero]

lemma wallHomogeneousTensor_tsupport_surface {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a) :
    tsupport (wallHomogeneousTensor χ v a)⊆(fun x : Coord3 => (boxCoordinates x).1) ⁻¹' tsupport a := by
  apply closure_minimal _ ((isClosed_tsupport a).preimage (continuous_fst.comp boxCoordinates.continuous))
  intro x hx
  by_contra hn
  have ha₀ : a (boxCoordinates x).1=0 := image_eq_zero_of_notMem_tsupport hn
  have hq := wallHomogeneousQuotient_zero_off_surface hv ha hn
  apply hx
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [wallHomogeneousTensor,wallMatrix,ha₀,hq]

lemma wallHomogeneousTensor_source_off_one {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a)
    (hz : ∀ q,wallDerivative v (q,0)=0)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0)
    {x : Coord3} (hx : χ =ᶠ[𝓝 (boxCoordinates x)] (fun _ => 1)) (j : Fin 2) :
    x∉tsupport (symmetricSource (wallHomogeneousTensor χ v a) (wallCoordinatePair v) j) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  have hloc : ∀ᶠ y in 𝓝 (boxCoordinates x),χ =ᶠ[𝓝 y] (fun _ => 1) := hx.eventually_nhds
  have hp : ∀ᶠ y in 𝓝 x,χ =ᶠ[𝓝 (boxCoordinates y)] (fun _ => 1) :=
    boxCoordinates.continuous.continuousAt.eventually hloc
  filter_upwards [hp] with y hy
  have he := wallHomogeneousTensor_source_eq hχ hv ha hz hne y hy
  fin_cases j
  · exact he.1
  · exact he.2

end ScalarConductivity

end

end OAI
