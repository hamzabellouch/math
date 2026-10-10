import OAI.MeasureTheory.Falconer.Graphs.GraphLiftJacobian

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

noncomputable def graphLiftInverse (q : GraphLiftSpace) : GraphLiftSpace :=
  ![2*q 0*Real.cos ((q 1-q 2)/2), (q 1+q 2)/2, Real.tan ((q 1-q 2)/2)]

def graphLiftStrip : Set GraphLiftSpace := {q | |q 1-q 2| < Real.pi}

theorem graphLiftInverse_left (p : GraphLiftSpace) :
    graphLiftInverse (graphLiftMap p) = p := by
  have he : (p 1+Real.arctan (p 2)-(p 1-Real.arctan (p 2)))/2 = Real.arctan (p 2) := by ring
  have hs : Real.sqrt (1+(p 2)^2) ≠ 0 := by positivity
  ext i
  fin_cases i <;> simp [graphLiftInverse, graphLiftMap, Real.tan_arctan, Real.cos_arctan]
  · field_simp

theorem graphLiftMap_mem_strip (p : GraphLiftSpace) : graphLiftMap p ∈ graphLiftStrip := by
  have ha := Real.arctan_mem_Ioo (p 2)
  change |(p 1+Real.arctan (p 2))-(p 1-Real.arctan (p 2))| < Real.pi
  exact abs_lt.mpr ⟨by linarith [ha.1],by linarith [ha.2]⟩

theorem graphLiftInverse_right (q : GraphLiftSpace) (hq : q ∈ graphLiftStrip) :
    graphLiftMap (graphLiftInverse q) = q := by
  change |q 1-q 2| < Real.pi at hq
  have hb := abs_lt.mp hq
  have ha := Real.arctan_tan (x := (q 1-q 2)/2) (by linarith [hb.1]) (by linarith [hb.2])
  have hc := Real.cos_arctan (Real.tan ((q 1-q 2)/2))
  rw [ha] at hc
  have hs : Real.sqrt (1+Real.tan ((q 1-q 2)/2)^2) ≠ 0 := by positivity
  ext i
  fin_cases i <;> simp [graphLiftMap,graphLiftInverse,ha]
  · rw [hc]
    field_simp
  · ring
  · ring

theorem graphLiftMap_range : Set.range graphLiftMap = graphLiftStrip := by
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    exact graphLiftMap_mem_strip p
  · intro hq
    exact ⟨graphLiftInverse q, graphLiftInverse_right q hq⟩

theorem graphLiftMap_contDiff : ContDiff ℝ ∞ graphLiftMap := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [graphLiftMap]
  · exact ((contDiff_apply ℝ ℝ 0).mul
      ((contDiff_const.add ((contDiff_apply ℝ ℝ 2).pow 2)).sqrt (fun p => by positivity))).div_const 2
  · exact (contDiff_apply ℝ ℝ 1).add (Real.contDiff_arctan.comp (contDiff_apply ℝ ℝ 2))
  · exact (contDiff_apply ℝ ℝ 1).sub (Real.contDiff_arctan.comp (contDiff_apply ℝ ℝ 2))

theorem graphLiftMap_strip_lintegral (f : GraphLiftSpace → ℝ≥0∞) :
    (∫⁻ q in graphLiftStrip, f q) =
      ∫⁻ p, ENNReal.ofReal ((Real.sqrt (1+(p 2)^2))⁻¹) * f (graphLiftMap p) := by
  simpa only [image_univ, graphLiftMap_range, Measure.restrict_univ] using
    graphLiftMap_lintegral univ MeasurableSet.univ f

end PlanarFalconer

end OAI
