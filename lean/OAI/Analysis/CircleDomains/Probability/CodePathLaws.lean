import OAI.Analysis.CircleDomains.Probability.MeanVisitDensity
import OAI.Analysis.CircleDomains.Probability.CodeHitMeasures

namespace OAI

/-! Forgetting the optional tags produces the actual path law. Its full
mean visit function differs from the preterminal function by exactly one
unit at the prescribed terminal point. -/

open Set MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

def codePath (d : PathCodeData X Y) (Γ : BasePathCode d) : C(PathTime, X) := Γ.val.1

theorem measurable_codePath (d : PathCodeData X Y) : Measurable (codePath d) :=
  measurable_fst.comp measurable_subtype_coe

def codePathLaw (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d)) :
    ProbabilityMeasure C(PathTime, X) := P.map (codePath d)

variable [BorelSpace X] [BorelSpace C(PathTime, X)] [SecondCountableTopology X]

omit [BorelSpace X] [SecondCountableTopology X] in
theorem pathHitProbability_codePathLaw (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (x : X) :
    pathHitProbability (codePathLaw d P) x = codeHitProbability d P x := by
  exact Measure.map_apply (measurable_codePath d) (isClosed_paths_hitting x).measurableSet

theorem meanVisitCount_codePathLaw (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (x : X) :
    meanVisitCount (codePathLaw d P) x =
      meanCodePreVisits d P x + if d.target = x then 1 else 0 := by
  classical
  have hv : Measurable (fun γ : C(PathTime, X) => visitCount γ x) :=
    measurable_visitCount.comp (measurable_id.prodMk measurable_const)
  unfold meanVisitCount codePathLaw
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map hv (measurable_codePath d)]
  have he : ∀ Γ : BasePathCode d, visitCount (codePath d Γ) x =
      preterminalVisitCount Γ.val.1 x + if d.target = x then 1 else 0 := by
    intro Γ
    rw [visitCount_eq_preterminal_add_terminal]
    change preterminalVisitCount Γ.val.1 x + terminalVisitCount Γ.val.1 x = _
    rw [terminalVisitCount, Γ.property.2.1.2.1]
  simp_rw [he]
  have hm : Measurable (fun Γ : BasePathCode d => preterminalVisitCount Γ.val.1 x) :=
    measurable_preterminalVisitCount.comp
      ((measurable_fst.comp measurable_subtype_coe).prodMk measurable_const)
  rw [lintegral_add_left hm]
  simp only [lintegral_const, measure_univ, mul_one, meanCodePreVisits]

theorem codeHitProbability_le_meanCodeVisits (d : PathCodeData X Y)
    (P : ProbabilityMeasure (BasePathCode d)) (x : X) :
    codeHitProbability d P x ≤ meanCodePreVisits d P x + if d.target = x then 1 else 0 := by
  rw [← meanVisitCount_codePathLaw, ← pathHitProbability_codePathLaw]
  exact pathHitProbability_le_meanVisitCount (codePathLaw d P) x

end CircleDomainRigidity

end

end OAI
