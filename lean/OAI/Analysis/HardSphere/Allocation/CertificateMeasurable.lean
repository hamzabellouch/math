import Mathlib
import OAI.Analysis.HardSphere.Bridges.ConfinedLift
import OAI.Analysis.HardSphere.PathBounds.GridTailTransfer

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener PathCutoff CellOrbital BathSlice

lemma regular_mono_constants {L : Length} {m : ℕ} {r R C R' C' S : ℝ} {u : Time}
    {ω : ConfigurationPath 1 L} (hR : R≤R') (hC : C≤C')
    (h : Regular m r R C u S ω) : Regular m r R' C' u S ω := by
  refine ⟨⟨fun j ↦ (h.1.1 j).trans hR,?_⟩,h.2⟩
  exact h.1.2.trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))

lemma certificate_mono_constants {N K : ℕ} [Nontrivial (Fin N)] {L : Length}
    {m : ℕ} {r R C R' C' S s₀ ell θ H D : ℝ} {u : Time} {v : Fin 3→Fin K}
    {ω : ConfigurationPath N L} (hR : R≤R') (hC : C≤C')
    (h : Certificate m r R C S s₀ ell θ H D u v ω) :
    Certificate m r R' C' S s₀ ell θ H D u v ω :=
  ⟨h.low,h.closeY,h.closeZ,h.visit,fun i hi ↦ regular_mono_constants hR hC (h.regular i hi),h.long⟩

lemma certificate_measurable {N K : ℕ} [Nontrivial (Fin N)] [NeZero K] {L : Length}
    (m : ℕ) (r R C S s₀ ell θ H D : ℝ) (u : Time) (v : Fin 3→Fin K) :
    MeasurableSet {ω : ConfigurationPath N L | Certificate m r R C S s₀ ell θ H D u v ω} := by
  classical
  have hc : Measurable (fun n : ℕ ↦ (n:ℝ)) := measurable_of_countable _
  have hlo : MeasurableSet {ω : ConfigurationPath N L | ell*D≤(centeredCount L (gridCenter L v) (ω 0):ℝ)} :=
    measurableSet_le measurable_const (hc.comp
      ((centeredCount_measurable L (gridCenter L v)).comp (continuous_eval_const 0).measurable))
  have hY : MeasurableSet {ω : ConfigurationPath N L | ((localCloseLabels L s₀ (gridCenter L v) (ω 0)).card:ℝ)<θ*D} :=
    measurableSet_lt ((localCloseLabels_measurable L s₀ (gridCenter L v)).comp (continuous_eval_const 0).measurable) measurable_const
  have hZ : MeasurableSet {ω : ConfigurationPath N L | ((localCloseLabels L s₀ (gridCenter L v) (ω 1)).card:ℝ)<θ*D} :=
    measurableSet_lt ((localCloseLabels_measurable L s₀ (gridCenter L v)).comp (continuous_eval_const 1).measurable) measurable_const
  have hv : Measurable (fun ω : ConfigurationPath N L ↦ (visitors (gridCenter L v) ω).card) := by
    have he : (fun ω : ConfigurationPath N L ↦ (visitors (gridCenter L v) ω).card) =
        ShiftVisits.visitorCount L (gridShift L) Set.univ (gridSite v) :=
      funext fun ω ↦ (grid_visitors_eq L v ω).symm
    rw [he]
    exact ShiftVisits.visitorCount_measurable (n:=N) L (gridShift L) MeasurableSet.univ (gridSite v)
  have ht : Measurable (fun ω : ConfigurationPath N L ↦ (longVisitors (gridCenter L v) ω).card) := by
    have he : (fun ω : ConfigurationPath N L ↦ (longVisitors (gridCenter L v) ω).card) =
        ShiftVisits.visitorCount L (gridShift L) {p | 1 < intervalDiameter 0 1 p} (gridSite v) :=
      funext fun ω ↦ (grid_longVisitors_eq L v ω).symm
    rw [he]
    exact ShiftVisits.visitorCount_measurable (n:=N) L (gridShift L)
      (measurableSet_lt measurable_const (intervalDiameter_continuous L 0 1).measurable) (gridSite v)
  have hreg : MeasurableSet {ω : ConfigurationPath N L | ∀i,pathVisitsBall L 12 (gridCenter L v) i ω→Regular m r R C u S (onePathAt i ω)} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    have he : {ω : ConfigurationPath N L | pathVisitsBall L 12 (gridCenter L v) i ω→Regular m r R C u S (onePathAt i ω)}=
      {ω | pathVisitsBall L 12 (gridCenter L v) i ω}ᶜ∪{ω | Regular m r R C u S (onePathAt i ω)} := by ext ω; simp [imp_iff_not_or]
    rw [he]
    exact (pathVisitsBall_isClosed L 12 (gridCenter L v) i).measurableSet.compl.union
      ((regular_measurable m r R C u S).preimage (onePathAt_continuous i).measurable)
  have he : {ω : ConfigurationPath N L | Certificate m r R C S s₀ ell θ H D u v ω}=
      {ω | ell*D≤(centeredCount L (gridCenter L v) (ω 0):ℝ)} ∩
      ({ω | ((localCloseLabels L s₀ (gridCenter L v) (ω 0)).card:ℝ)<θ*D} ∩
      ({ω | ((localCloseLabels L s₀ (gridCenter L v) (ω 1)).card:ℝ)<θ*D} ∩
      ({ω | ((visitors (gridCenter L v) ω).card:ℝ)≤H*D} ∩
      ({ω | ∀i,pathVisitsBall L 12 (gridCenter L v) i ω→Regular m r R C u S (onePathAt i ω)} ∩
      {ω | ((longVisitors (gridCenter L v) ω).card:ℝ)<θ*D})))) := by
    ext ω
    constructor
    · exact fun h ↦ ⟨h.low,h.closeY,h.closeZ,h.visit,h.regular,h.long⟩
    · exact fun h ↦ ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩
  rw [he]
  exact hlo.inter (hY.inter (hZ.inter ((measurableSet_le (hc.comp hv) measurable_const).inter
    (hreg.inter (measurableSet_lt (hc.comp ht) measurable_const)))))

end HardSphere.Groups

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking PathCutoff CellOrbital

lemma projection_square_distance (L : Length) (x y : Point) :
    (torusDistance L (projectPoint L x) (projectPoint L y))^2 ≤ square (x-y) := by
  rw [torusDistance,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))]
  unfold square
  apply Finset.sum_le_sum
  intro j _
  have h : dist (projectPoint L x j) (projectPoint L y j) ≤ |x j-y j| := by
    rw [dist_eq_norm]
    change ‖(x j:AddCircle L.val)-(y j:AddCircle L.val)‖ ≤ _
    rw [←AddCircle.coe_sub]
    exact QuotientAddGroup.norm_mk_le_norm
  simpa only [Pi.sub_apply,sq_abs] using pow_le_pow_left₀ dist_nonneg h 2

lemma eligible_near_lift {N K : ℕ} {L : Length} (hL : 50<L.val)
    (m : ℕ) (r R C S s₀ : ℝ) (u : Time) (v : Fin 3 → Fin K)
    (c : Point) (hc : projectPoint L c=gridCenter L v)
    (i : Fin N) (ω : ConfigurationPath N L) (hi : Eligible m r R C S s₀ u v i ω) :
    ∃f : C(Time,Point),projectCurve L f=onePathAt i ω ∧
      ‖f 0-c‖ ≤ 1 ∧ ‖f 1-c‖ ≤ 3 ∧ TrialConfined L c f := by
  let y := nearestLift L c (ω 0 i)
  have hyc : ‖y-c‖ ≤ 1 := nearestLift_bound L c (ω 0 i) (by rw [hc]; exact centeredCell_distance hi.1.1)
  obtain ⟨ζ,hζ,hζ0⟩ := exists_pathLift_at (onePathAt i ω) y (nearestLift_project L c (ω 0 i))
  let f : C(Time,Point) := ⟨fun s j ↦ ζ j s,by fun_prop⟩
  have hf : projectCurve L f=onePathAt i ω := by
    ext s k j
    fin_cases k
    exact hζ j s
  have hf0 : f 0=y := hζ0
  have hp (s : Time) : projectPoint L (f s)=ω s i := by
    exact congrArg (fun g : ConfigurationPath 1 L ↦ g s 0) hf
  have hconf := confined_lift hL c f (by rw [hf0]; exact hyc.trans (by norm_num))
    (fun s ↦ by rw [hp,hc]; exact hi.2.2 s)
  refine ⟨f,hf,by rw [hf0]; exact hyc,?_,hconf⟩
  have hl := local_norm_le_torus hL (f 1) c ((hconf 1).1.trans (by norm_num))
  have he : projectPoint L (f 1)=ω 1 i := by
    have hh := congrArg (fun g : ConfigurationPath 1 L ↦ g 1 0) hf
    exact hh
  rw [he,hc] at hl
  exact hl.trans hi.1.2.1

end HardSphere.Groups

end
end

end

end OAI
