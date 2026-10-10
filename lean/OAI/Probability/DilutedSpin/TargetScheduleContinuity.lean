import OAI.Probability.DilutedSpin.SpatialScheduledContinuity
import OAI.Probability.DilutedSpin.TargetEvaluationContinuity

namespace OAI

section
section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance targetScheduleAverageDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_expect {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (D : (α → Fin L) → Prop) (F : (α → Fin L) → Ω → ℝ) :
    average D (fun q => P.expect (F q))=P.expect (fun x => average D (fun q => F q x)) := by
  unfold average
  calc
    _ = (depthLaw α L).expect (fun q => P.expect (fun x => if D q then F q x else 0)) := by
      apply FiniteLaw.expect_congr
      intro q
      split_ifs with h
      · rfl
      · exact (P.expect_const 0).symm
    _ = _ := FiniteLaw.expect_comm _ _ _

lemma average_mono_on (D : (α → Fin L) → Prop) (F G : (α → Fin L) → ℝ)
    (h : ∀ q, D q → F q ≤ G q) : average D F ≤ average D G := by
  apply FiniteLaw.expect_mono
  intro q
  split_ifs with hq
  · exact h q hq
  · exact le_rfl

lemma average_mul_left (D : (α → Fin L) → Prop) (F : (α → Fin L) → ℝ) (c : ℝ) :
    average D (fun q => c*F q)=c*average D F := by
  unfold average
  rw [← FiniteLaw.expect_mul_left]
  apply FiniteLaw.expect_congr
  intro q
  split_ifs <;> simp

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
noncomputable local instance targetScheduleTopologyDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω : Type} [Fintype Ω] {L N : ℕ} [NeZero L]

/-- A branching-schedule projector evaluated on the SAME actual full path.
Its initial p coordinates are retained, not independently resampled. -/
noncomputable def scheduledTailProjection (H d p : ℕ) (S : ReducedTopology)
    (q : S.Vertex → Fin L) (T : KernelTower Ω (H+p))
    (f : FinitePath Ω (H+p) → Fin N → ℝ) (x : FinitePath Ω (H+p)) (i : Fin N) : ℝ :=
  PrescribedTree.tailMean (realize H d S (fun v => (q v).val)) p T (fun y => f y i) x

omit [NeZero L] in
lemma scheduledTailProjection_bound (H d p : ℕ) (S : ReducedTopology)
    (q : S.Vertex → Fin L) (T : KernelTower Ω (H+p))
    (f : FinitePath Ω (H+p) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1)
    (x : FinitePath Ω (H+p)) (i : Fin N) : |scheduledTailProjection H d p S q T f x i|≤1 :=
  PrescribedTree.tailMean_bound _ p T _ (fun y => hf y i) x

noncomputable def tailScheduleChange (H d p : ℕ) (S : ReducedTopology) (s : S.Vertex → Bool)
    (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → Fin N → ℝ) (q : S.Vertex → Fin L) : ℝ :=
  (KernelTower.law (H+p) T).expect (fun x => FiniteLaw.spatialSq (fun i =>
    scheduledTailProjection H d p S q T f x i-
    scheduledTailProjection H d p S (fun v => DepthAverage.shiftPerm (s v) (q v)) T f x i))

omit [NeZero L] in
lemma tailScheduleChange_succ (H d p : ℕ) (S : ReducedTopology) (s : S.Vertex → Bool)
    (T : KernelTower Ω (H+(p+1))) (f : FinitePath Ω (H+(p+1)) → Fin N → ℝ) (q : S.Vertex → Fin L) :
    tailScheduleChange H d (p+1) S s T f q=
      T.1.expect (fun x => tailScheduleChange H d p S s (T.2 x) (fun y => f (x,y)) q) := by
  unfold tailScheduleChange
  exact KernelTower.law_succ_expect (Ω := Ω) (H+p) T _

/-- Uniform simultaneous schedule continuity after an arbitrary real sampled
prefix. In particular p=d gives the physical evaluation-depth geometry. -/
theorem averaged_tailScheduleChange_le (H d p : ℕ) (hheight : d+H=L)
    (S : ReducedTopology) (η : ℝ) (hlarge : 1<η*(L:ℝ)) (s : S.Vertex → Bool)
    (D : (S.Vertex → Fin L) → Prop)
    (hD : ∀ q, D q → Admissible S (fun v => (q v).val) d L ∧ DepthAverage.Regular η q)
    (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    DepthAverage.average D (tailScheduleChange H d p S s T f) ≤
      (Fintype.card S.Vertex:ℝ)*(∑ v : S.Vertex, (vertexArity S v:ℝ)^2)/(L:ℝ) := by
  induction p with
  | zero =>
    have he : tailScheduleChange (L := L) H d 0 S s T f=spatialScheduleChange H d S s T f := by
      funext q
      unfold tailScheduleChange scheduledTailProjection
      simp only [PrescribedTree.tailMean,FiniteLaw.expect_const,FiniteLaw.spatialSq,spatialScheduleChange]
      rfl
    rw [he]
    exact averaged_spatialScheduleChange_le H d hheight S η hlarge s D hD T f hf
  | succ p ih =>
    have he : tailScheduleChange (L := L) H d (p+1) S s T f=
        fun q => T.1.expect (fun x => tailScheduleChange H d p S s (T.2 x) (fun y => f (x,y)) q) :=
      funext (tailScheduleChange_succ H d p S s T f)
    rw [he,DepthAverage.average_expect]
    calc
      _ ≤ T.1.expect (fun _ => (Fintype.card S.Vertex:ℝ)*
          (∑ v : S.Vertex, (vertexArity S v:ℝ)^2)/(L:ℝ)) :=
        T.1.expect_mono (fun x => ih (T.2 x) (fun y => f (x,y)) (fun y => hf (x,y)))
      _ = _ := T.1.expect_const _

/-- Full actual target contraction continuity for simultaneous shifts of
any subset of branching depths. The target may depend on EVERY schedule
coordinate, so no regularity of a union old/target shape is postulated. -/
theorem averaged_target_schedule_change_le (H d p : ℕ) (hheight : d+H=L)
    (S : ReducedTopology) (η : ℝ) (hlarge : 1<η*(L:ℝ)) (s : S.Vertex → Bool)
    (D : (S.Vertex → Fin L) → Prop)
    (hD : ∀ q, D q → Admissible S (fun v => (q v).val) d L ∧ DepthAverage.Regular η q)
    (T : KernelTower Ω (H+p)) (f : FinitePath Ω (H+p) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1)
    (Target : (S.Vertex → Fin L) → PrescribedTree (H+p))
    (a b : (q : S.Vertex → Fin L) → (Target q).Leaf) :
    DepthAverage.average D (fun q => PrescribedTree.targetContractionChangeSq (Target q) T (a q) (b q)
      (scheduledTailProjection H d p S q T f)
      (scheduledTailProjection H d p S (fun v => DepthAverage.shiftPerm (s v) (q v)) T f)) ≤
      4*((Fintype.card S.Vertex:ℝ)*(∑ v : S.Vertex, (vertexArity S v:ℝ)^2)/(L:ℝ)) := by
  calc
    _ ≤ DepthAverage.average D (fun q => 4*tailScheduleChange H d p S s T f q) := by
      apply DepthAverage.average_mono_on
      intro q _
      exact PrescribedTree.targetContractionChangeSq_le (Target q) T (a q) (b q) _ _
        (scheduledTailProjection_bound H d p S q T f hf)
        (scheduledTailProjection_bound H d p S _ T f hf)
    _ = 4*DepthAverage.average D (tailScheduleChange H d p S s T f) := DepthAverage.average_mul_left _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (averaged_tailScheduleChange_le H d p hheight S η hlarge s D hD T f hf) (by norm_num)

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
