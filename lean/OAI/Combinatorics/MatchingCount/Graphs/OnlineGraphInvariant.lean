import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineInitial

namespace OAI

namespace MatchingFPRAS.OnlineGraph
open TreeTyped TreeFraction ExecutableAdaptive ExecutableScaling ExecutableSource
open PhysicalStream OnlineSchedule

abbrev Edges := List (ℕ×ℕ)
variable (f : Edges→Edges) (hf : ∀ es e,e∈f es↔e∈es)
def graph (g : GraphData) : GraphData := (g.1,f g.2)
def data (x : SparseStageData) : SparseStageData :=
  (((graph f x.1.1.1,x.1.1.2),x.1.2),x.2)
def request (x : RequestInput) : RequestInput := (data f x.1,x.2)
def state (x : OnlineTrial.State) : OnlineTrial.State := (request f x.1,x.2)
def seed (x : OnlineInitial.Seed) : OnlineInitial.Seed := (graph f x.1,x.2)
include hf
lemma stageCell (es : Edges) (q : Fraction) (v : Vector) (ij : (ℕ×ℕ)) :
    ExecutableAdaptive.stageCell (((f es,q),v),ij)=ExecutableAdaptive.stageCell (((es,q),v),ij) := by
  simp only [ExecutableAdaptive.stageCell,rawCell,hf]
lemma stageRow (es : Edges) (q : Fraction) (v : Vector) (vs : List ℕ) (i : ℕ) :
    ExecutableAdaptive.stageRow ((((f es,q),v),vs),i)=ExecutableAdaptive.stageRow ((((es,q),v),vs),i) := by
  unfold ExecutableAdaptive.stageRow
  simp only [stageCell f hf]
lemma stageMatrix (g : GraphData) (fuel : List Bool) (v : Vector) :
    ExecutableAdaptive.stageMatrix ((graph f g,fuel),v)=ExecutableAdaptive.stageMatrix ((g,fuel),v) := by
  unfold ExecutableAdaptive.stageMatrix cellData graph
  simp only [stageRow f hf]
lemma current (x : SparseStageData) : sparseCurrentMatrix (data f x)=sparseCurrentMatrix x := by
  exact stageMatrix f hf x.1.1.1 x.1.1.2 x.2
lemma next (x : SparseStageData) : sparseNextMatrix (data f x)=sparseNextMatrix x := by
  exact stageMatrix f hf x.1.1.1 (false::x.1.1.2) x.2
lemma bag (x : SparseStageData) : sparseBagInput (data f x)=sparseBagInput x := by
  unfold sparseBagInput
  rw [current f hf]
  rfl
lemma generated (x : SparseStageData) : sparseGeneratedInput (data f x)=sparseGeneratedInput x := by
  unfold sparseGeneratedInput
  rw [bag f hf]
  rfl
lemma update (x : SparseStageData) : sparseUpdateData (data f x)=sparseUpdateData x := by
  unfold sparseUpdateData
  rw [generated f hf,next f hf]
  rfl
lemma stage (x : SparseStageData) (bs : List NumericMarking.SampleBits) :
    sparseStage (data f x,bs)=sparseStage (x,bs) := by
  unfold sparseStage
  rw [update f hf]
lemma certificateMatrix (g : GraphData) (v : Vector) :
    ExecutableSource.certificateMatrix (graph f g,v)=ExecutableSource.certificateMatrix (g,v) := by
  unfold ExecutableSource.certificateMatrix certificateCellData graph
  simp only [stageRow f hf]
lemma certificate (x : SparseStageData) (b : NumericMarking.SampleBits) :
    sparseCertificate (data f x,b)=sparseCertificate (x,b) := by
  unfold sparseCertificate sparseCertificateData sparseCertificateMatrixArg
  rw [generated f hf]
  change generatedCertificate ((_,ExecutableSource.certificateMatrix (graph f x.1.1.1,x.2)),b)=_
  rw [certificateMatrix f hf]
lemma sourcePrecision (x : RequestInput) : OnlineSchedule.sourcePrecision (request f x)=OnlineSchedule.sourcePrecision x := by
  unfold OnlineSchedule.sourcePrecision request
  rw [bag f hf]
  rfl
lemma sourceRequest (x : RequestInput) : OnlineSchedule.sourceRequest (request f x)=OnlineSchedule.sourceRequest x := by
  unfold OnlineSchedule.sourceRequest
  rw [sourcePrecision f hf]
  change (_,(_,List.range ((sourceTables (sparseBagInput (data f x.1))).1.length)))=_
  rw [bag f hf]

omit hf in
lemma carry (_ : ∀ edges edge,edge∈f edges↔edge∈edges)
    (x : OnlineTrial.State) (y : Fraction×Vector) :
    OnlineTrial.carry (state f x,y)=state f (OnlineTrial.carry (x,y)) := rfl
lemma step_mean (x : OnlineTrial.State) (h : OnlineTrial.State→ℚ) :
    (OnlineTrial.step (state f x)).mean h=(OnlineTrial.step x).mean (h ∘ state f) := by
  unfold OnlineTrial.step OnlineTrial.prepare OnlineStage.execute
  simp only [Experiment.mean_map]
  change (OnlineSample.many (x.1.2,OnlineSchedule.sourceRequest (request f x.1))).mean
    (fun bs=>h (OnlineTrial.carry (state f x,sparseStage (data f x.1.1,bs))))=_
  rw [sourceRequest f hf]
  simp only [stage f hf,carry f hf,Function.comp_apply]
lemma fold_mean (as : List Bool) (x : OnlineTrial.State) (h : OnlineTrial.State→ℚ) :
    (OnlineTree.foldM OnlineTrial.body as (state f x)).mean h=
      (OnlineTree.foldM OnlineTrial.body as x).mean (h ∘ state f) := by
  induction as generalizing x h with
  | nil => rfl
  | cons a as ih =>
    simp only [OnlineTree.foldM,OnlineTrial.body,Experiment.mean_bind]
    rw [step_mean f hf]
    change (OnlineTrial.step x).mean (fun y=>(OnlineTree.foldM OnlineTrial.body as (state f y)).mean h)=_
    simp_rw [ih]
lemma checked_mean (x : OnlineTrial.State) (h : Fraction→ℚ) :
    (OnlineGuard.checked (state f x)).mean h=(OnlineGuard.checked x).mean h := by
  unfold OnlineGuard.checked OnlineGuard.test
  simp only [Experiment.mean_map]
  change (OnlineSample.many (16,OnlineSchedule.sourceRequest (request f x.1))).mean
    (fun bs=>h (OnlineGuard.finish (x.2,OnlineGuard.accept (data f x.1.1,bs))))=_
  rw [sourceRequest f hf]
  unfold OnlineGuard.accept
  simp only [certificate f hf]
lemma trial_mean (as : List Bool) (x : OnlineTrial.State) (h : Fraction→ℚ) :
    (OnlineGuard.trial (as,state f x)).mean h=(OnlineGuard.trial (as,x)).mean h := by
  unfold OnlineGuard.trial OnlineTrial.sweep
  simp only [Experiment.mean_bind]
  rw [fold_mean f hf]
  change (OnlineTree.foldM OnlineTrial.body as x).mean (fun y=>(OnlineGuard.checked (state f y)).mean h)=_
  simp_rw [checked_mean f hf]
lemma trials_mean (r : ℕ) (as : List Bool) (x : OnlineTrial.State) (h : List Fraction→ℚ) :
    (OnlineAmplification.trials (r,(as,state f x))).mean h=(OnlineAmplification.trials (r,(as,x))).mean h := by
  unfold OnlineAmplification.trials
  induction r generalizing h with
  | zero => rfl
  | succ r ih =>
    simp only [List.replicate_succ,OnlineTree.traverseM,Experiment.mean_bind,Experiment.mean_map]
    rw [trial_mean f hf]
    simp_rw [ih]
lemma run_mean (r : ℕ) (as : List Bool) (x : OnlineTrial.State) (h : Fraction→ℚ) :
    (OnlineAmplification.run (r,(as,state f x))).mean h=(OnlineAmplification.run (r,(as,x))).mean h := by
  unfold OnlineAmplification.run
  simp only [Experiment.mean_map]
  exact trials_mean f hf r as x _
omit hf in
lemma initialize_eq (x : OnlineInitial.Seed) :
    OnlineInitial.initializeInput (seed f x)=
      ((OnlineInitial.initializeInput x).1,((OnlineInitial.initializeInput x).2.1,state f (OnlineInitial.initializeInput x).2.2)) := rfl
lemma initialize_mean (x : OnlineInitial.Seed) (h : Fraction→ℚ) :
    (OnlineAmplification.run (OnlineInitial.initializeInput (seed f x))).mean h=
      (OnlineAmplification.run (OnlineInitial.initializeInput x)).mean h := by
  rw [initialize_eq]
  exact run_mean f hf _ _ _ h
end MatchingFPRAS.OnlineGraph

end OAI
