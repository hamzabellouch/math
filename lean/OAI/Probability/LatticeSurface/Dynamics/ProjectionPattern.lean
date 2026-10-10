import Mathlib
import OAI.Probability.LatticeSurface.Dynamics.ProjectionPath

namespace OAI

namespace ProjectionComparison

open Set

variable {V E : Type*}

def faceGraph (S : System V E) (F : Finset E) : SimpleGraph V where
  Adj x y := x≠y ∧ ∃ e,e∈F ∧ ((S.left e=x ∧ S.right e=y) ∨ (S.left e=y ∧ S.right e=x))
  symm := ⟨by rintro x y ⟨hne,e,he,hor⟩;exact ⟨hne.symm,e,he,hor.symm⟩⟩
  loopless := ⟨by intro x hx;exact hx.1 rfl⟩

noncomputable def faceComponent [Fintype V] (S : System V E) (F : Finset E) (x : V) : Finset V :=
  by classical exact {y | (faceGraph S F).Reachable x y}.toFinset

noncomputable def faceAverage [Fintype V] (S : System V E) (F : Finset E) (d : V → ℝ) (x : V) : ℝ := by
  classical exact if ∀ p∈S.pins,¬(faceGraph S F).Reachable x p then
    (∑y∈faceComponent S F x,d y)/(faceComponent S F x).card else 0

end ProjectionComparison

namespace ProjectionComparison

open Set MeasureTheory

variable {V E : Type*} [Fintype E]

noncomputable def activePattern (S : System V E) (h : V → ℝ) : Finset E :=
  by classical exact Finset.univ.filter (fun e => h (S.left e)-h (S.right e)=S.cost e)

lemma mem_activePattern (S : System V E) (h : V → ℝ) (e : E) :
    e∈activePattern S h ↔ h (S.left e)-h (S.right e)=S.cost e := by classical simp [activePattern]

lemma faceGraph_pattern (S : System V E) (h : V → ℝ) :
    faceGraph S (activePattern S h)=activeGraph S h := by
  ext x y
  simp only [faceGraph,activeGraph,mem_activePattern]

lemma faceComponent_pattern [Fintype V] (S : System V E) (h : V → ℝ) (x : V) :
    faceComponent S (activePattern S h) x=activeComponent S h x := by
  classical
  simp only [faceComponent,activeComponent,faceGraph_pattern]

lemma measurableSet_activePattern (S : System V E) (H : ℝ → V → ℝ)
    (hc : ∀ x,Continuous (fun t => H t x)) (F : Finset E) :
    MeasurableSet {t | activePattern S (H t)=F} := by
  classical
  have hset : {t | activePattern S (H t)=F} = ⋂ e : E,{t | (H t (S.left e)-H t (S.right e)=S.cost e) ↔ e∈F} := by
    ext t
    simp only [mem_ofPred_eq,mem_iInter]
    exact ⟨fun he e => by rw [← mem_activePattern,he],fun he => Finset.ext fun e => by rw [mem_activePattern];exact he e⟩
  rw [hset]
  apply MeasurableSet.iInter
  intro e
  have hm : MeasurableSet {t | H t (S.left e)-H t (S.right e)=S.cost e} :=
    ((hc (S.left e)).sub (hc (S.right e))).measurable (measurableSet_singleton (S.cost e))
  by_cases he : e∈F
  · simpa only [he,iff_true] using hm
  · simpa only [he,iff_false,Set.compl_ofPred] using hm.compl

noncomputable def patternWeight (S : System V E) (H : ℝ → V → ℝ) (F : Finset E) (t : ℝ) : ℝ :=
  by classical exact if activePattern S (H t)=F then 1 else 0

lemma measurable_patternWeight (S : System V E) (H : ℝ → V → ℝ)
    (hc : ∀ x,Continuous (fun t => H t x)) (F : Finset E) :
    Measurable (patternWeight S H F) := by
  classical
  exact Measurable.ite (measurableSet_activePattern S H hc F) measurable_const measurable_const

lemma intervalIntegrable_patternWeight (S : System V E) (H : ℝ → V → ℝ)
    (hc : ∀ x,Continuous (fun t => H t x)) (F : Finset E) :
    IntervalIntegrable (patternWeight S H F) volume 0 1 := by
  have hi : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1 := intervalIntegrable_const
  apply hi.mono_fun (measurable_patternWeight S H hc F).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  classical
  simp only [patternWeight]
  split_ifs <;> norm_num

lemma sum_patternWeight (S : System V E) (H : ℝ → V → ℝ) (t : ℝ) :
    (∑ F,patternWeight S H F t)=1 := by
  classical
  simp [patternWeight,eq_comm]

lemma sum_patternWeight_mul (S : System V E) (H : ℝ → V → ℝ) (t : ℝ) (a : Finset E → ℝ) :
    (∑ F,patternWeight S H F t*a F)=a (activePattern S (H t)) := by
  classical
  simp [patternWeight,eq_comm]

end ProjectionComparison

end OAI
