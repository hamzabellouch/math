import OAI.Combinatorics.ContingencyTables.Machines.FairBits
import OAI.Combinatorics.MatchingCount.Complexity.OnlineWordCost

namespace OAI

/-! # Executing a computed finite Boolean sampler

The program reads a fresh word on the physical online machine, preserves
the input, and runs the deterministic binary sampler on that word.
-/

namespace ContingencyTables.FiniteWordExecution
open MatchingFPRAS MatchingFPRAS.PhysicalStream Polynomial

variable {A B : Type} [TreeTyped.Codec A] [TreeTyped.Codec B]

def source (n : A → ℕ) (a : A) : Experiment (List Bool) := OnlineWord.prepend (n a) []

noncomputable def sourceRealizer {n : A → ℕ} (N : TreeTyped.Realizer n) :
    OnlineTree.Realizer (source n) :=
  (OnlineTree.composition (OnlineTree.deterministic N) OnlineWord.naturalRealizer).congr
    (by intro a g; rfl)

def wordMeasure (n : A → ℕ) (a : A) : ℕ := TreeTyped.weight a+n a

theorem work_source {n : A → ℕ} {N : TreeTyped.Realizer n}
    (hN : TreeTyped.PolynomialTime N) :
    OnlineTree.WorkBound (sourceRealizer N) (wordMeasure n) := by
  unfold sourceRealizer
  apply OnlineTree.work_congr
  have hN' : OnlineTree.WorkBound (OnlineTree.deterministic N) (wordMeasure n) :=
    OnlineTree.work_of_polynomial (OnlineTree.polynomial_deterministic hN) X (by
      intro a
      simp only [eval_X,wordMeasure]
      omega)
  apply OnlineTree.work_composition hN' OnlineWord.work_natural (5*X+1)
  intro a
  change n a+TreeTyped.weight (n a)≤(5*X+1).eval (wordMeasure n a)
  have hw := TreeTyped.weight_nat_numeric (n a)
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one,wordMeasure]
  omega

def experiment (n : A → ℕ) (f : A×List Bool → B) (a : A) : Experiment B :=
  (source n a).map (fun bs => f (a,bs))

noncomputable def realizer {n : A → ℕ} {f : A×List Bool → B}
    (N : TreeTyped.Realizer n) (F : TreeTyped.Realizer f) : OnlineTree.Realizer (experiment n f) :=
  (OnlineTree.composition
    (OnlineTree.pair (OnlineTree.deterministic TreeTyped.identity) (sourceRealizer N))
    (OnlineTree.deterministic F)).congr (by
      intro a g
      simp only [Experiment.mean_bind,Experiment.mean,Experiment.mean_map,experiment,id_eq])

/-- Runtime is polynomial in the input's encoded size plus the number of
fresh bits. -/
theorem work_realizer {n : A → ℕ} {f : A×List Bool → B}
    {N : TreeTyped.Realizer n} {F : TreeTyped.Realizer f}
    (hN : TreeTyped.PolynomialTime N) (hF : TreeTyped.PolynomialTime F) :
    OnlineTree.WorkBound (realizer N F) (wordMeasure n) := by
  unfold realizer
  apply OnlineTree.work_congr
  apply OnlineTree.work_then_polynomial _ (OnlineTree.polynomial_deterministic hF)
  have hid : OnlineTree.WorkBound (OnlineTree.deterministic (TreeTyped.identity (A := A)))
      (wordMeasure n) :=
    OnlineTree.work_of_polynomial (OnlineTree.polynomial_deterministic TreeTyped.polynomial_identity) X (by
      intro a
      simp only [eval_X,wordMeasure]
      omega)
  apply OnlineTree.work_pair hid (work_source hN) X
  intro a
  simp only [eval_X,wordMeasure]
  omega

omit [TreeTyped.Codec A] [TreeTyped.Codec B] in

theorem experiment_mean (n : A → ℕ) (f : A×List Bool → B) (a : A) (g : B → ℚ) :
    (experiment n f a).mean g=
      average (fun bits : Bits (n a) => g (f (a,List.ofFn bits))) := by
  unfold experiment source
  rw [Experiment.mean_map,OnlineWord.mean_prepend_nil]

end ContingencyTables.FiniteWordExecution

end OAI
