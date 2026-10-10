import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.OnlineSample
import OAI.Combinatorics.MatchingCount.Complexity.OnlineWordCost
import OAI.Combinatorics.MatchingCount.Complexity.OnlineTraverseCost

namespace OAI

namespace MatchingFPRAS.OnlineSample
open TreeTyped PhysicalStream Polynomial

variable {A B : Type} [Codec A] [Codec B]
lemma work_repeatInput : TreeTyped.WorkBound (repeatInputRealizer (A:=A)) (fun x=>x.1+weight x) := by
  unfold repeatInputRealizer
  apply TreeTyped.work_congr
  apply TreeTyped.work_then_polynomial _ (polynomial_mapWith polynomial_first)
  apply TreeTyped.work_pair _ _ X (by intro x; simp only [Polynomial.eval_X];omega)
  · exact TreeTyped.work_of_polynomial polynomial_second X (fun x=>by simp only [Polynomial.eval_X];omega)
  · apply TreeTyped.work_composition
      (TreeTyped.work_of_polynomial polynomial_first X (fun x=>by simp only [Polynomial.eval_X];omega))
      range_numeric_work X
    intro x
    simp only [Polynomial.eval_X,id_eq]
    omega

def mass (m : A→ℕ) (as : List A) : ℕ := weight as+(as.map m).sum
lemma weight_le_mass (m : A→ℕ) (as : List A) : weight as ≤ mass m as := Nat.le_add_right _ _
lemma mass_mem (m : A→ℕ) (as : List A) (a : A) (ha : a∈as) : m a ≤ mass m as :=
  by
  have h : m a ≤ (as.map m).sum := by
    induction as with
    | nil => simp at ha
    | cons b bs ih =>
      simp only [List.mem_cons] at ha
      simp only [List.map_cons,List.sum_cons]
      rcases ha with rfl | ha
      · omega
      · have := ih ha;omega
  unfold mass;omega
lemma weight_replicate (n : ℕ) (a : A) : weight (List.replicate n a)=n*(1+weight a)+1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ,weight_cons,ih,Nat.succ_mul];omega
lemma mass_replicate (m : A→ℕ) (n : ℕ) (a : A) :
    mass m (List.replicate n a)=n*(1+weight a+m a)+1 := by
  simp only [mass,weight_replicate,List.map_replicate,List.sum_replicate,Nat.nsmul_eq_mul]
  ring
lemma work_traverse_mass {f : A→Experiment B} {F : OnlineTree.Realizer f} {m : A→ℕ}
    (hF : OnlineTree.WorkBound F m) : OnlineTree.WorkBound (OnlineTree.traverse F) (mass m) :=
  OnlineTree.work_traverse hF X X (by intro as;simpa using weight_le_mass m as)
    (by intro as a ha;simpa using mass_mem m as a ha)

def repeatMeasure (m : A→ℕ) (x : ℕ×A) : ℕ := x.1+weight x+m x.2
lemma work_repeat {f : A→Experiment B} {F : OnlineTree.Realizer f} {m : A→ℕ}
    (hF : OnlineTree.WorkBound F m) : OnlineTree.WorkBound
      (OnlineTree.composition (OnlineTree.deterministic repeatInputRealizer) (OnlineTree.traverse F))
      (repeatMeasure m) := by
  apply OnlineTree.work_composition
    (OnlineTree.work_deterministic (TreeTyped.work_remeasure work_repeatInput X
      (fun x=>by simp only [Polynomial.eval_X,repeatMeasure];omega))) (work_traverse_mass hF) (X*(X+1)+1)
  intro x
  change mass m (List.replicate x.1 x.2) ≤ _
  rw [mass_replicate]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one]
  have hx : x.1 ≤ repeatMeasure m x := by unfold repeatMeasure;omega
  have hw : weight x.2+m x.2 ≤ repeatMeasure m x := by
    have := weight_snd x;unfold repeatMeasure;omega
  nlinarith

def pairMeasure (x : ℕ×ℕ) : ℕ := x.1+x.2+weight x
lemma work_firstWord : OnlineTree.WorkBound
    (OnlineTree.composition (OnlineTree.deterministic (TreeTyped.first (A:=ℕ) (B:=ℕ))) OnlineWord.naturalRealizer)
    pairMeasure := by
  apply OnlineTree.work_composition
    (OnlineTree.work_deterministic (TreeTyped.work_of_polynomial polynomial_first X
      (fun x=>by simp [pairMeasure]))) OnlineWord.work_natural X
  intro x
  change x.1+weight x.1 ≤ _
  simp only [Polynomial.eval_X,pairMeasure]
  have := weight_fst x
  omega
lemma work_words : OnlineTree.WorkBound wordsRealizer pairMeasure := by
  unfold wordsRealizer
  apply OnlineTree.work_congr
  apply OnlineTree.work_composition
    (OnlineTree.work_deterministic (TreeTyped.work_composition
      (TreeTyped.work_of_polynomial (polynomial_pair polynomial_second polynomial_first) X
        (fun x=>by simp [pairMeasure])) work_repeatInput (2*X+1) (by
          intro x;simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
            Polynomial.eval_one]
          simp only [pairMeasure,weight_prod];have := weight_fst x;have := weight_snd x;omega)))
    (work_traverse_mass OnlineWord.work_natural) (X*(2*X+1)+1)
  intro x
  change mass (fun n=>n+weight n) (List.replicate x.2 x.1) ≤ _
  rw [mass_replicate]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
  have h1 : x.2 ≤ pairMeasure x := by unfold pairMeasure;omega
  have h2 : weight x.1+x.1+weight x.1 ≤ 2*pairMeasure x := by have := weight_fst x;unfold pairMeasure;omega

  have h := Nat.mul_le_mul h1 (show 1+weight x.1+(x.1+weight x.1) ≤ 2*pairMeasure x+1 by omega)
  nlinarith
lemma work_local : OnlineTree.WorkBound localRealizer pairMeasure := by
  unfold localRealizer
  exact OnlineTree.work_pair work_firstWord work_words X (fun x=>by simp [pairMeasure])
lemma work_scan : OnlineTree.WorkBound scanRealizer pairMeasure := by
  unfold scanRealizer
  exact OnlineTree.work_pair work_firstWord work_local X (fun x=>by simp [pairMeasure])

def scansMeasure (x : (ℕ×ℕ)×ℕ) : ℕ := pairMeasure x.1+x.2+weight x
lemma work_scans : OnlineTree.WorkBound scansRealizer scansMeasure := by
  unfold scansRealizer
  apply OnlineTree.work_congr
  apply OnlineTree.work_composition
    (OnlineTree.work_deterministic (TreeTyped.work_composition
      (TreeTyped.work_of_polynomial (polynomial_pair polynomial_second polynomial_first) X
        (fun x=>by simp [scansMeasure])) work_repeatInput (2*X+1) (by
          intro x
          simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
          simp only [scansMeasure,weight_prod]
          have := weight_fst x;have := weight_snd x;omega)))
    (work_traverse_mass work_scan) (X*(2*X+1)+1)
  intro x
  change mass pairMeasure (List.replicate x.2 x.1) ≤ _
  rw [mass_replicate]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
  have h1 : x.2 ≤ scansMeasure x := by unfold scansMeasure;omega
  have h2 : weight x.1+pairMeasure x.1 ≤ 2*scansMeasure x := by
    have := weight_fst x;unfold scansMeasure;omega
  have h := Nat.mul_le_mul h1 (show 1+weight x.1+pairMeasure x.1 ≤ 2*scansMeasure x+1 by omega)
  omega

def markMeasure (x : ℕ×ℕ) : ℕ := x.2+weight x
lemma work_markWord : OnlineTree.WorkBound markWordRealizer markMeasure := by
  apply OnlineTree.work_mapSecond OnlineWord.work_natural X X
  · intro x;simp only [Polynomial.eval_X,markMeasure];have := weight_snd x;omega
  · intro x;simp only [Polynomial.eval_X,markMeasure];have := weight_fst x;omega
omit [Codec A] in
lemma sum_map_le (m : A→ℕ) (as : List A) (M : ℕ) (h : ∀ a∈as,m a ≤ M) :
    (as.map m).sum ≤ as.length*M := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun a ha=>h a (by simp [ha]))
    simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.add_mul,Nat.one_mul]
    omega
lemma mass_le (m : A→ℕ) (as : List A) (M : ℕ) (hw : weight as ≤ M) (h : ∀ a∈as,m a ≤ M) :
    mass m as ≤ M*(M+1) := by
  have h1 := sum_map_le m as M h
  have h2 := Nat.mul_le_mul_right M ((list_length_le_weight as).trans hw)
  unfold mass
  nlinarith

def marksMeasure (x : ℕ×List ℕ) : ℕ := x.1+weight x
lemma work_marks : OnlineTree.WorkBound marksRealizer marksMeasure := by
  have hp : TreeTyped.PolynomialTime markRequestsRealizer := polynomial_congr _
    (polynomial_mapWith (polynomial_pair polynomial_second polynomial_first))
  obtain ⟨p,hp'⟩ := hp
  have hp : TreeTyped.PolynomialTime markRequestsRealizer := ⟨p,hp'⟩
  apply OnlineTree.work_composition
    (OnlineTree.work_deterministic (TreeTyped.work_of_polynomial hp X (fun x=>by simp [marksMeasure])))
    (work_traverse_mass work_markWord) ((p+X)*((p+X)+1))
  intro x
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one]
  apply mass_le
  · have hw : weight (markRequests x) ≤ p.eval (marksMeasure x) :=
      (Nat.le_add_left _ _).trans ((hp' x).trans (polynomial_eval_monotone p (by unfold marksMeasure;omega)))
    omega
  · intro a ha
    have hw := weight_mem ha
    have hb : weight (markRequests x) ≤ p.eval (marksMeasure x) :=
      (Nat.le_add_left _ _).trans ((hp' x).trans (polynomial_eval_monotone p (by unfold marksMeasure;omega)))
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    unfold marksMeasure at hb
    unfold markMeasure marksMeasure
    dsimp only
    omega

def requestMeasure (x : Request) : ℕ := scansMeasure x.1+marksMeasure x.2+weight x
lemma work_sample : OnlineTree.WorkBound sampleRealizer requestMeasure := by
  unfold sampleRealizer
  apply OnlineTree.work_pair _ _ X (fun x=>by simp [requestMeasure])
  · apply OnlineTree.work_composition
      (OnlineTree.work_deterministic (TreeTyped.work_of_polynomial polynomial_first X
        (fun x=>by simp [requestMeasure]))) work_scans X
    intro x
    simp only [Experiment.All,Polynomial.eval_X]
    unfold requestMeasure;omega
  · apply OnlineTree.work_composition
      (OnlineTree.work_deterministic (TreeTyped.work_of_polynomial polynomial_second X
        (fun x=>by simp [requestMeasure]))) work_marks X
    intro x
    simp only [Experiment.All,Polynomial.eval_X]
    unfold requestMeasure;omega
lemma work_many : OnlineTree.WorkBound manyRealizer (repeatMeasure requestMeasure) := work_repeat work_sample
end MatchingFPRAS.OnlineSample

end OAI
