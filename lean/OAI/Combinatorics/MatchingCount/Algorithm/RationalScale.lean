import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Endpoints
import OAI.Combinatorics.MatchingCount.Tapes.RunBits

namespace OAI

namespace MatchingFPRAS.Counting
open Finset

variable {n : ℕ}
lemma rowMaximum_cast (hn : 2≤n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ) (i : Fin n) :
    (rowMaximum hn G v i:ℝ)=RealStage.rowMaximum hn (fun i j=>(G i j:ℝ)) (fun i=>(v i:ℝ)) i := by
  unfold rowMaximum RealStage.rowMaximum
  rw [Finset.apply_sup'_eq_sup'_comp _ (fun q : ℚ=>(q:ℝ)) (by intro a b; exact Rat.cast_max a b)]
  simp only [Function.comp_apply,Rat.cast_div]
lemma scaleUpdate_cast (hn : 2≤n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ) (i j : Fin n) :
    (scaleUpdate hn G v i j:ℝ)=RealStage.scaleUpdate hn (fun i j=>(G i j:ℝ)) (fun i=>(v i:ℝ)) i j := by
  by_cases h : j=i
  · subst j
    simp only [scaleUpdate,RealStage.scaleUpdate,Function.update_self,rowMaximum_cast]
  · simp only [scaleUpdate,RealStage.scaleUpdate,Function.update_of_ne h]
lemma scalingTrace_cast (hn : 2≤n) (G : Fin n → Fin n → ℚ) (k : ℕ) (i : Fin n) :
    (scalingTrace hn G k i:ℝ)=RealStage.scalingTrace hn (fun i j=>(G i j:ℝ)) k i := by
  induction k generalizing i with
  | zero => norm_num [scalingTrace,RealStage.scalingTrace]
  | succ k ih =>
    simp only [scalingTrace,RealStage.scalingTrace]
    split_ifs with h
    · rw [scaleUpdate_cast]
      have hi : (fun j=>(Counting.scalingTrace hn G k j:ℝ))=RealStage.scalingTrace hn (fun i j=>(G i j:ℝ)) k := by
        funext j
        exact ih j
      rw [hi]
    · exact ih i
lemma ratioEstimate_cast (a d : ℚ) :
    (ratioEstimate a d:ℝ)=RealStage.ratioEstimate a d := by
  simp only [ratioEstimate,RealStage.ratioEstimate]
  have hp : (0:ℝ)<a ↔ (0:ℚ)<a := by exact_mod_cast Iff.rfl
  simp only [hp]
  split_ifs <;> push_cast <;> rfl
lemma upperEstimate_cast (D : ℕ) (d z : ℚ) :
    (upperEstimate D d z:ℝ)=RealStage.upperEstimate D d z := by
  simp only [upperEstimate,RealStage.upperEstimate]
  have hp : (0:ℝ)<d ↔ (0:ℚ)<d := by exact_mod_cast Iff.rfl
  simp only [hp]
  split_ifs <;> push_cast <;> norm_num [alpha,RealStage.alpha]
lemma sigma_cast (D K : ℕ) (e : ℚ) : (sigma D K e:ℝ)=RealStage.sigma D K e := by
  simp only [sigma,RealStage.sigma,alpha,RealStage.alpha]
  push_cast
  rfl
end MatchingFPRAS.Counting
namespace MatchingFPRAS.FiniteTrial
open Finset

def cooling (n : ℕ) : ℚ := (1+1/(n:ℚ))⁻¹
lemma cooling_cast (n : ℕ) : (cooling n:ℝ)=Trial.cooling n := by
  simp [cooling,Trial.cooling]

def raw (G : GraphInput) (j : ℕ) (a b : Fin G.n) : ℚ :=
  if (min a b,max a b)∈G.edges then 1 else cooling G.n^j
lemma raw_cast (G : GraphInput) (j : ℕ) (a b : Fin G.n) :
    (raw G j a b:ℝ)=Trial.raw G j a b := by
  unfold raw Trial.raw GraphBridge.rawActivity
  split_ifs <;> simp [cooling_cast]

structure ScaleState (G : GraphInput) (j : ℕ) where
  scale : Fin G.n → ℚ
  positive : ∀ i,0<scale i
  upper : ∀ i,scale i≤2^j

def ScaleState.toReal {G : GraphInput} {j : ℕ} (s : ScaleState G j) : Trial.ScaleState G j where
  scale i:=(s.scale i:ℝ)
  positive i:=by exact_mod_cast s.positive i
  upper i:=by exact_mod_cast s.upper i

def ScaleState.activity {G : GraphInput} {j : ℕ} (s : ScaleState G j) : Fin G.n → Fin G.n → ℚ :=
  fun a b=>raw G j a b*s.scale a*s.scale b

def ScaleState.nextActivity {G : GraphInput} {j : ℕ} (s : ScaleState G j) : Fin G.n → Fin G.n → ℚ :=
  fun a b=>raw G (j+1) a b*s.scale a*s.scale b
lemma ScaleState.activity_cast {G : GraphInput} {j : ℕ} (s : ScaleState G j) :
    (fun a b=>(s.activity a b:ℝ))=s.toReal.activity := by
  funext a b
  simp only [ScaleState.activity,Trial.ScaleState.activity,Rat.cast_mul,raw_cast,ScaleState.toReal]
lemma ScaleState.nextActivity_cast {G : GraphInput} {j : ℕ} (s : ScaleState G j) :
    (fun a b=>(s.nextActivity a b:ℝ))=s.toReal.nextActivity := by
  funext a b
  simp only [ScaleState.nextActivity,Trial.ScaleState.nextActivity,Rat.cast_mul,raw_cast,ScaleState.toReal]
lemma ScaleState.activity_pos {G : GraphInput} {j : ℕ} (s : ScaleState G j) (a b : Fin G.n) :
    0<s.activity a b := by
  have h:=s.toReal.activity_pos a b
  rw [←s.activity_cast] at h
  dsimp only at h
  exact_mod_cast h
lemma ScaleState.nextActivity_pos {G : GraphInput} {j : ℕ} (s : ScaleState G j) (a b : Fin G.n) :
    0<s.nextActivity a b := by
  have h:=s.toReal.nextActivity_pos a b
  rw [←s.nextActivity_cast] at h
  dsimp only at h
  exact_mod_cast h

def initialScaleState (G : GraphInput) (hn : 2≤G.n) : ScaleState G 0 where
  scale _:=Initializer.initialScale G.n
  positive _:=Initializer.initialScale_pos G.n hn
  upper i:=by
    have h:=(Trial.initialScaleState G hn).upper i
    change (Initializer.initialScale G.n:ℝ)≤2^0 at h
    exact_mod_cast h
lemma initialScaleState_cast (G : GraphInput) (hn : 2≤G.n) :
    (initialScaleState G hn).toReal=Trial.initialScaleState G hn := rfl
end MatchingFPRAS.FiniteTrial

end OAI
