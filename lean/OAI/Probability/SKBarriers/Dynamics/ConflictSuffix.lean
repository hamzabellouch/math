import Mathlib
import OAI.Probability.SKBarriers.Locking.SignedLocking
import OAI.Probability.SKBarriers.Locking.OverlapPacking
import OAI.Probability.SKBarriers.Dynamics.ProtectedBlock

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem signed_locking_of_not_mem {n : ℕ} (v x y : Config n) (h b : ℝ)
    (hq : h≤overlap x y) (hx : |overlap v x|≤b) (hy : |overlap v y|≤b)
    (havoid : (![v,x,y] : ReplicaConfig n 3)∉signedLockingSet n h b) :
    |overlap v x-overlap v y|≤2*(n:ℝ)^(-(1:ℝ)/100) := by
  classical
  by_contra H
  apply havoid
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,hq,hx,hy,lt_of_not_ge H⟩

theorem magnitude_locking_of_signed_avoid {n : ℕ} (v x y : Config n) (h b : ℝ)
    (hq : h≤|overlap x y|) (hx : |overlap v x|≤b) (hy : |overlap v y|≤b)
    (havoid : (![v,x,y] : ReplicaConfig n 3)∉signedLockingSet n h b)
    (havoid' : (![v,x,flip y] : ReplicaConfig n 3)∉signedLockingSet n h b) :
    abs (|overlap v x|-|overlap v y|)≤2*(n:ℝ)^(-(1:ℝ)/100) := by
  by_cases hp : 0≤overlap x y
  · exact (abs_abs_sub_abs_le_abs_sub _ _).trans
      (signed_locking_of_not_mem v x y h b (by simpa only [abs_of_nonneg hp] using hq) hx hy havoid)
  · have H := signed_locking_of_not_mem v x (flip y) h b
      (by simpa only [overlap_flip_right,abs_of_neg (lt_of_not_ge hp)] using hq)
      hx (by simpa only [overlap_flip_right,abs_neg] using hy) havoid'
    simpa only [overlap_flip_right,abs_neg] using (abs_abs_sub_abs_le_abs_sub _ _).trans H

theorem conflicts_are_suffix {n : ℕ} (A : Finset ℕ) (v : ℕ → Config n) (w : Config n)
    (r : ℕ → ℝ) (b b' t E F ρ : ℝ)
    (_hE : 0≤E) (ht : 0≤t) (hsmall : 2*t+E+F<b')
    (hsep : 2*E+2*F<3*ρ)
    (hr : ∀ i∈A,r i∈Icc t (2*t))
    (hspacing : ∀ i∈A,∀ j∈A,i<j → 3*ρ≤r j-r i)
    (hold : ∀ i∈A,∀ j∈A,i<j → |overlap (v i) (v j)-r i|≤E)
    (htransfer : ∀ i∈A,|overlap (v i) w|≤b → |overlap (v i) w-r i|≤E+F)
    (hlock : ∀ i∈A,∀ j∈A,i<j → b< |overlap (v i) w| →
      |overlap (v j) (v i)|≤b' → |overlap (v j) w|≤b' →
      abs (|overlap (v j) (v i)|-|overlap (v j) w|)≤F)
    (hF : 0≤F) :
    IsRetainedSuffix A (A.filter (fun i => b< |overlap (v i) w|)) := by
  classical
  constructor
  · exact Finset.filter_subset _ _
  · intro i j hi hj hij
    have hi' := (Finset.mem_filter.mp hi).1
    have hb := (Finset.mem_filter.mp hi).2
    by_cases hij' : i=j
    · simpa [hij'] using hi
    · have hijlt : i<j := lt_of_le_of_ne hij hij'
      by_contra h
      have hjc : |overlap (v j) w|≤b := by
        simpa only [Finset.mem_filter,hj,true_and,not_lt] using h
      have HO := hold i hi' j hj hijlt
      rw [overlap_comm (v i) (v j)] at HO
      have HN := htransfer j hj hjc
      have hri : 0≤r i := ht.trans (hr i hi').1
      have hrj : 0≤r j := ht.trans (hr j hj).1
      have HOA : abs (|overlap (v j) (v i)|-r i)≤E := by
        simpa only [abs_of_nonneg hri] using (abs_abs_sub_abs_le_abs_sub _ _).trans HO
      have HNA : abs (|overlap (v j) w|-r j)≤E+F := by
        simpa only [abs_of_nonneg hrj] using (abs_abs_sub_abs_le_abs_sub _ _).trans HN
      have hbi : |overlap (v j) (v i)|≤b' := by
        linarith only [(abs_le.mp HOA).2,(hr i hi').2,hsmall,hF]
      have hbj : |overlap (v j) w|≤b' := by
        linarith only [(abs_le.mp HNA).2,(hr j hj).2,hsmall]
      have HL := hlock i hi' j hj hijlt hb hbi hbj
      linarith only [(abs_le.mp HOA).2,(abs_le.mp HNA).1,(abs_le.mp HL).1,
        hspacing i hi' j hj hijlt,hsep]

theorem conflict_filter_card {n : ℕ} (hn : 0<n) (A : Finset ℕ)
    (v : ℕ → Config n) (w : Config n) (b e : ℝ)
    (hb : 0<b) (he : 0≤e) (heb : e<b^2/2)
    (hpair : ∀ i∈A,∀ j∈A,i≠j → |overlap (v i) (v j)|≤e) :
    (A.filter (fun i => b< |overlap (v i) w|)).card≤⌈2/b^2⌉₊ := by
  classical
  have H := overlap_conflict_card hn (A.filter (fun i => b< |overlap (v i) w|)) v w b e hb he heb
    (fun i hi j hj hij => hpair i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  exact_mod_cast H.le.trans (Nat.le_ceil (2/b^2))

end SK.Analytic

end
end

end OAI
