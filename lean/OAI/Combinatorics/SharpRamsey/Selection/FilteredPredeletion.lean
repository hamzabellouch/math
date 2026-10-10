import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.PredeletionMean

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k)
local instance filtFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance filtBlockDec : DecidableEq (Block w) := Classical.decEq _

lemma filteredPopulation_loss
    (z : (model w n k p θ G t).FreshHistory)
    (bad : Finset ((model w n k p θ G t).Index z.1))
    (live : Finset (Fin w)) (keep : Fin w→Prop) [DecidablePred keep] :
    (∑ i∈live,(goodMiddle w n k p θ G t z bad i).card) ≤
      (∑ i∈live.filter keep,(goodMiddle w n k p θ G t z bad i).card)+
        (2*(n+k))*(live.filter (fun i=>¬keep i)).card := by
  rw [←sum_filter_add_sum_filter_not live keep]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ i∈live.filter (fun i=>¬keep i),2*(n+k) := by
      apply sum_le_sum
      intro i _
      simpa only [Fintype.card_fin] using card_le_univ (goodMiddle w n k p θ G t z bad i)
    _ = _ := by simp [Nat.mul_comm]

lemma filtered_predeletion_mean (hkn : k≤n)
    (hp : ∀ z,0<(model w n k p θ G t).remaining z)
    (bad : ∀ z : (model w n k p θ G t).FreshHistory,Finset ((model w n k p θ G t).Index z.1))
    (keep : (model w n k p θ G t).FreshHistory→Fin w→Prop)
    (B ε : ℝ)
    (hbad : (∑ z,((model w n k p θ G t).freshLaw hp).mass z*((bad z).card:ℝ))≤B)
    (hrep : (n:ℝ)*(∑ z,((model w n k p θ G t).freshLaw hp).mass z*
      (((model w n k p θ G t).freshSelected z∩bad z).card:ℝ))≤B)
    (hdrop : ∀ z,((model w n k p θ G t).freshLaw hp).mass z≠0→
      (((univ\badWindows ((model w n k p θ G t).representative z) (bad z)).filter
        (fun i=>¬keep z i)).card:ℝ)≤ε*w) :
    (∑ z,((model w n k p θ G t).freshLaw hp).mass z*
      ((w*(2*(n+k)):ℝ)-(∑ i∈(univ\badWindows ((model w n k p θ G t).representative z) (bad z)).filter (keep z),
        (goodMiddle w n k p θ G t z (bad z) i).card:ℕ)))≤5*B+(w*(2*(n+k)):ℝ)*ε := by
  classical
  let M:=model w n k p θ G t
  let live:=fun z=>univ\badWindows (M.representative z) (bad z)
  have hpnt (z : M.FreshHistory) (hz : (M.freshLaw hp).mass z≠0) :
      ((w*(2*(n+k)):ℝ)-(∑ i∈(live z).filter (keep z),
        (goodMiddle w n k p θ G t z (bad z) i).card:ℕ))≤
      (w*(2*(n+k)):ℝ)-(∑ i∈live z,(goodMiddle w n k p θ G t z (bad z) i).card:ℕ)+
        (w*(2*(n+k)):ℝ)*ε := by
    have hh := (Nat.cast_le (α:=ℝ)).mpr (filteredPopulation_loss w n k p θ G t z (bad z) (live z) (keep z))
    push_cast at hh
    have hd:=mul_le_mul_of_nonneg_left (hdrop z hz) (show (0:ℝ)≤2*((n:ℝ)+k) by positivity)
    dsimp only [live] at hh ⊢
    push_cast
    nlinarith
  calc
    _ ≤ ∑ z,(M.freshLaw hp).mass z*((w*(2*(n+k)):ℝ)-
        (∑ i∈live z,(goodMiddle w n k p θ G t z (bad z) i).card:ℕ)+(w*(2*(n+k)):ℝ)*ε) := by
      apply sum_le_sum
      intro z _
      by_cases hs : (M.freshLaw hp).mass z=0
      · dsimp only [M] at hs ⊢
        simp only [hs,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (hpnt z hs) ((M.freshLaw hp).nonneg z)
    _ = (∑ z,(M.freshLaw hp).mass z*((w*(2*(n+k)):ℝ)-
        (∑ i∈live z,(goodMiddle w n k p θ G t z (bad z) i).card:ℕ)))+(w*(2*(n+k)):ℝ)*ε := by
      simp only [mul_add,sum_add_distrib,←sum_mul,(M.freshLaw hp).total,one_mul]
    _ ≤ _ := add_le_add (bad_predeletion_five w n k p θ G t hkn hp bad B hbad hrep) le_rfl
end
end SharpLogRamsey.Selection.Windows

end

end OAI
