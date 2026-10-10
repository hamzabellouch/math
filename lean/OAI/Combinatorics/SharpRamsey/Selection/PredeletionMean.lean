import Mathlib
import OAI.Combinatorics.SharpRamsey.Windows.GoodPopulation

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset ExposureModel
open scoped Classical BigOperators
noncomputable section
variable {Ω Θ β : Type} [Fintype Ω] [Fintype Θ] [Fintype β]
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ) (G : Ω→Slot w (n+k)→β) (t : Fin k)
local instance preFinDec (j : ℕ) : DecidableEq (Fin j) := Classical.decEq _
local instance preBlockDec : DecidableEq (Block w) := Classical.decEq _

lemma bad_predeletion_mean
    (hp : ∀ z,0<(model w n k p θ G t).remaining z)
    (bad : ∀ z : (model w n k p θ G t).FreshHistory,Finset ((model w n k p θ G t).Index z.1)) :
    (∑ z,((model w n k p θ G t).freshLaw hp).mass z*
      ((w*(2*(n+k)):ℝ)-(∑ i∈univ\badWindows ((model w n k p θ G t).representative z) (bad z),
        (goodMiddle w n k p θ G t z (bad z) i).card:ℕ)))≤
      (∑ z,((model w n k p θ G t).freshLaw hp).mass z*((bad z).card:ℝ))+
      (2*(n+k):ℕ)*(∑ z,((model w n k p θ G t).freshLaw hp).mass z*
        (((model w n k p θ G t).freshSelected z∩bad z).card:ℝ)) := by
  let M:=model w n k p θ G t
  have hpnt (z : M.FreshHistory) :
      ((w*(2*(n+k)):ℝ)-(∑ i∈univ\badWindows (M.representative z) (bad z),
        (goodMiddle w n k p θ G t z (bad z) i).card:ℕ))≤
      ((bad z).card:ℝ)+((badWindows (M.representative z) (bad z)).card:ℝ)*(2*(n+k):ℕ) := by
    have hh:=goodPopulation_predeletion w n k p θ G t z (bad z) (badWindows (M.representative z) (bad z))
    have hh' := (Nat.cast_le (α:=ℝ)).mpr hh
    push_cast at hh'
    change (w:ℝ)*(2*((n:ℝ)+(k:ℝ)))≤
      (∑ i∈univ\badWindows (M.representative z) (bad z),
        ((goodMiddle w n k p θ G t z (bad z) i).card:ℝ))+
        ((bad z).card:ℝ)+((badWindows (M.representative z) (bad z)).card:ℝ)*(2*((n:ℝ)+(k:ℝ))) at hh'
    push_cast
    linarith

  calc
    _ ≤ ∑ z,(M.freshLaw hp).mass z*(((bad z).card:ℝ)+
        ((badWindows (M.representative z) (bad z)).card:ℝ)*(2*(n+k):ℕ)) :=
      sum_le_sum (fun z _=>mul_le_mul_of_nonneg_left (hpnt z) ((M.freshLaw hp).nonneg z))
    _ = (∑ z,(M.freshLaw hp).mass z*((bad z).card:ℝ))+
        (2*(n+k):ℕ)*(∑ z,(M.freshLaw hp).mass z*
          ((badWindows (M.representative z) (bad z)).card:ℝ)) := by
      simp only [mul_add,sum_add_distrib,mul_sum,mul_left_comm,mul_comm]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (bad_windows_mean w n k p θ G t hp bad) (show (0:ℝ)≤((2*(n+k):ℕ):ℝ) by positivity))

theorem bad_predeletion_five (hkn : k≤n)
    (hp : ∀ z,0<(model w n k p θ G t).remaining z)
    (bad : ∀ z : (model w n k p θ G t).FreshHistory,Finset ((model w n k p θ G t).Index z.1))
    (B : ℝ)
    (hbad : (∑ z,((model w n k p θ G t).freshLaw hp).mass z*((bad z).card:ℝ))≤B)
    (hrep : (n:ℝ)*(∑ z,((model w n k p θ G t).freshLaw hp).mass z*
      (((model w n k p θ G t).freshSelected z∩bad z).card:ℝ))≤B) :
    (∑ z,((model w n k p θ G t).freshLaw hp).mass z*
      ((w*(2*(n+k)):ℝ)-(∑ i∈univ\badWindows ((model w n k p θ G t).representative z) (bad z),
        (goodMiddle w n k p θ G t z (bad z) i).card:ℕ)))≤5*B := by
  have h:=bad_predeletion_mean w n k p θ G t hp bad
  have hh : (2*(n+k):ℕ)≤4*n := by omega
  have hh' : ((2*(n+k):ℕ):ℝ)≤4*(n:ℝ) := by exact_mod_cast hh
  have hn : 0≤∑ z,((model w n k p θ G t).freshLaw hp).mass z*
      (((model w n k p θ G t).freshSelected z∩bad z).card:ℝ) :=
    sum_nonneg (fun z _=>mul_nonneg (((model w n k p θ G t).freshLaw hp).nonneg z) (by positivity))
  have hmul:=mul_le_mul_of_nonneg_right hh' hn
  nlinarith

end
end SharpLogRamsey.Selection.Windows

end

end OAI
