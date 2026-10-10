import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.Definitions
import Mathlib.GroupTheory.FreeGroup.Reduce

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular



abbrev FZ := FreeGroup ℤ

def shift : FZ ≃* FZ := FreeGroup.freeGroupCongr (Equiv.addRight 1)

def action : F2 →* Equiv.Perm FZ :=
  FreeGroup.lift (fun i => if i = 0 then shift.toEquiv else Equiv.mulLeft (FreeGroup.of 0))

def a : F2 := FreeGroup.of 0
def b : F2 := FreeGroup.of 1

def freeGen : ℕ → F2
  | 0 => b
  | n+1 => a * freeGen n * a⁻¹

@[simp] lemma action_a : action a = shift.toEquiv := by simp [action,a]
@[simp] lemma action_b : action b = Equiv.mulLeft (FreeGroup.of 0) := by simp [action,b]
@[simp] lemma shift_of (n : ℤ) : shift (FreeGroup.of n) = FreeGroup.of (n+1) := by
  simp [shift,FreeGroup.freeGroupCongr]

lemma action_freeGen (n : ℕ) : action (freeGen n) = Equiv.mulLeft (FreeGroup.of (n:ℤ)) := by
  induction n with
  | zero => simp [freeGen]
  | succ n ih =>
    ext w
    simp only [freeGen,map_mul,map_inv,action_a,ih,Equiv.Perm.mul_apply]
    change shift (FreeGroup.of (n:ℤ) * shift.symm w) = FreeGroup.of ((n+1:ℕ):ℤ) * w
    simp

def coordinate (w : F2) : FZ := action w 1

lemma coordinate_freeGen_mul (n : ℕ) (w : F2) :
    coordinate (freeGen n * w) = FreeGroup.of (n:ℤ) * coordinate w := by
  simp [coordinate,action_freeGen]

def Prefix (i : ℤ) (sign : Bool) (w : FZ) : Prop :=
  ∃ t, w.toWord = (i,sign)::t

lemma prefix_disjoint {i j : ℤ} {s t : Bool} {w : FZ}
    (h : Prefix i s w) (k : Prefix j t w) : i = j ∧ s = t := by
  rcases h with ⟨u,hu⟩; rcases k with ⟨v,hv⟩
  simpa using (List.cons.inj (hu.symm.trans hv)).1

lemma prefix_mul_of_not_negative (i : ℤ) (w : FZ) (h : ¬ Prefix i false w) :
    Prefix i true (FreeGroup.of i * w) := by
  unfold Prefix at *
  rw [FreeGroup.toWord_mul,FreeGroup.toWord_of,List.singleton_append,FreeGroup.reduce.cons,
    FreeGroup.reduce_toWord]
  cases hw : w.toWord with
  | nil => exact ⟨[],rfl⟩
  | cons z t =>
    rcases z with ⟨j,s⟩
    have hn : ¬ (i = j ∧ true = !s) := by
      rintro ⟨rfl,hs⟩
      cases s with
      | false => exact h ⟨t,hw⟩
      | true => simp at hs
    simp only [hn,ite_false]
    exact ⟨(j,s)::t,rfl⟩

lemma positive_of_not_negative_inverse (n : ℕ) (w : F2)
    (h : ¬ Prefix (n:ℤ) false (coordinate ((freeGen n)⁻¹ * w))) :
    Prefix (n:ℤ) true (coordinate w) := by
  have he := coordinate_freeGen_mul n ((freeGen n)⁻¹ * w)
  simp only [mul_inv_cancel_left] at he
  rw [he]
  exact prefix_mul_of_not_negative _ _ h


end KaplanskyConsequences.Regular

end

end OAI
