import OAI.Probability.InvariantIsing.Cavity.CavityRationalWindows
import OAI.Probability.InvariantIsing.Cavity.CavityRationalBaseOrder
import OAI.Probability.InvariantIsing.Cavity.CavityRationalFamily

namespace OAI

/-! The exact finite group equivalences in the rational cavity coupling. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityRationalSize (n d r : ℕ) : ℕ := (r+(d+n+3))*n

def cavityRationalRetained {m : ℕ} (n d : ℕ) (s : Fin m → ℕ) (r : ℕ) (a : Fin m) : ℕ :=
  cavityRationalCount s (d+n+3) (r+1) a-n

def cavityRationalFullGroup {m n : ℕ} (s : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (d r : ℕ) : Fin (cavityRationalSize n d r+n) → Fin m :=
  cavityOrderedGroup (cavityRationalCount s (d+n+3) (r+1))
    (cavityRationalFull_sum s hsum (d+n+3) r)

lemma cavityRationalSize_ge_three (n d r : ℕ) (hn : 0 < n) :
    3 ≤ cavityRationalSize n d r := by
  have hh := Nat.le_mul_of_pos_right (r+(d+n+3)) hn
  unfold cavityRationalSize
  omega

lemma cavityRationalRetained_full {m n : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (d r : ℕ) (a : Fin m) :
    cavityRationalRetained n d s r a+n=cavityRationalCount s (d+n+3) (r+1) a := by
  unfold cavityRationalRetained
  apply Nat.sub_add_cancel
  have hh := Nat.le_mul_of_pos_right (r+1+(d+n+3)) (hs a)
  unfold cavityRationalCount
  omega

def cavityRationalRetainedEquiv {m n : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (d r : ℕ) (a : Fin m) :
    {i : Fin (cavityRationalSize n d r+n) // cavityRationalFullGroup s hsum d r i=a} ≃
      Fin (cavityRationalRetained n d s r a+n) :=
  (cavityGroupIndexEquiv (cavityRationalCount s (d+n+3) (r+1))
    (cavityOrderedEquiv _ (cavityRationalFull_sum s hsum (d+n+3) r)) a).symm.trans
      (finCongr (cavityRationalRetained_full s hs d r a).symm)

def cavityRationalBaseEquiv {m n d : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (g : Fin d → Fin m)
    (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a) (r : ℕ) :
    (((a : Fin m) × Fin (cavityRationalRetained n d s r a)) ⊕ Fin d) ≃
      Fin (cavityRationalSize n d r) :=
  cavityOrderedBase (cavityRationalRetained n d s r) g (cavityRationalBase_sum s hs hsum g hg r)

lemma cavityRationalBase_dimension {m n d : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (g : Fin d → Fin m)
    (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a) (r : ℕ) (a : Fin m) :
    cavityBaseGroupDimension (cavityRationalRetained n d s r) g a=
      cavityRationalCount s (d+n+3) r a :=
  cavityRationalBase_counts s hs hsum g hg r a

end InvariantIsing

end

end OAI
