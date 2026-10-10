import OAI.Probability.InvariantIsing.Cavity.CavityAffineCounts

namespace OAI

/-! The retained and special axes for counts with a fixed residue offset. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityAffineRetained {m : ℕ} (n d : ℕ) (s c : Fin m → ℕ) (r : ℕ) (a : Fin m) : ℕ :=
  cavityRationalRetained n d s r a+c a

lemma cavityAffineRetained_ge {m n d : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (r : ℕ) (a : Fin m) : d ≤ cavityAffineRetained n d s c r a :=
  (cavityRationalRetained_ge s hs r a).trans (Nat.le_add_right _ _)

lemma cavityAffineRetained_full {m n : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (d r : ℕ) (a : Fin m) :
    cavityAffineRetained n d s c r a+n=cavityAffineCount s c (d+n+3) (r+1) a := by
  dsimp only [cavityAffineRetained, cavityAffineCount]
  rw [Nat.add_right_comm, cavityRationalRetained_full s hs]

lemma cavityAffineFull_sum {m n : ℕ} (s c : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (q r : ℕ) : ∑ a, cavityAffineCount s c q (r+1) a=cavityAffineSize n q c r+n := by
  rw [cavityAffineCount_sum s c hsum, cavityAffineSize_succ]

def cavityAffineFullGroup {m n : ℕ} (s c : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (d r : ℕ) : Fin (cavityAffineSize n (d+n+3) c r+n) → Fin m :=
  cavityOrderedGroup (cavityAffineCount s c (d+n+3) (r+1))
    (cavityAffineFull_sum s c hsum (d+n+3) r)

def cavityAffineRetainedEquiv {m n : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (d r : ℕ) (a : Fin m) :
    {i : Fin (cavityAffineSize n (d+n+3) c r+n) // cavityAffineFullGroup s c hsum d r i=a} ≃
      Fin (cavityAffineRetained n d s c r a+n) :=
  (cavityGroupIndexEquiv (cavityAffineCount s c (d+n+3) (r+1))
    (cavityOrderedEquiv _ (cavityAffineFull_sum s c hsum (d+n+3) r)) a).symm.trans
      (finCongr (cavityAffineRetained_full s c hs d r a).symm)

lemma cavityAffineBase_dimension {m n d : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (g : Fin d → Fin m)
    (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a) (r : ℕ) (a : Fin m) :
    cavityBaseGroupDimension (cavityAffineRetained n d s c r) g a=
      cavityAffineCount s c (d+n+3) r a := by
  have hh := cavityRationalBase_dimension s hs hsum g hg r a
  simp only [cavityBaseGroupDimension_filter_card] at hh ⊢
  dsimp only [cavityAffineRetained, cavityAffineCount]
  rw [Nat.add_right_comm, hh]

lemma cavityAffineBase_sum {m n d : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (g : Fin d → Fin m)
    (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a) (r : ℕ) :
    ∑ a, cavityBaseGroupDimension (cavityAffineRetained n d s c r) g a=
      cavityAffineSize n (d+n+3) c r := by
  simp_rw [cavityAffineBase_dimension s c hs hsum g hg r]
  exact cavityAffineCount_sum s c hsum (d+n+3) r

def cavityAffineBaseEquiv {m n d : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (g : Fin d → Fin m)
    (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a) (r : ℕ) :
    (((a : Fin m) × Fin (cavityAffineRetained n d s c r a)) ⊕ Fin d) ≃
      Fin (cavityAffineSize n (d+n+3) c r) :=
  cavityOrderedBase (cavityAffineRetained n d s c r) g (cavityAffineBase_sum s c hs hsum g hg r)

end InvariantIsing

end

end OAI
