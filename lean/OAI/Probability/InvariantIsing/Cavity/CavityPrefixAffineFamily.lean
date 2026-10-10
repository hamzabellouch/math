import OAI.Probability.InvariantIsing.Cavity.CavityAffineFamily
import OAI.Probability.InvariantIsing.Cavity.CavityAffineWindows

namespace OAI

/-! One spectrum on all sizes for each fixed vector of residue offsets. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityPrefixAffineSize {m : ℕ} (n q : ℕ) (c : Fin m → ℕ) (r : ℕ) : ℕ :=
  (∑ a, c a)+(r+q)*n

lemma cavityPrefixAffineCount_sum {m n : ℕ} (s c : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (q r : ℕ) : ∑ a, cavityAffineCount s c q r a=cavityPrefixAffineSize n q c r := by
  simpa only [cavityAffineSize, cavityPrefixAffineSize, Nat.add_comm] using
    cavityAffineCount_sum s c hsum q r

lemma cavityPrefixAffineFull_sum {m n : ℕ} (s c : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (q r : ℕ) : ∑ a, cavityAffineCount s c q (r+1) a=cavityPrefixAffineSize n q c r+n := by
  rw [cavityPrefixAffineCount_sum s c hsum]
  simp only [cavityPrefixAffineSize]
  ring

def cavityPrefixAffineFullGroup {m n : ℕ} (s c : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (d r : ℕ) : Fin (cavityPrefixAffineSize n (d+n+3) c r+n) → Fin m :=
  cavityOrderedGroup (cavityAffineCount s c (d+n+3) (r+1))
    (cavityPrefixAffineFull_sum s c hsum (d+n+3) r)

def cavityPrefixAffineRetainedEquiv {m n : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (d r : ℕ) (a : Fin m) :
    {i : Fin (cavityPrefixAffineSize n (d+n+3) c r+n) // cavityPrefixAffineFullGroup s c hsum d r i=a} ≃
      Fin (cavityAffineRetained n d s c r a+n) :=
  (cavityGroupIndexEquiv (cavityAffineCount s c (d+n+3) (r+1))
    (cavityOrderedEquiv _ (cavityPrefixAffineFull_sum s c hsum (d+n+3) r)) a).symm.trans
      (finCongr (cavityAffineRetained_full s c hs d r a).symm)

def cavityPrefixAffineBaseEquiv {m n d : ℕ} (s c : Fin m → ℕ) (hs : ∀ a, 0 < s a)
    (hsum : ∑ a, s a=n) (g : Fin d → Fin m)
    (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a) (r : ℕ) :
    (((a : Fin m) × Fin (cavityAffineRetained n d s c r a)) ⊕ Fin d) ≃
      Fin (cavityPrefixAffineSize n (d+n+3) c r) :=
  cavityOrderedBase (cavityAffineRetained n d s c r) g (by
    simpa only [cavityAffineSize, cavityPrefixAffineSize, Nat.add_comm] using
      cavityAffineBase_sum s c hs hsum g hg r)

lemma cavityPrefixAffineLabel_progression {m n : ℕ} (hm : 0 < m)
    (s c : Fin m → ℕ) (hsum : ∑ a, s a=n) (hn : 0 < n) (q r : ℕ) :
    cavityAffineLabel hm s c hsum (cavityPrefixAffineSize n q c r)=
      cavityOrderedGroup (cavityAffineCount s c q r) (cavityPrefixAffineCount_sum s c hsum q r) :=
  cavityAffineLabel_eq_ordered hm s c hsum hn _ (r+q) (Nat.add_comm _ _) _

lemma cavityPrefixAffineFullGroup_eq {m n : ℕ} (hm : 0 < m)
    (s c : Fin m → ℕ) (hsum : ∑ a, s a=n) (hn : 0 < n) (d r : ℕ) :
    cavityPrefixAffineFullGroup s c hsum d r=
      cavityAffineLabel hm s c hsum (cavityPrefixAffineSize n (d+n+3) c r+n) := by
  symm
  apply cavityAffineLabel_eq_ordered hm s c hsum hn _ (r+1+(d+n+3)) _
  dsimp only [cavityPrefixAffineSize]
  ring

lemma cavityPrefixAffineBase_label {m n d : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (g : Fin d → Fin m) (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) (i : Fin (cavityPrefixAffineSize n (d+n+3) c r)) :
    Sum.elim (fun w => w.1) g ((cavityPrefixAffineBaseEquiv s c hs hsum g hg r).symm i)=
      cavityAffineLabel hm s c hsum (cavityPrefixAffineSize n (d+n+3) c r) i := by
  rw [cavityPrefixAffineLabel_progression hm s c hsum hn]
  change Sum.elim _ g ((cavityOrderedBase _ g _).symm i)=_
  rw [cavityOrderedBase_label]
  have hcount : cavityBaseGroupDimension (cavityAffineRetained n d s c r) g=
      cavityAffineCount s c (d+n+3) r := by
    funext a
    exact cavityAffineBase_dimension s c hs hsum g hg r a
  simp only [hcount]

lemma cavityPrefixAffineBase_canonical_label {m n d : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (g : Fin d → Fin m) (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) (i : Fin (cavityPrefixAffineSize n (d+n+3) c r)) :
    ((cavityBaseGroupEquiv (cavityAffineRetained n d s c r)
      (cavityPrefixAffineBaseEquiv s c hs hsum g hg r) g).symm i).1=
      cavityAffineLabel hm s c hsum (cavityPrefixAffineSize n (d+n+3) c r) i :=
  (cavityBaseGroupEquiv_label _ _ _ i).trans (cavityPrefixAffineBase_label hm s c hs hsum hn g hg r i)

lemma cavityPrefixAffineBase_partition {m n d : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (g : Fin d → Fin m) (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) :
    cavityBaseGroup (cavityAffineRetained n d s c r) (cavityPrefixAffineBaseEquiv s c hs hsum g hg r) g=
      cavitySpectralGroup (cavityAffineLabel hm s c hsum (cavityPrefixAffineSize n (d+n+3) c r)) := by
  funext a
  apply Finset.ext
  intro i
  simp only [cavityBaseGroup, cavitySpectralGroup, Finset.mem_filter, Finset.mem_univ, true_and,
    cavityPrefixAffineBase_label hm s c hs hsum hn g hg r i]

end InvariantIsing

end

end OAI
