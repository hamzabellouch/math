import OAI.Probability.InvariantIsing.Cavity.CavityRationalRetained

namespace OAI

/-! Both sides of the physical rational-count coupling have exactly the
labels of the single global spectral family. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma cavityRationalFullGroup_eq {m n : ℕ} (hm : 0 < m) (s : Fin m → ℕ)
    (hsum : ∑ a, s a=n) (hn : 0 < n) (d r : ℕ) :
    cavityRationalFullGroup s hsum d r=
      cavityRationalLabel hm s hsum (cavityRationalSize n d r+n) := by
  symm
  apply cavityRationalLabel_eq_ordered hm s hsum hn
  unfold cavityRationalSize
  ring

lemma cavityRationalBase_label {m n d : ℕ} (hm : 0 < m) (s : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (g : Fin d → Fin m) (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) (i : Fin (cavityRationalSize n d r)) :
    Sum.elim (fun w => w.1) g ((cavityRationalBaseEquiv s hs hsum g hg r).symm i)=
      cavityRationalLabel hm s hsum (cavityRationalSize n d r) i := by
  dsimp only [cavityRationalSize] at i ⊢
  rw [cavityRationalLabel_progression hm s hsum hn (d+n+3) r]
  exact cavityRationalBase_order s hs hsum g hg r i

lemma cavityRationalBase_canonical_label {m n d : ℕ} (hm : 0 < m) (s : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (g : Fin d → Fin m) (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) (i : Fin (cavityRationalSize n d r)) :
    ((cavityBaseGroupEquiv (cavityRationalRetained n d s r)
      (cavityRationalBaseEquiv s hs hsum g hg r) g).symm i).1=
      cavityRationalLabel hm s hsum (cavityRationalSize n d r) i :=
  (cavityBaseGroupEquiv_label _ _ _ i).trans (cavityRationalBase_label hm s hs hsum hn g hg r i)

lemma cavityRationalBase_partition {m n d : ℕ} (hm : 0 < m) (s : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (g : Fin d → Fin m) (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) :
    cavityBaseGroup (cavityRationalRetained n d s r) (cavityRationalBaseEquiv s hs hsum g hg r) g=
      cavitySpectralGroup (cavityRationalLabel hm s hsum (cavityRationalSize n d r)) := by
  funext a
  apply Finset.ext
  intro i
  simp only [cavityBaseGroup, cavitySpectralGroup, Finset.mem_filter, Finset.mem_univ, true_and,
    cavityRationalBase_label hm s hs hsum hn g hg r i]

end InvariantIsing

end

end OAI
