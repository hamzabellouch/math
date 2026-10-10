import OAI.Probability.InvariantIsing.Cavity.CavityAffineRetained

namespace OAI

/-! One spectrum on all sizes for each fixed vector of residue offsets. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityAffineLabel {m n : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hsum : ∑ a, s a=n) (N : ℕ) : Fin N → Fin m :=
  if h : (∑ a, c a) ≤ N ∧ n∣(N-∑ a, c a) then
    cavityOrderedGroup (fun a => (N-∑ a, c a)/n*s a+c a) (by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum,
        Nat.div_mul_cancel h.2, Nat.sub_add_cancel h.1])
  else fun _ => ⟨0,hm⟩

lemma cavityAffineLabel_eq_ordered {m n : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hsum : ∑ a, s a=n) (hn : 0 < n) (N v : ℕ)
    (hN : N=v*n+∑ a, c a) (hc : ∑ a, (v*s a+c a)=N) :
    cavityAffineLabel hm s c hsum N=cavityOrderedGroup (fun a => v*s a+c a) hc := by
  have hsub : N-∑ a, c a=v*n := by omega
  have hd : n∣(N-∑ a, c a) := hsub ▸ dvd_mul_left n v
  have hle : (∑ a, c a) ≤ N := by omega
  have hv : (N-∑ a, c a)/n=v :=
    Nat.eq_of_mul_eq_mul_right hn ((Nat.div_mul_cancel hd).trans hsub)
  have hh : (∑ a, c a) ≤ N ∧ n∣(N-∑ a, c a) := ⟨hle,hd⟩
  simp only [cavityAffineLabel, dite_eq_left hh]
  apply cavityOrderedGroup_congr
  funext a
  rw [hv]

lemma cavityAffineLabel_progression {m n : ℕ} (hm : 0 < m)
    (s c : Fin m → ℕ) (hsum : ∑ a, s a=n) (hn : 0 < n) (q r : ℕ) :
    cavityAffineLabel hm s c hsum (cavityAffineSize n q c r)=
      cavityOrderedGroup (cavityAffineCount s c q r) (cavityAffineCount_sum s c hsum q r) :=
  cavityAffineLabel_eq_ordered hm s c hsum hn _ (r+q) rfl _

lemma cavityAffineFullGroup_eq {m n : ℕ} (hm : 0 < m)
    (s c : Fin m → ℕ) (hsum : ∑ a, s a=n) (hn : 0 < n) (d r : ℕ) :
    cavityAffineFullGroup s c hsum d r=
      cavityAffineLabel hm s c hsum (cavityAffineSize n (d+n+3) c r+n) := by
  symm
  apply cavityAffineLabel_eq_ordered hm s c hsum hn _ (r+1+(d+n+3)) _
  dsimp only [cavityAffineSize]
  ring

lemma cavityAffineBase_label {m n d : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (g : Fin d → Fin m) (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) (i : Fin (cavityAffineSize n (d+n+3) c r)) :
    Sum.elim (fun w => w.1) g ((cavityAffineBaseEquiv s c hs hsum g hg r).symm i)=
      cavityAffineLabel hm s c hsum (cavityAffineSize n (d+n+3) c r) i := by
  rw [cavityAffineLabel_progression hm s c hsum hn]
  change Sum.elim _ g ((cavityOrderedBase _ g _).symm i)=_
  rw [cavityOrderedBase_label]
  have hcount : cavityBaseGroupDimension (cavityAffineRetained n d s c r) g=
      cavityAffineCount s c (d+n+3) r := by
    funext a
    exact cavityAffineBase_dimension s c hs hsum g hg r a
  simp only [hcount]

lemma cavityAffineBase_canonical_label {m n d : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (g : Fin d → Fin m) (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) (i : Fin (cavityAffineSize n (d+n+3) c r)) :
    ((cavityBaseGroupEquiv (cavityAffineRetained n d s c r)
      (cavityAffineBaseEquiv s c hs hsum g hg r) g).symm i).1=
      cavityAffineLabel hm s c hsum (cavityAffineSize n (d+n+3) c r) i :=
  (cavityBaseGroupEquiv_label _ _ _ i).trans (cavityAffineBase_label hm s c hs hsum hn g hg r i)

lemma cavityAffineBase_partition {m n d : ℕ} (hm : 0 < m) (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) (hn : 0 < n)
    (g : Fin d → Fin m) (hg : ∀ a, (Finset.univ.filter (fun j => g j=a)).card=n-s a)
    (r : ℕ) :
    cavityBaseGroup (cavityAffineRetained n d s c r) (cavityAffineBaseEquiv s c hs hsum g hg r) g=
      cavitySpectralGroup (cavityAffineLabel hm s c hsum (cavityAffineSize n (d+n+3) c r)) := by
  funext a
  apply Finset.ext
  intro i
  simp only [cavityBaseGroup, cavitySpectralGroup, Finset.mem_filter, Finset.mem_univ, true_and,
    cavityAffineBase_label hm s c hs hsum hn g hg r i]

end InvariantIsing

end

end OAI
