import OAI.Probability.InvariantIsing.Cavity.CavityRationalMass

namespace OAI

/-! Exact contiguous full-system windows for a rational spectral law. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma cavityRationalFull_sum {m n : ℕ} (s : Fin m → ℕ) (hs : ∑ a, s a=n)
    (q r : ℕ) : ∑ a, cavityRationalCount s q (r+1) a=(r+q)*n+n := by
  rw [cavityRationalCount_sum s hs]
  ring

lemma cavityRationalFullStart_ratio {m n q : ℕ} (s : Fin m → ℕ) (hn : 0<n) (hq : 0<q)
    (r : ℕ) (a : Fin m) :
    (cavityOrderedStart (cavityRationalCount s q (r+1)) a : ℝ)/((r+q)*n+n : ℕ)=
      (cavityOrderedStart s a : ℝ)/n := by
  have he : (r+q)*n+n=(r+1+q)*n := by ring
  rw [he]
  exact cavityRationalStart_ratio s hn hq (r+1) a

lemma cavityRationalFullEnd_ratio {m n q : ℕ} (s : Fin m → ℕ) (hn : 0<n) (hq : 0<q)
    (r : ℕ) (a : Fin m) :
    ((cavityOrderedStart (cavityRationalCount s q (r+1)) a+
      cavityRationalCount s q (r+1) a : ℕ) : ℝ)/((r+q)*n+n : ℕ)=
      (cavityOrderedStart s a+s a : ℝ)/n := by
  have he : (r+q)*n+n=(r+1+q)*n := by ring
  rw [he]
  exact cavityRationalEnd_ratio s hn hq (r+1) a

lemma cavityRationalFullStart_alternative {m : ℕ} (s : Fin m → ℕ) (q : ℕ) (a : Fin m) :
    (∀ r, cavityOrderedStart (cavityRationalCount s q (r+1)) a=0) ∨
    Tendsto (fun r => cavityOrderedStart (cavityRationalCount s q (r+1)) a) atTop atTop := by
  rcases cavityRationalStart_alternative s q a with hz | ht
  · exact Or.inl (fun r => hz (r+1))
  · exact Or.inr (ht.comp (tendsto_add_atTop_nat 1))

lemma cavityRationalFullEnd_tendsto {m : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0<s a)
    (q : ℕ) (a : Fin m) :
    Tendsto (fun r => cavityOrderedStart (cavityRationalCount s q (r+1)) a+
      cavityRationalCount s q (r+1) a) atTop atTop :=
  (cavityRationalEnd_tendsto s hs q a).comp (tendsto_add_atTop_nat 1)

lemma cavityRationalFullWindow_size {m n q : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0<s a)
    (hq : n≤q) (r : ℕ) (a : Fin m) :
    cavityOrderedStart (cavityRationalCount s q (r+1)) a+n ≤
      cavityOrderedStart (cavityRationalCount s q (r+1)) a+cavityRationalCount s q (r+1) a := by
  have hh := Nat.le_mul_of_pos_right (r+1+q) (hs a)
  unfold cavityRationalCount
  omega

lemma cavityRationalMass_positive {m n : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0<s a)
    (hn : 0<n) (a : Fin m) : 0<(s a : ℝ)/n :=
  div_pos (by exact_mod_cast hs a) (by exact_mod_cast hn)

lemma cavityRationalMass_sum {m n : ℕ} (s : Fin m → ℕ) (hs : ∑ a, s a=n) (hn : 0<n) :
    ∑ a, (s a : ℝ)/n=1 := by
  rw [← Finset.sum_div, ← Nat.cast_sum, hs, div_self (Nat.cast_ne_zero.mpr hn.ne')]

lemma cavityRationalMass_difference {m n : ℕ} (s : Fin m → ℕ) (a : Fin m) :
    (cavityOrderedStart s a+s a : ℝ)/n-(cavityOrderedStart s a : ℝ)/n=(s a : ℝ)/n := by
  ring

end InvariantIsing

end

end OAI
