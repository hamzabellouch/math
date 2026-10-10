import OAI.Probability.InvariantIsing.Cavity.CavityRationalRetained

namespace OAI

/-! Fixed integer offsets in the block counts cover every residue class
of physical dimensions without changing the limiting rational masses. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

def cavityAffineCount {m : ℕ} (s c : Fin m → ℕ) (q r : ℕ) (a : Fin m) : ℕ :=
  cavityRationalCount s q r a+c a

def cavityAffineSize {m : ℕ} (n q : ℕ) (c : Fin m → ℕ) (r : ℕ) : ℕ :=
  (r+q)*n+∑ a, c a

lemma cavityAffineCount_sum {m n : ℕ} (s c : Fin m → ℕ) (hsum : ∑ a, s a=n)
    (q r : ℕ) : ∑ a, cavityAffineCount s c q r a=cavityAffineSize n q c r := by
  simp only [cavityAffineCount, Finset.sum_add_distrib, cavityRationalCount_sum s hsum,
    cavityAffineSize]

lemma cavityAffineSize_tendsto {m : ℕ} (n q : ℕ) (c : Fin m → ℕ) (hn : 0 < n) :
    Tendsto (cavityAffineSize n q c) atTop atTop :=
  tendsto_atTop_mono (fun _ => Nat.le_add_right _ _) (cavityRationalDimension_tendsto n q hn)

lemma cavityAffineCount_tendsto {m : ℕ} (s c : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (q : ℕ) (a : Fin m) :
    Tendsto (fun r => cavityAffineCount s c q r a) atTop atTop :=
  tendsto_atTop_mono (fun _ => Nat.le_add_right _ _) (cavityRationalCount_tendsto s hs q a)

lemma cavityAffineSize_ge_three {m : ℕ} (n d : ℕ) (c : Fin m → ℕ)
    (r : ℕ) (hn : 0 < n) : 3 ≤ cavityAffineSize n (d+n+3) c r :=
  (cavityRationalSize_ge_three n d r hn).trans (Nat.le_add_right _ _)

lemma cavityAffineSize_succ {m : ℕ} (n q : ℕ) (c : Fin m → ℕ) (r : ℕ) :
    cavityAffineSize n q c (r+1)=cavityAffineSize n q c r+n := by
  dsimp only [cavityAffineSize]
  ring

lemma cavity_affine_ratio_tendsto (s c n d q : ℕ) (hn : 0 < n) (hq : 0 < q) :
    Tendsto (fun r : ℕ => (((r+q)*s+c : ℕ) : ℝ)/((r+q)*n+d : ℕ)) atTop
      (𝓝 ((s : ℝ)/n)) := by
  have ha : Tendsto (fun r : ℕ => (r+q : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.mul_one, Nat.cast_add] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (cavityRationalDimension_tendsto 1 q (by omega))
  have hi := tendsto_inv_atTop_zero.comp ha
  have ht := (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (s : ℝ)) atTop (𝓝 (s : ℝ))).add (hi.const_mul (c : ℝ))).div
    (tendsto_const_nhds.add (hi.const_mul (d : ℝ)))
    (by exact_mod_cast hn.ne' : (n : ℝ)+(d : ℝ)*0≠0))
  simp only [mul_zero, add_zero] at ht
  apply ht.congr
  intro r
  have hr : (r+q : ℝ)≠0 := by exact_mod_cast (show r+q≠0 by omega)
  have hd : (r+q : ℝ)*(n : ℝ)+d≠0 := by positivity
  dsimp only [Pi.div_apply, Function.comp_def]
  push_cast
  field_simp

lemma cavityAffineCount_ratio {m n : ℕ} (s c : Fin m → ℕ)
    (hn : 0 < n) {q : ℕ} (hq : 0 < q) (a : Fin m) :
    Tendsto (fun r => (cavityAffineCount s c q r a : ℝ)/cavityAffineSize n q c r)
      atTop (𝓝 ((s a : ℝ)/n)) :=
  cavity_affine_ratio_tendsto (s a) (c a) n (∑ a, c a) q hn hq

lemma cavityAffineStart {m : ℕ} (s c : Fin m → ℕ) (q r : ℕ) (a : Fin m) :
    cavityOrderedStart (cavityAffineCount s c q r) a=
      (r+q)*cavityOrderedStart s a+cavityOrderedStart c a := by
  simp only [cavityOrderedStart, cavityAffineCount, cavityRationalCount,
    Finset.sum_add_distrib, Finset.mul_sum]

lemma cavityAffineStart_ratio {m n : ℕ} (s c : Fin m → ℕ)
    (hn : 0 < n) {q : ℕ} (hq : 0 < q) (a : Fin m) :
    Tendsto (fun r => (cavityOrderedStart (cavityAffineCount s c q r) a : ℝ)/
      cavityAffineSize n q c r) atTop (𝓝 ((cavityOrderedStart s a : ℝ)/n)) := by
  simpa only [cavityAffineStart, cavityAffineSize] using
    cavity_affine_ratio_tendsto (cavityOrderedStart s a) (cavityOrderedStart c a)
      n (∑ a, c a) q hn hq

lemma cavityAffineEnd_ratio {m n : ℕ} (s c : Fin m → ℕ)
    (hn : 0 < n) {q : ℕ} (hq : 0 < q) (a : Fin m) :
    Tendsto (fun r => ((cavityOrderedStart (cavityAffineCount s c q r) a+
      cavityAffineCount s c q r a : ℕ) : ℝ)/cavityAffineSize n q c r)
      atTop (𝓝 (((cavityOrderedStart s a+s a : ℕ) : ℝ)/n)) := by
  simpa only [Nat.cast_add, add_div] using
    (cavityAffineStart_ratio s c hn hq a).add (cavityAffineCount_ratio s c hn hq a)

end InvariantIsing

end

end OAI
