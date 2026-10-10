import OAI.Probability.InvariantIsing.Cavity.CavityRationalCounts

namespace OAI

/-! The rational count progression has exactly the prescribed normalized
masses at every size, and its ordered block endpoints have exact limits. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma cavityRationalCount_ratio {m n q : ℕ} (s : Fin m → ℕ) (hn : 0<n) (hq : 0<q)
    (r : ℕ) (a : Fin m) :
    (cavityRationalCount s q r a : ℝ)/((r+q)*n : ℕ)=(s a : ℝ)/n := by
  have hq' : (r+q : ℝ)≠0 := by exact_mod_cast (show r+q≠0 by omega)
  have hn' : (n : ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [cavityRationalCount, Nat.cast_mul, Nat.cast_add]
  field_simp

lemma cavityRationalDimension_tendsto (n q : ℕ) (hn : 0<n) :
    Tendsto (fun r : ℕ => (r+q)*n) atTop atTop := by
  apply tendsto_atTop_mono (fun r => ?_) tendsto_id
  change r≤(r+q)*n
  exact (Nat.le_add_right r q).trans (Nat.le_mul_of_pos_right _ hn)

lemma cavityRationalStart (m : ℕ) (s : Fin m → ℕ) (q r : ℕ) (a : Fin m) :
    cavityOrderedStart (cavityRationalCount s q r) a = (r+q)*cavityOrderedStart s a := by
  simp only [cavityOrderedStart, cavityRationalCount, Finset.mul_sum]

lemma cavityRationalStart_ratio {m n q : ℕ} (s : Fin m → ℕ) (hn : 0<n) (hq : 0<q)
    (r : ℕ) (a : Fin m) :
    (cavityOrderedStart (cavityRationalCount s q r) a : ℝ)/((r+q)*n : ℕ)=
      (cavityOrderedStart s a : ℝ)/n := by
  rw [cavityRationalStart]
  have hq' : (r+q : ℝ)≠0 := by exact_mod_cast (show r+q≠0 by omega)
  have hn' : (n : ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  push_cast
  field_simp

lemma cavityRationalEnd_ratio {m n q : ℕ} (s : Fin m → ℕ) (hn : 0<n) (hq : 0<q)
    (r : ℕ) (a : Fin m) :
    ((cavityOrderedStart (cavityRationalCount s q r) a+cavityRationalCount s q r a : ℕ) : ℝ)/
      ((r+q)*n : ℕ) = (cavityOrderedStart s a+s a : ℝ)/n := by
  rw [Nat.cast_add, add_div, cavityRationalStart_ratio s hn hq r a,
    cavityRationalCount_ratio s hn hq r a, ← add_div]

lemma cavityRationalStart_alternative {m : ℕ} (s : Fin m → ℕ) (q : ℕ) (a : Fin m) :
    (∀ r, cavityOrderedStart (cavityRationalCount s q r) a=0) ∨
    Tendsto (fun r => cavityOrderedStart (cavityRationalCount s q r) a) atTop atTop := by
  by_cases ha : cavityOrderedStart s a=0
  · left
    intro r
    rw [cavityRationalStart,ha,Nat.mul_zero]
  · right
    simpa only [cavityRationalStart] using
      cavityRationalDimension_tendsto (cavityOrderedStart s a) q (Nat.pos_of_ne_zero ha)

lemma cavityRationalEnd_tendsto {m : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0<s a)
    (q : ℕ) (a : Fin m) :
    Tendsto (fun r => cavityOrderedStart (cavityRationalCount s q r) a+
      cavityRationalCount s q r a) atTop atTop := by
  simpa only [cavityRationalStart, cavityRationalCount, ← Nat.mul_add] using
    cavityRationalDimension_tendsto (cavityOrderedStart s a+s a) q (by have := hs a; omega)

end InvariantIsing

end

end OAI
