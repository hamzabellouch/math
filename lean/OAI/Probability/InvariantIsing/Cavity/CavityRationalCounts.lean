import OAI.Probability.InvariantIsing.Cavity.CavityOrderedGroups

namespace OAI

/-! A rational spectral law gives an exact arithmetic progression of
positive multiplicities and the finite exceptional-axis multiplicities. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityRationalCount {m : ℕ} (s : Fin m → ℕ) (q r : ℕ) (a : Fin m) : ℕ :=
  (r+q)*s a

lemma cavityRationalCount_sum {m n : ℕ} (s : Fin m → ℕ) (hs : ∑ a, s a=n)
    (q r : ℕ) : ∑ a, cavityRationalCount s q r a=(r+q)*n := by
  simp only [cavityRationalCount, ← Finset.mul_sum, hs]

lemma cavityRationalCount_step {m : ℕ} (s : Fin m → ℕ) (q r : ℕ) (a : Fin m) :
    cavityRationalCount s q (r+1) a=cavityRationalCount s q r a+s a := by
  unfold cavityRationalCount
  ring

lemma cavityRationalCount_positive {m : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0<s a)
    {q : ℕ} (hq : 0<q) (r : ℕ) (a : Fin m) : 0<cavityRationalCount s q r a :=
  Nat.mul_pos (by omega) (hs a)

lemma cavityRationalCount_tendsto {m : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0<s a)
    (q : ℕ) (a : Fin m) : Filter.Tendsto (fun r => cavityRationalCount s q r a)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono (fun r => ?_) Filter.tendsto_id
  change r ≤ (r+q)*s a
  exact (Nat.le_add_right r q).trans (Nat.le_mul_of_pos_right _ (hs a))

lemma cavityRationalCount_le_total {m n : ℕ} (s : Fin m → ℕ) (hs : ∑ a, s a=n)
    (a : Fin m) : s a≤n := by
  rw [← hs]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

lemma cavityRationalSpecial_sum {m n : ℕ} (s : Fin m → ℕ) (hs : ∑ a, s a=n) :
    ∑ a, (n-s a)=m*n-n := by
  rw [Finset.sum_tsub_distrib Finset.univ (fun a _ => cavityRationalCount_le_total s hs a)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hs]

lemma cavityRationalRetained_ge {m n d : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0<s a)
    (r : ℕ) (a : Fin m) : d≤cavityRationalCount s (d+n+3) (r+1) a-n := by
  have hp := Nat.le_mul_of_pos_right (r+1+(d+n+3)) (hs a)
  unfold cavityRationalCount
  omega

lemma cavityRationalRetained_base {m n d : ℕ} (s : Fin m → ℕ) (hs : ∀ a, 0<s a)
    (hsum : ∑ a, s a=n) (r : ℕ) (a : Fin m) :
    (cavityRationalCount s (d+n+3) (r+1) a-n)+(n-s a)=
      cavityRationalCount s (d+n+3) r a := by
  have hsn := cavityRationalCount_le_total s hsum a
  have hp := Nat.le_mul_of_pos_right (r+1+(d+n+3)) (hs a)
  rw [cavityRationalCount_step]
  have hbase : n≤cavityRationalCount s (d+n+3) r a := by
    unfold cavityRationalCount
    have h := Nat.le_mul_of_pos_right (r+(d+n+3)) (hs a)
    omega
  omega

end InvariantIsing

end

end OAI
