import OAI.Probability.BenjaminiSchramm.GhostCritical

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_tail_square_scale [Countable E]
    (G : BondGraph V E) (C : ℝ) (hC : 0 < C)
    (hvol : ∀ x n, 0 < n → criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n)
    (Q : Finset E) (x : V) (p : unitInterval) (hp : p ≤ pc G)
    (m n : ℕ) (hm : 0 < m) (hmC : 12 * C ≤ m) (hmn : m ^ 2 ≤ n) :
    finiteClusterTail G Q x n p ≤
      (6 * C / m) * Real.exp (-((pc G : ℝ) - p) * m / (24 * C)) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let h : unitInterval := ⟨1 / (m : ℝ) ^ 2,⟨by positivity,
    (div_le_one (by positivity)).mpr (by nlinarith)⟩⟩
  have hh : (h : ℝ) * (m : ℝ) ^ 2 = 1 := by dsimp [h]; field_simp
  have hn : 1 ≤ (h : ℝ) * n := by
    rw [←hh]
    apply mul_le_mul_of_nonneg_left _ h.2.1
    exact_mod_cast hmn
  have hB0 : 0 < 3 * C / m := by positivity
  have hsmall : 3 * C / m ≤ 1 / 4 := by
    apply (div_le_iff₀ hmR).mpr
    linarith
  have hb (r : unitInterval) (_hpr : p ≤ r) (hr : r ≤ pc G) (y : V) :=
    critical_ghost_bound_at_square_scale G C hC.le hvol Q y r h hr m hm hh.le
  have ht := tail_transfer_of_ghost_bound G Q x n p (pc G) h (3 * C / m)
    hp hn hB0 hsmall hb
  have he : -((pc G : ℝ) - p) / (8 * (3 * C / m)) =
      -((pc G : ℝ) - p) * m / (24 * C) := by field_simp; ring
  rw [he] at ht
  convert ht using 1; ring

theorem finite_tail_antitone (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : unitInterval) : Antitone (fun n => finiteClusterTail G Q x n p) := by
  intro n m hnm
  apply bernoulliPolynomial_mono _ _ _ p p.2
  intro ω _
  dsimp [finiteClusterTailIndicator]
  split_ifs <;> norm_num
  omega

theorem square_block_tail_sum (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : unitInterval) (m : ℕ) :
    (∑ i ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2), finiteClusterTail G Q x (i + 1) p) ≤
      (2 * m + 1 : ℕ) * finiteClusterTail G Q x (m ^ 2) p := by
  calc
    _ ≤ ∑ _i ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2), finiteClusterTail G Q x (m ^ 2) p := by
      apply Finset.sum_le_sum
      intro i hi
      exact finite_tail_antitone G Q x p ((Finset.mem_Ico.mp hi).1.trans (Nat.le_succ i))
    _ = _ := by
      simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul]
      congr 1
      have he : (m + 1) ^ 2 - m ^ 2 = 2 * m + 1 := by
        have hh : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
        omega
      rw [he]

theorem sum_exp_neg_le (t : ℝ) (ht : 0 < t) (N : ℕ) :
    (∑ i ∈ Finset.range N, Real.exp (-t * i)) ≤ 1 + 1 / t := by
  have hq : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-t) := sub_pos.mpr hq
  have hsum : (∑ i ∈ Finset.range N, Real.exp (-t * i)) ≤
      1 / (1 - Real.exp (-t)) := by
    simp_rw [mul_comm (-t),Real.exp_nat_mul]
    apply (le_div_iff₀ hden).mpr
    rw [geom_sum_mul_neg]
    linarith [pow_nonneg (Real.exp_pos (-t)).le N]
  apply hsum.trans
  apply (div_le_iff₀ hden).mpr
  have he := Real.add_one_le_exp t
  have he0 := Real.exp_pos t
  rw [Real.exp_neg]
  apply (mul_le_mul_iff_right₀ he0).mp
  field_simp
  nlinarith

theorem finite_mean_upper_from_volume [Countable E]
    (G : BondGraph V E) (C : ℝ) (hC : 0 < C)
    (hvol : ∀ x n, 0 < n → criticalTail G (volumeEvent G) x n ≤ C / Real.sqrt n)
    (M : ℕ) (hM : 0 < M) (hMC : 12 * C ≤ M)
    (Q : Finset E) (x : V) (p : unitInterval) (hp : p < pc G) :
    bernoulliPolynomial Q (fun ω => ((finiteRootComponent G ω x).card : ℝ)) p ≤
      (M : ℝ) ^ 2 + 18 * C * (1 + 24 * C / ((pc G : ℝ) - p)) := by
  let δ : ℝ := (pc G : ℝ) - p
  have hδ : 0 < δ := sub_pos.mpr hp
  let f := fun n => finiteClusterTail G Q x (n + 1) p
  let g := fun m : ℕ => Real.exp (-(δ / (24 * C)) * m)
  have hpartial (K : ℕ) : (∑ i ∈ Finset.range (K ^ 2), f i) ≤
      (M : ℝ) ^ 2 + 18 * C * (∑ m ∈ Finset.range K, g m) := by
    induction K with
    | zero => simp
    | succ K ih =>
      by_cases hKM : K < M
      · have hf1 : (∑ i ∈ Finset.range ((K + 1) ^ 2), f i) ≤ ((K + 1) ^ 2 : ℕ) := by
          calc
            _ ≤ ∑ _i ∈ Finset.range ((K + 1) ^ 2), (1 : ℝ) :=
              Finset.sum_le_sum (fun i _ => finiteClusterTail_le_one G Q x (i + 1) p)
            _ = _ := by simp
        have hsq : (((K + 1) ^ 2 : ℕ) : ℝ) ≤ (M : ℝ) ^ 2 := by
          exact_mod_cast Nat.pow_le_pow_left (show K + 1 ≤ M by omega) 2
        have hg0 : 0 ≤ 18 * C * (∑ m ∈ Finset.range (K + 1), g m) :=
          mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
        exact hf1.trans (hsq.trans (le_add_of_nonneg_right hg0))
      · have hMK : M ≤ K := by omega
        have hK : 0 < K := hM.trans_le hMK
        have hKC : 12 * C ≤ K := hMC.trans (by exact_mod_cast hMK)
        have ht := finite_tail_square_scale G C hC hvol Q x p hp.le K (K ^ 2) hK hKC le_rfl
        have hblock := square_block_tail_sum G Q x p K
        have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
        have hratio : (2 * (K : ℝ) + 1) * (6 * C / K) ≤ 18 * C := by
          rw [←mul_div_assoc]
          apply (div_le_iff₀ (show 0 < (K : ℝ) by positivity)).mpr
          nlinarith
        have hblock' : (∑ i ∈ Finset.Ico (K ^ 2) ((K + 1) ^ 2), f i) ≤ 18 * C * g K := by
          apply hblock.trans
          apply (mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ (2 * K + 1 : ℕ))).trans
          have he : -δ * K / (24 * C) = -(δ / (24 * C)) * K := by ring
          change (2 * K + 1 : ℕ) * ((6 * C / K) * Real.exp (-δ * K / (24 * C))) ≤ _
          rw [he]
          have hh := mul_le_mul_of_nonneg_right hratio (Real.exp_pos (-(δ / (24 * C)) * K)).le
          push_cast
          simpa only [mul_assoc,g] using hh
        rw [←Finset.sum_range_add_sum_Ico f (Nat.pow_le_pow_left (Nat.le_succ K) 2),
          Finset.sum_range_succ]
        have hh := add_le_add ih hblock'
        simpa only [mul_add,add_assoc] using hh
  let N := (insert x (searchVertices G Q)).card
  have hN : N ≤ N ^ 2 := Nat.le_self_pow two_ne_zero N
  rw [finiteClusterSize_eq_sum_tail]
  have hle : (∑ i ∈ Finset.range N, f i) ≤ ∑ i ∈ Finset.range (N ^ 2), f i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN)
      (fun i _ _ => finiteClusterTail_nonneg G Q x (i + 1) p)
  apply (hle.trans (hpartial N)).trans
  have ht : 0 < δ / (24 * C) := by positivity
  have hs := sum_exp_neg_le (δ / (24 * C)) ht N
  have he : 1 / (δ / (24 * C)) = 24 * C / δ := by field_simp
  rw [he] at hs
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hs (show 0 ≤ 18 * C by positivity))

theorem susceptibility_upper_of_critical_volume [Countable E]
    (G : BondGraph V E) (hqt : QuasiTransitive G)
    (hvol : ∀ x, PowerTail (criticalTail G (volumeEvent G) x) (1 / 2)) :
    ∃ A : ℝ, 0 < A ∧ ∀ p : unitInterval, p < pc G → ∀ x,
      susceptibility G p x ≤ A / ((pc G : ℝ) - p) := by
  obtain ⟨C,hC,hb⟩ := uniform_critical_volume_upper_of_powerTail G hqt hvol
  obtain ⟨M,hMC⟩ := exists_nat_gt (12 * C)
  have hM : 0 < M := by
    have hh : (0 : ℝ) < M := (by positivity : 0 < 12 * C).trans hMC
    exact_mod_cast hh
  let A : ℝ := (M : ℝ) ^ 2 + 18 * C + 432 * C ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  intro p hp x
  have hδ : 0 < (pc G : ℝ) - p := sub_pos.mpr hp
  have hδ1 : (pc G : ℝ) - p ≤ 1 := by linarith [(pc G).2.2,p.2.1]
  have hbound := (susceptibility_bound_of_finite_size G x p
    ((M : ℝ) ^ 2 + 18 * C * (1 + 24 * C / ((pc G : ℝ) - p)))
    (fun Q => finite_mean_upper_from_volume G C hC hb M hM hMC.le Q x p hp)).2
  apply hbound.trans
  apply (le_div_iff₀ hδ).mpr
  have hbase := mul_le_mul_of_nonneg_left hδ1
    (show 0 ≤ (M : ℝ) ^ 2 + 18 * C by positivity)
  have hid :
      ((M : ℝ) ^ 2 + 18 * C * (1 + 24 * C / ((pc G : ℝ) - p))) *
          ((pc G : ℝ) - p) =
      ((M : ℝ) ^ 2 + 18 * C) * ((pc G : ℝ) - p) + 432 * C ^ 2 := by
    field_simp
    ring
  rw [hid]
  dsimp [A]
  linarith

end Percolation.BenjaminiSchramm

end OAI
