import OAI.MathematicalPhysics.CriticalSK.GaussianConcentration
import OAI.MathematicalPhysics.CriticalSK.PathEnergy

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

namespace CriticalSK

lemma sum_consecutive_blocks (K d : ℕ) (f : ℕ → ℝ) :
    (∑ b ∈ Finset.range K, ∑ i ∈ Finset.range d, f (b * d + i)) =
      ∑ i ∈ Finset.range (K * d), f i := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]

def blockIndices (d l : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (B ×ˢ Finset.range l).image (fun p => p.1 * d + p.2)

lemma block_index_injective (d l : ℕ) (B : Finset ℕ) (hd : 0 < d) (hl : l ≤ d) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * d + p.2) (B ×ˢ Finset.range l : Finset _ ) := by
  rintro ⟨b, i⟩ hbi ⟨c, k⟩ hck he
  have hi : i < d := (Finset.mem_range.mp (Finset.mem_product.mp hbi).2).trans_le hl
  have hk : k < d := (Finset.mem_range.mp (Finset.mem_product.mp hck).2).trans_le hl
  have hi' : i = k := by
    have hm := congrArg (fun n => n % d) he
    simpa only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hk] using hm
  have hb : b = c := by
    simp only [hi', Nat.add_right_cancel_iff] at he
    exact Nat.eq_of_mul_eq_mul_right hd he
  exact Prod.ext hb hi'

lemma blockIndices_sum (d l : ℕ) (B : Finset ℕ) (hd : 0 < d) (hl : l ≤ d) (f : ℕ → ℝ) :
    (∑ b ∈ B, ∑ i ∈ Finset.range l, f (b * d + i)) =
      ∑ i ∈ blockIndices d l B, f i := by
  rw [blockIndices, Finset.sum_image (block_index_injective d l B hd hl), Finset.sum_product]

lemma blockIndices_lower (d l a : ℕ) (B : Finset ℕ) (hB : ∀ b ∈ B, a ≤ b * d) :
    ∀ i ∈ blockIndices d l B, a ≤ i := by
  intro i hi
  obtain ⟨⟨b, k⟩, hbk, rfl⟩ := Finset.mem_image.mp hi
  exact (hB b (Finset.mem_product.mp hbk).1).trans (Nat.le_add_right _ _)

lemma sum_supported_le (N : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hzero : ∀ i, N ≤ i → f i = 0) (s : Finset ℕ) :
    (∑ i ∈ s, f i) ≤ ∑ i ∈ Finset.range N, f i := by
  have he : (∑ i ∈ s, f i) = ∑ i ∈ s.filter (fun i => i < N), f i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rfl
    · exact hzero i (Nat.le_of_not_gt hi)
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  · exact fun i _ _ => hf i

lemma supported_mass (n : ℕ) (u : ℕ → ℝ) (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (s : Finset ℕ) :
    (∑ i ∈ s, u i ^ 2) ≤ ∑ i ∈ Finset.range (n + 1), u i ^ 2 :=
  sum_supported_le _ _ (fun i => sq_nonneg _) (fun i hi => by rw [hu i hi]; norm_num) s

lemma supported_shift_mass (n k : ℕ) (u : ℕ → ℝ) (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (s : Finset ℕ) :
    (∑ i ∈ s, u (i + k) ^ 2) ≤ ∑ i ∈ Finset.range (n + 1), u i ^ 2 := by
  have he : (∑ i ∈ s, u (i + k) ^ 2) = ∑ i ∈ s.image (fun i => i + k), u i ^ 2 := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => Nat.add_right_cancel h
  rw [he]
  exact supported_mass n u hu _

lemma supported_energy_tail (n : ℕ) (u : ℕ → ℝ) (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (s : Finset ℕ) (r : ℝ) (hr : ∀ i ∈ s, r ≤ (i + 1 : ℝ) / (n + 1)) :
    r * (∑ i ∈ s, u i ^ 2) ≤ 2 * pathEnergy n u := by
  calc
    _ = ∑ i ∈ s, r * u i ^ 2 := Finset.mul_sum ..
    _ ≤ ∑ i ∈ s, (i + 1 : ℝ) / (n + 1) * u i ^ 2 := by
      gcongr with i hi
      exact hr i hi
    _ ≤ ∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (n + 1) * u i ^ 2 :=
      sum_supported_le _ _ (by intro i; positivity)
        (fun i hi => by rw [hu i hi]; ring) s
    _ ≤ _ := pathEnergy_weighted_mass n u

lemma supported_energy_gradient (n : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0) (s : Finset ℕ) :
    (∑ i ∈ s, (u (i + 1) - u i) ^ 2) ≤ 20 * pathEnergy n u := by
  have hs := sum_supported_le (n + 1) (fun i => (u (i + 1) - u i) ^ 2)
    (fun _ => sq_nonneg _) (fun i hi => by rw [hu i hi, hu (i + 1) (by omega)]; ring) s
  rw [Finset.sum_range_succ, hu (n + 1) le_rfl, zero_sub, neg_sq] at hs
  have hn := supported_energy_tail n u hu {n} 1 (by
    intro i hi
    have : i = n := Finset.mem_singleton.mp hi
    subst i
    rw [div_self (by positivity : (n + 1 : ℝ) ≠ 0)])
  simp only [Finset.sum_singleton, one_mul] at hn
  have hg := pathEnergy_gradient n u
  linarith

lemma supported_shift_energy_gradient (n k : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0) (s : Finset ℕ) :
    (∑ i ∈ s, (u (i + k + 1) - u (i + k)) ^ 2) ≤ 20 * pathEnergy n u := by
  have he : (∑ i ∈ s, (u (i + k + 1) - u (i + k)) ^ 2) =
      ∑ i ∈ s.image (fun i => i + k), (u (i + 1) - u i) ^ 2 := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => Nat.add_right_cancel h
  rw [he]
  exact supported_energy_gradient n u hu _

lemma many_block_prefix_abs_bound (ξ w : ℕ → ℝ) (d : ℕ) (B : Finset ℕ)
    (hd : 0 < d) {bnd : ℝ} (hbnd : 0 ≤ bnd)
    (hpref : ∀ b ∈ B, ∀ k < d,
      |∑ i ∈ Finset.range (k + 1), ξ (b * d + i)| ≤ bnd) :
    (∑ b ∈ B, |∑ i ∈ Finset.range d, ξ (b * d + i) * w (b * d + i)|) ≤
      bnd / d * (∑ i ∈ blockIndices d d B, |w i|) +
        2 * bnd * ∑ i ∈ blockIndices d (d - 1) B, |w (i + 1) - w i| := by
  have hd' : d - 1 + 1 = d := by omega
  have hblock (b : ℕ) (hb : b ∈ B) := block_prefix_weight_bound
    (fun i => ξ (b * d + i)) (fun i => w (b * d + i)) (d - 1) hbnd
    (fun k hk => hpref b hb k (by omega))
  simp only [hd', Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd)), Nat.cast_one,
    sub_add_cancel] at hblock
  calc
    _ ≤ ∑ b ∈ B, (bnd / d * (∑ i ∈ Finset.range d, |w (b * d + i)|) +
        2 * bnd * ∑ i ∈ Finset.range (d - 1), |w (b * d + i + 1) - w (b * d + i)|) := by
      exact Finset.sum_le_sum (fun b hb => by simpa only [Nat.add_assoc] using hblock b hb)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [blockIndices_sum d d B hd le_rfl (fun i => |w i|),
        blockIndices_sum d (d - 1) B hd (Nat.sub_le _ _) (fun i => |w (i + 1) - w i|)]

lemma supported_shift_energy_tail (n k : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0) (s : Finset ℕ) (r : ℝ)
    (hr : ∀ i ∈ s, r ≤ (i + k + 1 : ℕ) / (n + 1 : ℝ)) :
    r * (∑ i ∈ s, u (i + k) ^ 2) ≤ 2 * pathEnergy n u := by
  have he : (∑ i ∈ s, u (i + k) ^ 2) = ∑ i ∈ s.image (fun i => i + k), u i ^ 2 := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => Nat.add_right_cancel h
  rw [he]
  apply supported_energy_tail n u hu _ r
  intro i hi
  rcases Finset.mem_image.mp hi with ⟨j, hj, hji⟩
  subst i
  simpa only [Nat.cast_add, Nat.cast_one] using hr j hj

lemma localized_product_mass (s : Finset ℕ) (u : ℕ → ℝ) {M : ℝ}
    (h0 : (∑ i ∈ s, u i ^ 2) ≤ M) (h1 : (∑ i ∈ s, u (i + 1) ^ 2) ≤ M) :
    (∑ i ∈ s, |u i * u (i + 1)|) ≤ M := by
  have h : (∑ i ∈ s, |u i * u (i + 1)|) ≤
      (∑ i ∈ s, (u i ^ 2 + u (i + 1) ^ 2) / 2) := by
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    nlinarith [sq_abs (u i), sq_abs (u (i + 1)), sq_nonneg (|u i| - |u (i + 1)|)]
  rw [← Finset.sum_div, Finset.sum_add_distrib] at h
  linarith

lemma localized_square_variation (n : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0) (s : Finset ℕ) {M : ℝ} (hM : 0 ≤ M)
    (h0 : (∑ i ∈ s, u i ^ 2) ≤ M) (h1 : (∑ i ∈ s, u (i + 1) ^ 2) ≤ M) :
    (∑ i ∈ s, |u (i + 1) ^ 2 - u i ^ 2|) ≤
      Real.sqrt (80 * pathEnergy n u * M) := by
  have hs := square_weight_variation s u
  have hg := supported_energy_gradient n u hu s
  have he := pathEnergy_nonneg n u
  have hm : (2 * ∑ i ∈ s, (u i ^ 2 + u (i + 1) ^ 2)) ≤ 4 * M := by
    rw [Finset.sum_add_distrib]
    linarith
  have hn : 0 ≤ ∑ i ∈ s, (u (i + 1) - u i) ^ 2 := by positivity
  have hb := mul_le_mul hg hm (by positivity) (by positivity : 0 ≤ 20 * pathEnergy n u)
  have hsq : (∑ i ∈ s, |u (i + 1) ^ 2 - u i ^ 2|) ^ 2 ≤ 80 * pathEnergy n u * M := by
    nlinarith
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr hsq

lemma localized_product_variation (n : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0) (s : Finset ℕ) {M : ℝ} (hM : 0 ≤ M)
    (h1 : (∑ i ∈ s, u (i + 1) ^ 2) ≤ M) :
    (∑ i ∈ s, |u (i + 1) * u (i + 2) - u i * u (i + 1)|) ≤
      Real.sqrt (80 * pathEnergy n u * M) := by
  have hs := product_weight_variation s u
  have hg0 := supported_energy_gradient n u hu s
  have hg1 := supported_shift_energy_gradient n 1 u hu s
  have he := pathEnergy_nonneg n u
  have hg : (2 * ∑ i ∈ s, ((u (i + 1) - u i) ^ 2 + (u (i + 2) - u (i + 1)) ^ 2)) ≤
      80 * pathEnergy n u := by
    rw [Finset.sum_add_distrib]
    simp only [Nat.add_assoc] at hg1
    linarith
  have hn : 0 ≤ ∑ i ∈ s, u (i + 1) ^ 2 := by positivity
  have hb := mul_le_mul hg h1 hn (by positivity : 0 ≤ 80 * pathEnergy n u)
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr (hs.trans hb)

lemma sum_covered_by_shells (B R : Finset ℕ) (S : ℕ → Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ b, 0 ≤ f b) (hcover : ∀ b ∈ B, ∃ r ∈ R, b ∈ S r) :
    (∑ b ∈ B, f b) ≤ ∑ r ∈ R, ∑ b ∈ B.filter (fun b => b ∈ S r), f b := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b hb
  obtain ⟨r, hr, hbr⟩ := hcover b hb
  calc
    f b = if b ∈ S r then f b else 0 := by rw [ite_eq_left hbr]
    _ ≤ ∑ x ∈ R, if b ∈ S x then f b else 0 := by
      exact Finset.single_le_sum (f := fun x => if b ∈ S x then f b else 0)
        (fun x _ => by split_ifs <;> first | exact hf b | exact le_rfl) hr

lemma sum_range_eq_of_supported (f : ℕ → ℝ) (N M : ℕ) (hNM : N ≤ M)
    (hf : ∀ i, N ≤ i → f i = 0) :
    (∑ i ∈ Finset.range M, f i) = ∑ i ∈ Finset.range N, f i := by
  symm
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro i _ hi
  exact hf i (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hi))

lemma shell_indices_mass (n j r d l k : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i ^ 2) = 1)
    (B : Finset ℕ) (hB : ∀ b ∈ B, b ∈ blockShell j r)
    {σ : ℝ} (hσ : 0 < σ) (he : pathEnergy n u ≤ σ)
    (hsize : (n + 1 : ℝ) * σ ≤ (8 : ℝ)^j * d) :
    (∑ i ∈ blockIndices d l B, u (i + k) ^ 2) ≤ 2 * (1 / 2 : ℝ) ^ r := by
  by_cases hr : r = 0
  · subst r
    have hm := supported_shift_mass n k u hu (blockIndices d l B)
    rw [hnorm] at hm
    simpa only [pow_zero, mul_one] using hm.trans (by norm_num : (1 : ℝ) ≤ 2)
  · have hr' : 0 < r := Nat.pos_of_ne_zero hr
    have hlo (i : ℕ) (hi : i ∈ blockIndices d l B) :
        (2 : ℝ) ^ r * σ ≤ (i + k + 1 : ℕ) / (n + 1 : ℝ) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
      have hi' := blockIndices_lower d l (2 ^ r * 8 ^ j * d) B
        (fun b hb => Nat.mul_le_mul_right d (blockShell_lower j r b hr' (hB b hb))) i hi
      have hc : (2 : ℝ)^r * 8^j * d ≤ (i : ℝ) + k + 1 := by
        exact_mod_cast hi'.trans (by omega : i ≤ i + k + 1)
      have hm := mul_le_mul_of_nonneg_left hsize (by positivity : (0 : ℝ) ≤ 2^r)
      push_cast
      nlinarith
    have ht := supported_shift_energy_tail n k u hu (blockIndices d l B)
      ((2 : ℝ)^r * σ) hlo
    have hm : (2 : ℝ)^r * (∑ i ∈ blockIndices d l B, u (i + k)^2) ≤ 2 := by
      apply (mul_le_mul_iff_right₀ hσ).mp
      nlinarith
    have hp : (2 : ℝ)^r * (1 / 2 : ℝ)^r = 1 := by
      rw [← mul_pow]
      norm_num
    nlinarith [show (0 : ℝ) < 2^r by positivity]

lemma half_pow_le_three_quarters_sq (r : ℕ) :
    (1 / 2 : ℝ)^r ≤ ((3 / 4 : ℝ)^r)^2 := by
  rw [← pow_mul, mul_comm r 2, pow_mul]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) r

lemma sqrt_shell_energy_bound {e : ℝ} (he : 0 ≤ e) (r : ℕ) :
    Real.sqrt (80 * e * (2 * (1 / 2 : ℝ)^r)) ≤
      13 * Real.sqrt e * (3 / 4 : ℝ)^r := by
  apply (Real.sqrt_le_iff).mpr ⟨by positivity, ?_⟩
  have hp := half_pow_le_three_quarters_sq r
  have hs := Real.sq_sqrt he
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 160 * e)
  nlinarith [sq_nonneg ((3 / 4 : ℝ)^r)]

lemma shell_square_mass_variation (n j r d : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i ^ 2) = 1)
    (B : Finset ℕ) (hB : ∀ b ∈ B, b ∈ blockShell j r)
    {σ : ℝ} (hσ : 0 < σ) (he : pathEnergy n u ≤ σ)
    (hsize : (n + 1 : ℝ) * σ ≤ (8 : ℝ)^j * d) :
    (∑ i ∈ blockIndices d d B, |u i ^ 2|) ≤ 2 * (3 / 4 : ℝ)^r ∧
    (∑ i ∈ blockIndices d (d - 1) B, |u (i + 1)^2 - u i^2|) ≤
      13 * Real.sqrt (pathEnergy n u) * (3 / 4 : ℝ)^r := by
  have hm (l k : ℕ) := shell_indices_mass n j r d l k u hu hnorm B hB hσ he hsize
  constructor
  · simp only [abs_sq]
    have h0 := hm d 0
    simp only [Nat.add_zero] at h0
    exact h0.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) _) (by norm_num))
  · apply (localized_square_variation n u hu _ (by positivity)
      (by simpa only [Nat.add_zero] using hm (d - 1) 0) (hm (d - 1) 1)).trans
    exact sqrt_shell_energy_bound (pathEnergy_nonneg n u) r

lemma shell_product_mass_variation (n j r d : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i ^ 2) = 1)
    (B : Finset ℕ) (hB : ∀ b ∈ B, b ∈ blockShell j r)
    {σ : ℝ} (hσ : 0 < σ) (he : pathEnergy n u ≤ σ)
    (hsize : (n + 1 : ℝ) * σ ≤ (8 : ℝ)^j * d) :
    (∑ i ∈ blockIndices d d B, |u i * u (i + 1)|) ≤ 2 * (3 / 4 : ℝ)^r ∧
    (∑ i ∈ blockIndices d (d - 1) B, |u (i + 1) * u (i + 2) - u i * u (i + 1)|) ≤
      13 * Real.sqrt (pathEnergy n u) * (3 / 4 : ℝ)^r := by
  have hm (l k : ℕ) := shell_indices_mass n j r d l k u hu hnorm B hB hσ he hsize
  constructor
  · apply (localized_product_mass _ u
      (by simpa only [Nat.add_zero] using hm d 0) (hm d 1)).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) _) (by norm_num)
  · exact (localized_product_variation n u hu _ (by positivity) (hm (d - 1) 1)).trans
      (sqrt_shell_energy_bound (pathEnergy_nonneg n u) r)

lemma weighted_geometric_three_quarters (N : ℕ) :
    (∑ r ∈ Finset.range N, (r + 1 : ℝ) * (3 / 4 : ℝ)^r) ≤ 16 := by
  have hident : (∑ r ∈ Finset.range N, (r + 1 : ℝ) * (3 / 4 : ℝ)^r) =
      16 - (4 * N + 16) * (3 / 4 : ℝ)^N := by
    induction N with
    | zero => norm_num
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; push_cast; ring
  rw [hident]
  have : 0 ≤ (4 * N + 16) * (3 / 4 : ℝ)^N := by positivity
  linarith

lemma shifted_weighted_geometric {a : ℝ} (ha : 1 ≤ a) (N : ℕ) :
    (∑ r ∈ Finset.range N, (a + r) * (3 / 4 : ℝ)^r) ≤ 16 * a := by
  calc
    _ ≤ ∑ r ∈ Finset.range N, a * ((r + 1) * (3 / 4 : ℝ)^r) := by
      apply Finset.sum_le_sum
      intro r _
      have h : a + r ≤ a * (r + 1) := by nlinarith [show (0 : ℝ) ≤ r by positivity]
      nlinarith [mul_le_mul_of_nonneg_right h (by positivity : (0 : ℝ) ≤ (3 / 4 : ℝ)^r)]
    _ = a * ∑ r ∈ Finset.range N, (r + 1 : ℝ) * (3 / 4 : ℝ)^r := by rw [Finset.mul_sum]
    _ ≤ 16 * a := by nlinarith [weighted_geometric_three_quarters N]

lemma weighted_multiscale_prefix (ξ w : ℕ → ℝ) (N j d : ℕ) (hd : 0 < d)
    (hw : ∀ i, N ≤ i → w i = 0) {h K e : ℝ} (hh : 0 ≤ h) (hK : 0 ≤ K) (_he : 0 ≤ e)
    (hpref : ∀ r < N, ∀ b < N, b ∈ blockShell j r → ∀ k < d,
      |∑ i ∈ Finset.range (k + 1), ξ (b * d + i)| ≤ K * (h + j + r + 1))
    (hmass : ∀ r < N, (∑ i ∈ blockIndices d d
      ((Finset.range N).filter (fun b => b ∈ blockShell j r)), |w i|) ≤ 2 * (3 / 4 : ℝ)^r)
    (hvar : ∀ r < N, (∑ i ∈ blockIndices d (d - 1)
      ((Finset.range N).filter (fun b => b ∈ blockShell j r)), |w (i + 1) - w i|) ≤
        13 * Real.sqrt e * (3 / 4 : ℝ)^r) :
    |∑ i ∈ Finset.range N, ξ i * w i| ≤
      32 * K * (h + j + 1) * (1 / d + 13 * Real.sqrt e) := by
  have hblock (r : ℕ) (hr : r < N) := many_block_prefix_abs_bound ξ w d
    ((Finset.range N).filter (fun b => b ∈ blockShell j r)) hd
    (by positivity : 0 ≤ K * (h + j + r + 1))
    (fun b hb k hk => hpref r hr b (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
      (Finset.mem_filter.mp hb).2 k hk)
  have hblock' (r : ℕ) (hr : r < N) :
      (∑ b ∈ (Finset.range N).filter (fun b => b ∈ blockShell j r),
        |∑ i ∈ Finset.range d, ξ (b * d + i) * w (b * d + i)|) ≤
      K * (2 / d + 26 * Real.sqrt e) * ((h + j + 1 + r) * (3 / 4 : ℝ)^r) := by
    calc
      _ ≤ K * (h + j + r + 1) / d * (2 * (3 / 4 : ℝ)^r) +
          2 * (K * (h + j + r + 1)) * (13 * Real.sqrt e * (3 / 4 : ℝ)^r) := by
        apply (hblock r hr).trans
        exact add_le_add (mul_le_mul_of_nonneg_left (hmass r hr) (by positivity))
          (mul_le_mul_of_nonneg_left (hvar r hr) (by positivity))
      _ = _ := by ring
  have hsum : (∑ i ∈ Finset.range N, ξ i * w i) =
      ∑ b ∈ Finset.range N, ∑ i ∈ Finset.range d, ξ (b * d + i) * w (b * d + i) := by
    rw [sum_consecutive_blocks N d (fun i => ξ i * w i)]
    symm
    exact sum_range_eq_of_supported (fun i => ξ i * w i) N (N * d)
      (by nlinarith) (fun i hi => by rw [hw i hi, mul_zero])
  rw [hsum]
  calc
    _ ≤ ∑ b ∈ Finset.range N, |∑ i ∈ Finset.range d, ξ (b * d + i) * w (b * d + i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Finset.range N, ∑ b ∈ (Finset.range N).filter (fun b => b ∈ blockShell j r),
        |∑ i ∈ Finset.range d, ξ (b * d + i) * w (b * d + i)| := by
      apply sum_covered_by_shells _ _ (blockShell j) _ (fun _ => abs_nonneg _)
      intro b hb
      obtain ⟨r, hr, hbr⟩ := blockShell_covers j b
      exact ⟨r, Finset.mem_range.mpr (hr.trans_lt (Finset.mem_range.mp hb)), hbr⟩
    _ ≤ ∑ r ∈ Finset.range N,
        K * (2 / d + 26 * Real.sqrt e) * ((h + j + 1 + r) * (3 / 4 : ℝ)^r) := by
      exact Finset.sum_le_sum (fun r hr => hblock' r (Finset.mem_range.mp hr))
    _ = K * (2 / d + 26 * Real.sqrt e) *
        (∑ r ∈ Finset.range N, ((h + j + 1 + r) * (3 / 4 : ℝ)^r)) := by rw [Finset.mul_sum]
    _ ≤ K * (2 / d + 26 * Real.sqrt e) * (16 * (h + j + 1)) := by
      exact mul_le_mul_of_nonneg_left (shifted_weighted_geometric (by linarith [show (0 : ℝ) ≤ j by positivity]) N) (by positivity)
    _ = _ := by ring

lemma square_multiscale_prefix (ξ : ℕ → ℝ) (n j d : ℕ) (hd : 0 < d) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i ^ 2) = 1)
    {σ h K : ℝ} (hσ : 0 < σ) (hh : 0 ≤ h) (hK : 0 ≤ K)
    (he : pathEnergy n u ≤ σ) (hsize : (n + 1 : ℝ) * σ ≤ (8 : ℝ)^j * d)
    (hpref : ∀ r < n + 1, ∀ b < n + 1, b ∈ blockShell j r → ∀ k < d,
      |∑ i ∈ Finset.range (k + 1), ξ (b * d + i)| ≤ K * (h + j + r + 1)) :
    |∑ i ∈ Finset.range (n + 1), ξ i * u i^2| ≤
      32 * K * (h + j + 1) * (1 / d + 13 * Real.sqrt (pathEnergy n u)) := by
  have hmv (r : ℕ) := shell_square_mass_variation n j r d u hu hnorm
    ((Finset.range (n + 1)).filter (fun b => b ∈ blockShell j r))
    (fun _ hb => (Finset.mem_filter.mp hb).2) hσ he hsize
  exact weighted_multiscale_prefix ξ (fun i => u i^2) (n + 1) j d hd
    (fun i hi => by rw [hu i hi]; norm_num) hh hK (pathEnergy_nonneg n u) hpref
    (fun r _ => (hmv r).1) (fun r _ => (hmv r).2)

lemma product_multiscale_prefix (ξ : ℕ → ℝ) (n j d : ℕ) (hd : 0 < d) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i ^ 2) = 1)
    {σ h K : ℝ} (hσ : 0 < σ) (hh : 0 ≤ h) (hK : 0 ≤ K)
    (he : pathEnergy n u ≤ σ) (hsize : (n + 1 : ℝ) * σ ≤ (8 : ℝ)^j * d)
    (hpref : ∀ r < n + 1, ∀ b < n + 1, b ∈ blockShell j r → ∀ k < d,
      |∑ i ∈ Finset.range (k + 1), ξ (b * d + i)| ≤ K * (h + j + r + 1)) :
    |∑ i ∈ Finset.range (n + 1), ξ i * (u i * u (i + 1))| ≤
      32 * K * (h + j + 1) * (1 / d + 13 * Real.sqrt (pathEnergy n u)) := by
  have hmv (r : ℕ) := shell_product_mass_variation n j r d u hu hnorm
    ((Finset.range (n + 1)).filter (fun b => b ∈ blockShell j r))
    (fun _ hb => (Finset.mem_filter.mp hb).2) hσ he hsize
  exact weighted_multiscale_prefix ξ (fun i => u i * u (i + 1)) (n + 1) j d hd
    (fun i hi => by rw [hu i hi, zero_mul]) hh hK (pathEnergy_nonneg n u) hpref
    (fun r _ => (hmv r).1) (fun r _ => by simpa only [Nat.add_assoc] using (hmv r).2)

lemma blockThreshold_linear_bound (c : ℝ≥0) (m j r : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    blockThreshold c m j r h ≤
      Real.sqrt (32 * (c : ℝ)) * Real.sqrt (m + 1) * (h + j + r + 1) := by
  have hlog : Real.log 16 ≤ 15 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16) using 1
    norm_num
  have hjr : (0 : ℝ) ≤ j + r := by positivity
  have hq : h^2 + (j + r : ℕ) * Real.log 16 ≤ 16 * (h + j + r + 1)^2 := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hlog hjr, mul_nonneg hh hjr,
      sq_nonneg h, sq_nonneg ((j : ℝ) + r)]
  unfold blockThreshold
  apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  calc
    _ ≤ 2 * (m + 1) * (c : ℝ) * (16 * (h + j + r + 1)^2) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      ring

lemma blockThreshold_length_bound (c : ℝ≥0) (d j r : ℕ) (hd : 0 < d) {h : ℝ} (hh : 0 ≤ h) :
    blockThreshold c (d - 1) j r h ≤
      Real.sqrt (32 * (c : ℝ)) * Real.sqrt d * (h + j + r + 1) := by
  have hd' : (d - 1 : ℝ) + 1 = d := by ring
  have hnat : 1 ≤ d := hd
  simpa only [Nat.cast_sub hnat, Nat.cast_one, hd'] using blockThreshold_linear_bound c (d - 1) j r hh

end CriticalSK

end

end OAI
