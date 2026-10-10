import OAI.Geometry.RCD.Coordinates.WeightedConvolution
import Mathlib.Data.Nat.Dist
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-!
# Construction of the summable pinching envelope

The positive floor and the two geometric convolutions in
`pi:definition-E` are constructed here from a nonnegative summable
Poisson-defect sequence. No summability of square roots is assumed.
-/

open scoped BigOperators

noncomputable section

namespace RegularPointCoordinates

def forwardDefect (σ η : ℝ) (P : ℕ → ℝ) (i : ℕ) : ℝ :=
  η * σ ^ i + ∑ j ∈ Finset.range (i + 1), σ ^ (i - j) * P j

def symmetricDefect (ρ : ℝ) (P : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑' j, ρ ^ Nat.dist i j * P j

def pinchingEnvelope (ρ σ η : ℝ) (P : ℕ → ℝ) : ℕ → ℝ :=
  symmetricDefect ρ (forwardDefect σ η P)

theorem forwardDefect_nonneg {σ η : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η)
    {P : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (i : ℕ) :
    0 ≤ forwardDefect σ η P i :=
  add_nonneg (mul_nonneg hη (pow_nonneg hσ _))
    (Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg hσ _) (hP j))

theorem le_forwardDefect {σ η : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η)
    {P : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (i : ℕ) :
    P i ≤ forwardDefect σ η P i := by
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.range (i + 1)) => mul_nonneg (pow_nonneg hσ (i - j)) (hP j))
    (Finset.mem_range.mpr (Nat.lt_succ_self i))
  simp only [Nat.sub_self, pow_zero, one_mul] at h
  exact h.trans (le_add_of_nonneg_left (mul_nonneg hη (pow_nonneg hσ i)))

theorem forwardDefect_budget {σ η : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ < 1)
    (hη : 0 ≤ η) {P : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (hPs : Summable P) :
    Summable (forwardDefect σ η P) ∧
      (∑' i, forwardDefect σ η P i) ≤ (1 - σ)⁻¹ * (η + ∑' i, P i) := by
  have hg : Summable (fun i : ℕ => σ ^ i) := summable_geometric_of_lt_one hσ hσ1
  have hgvalue : (∑' i : ℕ, σ ^ i) = (1 - σ)⁻¹ := tsum_geometric_of_lt_one hσ hσ1
  have hfinite (k : ℕ) :
      (∑ i ∈ Finset.range k, forwardDefect σ η P i) ≤
        (1 - σ)⁻¹ * (η + ∑' i, P i) := by
    have hgeom := hg.sum_le_tsum (Finset.range k) (fun i _ => pow_nonneg hσ i)
    rw [hgvalue] at hgeom
    have hsum := hPs.sum_le_tsum (Finset.range k) (fun i _ => hP i)
    have hconv := weighted_geometric_stationary_convolution_le k P hP hσ hσ1
    have hcoeff : 0 ≤ (1 - σ)⁻¹ := by positivity
    simp only [forwardDefect, Finset.sum_add_distrib, ← Finset.mul_sum]
    have he := mul_le_mul_of_nonneg_left hgeom hη
    have hp := mul_le_mul_of_nonneg_left hsum hcoeff
    nlinarith
  exact ⟨summable_of_sum_range_le (forwardDefect_nonneg hσ hη hP) hfinite,
    Real.tsum_le_of_sum_range_le (forwardDefect_nonneg hσ hη hP) hfinite⟩

/-- A geometric kernel on the nonnegative integers has a uniform row
sum bound, also at rows next to the endpoint. -/
theorem geometric_distance_sum_le {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (i : ℕ) (s : Finset ℕ) :
    (∑ j ∈ s, ρ ^ Nat.dist i j) ≤ 2 * (1 - ρ)⁻¹ := by
  classical
  have hg : Summable (fun k : ℕ => ρ ^ k) := summable_geometric_of_lt_one hρ hρ1
  have hgv : (∑' k : ℕ, ρ ^ k) = (1 - ρ)⁻¹ := tsum_geometric_of_lt_one hρ hρ1
  let left := s.filter (fun j => j ≤ i)
  let right := s.filter (fun j => ¬ j ≤ i)
  have hl : (∑ j ∈ left, ρ ^ Nat.dist i j) ≤ (1 - ρ)⁻¹ := by
    have hinj : Set.InjOn (fun j => i - j) left := by
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      change i - a = i - b at hab
      omega
    calc
      _ = ∑ j ∈ left, ρ ^ (i - j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Nat.dist_eq_sub_of_le_right (Finset.mem_filter.mp hj).2]
      _ = ∑ k ∈ left.image (fun j => i - j), ρ ^ k := (Finset.sum_image hinj).symm
      _ ≤ ∑' k : ℕ, ρ ^ k := hg.sum_le_tsum _ (fun k _ => pow_nonneg hρ k)
      _ = _ := hgv
  have hr : (∑ j ∈ right, ρ ^ Nat.dist i j) ≤ (1 - ρ)⁻¹ := by
    have hinj : Set.InjOn (fun j => j - i) right := by
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      change a - i = b - i at hab
      omega
    calc
      _ = ∑ j ∈ right, ρ ^ (j - i) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hj).2))]
      _ = ∑ k ∈ right.image (fun j => j - i), ρ ^ k := (Finset.sum_image hinj).symm
      _ ≤ ∑' k : ℕ, ρ ^ k := hg.sum_le_tsum _ (fun k _ => pow_nonneg hρ k)
      _ = _ := hgv
  have he := Finset.sum_filter_add_sum_filter_not s (fun j => j ≤ i)
    (fun j => ρ ^ Nat.dist i j)
  change (∑ j ∈ left, ρ ^ Nat.dist i j) + (∑ j ∈ right, ρ ^ Nat.dist i j) = _ at he
  linarith

theorem geometric_distance_summable {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (i : ℕ) : Summable (fun j => ρ ^ Nat.dist i j) :=
  summable_of_sum_le (fun _ => pow_nonneg hρ _) (geometric_distance_sum_le hρ hρ1 i)

theorem geometric_distance_tsum_le {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (i : ℕ) : (∑' j, ρ ^ Nat.dist i j) ≤ 2 * (1 - ρ)⁻¹ :=
  Real.tsum_le_of_sum_le (fun _ => pow_nonneg hρ _) (geometric_distance_sum_le hρ hρ1 i)

theorem symmetricDefect_budget {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {P : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (hPs : Summable P) :
    Summable (symmetricDefect ρ P) ∧
      (∑' i, symmetricDefect ρ P i) ≤ 2 * (1 - ρ)⁻¹ * ∑' i, P i := by
  have hcol (j : ℕ) : Summable (fun i => ρ ^ Nat.dist i j * P j) := by
    simpa only [Nat.dist_comm] using (geometric_distance_summable hρ hρ1 j).mul_right (P j)
  have hcolbound (j : ℕ) : (∑' i, ρ ^ Nat.dist i j * P j) ≤
      2 * (1 - ρ)⁻¹ * P j := by
    rw [tsum_mul_right]
    simpa only [Nat.dist_comm] using mul_le_mul_of_nonneg_right
      (geometric_distance_tsum_le hρ hρ1 j) (hP j)
  have hnonneg : ∀ p : ℕ × ℕ, 0 ≤ ρ ^ Nat.dist p.2 p.1 * P p.1 :=
    fun p => mul_nonneg (pow_nonneg hρ _) (hP _)
  have hcols : Summable (fun j => ∑' i, ρ ^ Nat.dist i j * P j) :=
    Summable.of_nonneg_of_le (fun j => tsum_nonneg (fun i => hnonneg (j, i)))
      hcolbound (hPs.mul_left (2 * (1 - ρ)⁻¹))
  have hprod : Summable (fun p : ℕ × ℕ => ρ ^ Nat.dist p.2 p.1 * P p.1) :=
    (summable_prod_of_nonneg hnonneg).mpr ⟨hcol, hcols⟩
  have hrows := (summable_prod_of_nonneg
    (fun p : ℕ × ℕ => hnonneg (p.2, p.1))).mp hprod.prod_symm
  refine ⟨hrows.2, ?_⟩
  change (∑' i, ∑' j, ρ ^ Nat.dist i j * P j) ≤ _
  have hprod' : Summable (Function.uncurry fun j i => ρ ^ Nat.dist i j * P j) := hprod
  rw [hprod'.tsum_comm]
  calc
    _ ≤ ∑' j, 2 * (1 - ρ)⁻¹ * P j := hcols.tsum_le_tsum hcolbound
      (hPs.mul_left (2 * (1 - ρ)⁻¹))
    _ = _ := tsum_mul_left

theorem symmetricDefect_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ)
    {P : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (i : ℕ) :
    0 ≤ symmetricDefect ρ P i :=
  tsum_nonneg fun j => mul_nonneg (pow_nonneg hρ _) (hP j)

theorem symmetricDefect_row_summable {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {P : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (hPs : Summable P) (i : ℕ) :
    Summable (fun j => ρ ^ Nat.dist i j * P j) := by
  exact Summable.of_nonneg_of_le
    (fun j => mul_nonneg (pow_nonneg hρ _) (hP j))
    (fun j => mul_le_of_le_one_left (hP j) (pow_le_one₀ hρ hρ1.le)) hPs

theorem term_le_symmetricDefect {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {P : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (hPs : Summable P) (i j : ℕ) :
    ρ ^ Nat.dist i j * P j ≤ symmetricDefect ρ P i :=
  (symmetricDefect_row_summable hρ hρ1 hP hPs i).le_tsum j
    (fun k _ => mul_nonneg (pow_nonneg hρ _) (hP k))

theorem le_symmetricDefect {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {P : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (hPs : Summable P) (i : ℕ) :
    P i ≤ symmetricDefect ρ P i := by
  have h := term_le_symmetricDefect hρ hρ1 hP hPs i i
  simpa only [Nat.dist_self, pow_zero, one_mul] using h

/-- The two convolutions produce exactly the summability and positive
floor needed when choosing patch centers. The total is uniform whenever
the original Poisson-defect budget is uniform. -/
theorem pinchingEnvelope_spec {ρ σ η : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hη : 0 < η)
    {P : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (hPs : Summable P) :
    Summable (pinchingEnvelope ρ σ η P) ∧
      (∑' i, pinchingEnvelope ρ σ η P i) ≤
        (2 * (1 - ρ)⁻¹) * (1 - σ)⁻¹ * (η + ∑' i, P i) ∧
      ∀ i, P i ≤ pinchingEnvelope ρ σ η P i ∧
        η * ρ ^ i ≤ pinchingEnvelope ρ σ η P i ∧
        0 < pinchingEnvelope ρ σ η P i := by
  have hf := forwardDefect_budget hσ hσ1 hη.le hP hPs
  have hn := forwardDefect_nonneg hσ hη.le hP
  have he := symmetricDefect_budget hρ.le hρ1 hn hf.1
  refine ⟨he.1, ?_, fun i => ?_⟩
  · have hc : 0 ≤ 2 * (1 - ρ)⁻¹ := by positivity
    exact he.2.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hf.2 hc)
  · have hdom : P i ≤ pinchingEnvelope ρ σ η P i :=
      (le_forwardDefect hσ hη.le hP i).trans
        (le_symmetricDefect hρ.le hρ1 hn hf.1 i)
    have h0 : η ≤ forwardDefect σ η P 0 := by
      simpa [forwardDefect] using le_add_of_nonneg_right (hP 0) (a := η)
    have hterm := term_le_symmetricDefect hρ.le hρ1 hn hf.1 i 0
    have hfloor : η * ρ ^ i ≤ pinchingEnvelope ρ σ η P i := by
      simp only [Nat.dist_zero_right] at hterm
      calc
        η * ρ ^ i = ρ ^ i * η := mul_comm _ _
        _ ≤ ρ ^ i * forwardDefect σ η P 0 :=
          mul_le_mul_of_nonneg_left h0 (pow_nonneg hρ.le i)
        _ ≤ _ := hterm
    exact ⟨hdom, hfloor, (mul_pos hη (pow_pos hρ i)).trans_le hfloor⟩

end RegularPointCoordinates

end

end OAI
