import Mathlib

namespace OAI

/-!
# Finite-volume invariant Ising pressure

The spin prior is uniform probability, as in (1.1) and (7.1) of
*All-temperature pressure for orthogonally invariant Ising spin glasses*.
These deterministic comparison lemmas do not assume any asymptotic pressure formula.
-/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

/-- The cube, with exactly `2^N` configurations. -/
abbrev Spin (N : ℕ) := Fin N → Bool

/-- Real spin coordinates. -/
def spinValue (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma abs_spinValue (b : Bool) : |spinValue b| = 1 := by
  cases b <;> norm_num [spinValue]

@[simp] lemma spinValue_sq (b : Bool) : spinValue b ^ 2 = 1 := by
  cases b <;> norm_num [spinValue]

/-- Log partition with the uniform probability prior on a finite state space. -/
def logPartition {X : Type*} [Fintype X] (H : X → ℝ) : ℝ :=
  Real.log ((Fintype.card X : ℝ)⁻¹ * ∑ x, Real.exp (H x))

lemma sum_exp_pos {X : Type*} [Fintype X] [Nonempty X] (H : X → ℝ) :
    0 < ∑ x, Real.exp (H x) := by
  exact Finset.sum_pos (fun x _ => Real.exp_pos (H x)) Finset.univ_nonempty

lemma logPartition_eq {X : Type*} [Fintype X] [Nonempty X] (H : X → ℝ) :
    logPartition H = Real.log (∑ x, Real.exp (H x)) - Real.log (Fintype.card X) := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [logPartition, Real.log_mul (inv_ne_zero hc) (sum_exp_pos H).ne', Real.log_inv]
  ring

lemma logPartition_add_const {X : Type*} [Fintype X] [Nonempty X]
    (H : X → ℝ) (c : ℝ) :
    logPartition (fun x => H x + c) = logPartition H + c := by
  rw [logPartition_eq, logPartition_eq]
  simp_rw [Real.exp_add]
  rw [← Finset.sum_mul, Real.log_mul (sum_exp_pos H).ne' (Real.exp_ne_zero c),
    Real.log_exp]
  ring

lemma logPartition_le_add {X : Type*} [Fintype X] [Nonempty X]
    (H K : X → ℝ) (c : ℝ) (h : ∀ x, H x ≤ K x + c) :
    logPartition H ≤ logPartition K + c := by
  have hs : (∑ x, Real.exp (H x)) ≤ ∑ x, Real.exp (K x + c) :=
    Finset.sum_le_sum fun x _ => Real.exp_le_exp.mpr (h x)
  have hl : logPartition H ≤ logPartition (fun x => K x + c) := by
    rw [logPartition_eq, logPartition_eq]
    exact sub_le_sub_right (Real.log_le_log (sum_exp_pos H) hs) _
  simpa only [logPartition_add_const] using hl

lemma abs_logPartition_sub_le {X : Type*} [Fintype X] [Nonempty X]
    (H K : X → ℝ) (c : ℝ) (h : ∀ x, |H x - K x| ≤ c) :
    |logPartition H - logPartition K| ≤ c := by
  have h₁ := logPartition_le_add H K c fun x => by
    have := (abs_le.mp (h x)).2
    linarith
  have h₂ := logPartition_le_add K H c fun x => by
    have := (abs_le.mp (h x)).1
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Quadratic interaction energy, including the diagonal. -/
def quadraticEnergy {N : ℕ} (J : Matrix (Fin N) (Fin N) ℝ) (σ : Spin N) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, spinValue (σ i) * J i j * spinValue (σ j)

/-- Deterministic magnetic energy. -/
def fieldEnergy {N : ℕ} (c : Fin N → ℝ) (σ : Spin N) : ℝ :=
  ∑ i, c i * spinValue (σ i)

/-- Finite-volume pressure, normalized per site and by the probability spin prior. -/
def pressure {N : ℕ} (J : Matrix (Fin N) (Fin N) ℝ) (c : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * logPartition (fun σ => quadraticEnergy J σ + fieldEnergy c σ)

lemma fieldEnergy_sub {N : ℕ} (c d : Fin N → ℝ) (σ : Spin N) :
    fieldEnergy c σ - fieldEnergy d σ = ∑ i, (c i - d i) * spinValue (σ i) := by
  simp only [fieldEnergy, ← Finset.sum_sub_distrib, sub_mul]

lemma abs_fieldEnergy_sub_le {N : ℕ} (c d : Fin N → ℝ) (σ : Spin N) :
    |fieldEnergy c σ - fieldEnergy d σ| ≤ ∑ i, |c i - d i| := by
  rw [fieldEnergy_sub]
  calc
    |∑ i, (c i - d i) * spinValue (σ i)| ≤
        ∑ i, |(c i - d i) * spinValue (σ i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |c i - d i| := by simp only [abs_mul, abs_spinValue, mul_one]

/-- Equation (7.26): the normalized pressure is Lipschitz in the average field distance. -/
lemma abs_pressure_sub_field_le {N : ℕ} (J : Matrix (Fin N) (Fin N) ℝ)
    (c d : Fin N → ℝ) :
    |pressure J c - pressure J d| ≤ (N : ℝ)⁻¹ * ∑ i, |c i - d i| := by
  have h := abs_logPartition_sub_le
    (fun σ => quadraticEnergy J σ + fieldEnergy c σ)
    (fun σ => quadraticEnergy J σ + fieldEnergy d σ)
    (∑ i, |c i - d i|) (fun σ => by
      simpa only [add_sub_add_left_eq_sub] using abs_fieldEnergy_sub_le c d σ)
  simpa only [pressure, ← mul_sub, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
    using mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Nat.cast_nonneg N))

/-- Scalar diagonal shifts are deterministic on the Ising cube. -/
lemma quadraticEnergy_add_scalar {N : ℕ} (J : Matrix (Fin N) (Fin N) ℝ)
    (a : ℝ) (σ : Spin N) :
    quadraticEnergy (J + a • (1 : Matrix (Fin N) (Fin N) ℝ)) σ =
      quadraticEnergy J σ + a * N / 2 := by
  classical
  have hdiag : (∑ i : Fin N, ∑ j : Fin N,
      spinValue (σ i) * (a • (1 : Matrix (Fin N) (Fin N) ℝ)) i j *
        spinValue (σ j)) = a * N := by
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    simp_rw [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have he : ∀ i : Fin N, spinValue (σ i) * a * spinValue (σ i) = a := by
      intro i
      calc
        spinValue (σ i) * a * spinValue (σ i) = a * spinValue (σ i) ^ 2 := by ring
        _ = a := by rw [spinValue_sq, mul_one]
    simp_rw [he]
    simp [mul_comm]
  unfold quadraticEnergy
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  rw [hdiag]
  ring

/-- Equation (6.7): adding a scalar to the spectrum shifts pressure by half that scalar. -/
lemma pressure_add_scalar {N : ℕ} (hN : 0 < N)
    (J : Matrix (Fin N) (Fin N) ℝ) (c : Fin N → ℝ) (a : ℝ) :
    pressure (J + a • (1 : Matrix (Fin N) (Fin N) ℝ)) c = pressure J c + a / 2 := by
  simp only [pressure, quadraticEnergy_add_scalar]
  have he : (fun σ => quadraticEnergy J σ + a * N / 2 + fieldEnergy c σ) =
      (fun σ => quadraticEnergy J σ + fieldEnergy c σ + a * N / 2) := by
    funext σ
    ring
  rw [he, logPartition_add_const]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp

/-- A pointwise energy comparison gives the deterministic pressure comparison
used for spectral approximation in Section 6. -/
lemma abs_pressure_sub_interaction_le {N : ℕ}
    (J K : Matrix (Fin N) (Fin N) ℝ) (c : Fin N → ℝ) (δ : ℝ)
    (h : ∀ σ : Spin N, |quadraticEnergy J σ - quadraticEnergy K σ| ≤ N * δ) :
    |pressure J c - pressure K c| ≤ (N : ℝ)⁻¹ * (N * δ) := by
  have hp := abs_logPartition_sub_le
    (fun σ => quadraticEnergy J σ + fieldEnergy c σ)
    (fun σ => quadraticEnergy K σ + fieldEnergy c σ)
    (N * δ) (fun σ => by simpa only [add_sub_add_right_eq_sub] using h σ)
  simpa only [pressure, ← mul_sub, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
    using mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)

/-- The elementary log-sum bound, with the probability prior's entropy cost. -/
lemma logPartition_bounds {X : Type*} [Fintype X] [Nonempty X]
    (H : X → ℝ) (M : ℝ) (hM : ∀ x, H x ≤ M) (hx : ∃ x, H x = M) :
    M - Real.log (Fintype.card X) ≤ logPartition H ∧ logPartition H ≤ M := by
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hlo : Real.exp M ≤ ∑ x, Real.exp (H x) := by
    obtain ⟨x, hx⟩ := hx
    rw [← hx]
    exact Finset.single_le_sum (fun y _ => (Real.exp_pos (H y)).le) (Finset.mem_univ x)
  have hup : (∑ x, Real.exp (H x)) ≤ Fintype.card X * Real.exp M := by
    calc
      _ ≤ ∑ _ : X, Real.exp M :=
        Finset.sum_le_sum fun x _ => Real.exp_le_exp.mpr (hM x)
      _ = _ := by simp
  rw [logPartition_eq]
  constructor
  · exact sub_le_sub_right (by simpa using Real.log_le_log (Real.exp_pos M) hlo) _
  · have hl := Real.log_le_log (sum_exp_pos H) hup
    rw [Real.log_mul hc.ne' (Real.exp_ne_zero M), Real.log_exp] at hl
    linarith

/-- Uniform cube entropy is `N log 2`. -/
lemma log_card_spin (N : ℕ) : Real.log (Fintype.card (Spin N)) = N * Real.log 2 := by
  simp only [Spin, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

/-- Soft maximum estimate used in the zero-temperature corollary, valid at every
finite dimension and every positive inverse temperature. -/
lemma finite_groundState_squeeze {N : ℕ} (hN : 0 < N) (H : Spin N → ℝ)
    (β E : ℝ) (hβ : 0 < β) (hE : ∀ σ, H σ ≤ N * E)
    (hatt : ∃ σ, H σ = N * E) :
    E - Real.log 2 / β ≤ (N : ℝ)⁻¹ * logPartition (fun σ => β * H σ) / β ∧
      (N : ℝ)⁻¹ * logPartition (fun σ => β * H σ) / β ≤ E := by
  have hscale : ∀ σ, β * H σ ≤ β * (N * E) :=
    fun σ => mul_le_mul_of_nonneg_left (hE σ) hβ.le
  have hatt' : ∃ σ, β * H σ = β * (N * E) := by
    obtain ⟨σ, hσ⟩ := hatt
    exact ⟨σ, by rw [hσ]⟩
  obtain ⟨hlo, hhi⟩ := logPartition_bounds (fun σ => β * H σ) (β * (N * E)) hscale hatt'
  rw [log_card_spin] at hlo
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · have hl := mul_le_mul_of_nonneg_left hlo (inv_nonneg.mpr hn.le)
    apply (le_div_iff₀ hβ).mpr
    calc
      (E - Real.log 2 / β) * β = E * β - Real.log 2 := by field_simp
      _ = (N : ℝ)⁻¹ * (β * (N * E) - N * Real.log 2) := by field_simp
      _ ≤ _ := hl
  · apply (div_le_iff₀ hβ).mpr
    have hh := mul_le_mul_of_nonneg_left hhi (inv_nonneg.mpr hn.le)
    calc
      _ ≤ (N : ℝ)⁻¹ * (β * (N * E)) := hh
      _ = E * β := by field_simp

end InvariantIsing

end

end OAI
