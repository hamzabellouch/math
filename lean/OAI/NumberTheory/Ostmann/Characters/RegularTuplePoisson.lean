import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularTransfer
import OAI.NumberTheory.Ostmann.Arithmetic.PeriodicWeightPoisson
import OAI.NumberTheory.Ostmann.Characters.NormalizedFourierProfile

namespace OAI

/-! # Initial Poisson summation for the actual normalized residue transforms -/

namespace Ostmann
open scoped Classical BigOperators FourierTransform SchwartzMap

/-- Exact normalization and cofactor arguments for arbitrary local tests.
This applies to the phase giant and to every normalized residue indicator. -/
theorem tuple_regular_fourier {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (v : ℤ) :
    additiveFourier (tupleCRTFunction p hc F) (v : ZMod (∏ i, p i)) =
      (Real.sqrt (∏ i, p i : ℕ) : ℂ)⁻¹ *
        movingRegularTransform p (fun i => densityFourier (F i)) 1 v := by
  rw [tupleCRTFunction_fourier]
  simp only [map_intCast, Pi.intCast_apply]
  have hlocal (i : I) : additiveFourier (F i)
      ((tupleCofactor p i : ZMod (p i))⁻¹ * (v : ZMod (p i))) =
      (Real.sqrt (p i : ℝ) : ℂ)⁻¹ * densityFourier (F i)
        ((v : ZMod (p i)) * (tupleCofactor p i : ZMod (p i))⁻¹) := by
    have hs : (Real.sqrt (p i : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr
        (show (0 : ℝ) < p i by exact_mod_cast NeZero.pos (p i))).ne'
    unfold densityFourier
    rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul, mul_comm]
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib]
  have hs : (Real.sqrt (∏ i, p i : ℕ) : ℂ) = ∏ i, (Real.sqrt (p i : ℝ) : ℂ) := by
    rw [Nat.cast_prod, Real.sqrt_prod _ (fun i _ => Nat.cast_nonneg (p i)), Complex.ofReal_prod]
  rw [hs, Finset.prod_inv_distrib]
  unfold movingRegularTransform
  simp only [Nat.one_mul]

/-- The physical tuple divided by sqrt X is the actual initial regular
Fourier amplitude. The sign of the frequency is retained explicitly. -/
theorem tuple_regular_poisson_normalized {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X) :
    (∑' a : ℤ, (∏ i, F i (a : ZMod (p i))) * ψ ((a : ℝ) / X)) /
        (Real.sqrt X : ℂ) =
      ∑' v : ℤ, (Real.sqrt (X / (∏ i, p i : ℕ)) : ℂ) *
        𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) *
          movingRegularTransform p (fun i => densityFourier (F i)) 1 (-v) := by
  have hp := scaled_periodic_poisson (tupleCRTFunction p hc F) ψ X hX
  simp_rw [tupleCRTFunction_intCast, show ∀ v : ℤ,
    -(v : ZMod (∏ i, p i)) = ((-v : ℤ) : ZMod (∏ i, p i)) from fun v => (Int.cast_neg v).symm,
    tuple_regular_fourier p hc F] at hp
  rw [hp, div_eq_mul_inv, ← tsum_mul_left, ← tsum_mul_right]
  have hM : (0 : ℝ) < (∏ i, p i : ℕ) := by exact_mod_cast NeZero.pos (∏ i, p i)
  have hx : (Real.sqrt X : ℂ) ^ 2 = X := by exact_mod_cast Real.sq_sqrt hX.le
  have hx0 : (Real.sqrt X : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hX).ne'
  have hm0 : (Real.sqrt (∏ i, p i : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hM).ne'
  rw [Real.sqrt_div hX.le]
  push_cast
  apply tsum_congr
  intro v
  field_simp [hx0, hm0]
  rw [hx]
  ring

/-- Compact Fourier support produces a finite integer-frequency amplitude;
there is no estimate or discarded tail in this step. -/
theorem tuple_regular_poisson_finite {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X) (N : ℕ)
    (hcut : H * (∏ i, p i : ℕ) ≤ N * X)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    (∑' a : ℤ, (∏ i, F i (a : ZMod (p i))) * ψ ((a : ℝ) / X)) /
        (Real.sqrt X : ℂ) =
      ∑ v ∈ Finset.Icc (-(N : ℤ)) N, (Real.sqrt (X / (∏ i, p i : ℕ)) : ℂ) *
        𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) *
          movingRegularTransform p (fun i => densityFourier (F i)) 1 (-v) := by
  rw [tuple_regular_poisson_normalized p hc F ψ X hX]
  apply tsum_eq_sum
  intro v hv
  have hn : (N : ℝ) < |(v : ℝ)| := by
    have hi : (N : ℤ) < |v| := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hv
      rcases hv with hv | hv
      · exact (show (N : ℤ) < -v by omega).trans_le (neg_le_abs v)
      · exact hv.trans_le (le_abs_self v)
    exact_mod_cast hi
  have hM : (0 : ℝ) < (∏ i, p i : ℕ) := by exact_mod_cast NeZero.pos (∏ i, p i)
  have hf : 𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) = 0 := by
    apply hsupp
    rw [abs_div, abs_mul, abs_of_pos hX, abs_of_pos hM, lt_div_iff₀ hM]
    exact hcut.trans_lt (mul_lt_mul_of_pos_right hn hX)
  rw [hf, mul_zero, zero_mul]

/-- Reversing the finite frequency interval gives exactly the profile used
by the sampled recursion. No symmetry assumption on the Schwartz window is
needed: the minus sign belongs to the normalized Fourier profile. -/
theorem tuple_regular_poisson_profile {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (F : ∀ i, ZMod (p i) → ℂ) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X) (N : ℕ)
    (hcut : H * (∏ i, p i : ℕ) ≤ N * X)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    (∑' a : ℤ, (∏ i, F i (a : ZMod (p i))) * ψ ((a : ℝ) / X)) /
        (Real.sqrt X : ℂ) =
      ∑ v ∈ Finset.Icc (-(N : ℤ)) N,
        normalizedFourierProfile (fun t => 𝓕 ψ t) v ((∏ i, p i : ℕ) / X) *
          movingRegularTransform p (fun i => densityFourier (F i)) 1 v := by
  rw [tuple_regular_poisson_finite p hc F ψ X H hX N hcut hsupp]
  symm
  have hM : ((∏ i, p i : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne (∏ i, p i))
  simp_rw [normalizedFourierProfile_original _ X ((∏ i, p i : ℕ) : ℝ) _ hX.ne' hM]
  unfold archimedeanLeafFactor
  simp only [mul_one]
  refine Finset.sum_bij (fun v _ => -v) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_Icc] at hv ⊢
    omega
  · intro v hv w hw he
    exact neg_injective he
  · intro v hv
    refine ⟨-v, ?_, neg_neg v⟩
    simp only [Finset.mem_Icc] at hv ⊢
    omega
  · intro v hv
    simp only [Int.cast_neg, neg_neg]

/-- A zero-mean local test removes every nonunit frequency at that prime.
This supplies the initial frequency guard for both kinds of physical test. -/
theorem movingRegularTransform_eq_zero_of_nonunit {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0) (D : ℕ) (v : ℤ)
    (hv : ¬ ∀ i, IsUnit (v : ZMod (p i))) :
    movingRegularTransform p g D v = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp hv
  have hz : (v : ZMod (p i)) = 0 := by
    simpa only [isUnit_iff_ne_zero, not_not] using hi
  unfold movingRegularTransform
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hz, zero_mul, hg])

/-- Inserting the exact initial unit guard changes no Fourier coefficient. -/
theorem movingRegularTransform_unit_guard {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0) (D : ℕ) (v : ℤ) :
    (if ∀ i, IsUnit (v : ZMod (p i)) then movingRegularTransform p g D v else 0) =
      movingRegularTransform p g D v := by
  split_ifs with hv
  · rfl
  · exact (movingRegularTransform_eq_zero_of_nonunit p g hg D v hv).symm

end Ostmann

end OAI
