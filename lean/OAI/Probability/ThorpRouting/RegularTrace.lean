import OAI.Probability.ThorpRouting.TraceBound

namespace OAI

namespace ThorpNine.Harmonic

namespace Thorp.LowPlanes
open scoped BigOperators Classical
open Casimir Specht UnitaryFinite

attribute [local instance] hsNorm hsInner hsFinite

lemma sharp_physical_fourier (d t : ℕ) :
    (2 * distance d t)^2 ≤ ∑ μ : Shapes (2^d),
      (Module.finrank ℂ (hilbertSpace μ.1) : ℝ)^2 *
        ‖sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d t) -
          uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ)‖^2 := by
  let V : Shapes (2^d) → Type := fun μ => hilbertSpace μ.1
  let : ∀ μ, NormedAddCommGroup (V μ) := fun _ => inferInstance
  let : ∀ μ, InnerProductSpace ℂ (V μ) := fun _ => inferInstance
  let : ∀ μ, FiniteDimensional ℂ (V μ) := fun _ => inferInstance
  let p := fun g : Equiv.Perm (Card d) => law d t g - 1/(Nat.factorial (2^d) : ℝ)
  have hb := FiniteFourier.l1_fourier_bound V (cardRepresentation d)
    (cardRepresentation_unitary d) (cardRepresentation_distinct d) (card_conjugacy_shapes d) p
  have he (μ : Shapes (2^d)) : weightedOperator (V := V μ) (cardRepresentation d μ) p =
      sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d t) -
        uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) := by
    rw [sampleOperator_weighted, sampleLaw_run]
    dsimp only [p]
    rw [weighted_sub]
    congr 1
    unfold uniformOperator
    rw [card_permutations]
    simp only [one_div]
  simp_rw [he] at hb
  convert hb using 1
  change (2 * ((1/2 : ℝ) * ∑ g, |p g|))^2 = (∑ g, |p g|)^2
  ring

lemma forward_bound (d v : ℕ) (hv : 0 < v) :
    (2 * distance d (v*d))^2 ≤ tailBound d v := by
  apply (sharp_physical_fourier d (v*d)).trans
  apply Finset.sum_le_sum
  intro μ _
  by_cases hz : μ.1.card - μ.1.rowLen 0 = 0
  · simp [hz, card_fourier_full_row d (v*d) μ hz]
  · simp only [hz, ite_false]
    have hu : uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) = 0 :=
      nontrivial_uniform_zero d μ.1 (cardLabels d μ) (by omega)
    rw [hu, sub_zero]
    exact mul_le_mul_of_nonneg_left
      (physical_power_bound d v hv (cardRepresentation d μ) (cardRepresentation_unitary d μ))
      (sq_nonneg _)

lemma distance_of_tail_bound (d v : ℕ) (hv : 0 < v)
    (ht : tailBound d v ≤ ((2 : ℝ)^d)^(-10 : ℤ)) :
    distance d (v*d) ≤ (1/2 : ℝ) * ((2 : ℝ)^d)^(-5 : ℤ) := by
  have hb := (forward_bound d v hv).trans ht
  have hn : 0 < (2 : ℝ)^d := by positivity
  have he : (((2 : ℝ)^d)^(-5 : ℤ))^2 = ((2 : ℝ)^d)^(-10 : ℤ) := by
    rw [pow_two, ←zpow_add₀ hn.ne']
    norm_num
  have hp : 0 < ((2 : ℝ)^d)^(-5 : ℤ) := zpow_pos hn _
  rw [←he] at hb
  have hh : 2 * distance d (v*d) ≤ ((2 : ℝ)^d)^(-5 : ℤ) := by
    nlinarith [distance_nonneg d (v*d)]
  linarith

theorem regular_trace_smoothing : MainStatement := by
  obtain ⟨u, hu, htail⟩ := uniform_tail_bound
  refine ⟨2 * (u : ℝ), ?_, ?_⟩
  · have h : (1 : ℝ) ≤ u := by exact_mod_cast hu
    linarith
  · intro d hd
    refine ⟨?_, ?_⟩
    · exact (regularTrace_le d u (by omega)).trans
        (add_le_add le_rfl (htail d hd u le_rfl))
    · intro v hv σ
      have hvR : (u : ℝ) ≤ v := by linarith
      have hvZ : (u : ℤ) ≤ v := by exact_mod_cast hvR
      have hv0 : 0 ≤ v := (Int.natCast_nonneg u).trans hvZ
      have hvn : u ≤ v.toNat := by
        rw [←Int.toNat_of_nonneg hv0] at hvZ
        exact_mod_cast hvZ
      change fromDistance d (v.toNat*d) σ ≤ _
      rw [fromDistance_eq]
      exact distance_of_tail_bound d v.toNat (by omega) (htail d hd v.toNat hvn)

end Thorp.LowPlanes

end ThorpNine.Harmonic

end OAI
