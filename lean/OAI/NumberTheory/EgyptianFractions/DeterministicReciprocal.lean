import OAI.NumberTheory.EgyptianFractions.ReciprocalPhase
import OAI.NumberTheory.EgyptianFractions.DeterministicPhaseWindow

namespace OAI
noncomputable section
open scoped BigOperators
open Filter
namespace Problem337

/-- The natural and integer closed interval sums agree under the canonical cast. -/
lemma sum_nat_interval_eq_int (f : ℤ → ℂ) (L R : ℕ) :
    (∑ n ∈ Finset.Icc L R, f n) = ∑ n ∈ Finset.Icc (L : ℤ) (R : ℤ), f n := by
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ))
  · intro n hn
    obtain ⟨hL, hR⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hL, by exact_mod_cast hR⟩
  · intro n hn m hm h
    exact_mod_cast h
  · intro n hn
    obtain ⟨hL, hR⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 ≤ n := (Int.natCast_nonneg L).trans hL
    refine ⟨n.toNat, ?_, Int.toNat_of_nonneg hn0⟩
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  · intro n hn
    rfl

/-- Integer-interval reciprocal cancellation in a natural dyadic piece. -/
lemma reciprocal_sum_dyadic_piece (A δ U Z : ℝ) (u L R : ℕ)
    (hu : 0 < u) (hU : U = (u : ℝ))
    (hlocal : ∀ L R : ℤ, U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
      ‖∑ n ∈ Finset.Icc L R, differencingPhase (Z / (n : ℝ))‖ ≤ A * U ^ (1 - δ)) :
    ‖∑ n ∈ (Finset.Ico u (2 * u) ∩ Finset.Icc L R),
      differencingPhase (Z / (n : ℝ))‖ ≤ A * U ^ (1 - δ) := by
  have heq : Finset.Ico u (2 * u) ∩ Finset.Icc L R =
      Finset.Icc (max u L) (min (2 * u - 1) R) := by
    ext n
    simp only [Finset.mem_inter, Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [heq]
  have hs := sum_nat_interval_eq_int
    (fun n => differencingPhase (Z / (n : ℝ))) (max u L) (min (2 * u - 1) R)
  simp only [Int.cast_natCast] at hs
  rw [hs]
  apply hlocal
  · subst U
    exact_mod_cast (le_max_left u L)
  · subst U
    have hh : min (2 * u - 1) R ≤ 2 * u := (min_le_left _ _).trans (Nat.sub_le _ _)
    exact_mod_cast hh

/-- The local reciprocal-phase theorem gives a uniform exponential saving over
an entire high residue level. The denominator range and local frequency range
are explicit, and no cancellation hypothesis remains. -/
theorem deterministic_reciprocal_sum_bound (D : ℝ) (hD : 255 ≤ D) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ᶠ S : ℝ in atTop, ∀ (m X Z : ℝ) (L R : ℕ),
        m ≤ S → Real.exp S ≤ X → X ≤ Real.exp (D * S / 4) →
        Real.exp (-m / 10000) * X ≤ (L : ℝ) → (R : ℝ) ≤ X →
        Real.exp (D * S) ≤ |Z| → |Z| ≤ Real.exp ((2 * D + 102) * S) →
        ‖∑ n ∈ Finset.Icc L R, differencingPhase (Z / (n : ℝ))‖ ≤
          A * X * Real.exp (-c * S) := by
  obtain ⟨A, δ, hA, hδ, hlocal⟩ := reciprocal_phase_local_power_saving (3 * D) (by linarith)
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hlocal
  refine ⟨2 * A, 4 * δ / 5, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    eventually_ge_atTop (10 * Real.log 2), eventually_ge_atTop (5 * U₀ / 4)] with S hS hSlarge hSU
  intro m X Z L R hm hXlo hXhi hL hR hZlo hZhi
  have hX : 0 < X := (Real.exp_pos S).trans_le hXlo
  have hUlarge : U₀ ≤ Real.exp (4 * S / 5) := by
    have he := Real.add_one_le_exp (4 * S / 5)
    linarith
  by_cases hempty : R < L
  · rw [Finset.Icc_eq_empty_of_lt hempty, Finset.sum_empty, norm_zero]
    positivity
  have hLR : L ≤ R := by omega
  have hLpos : 1 ≤ L := by
    have hh : (0 : ℝ) < L := (mul_pos (Real.exp_pos _) hX).trans_le hL
    exact_mod_cast (show 0 < L by exact_mod_cast hh)
  have hLupper : (L : ℝ) ≤ X := (Nat.cast_le.mpr hLR).trans hR
  have hhalf : Real.exp (4 * S / 5) ≤ (L : ℝ) / 2 :=
    (deterministic_phase_window S m D X ((L : ℝ) / 2) Z hS hSlarge hm hD
      hXlo hXhi (by linarith) (by linarith) hZlo hZhi).1
  have hsum := deterministic_phase_sum_bound (fun n => differencingPhase (Z / (n : ℝ)))
    L R S A δ hLpos hA.le hδ.le hhalf (by
      intro u hu hLu huR
      have hLu' : (L : ℝ) ≤ 2 * (u : ℝ) := by exact_mod_cast hLu
      have huX : (u : ℝ) ≤ X := (Nat.cast_le.mpr huR).trans hR
      obtain ⟨huexp, huZlo, huZhi⟩ := deterministic_phase_window S m D X u Z
        hS hSlarge hm hD hXlo hXhi (by linarith) huX hZlo hZhi
      apply reciprocal_sum_dyadic_piece A δ (u : ℝ) Z u L R hu rfl
      intro L' R'
      exact hU₀ u (hUlarge.trans huexp) Z L' R' huZlo huZhi)
  calc
    _ ≤ 2 * A * (R : ℝ) * Real.exp (-(4 * δ * S / 5)) := hsum
    _ ≤ (2 * A) * X * Real.exp (-(4 * δ / 5) * S) := by
      rw [show -(4 * δ / 5) * S = -(4 * δ * S / 5) by ring]
      gcongr

end Problem337

end

end OAI
