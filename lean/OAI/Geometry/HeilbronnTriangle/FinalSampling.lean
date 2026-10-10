import OAI.Geometry.HeilbronnTriangle.GeometricAlteration
import OAI.Geometry.HeilbronnTriangle.SamplingErrors
import OAI.Geometry.HeilbronnTriangle.FinalScaling

namespace OAI


noncomputable section

namespace Problem355.FinalSampling

open Finset

lemma deletion_margin {n : ℕ} {p q : ℝ} (hn : 0 < n)
    (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hrelative : 4 * (n : ℝ) * p + 8 * (n : ℝ) ^ 2 * q < 1) :
    (Nat.choose (2 * n) 2 : ℝ) * p + (Nat.choose (2 * n) 3 : ℝ) * q <
      ((2 * n - n + 1 : ℕ) : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc2 : (Nat.choose (2 * n) 2 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by
    have hc : (Nat.choose (2 * n) 2 : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast Nat.choose_le_pow (2 * n) 2
    norm_num [mul_pow] at hc
    exact hc
  have hc3 : (Nat.choose (2 * n) 3 : ℝ) ≤ 8 * (n : ℝ) ^ 3 := by
    have hc : (Nat.choose (2 * n) 3 : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ 3 := by
      exact_mod_cast Nat.choose_le_pow (2 * n) 3
    norm_num [mul_pow] at hc
    exact hc
  calc
    (Nat.choose (2 * n) 2 : ℝ) * p + (Nat.choose (2 * n) 3 : ℝ) * q ≤
        4 * (n : ℝ) ^ 2 * p + 8 * (n : ℝ) ^ 3 * q :=
      add_le_add (mul_le_mul_of_nonneg_right hc2 hp)
        (mul_le_mul_of_nonneg_right hc3 hq)
    _ = (4 * (n : ℝ) * p + 8 * (n : ℝ) ^ 2 * q) * n := by ring
    _ < (n : ℝ) := by simpa using mul_lt_mul_of_pos_right hrelative hn0
    _ < ((2 * n - n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show n < 2 * n - n + 1 by omega)

theorem power_configuration_of_marginal_bounds
    {Ω ι : Type*} [DecidableEq ι]
    (outcomes : Finset Ω) (weight : Ω → ℝ) (S : Finset ι)
    (f : Ω → ι → Point) (n : ℕ)
    (r H τ h B Cpair Ctriple : ℝ) (m : ℕ)
    (hn : 3 ≤ n) (hcard : S.card = 2 * n)
    (hr : 64 ≤ r) (hH : r ≤ H) (ht : 1 ≤ τ) (hh0 : 0 ≤ h)
    (hsample : (n : ℝ) ^ 2 * τ ≤ r ^ 2 * (H ^ 10) ^ 3)
    (hh : h ≤ 3 * B * τ) (hB : B ≤ r ^ 31)
    (hpoly : H ^ 10 ≤ r ^ m)
    (hCp : 0 ≤ Cpair) (hCt : 0 ≤ Ctriple)
    (hlarge : 4 * Cpair + 24 * Ctriple * (m + 1 : ℝ) ^ 2 < r)
    (hsize : (n : ℝ) ≤ Real.rpow r (100000 * (heilbronnK : ℝ)))
    (harea : r ^ 2 / 64 ≤ (n : ℝ) ^ 2 * (τ / (16 * (H ^ 10) ^ 3)))
    (hweight : ∀ ω ∈ outcomes, 0 ≤ weight ω)
    (hnorm : ∑ ω ∈ outcomes, weight ω = 1)
    (hsquare : ∀ ω ∈ outcomes, ∀ i ∈ S, pointInUnitSquare (f ω i))
    (hpair : ∀ e ∈ S.powersetCard 2,
      (∑ ω ∈ outcomes,
        if e ∈ Alteration.collisionEdges S (f ω) then weight ω else 0) ≤
          Cpair * H ^ 6 / (H ^ 10) ^ 3)
    (htriple : ∀ e ∈ S.powersetCard 3,
      (∑ ω ∈ outcomes,
        if e ∈ Alteration.badTripleEdges S (f ω)
          (Alteration.smallTriangle (τ / (16 * (H ^ 10) ^ 3))) then weight ω else 0) ≤
          Ctriple * (Real.log (2 * H ^ 10)) ^ 2 * h /
            ((H ^ 10) ^ 3 * r ^ 41)) :
    ∃ P : Finset Point, P.card = n ∧ pointsInUnitSquare P ∧
      triangleAreasAtLeast P (Real.rpow (n : ℝ) (-2 + heilbronnExponent)) := by
  classical
  have hr1 : 1 ≤ r := by linarith
  have hH0 : 0 < H := lt_of_lt_of_le (by linarith : 0 < r) hH
  have hn0 : 0 < n := by omega
  have hrelative := SamplingErrors.relative_error_lt_one hr1 hH ht hh0
    hsample hh hB hpoly hCp hCt hlarge
  have hrelative' :
      4 * (n : ℝ) * (Cpair * H ^ 6 / (H ^ 10) ^ 3) +
      8 * (n : ℝ) ^ 2 * (Ctriple * (Real.log (2 * H ^ 10)) ^ 2 * h /
        ((H ^ 10) ^ 3 * r ^ 41)) < 1 := by
    convert hrelative using 1; ring
  have hbudget := deletion_margin hn0
    (show 0 ≤ Cpair * H ^ 6 / (H ^ 10) ^ 3 by positivity)
    (show 0 ≤ Ctriple * (Real.log (2 * H ^ 10)) ^ 2 * h /
      ((H ^ 10) ^ 3 * r ^ 41) by positivity) hrelative'
  obtain ⟨P, hPn, hPsquare, hParea⟩ :=
    Alteration.exists_point_configuration_of_marginal_bounds outcomes weight S f n
      (τ / (16 * (H ^ 10) ^ 3)) hweight hnorm hsquare
      (by rw [hcard]; omega) _ _ hpair htriple (by simpa [hcard] using hbudget)
  refine ⟨P, hPn, hPsquare, ?_⟩
  have hK : 0 < (heilbronnK : ℝ) := by
    by_contra hK
    have he : 100000 * (heilbronnK : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_gt hK)
    have hpow : Real.rpow r (100000 * (heilbronnK : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hr1 he
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hpower := scaled_area_implies_heilbronn_power
    (show (0 : ℝ) < n by exact_mod_cast hn0) hr hK hsize harea
  have hpower' : Real.rpow (n : ℝ) (-2 + heilbronnExponent) ≤
      τ / (16 * (H ^ 10) ^ 3) := by
    simpa only [heilbronnExponent] using hpower
  intro p hp q hq s hs hpq hps hqs
  exact hpower'.trans (hParea p hp q hq s hs hpq hps hqs)

end Problem355.FinalSampling

end

end OAI
