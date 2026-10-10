import OAI.Geometry.HeilbronnTriangle.OrbitEstimate

namespace OAI


namespace Problem355.OrbitProbabilityBound

theorem conditional_mass_le
    {prob S O h N D E c A : ℝ}
    (hh : 0 < h) (hN : 0 < N) (hD : 0 < D) (hE : 0 < E)
    (hc : 0 < c) (hA : 0 ≤ A)
    (horbit : c * h ^ 8 / (D ^ 3 * E ^ 2) ≤ O)
    (hlift : prob = (h ^ 9 / (N ^ 9 * O)) * S)
    (hcount : S ≤ A * N ^ 6 / (D ^ 2 * E ^ 2)) :
    prob ≤ (A / c) * h * D / N ^ 3 := by
  have hbase : 0 < c * h ^ 8 / (D ^ 3 * E ^ 2) := by positivity
  have hO : 0 < O := hbase.trans_le horbit
  have hinv := one_div_le_one_div_of_le hbase horbit
  have hfactor : 0 ≤ h ^ 9 / N ^ 9 * (A * N ^ 6 / (D ^ 2 * E ^ 2)) := by
    positivity
  calc
    prob = (h ^ 9 / (N ^ 9 * O)) * S := hlift
    _ ≤ (h ^ 9 / (N ^ 9 * O)) * (A * N ^ 6 / (D ^ 2 * E ^ 2)) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = (h ^ 9 / N ^ 9 * (A * N ^ 6 / (D ^ 2 * E ^ 2))) * (1 / O) := by ring
    _ ≤ (h ^ 9 / N ^ 9 * (A * N ^ 6 / (D ^ 2 * E ^ 2))) *
        (1 / (c * h ^ 8 / (D ^ 3 * E ^ 2))) :=
      mul_le_mul_of_nonneg_left hinv hfactor
    _ = (A / c) * h * D / N ^ 3 := by
      field_simp

theorem conditional_mass_le_explicit
    {prob S O h N D E A : ℝ}
    (hh : 0 < h) (hN : 0 < N) (hD : 0 < D) (hE : 0 < E) (hA : 0 ≤ A)
    (horbit : (21 / 64 : ℝ) * h ^ 8 / (D ^ 3 * E ^ 2) ≤ O)
    (hlift : prob = (h ^ 9 / (N ^ 9 * O)) * S)
    (hcount : S ≤ A * N ^ 6 / (D ^ 2 * E ^ 2)) :
    prob ≤ (64 / 21 : ℝ) * A * h * D / N ^ 3 := by
  convert conditional_mass_le hh hN hD hE (by norm_num) hA horbit hlift hcount using 1; ring

theorem sl_conditional_mass_le
    {p k b e : ℕ} (hp : p.Prime) (hk : 0 < k) (hb : b ≤ k) (he : e ≤ k)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (p ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (p ^ k)))
    (hC : C = (P : Matrix _ _ _) *
      Matrix.diagonal ![1, ((p ^ b : ℕ) : ZMod (p ^ k)), ((p ^ e : ℕ) : ZMod (p ^ k))] *
      (Q : Matrix _ _ _))
    {prob S N A : ℝ} (hN : 0 < N) (hA : 0 ≤ A)
    (hlift : prob = (((p ^ k : ℕ) : ℝ) ^ 9 /
      (N ^ 9 * (Nat.card (Section04Orbit.slOrbit C) : ℝ))) * S)
    (hcount : S ≤ A * N ^ 6 /
      (((p ^ b : ℕ) : ℝ) ^ 2 * ((p ^ e : ℕ) : ℝ) ^ 2)) :
    prob ≤ (64 / 21 : ℝ) * A * ((p ^ k : ℕ) : ℝ) * ((p ^ b : ℕ) : ℝ) / N ^ 3 := by
  exact conditional_mass_le_explicit
    (by exact_mod_cast pow_pos hp.pos k) hN
    (by exact_mod_cast pow_pos hp.pos b)
    (by exact_mod_cast pow_pos hp.pos e) hA
    (Section04Orbit.slOrbit_lower_bound hp hk hb he C P Q hC) hlift hcount

end Problem355.OrbitProbabilityBound

end OAI
