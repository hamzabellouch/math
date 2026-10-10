import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondPoisson

namespace OAI

/-! # The actual square-root scale in the second Poisson transform -/

namespace Ostmann

noncomputable def quadraticSecondScale (M : ℝ) (e q b : ℕ) : ℝ :=
  Real.sqrt ((e : ℝ) * q / (M * b))

theorem quadraticSecondScale_pos {M : ℝ} {e q b : ℕ}
    (hM : 0 < M) (he : 0 < e) (hq : 0 < q) (hb : 0 < b) :
    0 < quadraticSecondScale M e q b := by
  unfold quadraticSecondScale
  exact Real.sqrt_pos.mpr (by positivity)

theorem quadraticSecondScale_argument {M : ℝ} {e q b : ℕ}
    (hM : 0 < M) (he : 0 < e) (hq : 0 < q) (hb : 0 < b) (a c : ℝ) :
    a * (c / quadraticSecondScale M e q b) ^ 2 =
      a * b * c ^ 2 / ((e : ℝ) * q / M) := by
  rw [div_pow, quadraticSecondScale, Real.sq_sqrt (by positivity)]
  field_simp

theorem quadraticSecondScale_dyadic {M B N : ℝ} {e q b : ℕ}
    (hM : 0 < M) (hB : 0 < B) (hN : 0 < N) (he : 0 < e)
    (hb : B ≤ b) (hb' : (b : ℝ) ≤ 2 * B)
    (hq : N ^ 2 ≤ q) (hq' : (q : ℝ) ≤ 4 * N ^ 2) :
    let X₀ := Real.sqrt ((e : ℝ) * N ^ 2 / (M * B))
    X₀ / 2 ≤ quadraticSecondScale M e q b ∧
      quadraticSecondScale M e q b ≤ 2 * X₀ := by
  have hb₀ : 0 < (b : ℝ) := hB.trans_le hb
  have hq₀ : 0 < (q : ℝ) := (sq_pos_of_pos hN).trans_le hq
  have he₀ : 0 < (e : ℝ) := by exact_mod_cast he
  have hlo : (e : ℝ) * N ^ 2 / (M * B) ≤
      2 * ((e : ℝ) * q / (M * b)) := by
    calc
      _ = 2 * ((e : ℝ) * N ^ 2 / (M * (2 * B))) := by ring
      _ ≤ 2 * ((e : ℝ) * q / (M * (2 * B))) := by gcongr
      _ ≤ _ := by gcongr
  have hhi : (e : ℝ) * q / (M * b) ≤
      4 * ((e : ℝ) * N ^ 2 / (M * B)) := by
    calc
      _ ≤ (e : ℝ) * q / (M * B) := by gcongr
      _ ≤ (e : ℝ) * (4 * N ^ 2) / (M * B) := by gcongr
      _ = _ := by ring
  dsimp
  have hs₀ := Real.sq_sqrt (show 0 ≤ (e : ℝ) * N ^ 2 / (M * B) by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ (e : ℝ) * q / (M * b) by positivity)
  have hn₀ := Real.sqrt_nonneg ((e : ℝ) * N ^ 2 / (M * B))
  have hn := Real.sqrt_nonneg ((e : ℝ) * q / (M * b))
  unfold quadraticSecondScale
  constructor <;> nlinarith

end Ostmann

end OAI
