import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrectionCutoffGeometry

namespace OAI

/-! # Rounding the coefficient interval preserves the actual correction cutoffs -/

namespace Ostmann

theorem quadratic_correction_base_mono {M H N : ℝ} {e B : ℕ}
    (hM : 0 < M) (hH : 0 < H) (hHN : H ≤ N) (he : 0 < e) (hB : 0 < B) :
    quadraticCorrectionBase M H e B ≤ quadraticCorrectionBase M N e B := by
  rw [quadratic_correction_base_formula hM hH he hB,
    quadratic_correction_base_formula hM (hH.trans_le hHN) he hB]
  gcongr

theorem quadratic_correction_base_double {M H N : ℝ} {e B : ℕ}
    (hM : 0 < M) (hH : 0 < H) (hN : 0 < N) (hNH : N ≤ 2 * H)
    (he : 0 < e) (hB : 0 < B) :
    quadraticCorrectionBase M N e B ≤ 2 * quadraticCorrectionBase M H e B := by
  rw [quadratic_correction_base_formula hM hH he hB,
    quadratic_correction_base_formula hM hN he hB]
  calc
    _ ≤ (2 * H) * Real.sqrt e / (Real.sqrt M * Real.sqrt B) := by gcongr
    _ = _ := by ring

theorem quadratic_rounded_correction_band {M H N J : ℝ} {e B b D d : ℕ}
    (hM : 0 < M) (hH : 0 < H) (hHN : H ≤ N) (hNH : N ≤ 2 * H)
    (he : 0 < e) (hB : 0 < B) (hJ : 1 ≤ J)
    (hb : B ≤ b) (hb' : b ≤ 2 * B) (hd : D < d) (hd' : d ≤ 2 * D) :
    ((d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J →
      (D : ℝ) ≤ 2 * quadraticCorrectionBase M N e B * J) ∧
    (quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ) →
      quadraticCorrectionBase M N e B / (8 * (2 * J)) ≤ (D : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := quadratic_correction_divisor_band hM hH he hB hJ hb hb' hd hd'
  have hbase := quadratic_correction_base_mono hM hH hHN he hB
  have hbase' := quadratic_correction_base_double hM hH (hH.trans_le hHN) hNH he hB
  constructor
  · intro h
    apply (hlo h).le.trans
    gcongr
  · intro h
    apply le_trans _ (hhi h).le
    calc
      _ ≤ (2 * quadraticCorrectionBase M H e B) / (8 * (2 * J)) := by gcongr
      _ = _ := by ring

end Ostmann

end OAI
