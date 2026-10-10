import OAI.Analysis.Cotype.GrowthScalarData

namespace OAI

noncomputable section

namespace Cotype
variable {m : ℕ}

theorem abs_character_finite {ι : Type*} [Fintype ι] [DecidableEq ι] (P s : ι → Bool) :
    |character P s| = 1 := by
  rcases mul_self_eq_one_iff.mp (character_sq P s) with h | h <;> simp [h]

theorem fourier_matrixTwist (Φ : SignMatrix m → Cube m → Cube m → ℝ) (P : SignMatrix m) :
    fourier (matrixTwist Φ) P = average (fun ε => average (fun δ =>
      fourier (fun S => Φ S ε δ) P * character P (xorCube (rowCube ε) (columnCube δ)))) := by
  unfold matrixTwist
  rw [fourier_average_family]
  have ht (ε δ : Cube m) : fourier (fun S => Φ (dampedSample ε δ S) ε δ) P =
      fourier (fun S => Φ S ε δ) P * character P (xorCube (rowCube ε) (columnCube δ)) := by
    have he (S : SignMatrix m) : dampedSample ε δ S = xorCube (xorCube (rowCube ε) (columnCube δ)) S := by
      funext ij; simp [dampedSample, xorCube]
    simp_rw [he]
    exact fourier_translate (fun S => Φ S ε δ) _ P
  simp_rw [fourier_average_family, ht]

theorem paritySign_one_or_neg_one (P : SignMatrix m) : paritySign P = 1 ∨ paritySign P = -1 := by
  have h := character_sq P (fun _ => true)
  change paritySign P * paritySign P = 1 at h
  exact mul_self_eq_one_iff.mp h

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {n k : ℕ} {T : X →L[ℝ] Y} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T n m Dg Df)

theorem normalized_coefficient_identity (hn : m+m ≤ n) (P : SignMatrix m)
    (hp : fourier (d.normalizedMatrix hn) P ≠ 0) :
    d.gamma * fourier (d.normalizedMatrix hn) P = average (fun ε => average (fun δ =>
      fourier (fun S => d.patternPairing hn S ε δ) P *
        character P (xorCube (rowCube ε) (columnCube δ)))) := by
  have ho : IsOdd (d.normalizedMatrix hn) := by
    intro S; unfold normalizedMatrix; rw [oddPart_isOdd]; ring
  have hpar : paritySign P = -1 := by
    rcases paritySign_one_or_neg_one P with h | h
    · exact False.elim (hp (odd_even_coefficient_zero ho h))
    · exact h
  unfold normalizedMatrix
  rw [fourier_const_mul, oddPart_preserves_odd_coefficient _ hpar]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt d.gamma_pos), one_mul]
  exact fourier_matrixTwist _ P

theorem exists_fixed_lift_coefficient (hn : m+m ≤ n) (P : SignMatrix m)
    {c : ℝ} (hc : 0 < c) (hp : c ≤ |fourier (d.normalizedMatrix hn) P|) :
    ∃ ε δ : Cube m, c * d.gamma ≤ |fourier (fun S => d.patternPairing hn S ε δ) P| := by
  have hp0 : fourier (d.normalizedMatrix hn) P ≠ 0 := abs_pos.mp (hc.trans_le hp)
  obtain ⟨z,hz,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Cube m × Cube m))
    (fun z => |fourier (fun S => d.patternPairing hn S z.1 z.2) P|) Finset.univ_nonempty
  refine ⟨z.1,z.2,?_⟩
  have hb : |d.gamma * fourier (d.normalizedMatrix hn) P| ≤
      |fourier (fun S => d.patternPairing hn S z.1 z.2) P| := by
    rw [d.normalized_coefficient_identity hn P hp0]
    apply abs_average_le_const
    intro ε
    apply abs_average_le_const
    intro δ
    rw [abs_mul, abs_character_finite, mul_one]
    exact hmax (ε,δ) (Finset.mem_univ _)
  rw [abs_mul, abs_of_pos d.gamma_pos] at hb
  exact (mul_le_mul_of_nonneg_right hp (le_of_lt d.gamma_pos)).trans (by simpa [mul_comm] using hb)

variable (d : GrowthPairingData T (k+m+m) m Dg Df)

theorem exists_rank_coefficient_constant
    (hcut : 4 ≤ degreeCutoff m) (hcutm : degreeCutoff m < m)
    (ha : 0 < 1/(2*24*Dg*Real.sqrt m)) (hb : 0 < 1/(2*24*Df*Real.sqrt m))
    (hsize : 80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤
      min ((m : ℝ)*(1/(2*24*Dg*Real.sqrt m))) ((m : ℝ)*(1/(2*24*Df*Real.sqrt m)))) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : GrowthPairingData T (k+m+m) m Dg Df),
      walshNorm k T ≤ 2 * walshNorm (k+m+m) T →
      ∃ (P : SignMatrix m) (ε δ : Cube m), 2 ≤ (binaryMatrix P).rank ∧
        c * d.gamma ≤ |fourier (fun S => d.patternPairing (by omega) S ε δ) P| := by
  obtain ⟨c,hc,hall⟩ := coefficientTarget_proved m _ _ hcut hcutm ha hb hsize
  refine ⟨c,hc,?_⟩
  intro d hslow
  have hm : 0 < m := by omega
  have hn : m+m ≤ k+m+m := by omega
  have hp : m+1 ≤ k+m+m := by omega
  have hd : 1+m ≤ k+m+m := by omega
  obtain ⟨P,hPr,hPc⟩ := hall (d.normalizedMatrix hn) (d.normalizedPrimal hp)
    (d.normalizedDual hd) (d.normalized_scalar_admissible hm hn hp hd hslow)
  obtain ⟨ε,δ,hfix⟩ := d.exists_fixed_lift_coefficient hn P hc hPc
  exact ⟨P,ε,δ,hPr,hfix⟩

end GrowthPairingData

end Cotype

end

end OAI
