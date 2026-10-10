import OAI.Geometry.NodalSets.Elliptic.RescaledHigherJets
import OAI.Geometry.NodalSets.Waves.ExponentialWaveBounds
import OAI.Geometry.NodalSets.Waves.NormalizedWaveRatio

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma planeWave_smooth (k : Coord →L[ℝ] ℝ) (s : ℝ) : ContDiff ℝ ∞ (planeWave k s) := by
  unfold planeWave
  have hh : ContDiff ℝ ∞ (fun v ↦ ((k v/s:ℝ):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (k.contDiff.div_const s)
  exact Complex.contDiff_exp.comp (contDiff_const.mul hh)

lemma planeWave_derivative_bound (k : Coord →L[ℝ] ℝ) {s B : ℝ}
    (hs : 1 ≤ s) (hB : 1 ≤ B) (hk : ‖k‖ ≤ B) (d : ℕ) (v : Coord) :
    ‖iteratedFDeriv ℝ d (planeWave k s) v‖ ≤ d.factorial*B^d := by
  let L : Coord →L[ℝ] ℂ := s⁻¹ • (Complex.I • Complex.ofRealCLM.comp k)
  have he : planeWave k s = Complex.exp ∘ L := by
    funext z
    simp [planeWave,L,Complex.real_smul,div_eq_mul_inv,mul_comm,mul_left_comm]
  have hL : ‖L‖ ≤ B := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
    intro z
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
    have hi : s⁻¹ ≤ 1 := (inv_le_one₀ hs0).mpr hs
    calc
      ‖L z‖ = s⁻¹*‖k z‖ := by simp [L,abs_of_pos hs0]
      _ ≤ 1*(B*‖z‖) := mul_le_mul hi ((k.le_opNorm z).trans (by gcongr)) (norm_nonneg _) zero_le_one
      _ = _ := by ring
  rw [he]
  have h := norm_iteratedFDeriv_comp_le (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞))
    (L.contDiff (n := ∞)) (n := d) (by exact_mod_cast (show (d:ℕ∞) ≤ ⊤ from le_top)) v
    (C := 1) (D := B)
    (fun j hj ↦ by
      rw [norm_iteratedFDeriv_complex_exp]
      simp [L,Complex.real_smul])
    (fun j hj hjd ↦ by
      by_cases hj1 : j = 1
      · subst j; simpa only [norm_iteratedFDeriv_one,L.fderiv,pow_one] using hL
      · rw [iteratedFDeriv_linear_high L v (by omega),norm_zero]
        positivity)
  simpa only [mul_one] using h

lemma uniform_planeWave_jets {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (K : T → Coord →L[ℝ] ℝ) (hK : Continuous K) (d : ℕ) :
    ∃ B > 0, ∀ t s, 1 ≤ s → ∀ v, ∀ j, j ≤ d →
      ‖iteratedFDeriv ℝ j (planeWave (K t) s) v‖ ≤ B := by
  obtain ⟨C,hC,hb⟩ := (isCompact_univ.image hK).isBounded.exists_pos_norm_le
  let D := max 1 C
  refine ⟨(d.factorial:ℝ)*D^d,by dsimp [D]; positivity,?_⟩
  intro t s hs v j hj
  have hnorm : ‖K t‖ ≤ D := (hb _ ⟨t,mem_univ _,rfl⟩).trans (le_max_right _ _)
  apply (planeWave_derivative_bound (K t) hs (le_max_left _ _) hnorm j v).trans
  have hfac : (j.factorial:ℝ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hj
  have hpow := pow_le_pow_right₀ (show 1 ≤ D from le_max_left _ _) hj
  gcongr

end
end Yau.Geometry

end OAI
