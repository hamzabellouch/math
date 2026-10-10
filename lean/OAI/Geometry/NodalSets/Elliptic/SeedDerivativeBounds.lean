import OAI.Geometry.NodalSets.Elliptic.RealPhaseJet
import OAI.Geometry.NodalSets.Elliptic.SeedJetLowerBound
import OAI.Geometry.NodalSets.Waves.ExponentialWaveBounds

namespace OAI

namespace Yau.Jets
open Yau.Geometry Set
open scoped ContDiff
noncomputable section

lemma oscillatorySeed_contDiff (S T : Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (hT : ContDiff ℝ ∞ T) (N : ℝ) : ContDiff ℝ ∞ (oscillatorySeed S T N) :=
  ((contDiff_const.mul hS).exp).mul ((contDiff_const.mul hT).cos)

theorem oscillatorySeed_derivative_bound (S T : Coord → ℝ)
    (hS : ContDiff ℝ ∞ S) (hT : ContDiff ℝ ∞ T) {Q : Set Coord} (hQ : IsCompact Q) (k : ℕ) :
    ∃ C > 0, ∀ N : ℝ, 1 ≤ N → ∀ x ∈ Q,
      ‖iteratedFDeriv ℝ k (oscillatorySeed S T N) x‖ ≤ C*N^k*Real.exp (N*S x) := by
  let phi : Coord → ℂ := fun x ↦ (S x:ℂ)+Complex.I*(T x:ℂ)
  have hp : ContDiff ℝ ∞ phi :=
    (Complex.ofRealCLM.contDiff.comp hS).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hT))
  have hb (j : Fin (k+1)) : ∃ C > 0, ∀ x ∈ Q, ‖iteratedFDeriv ℝ j.val phi x‖ ≤ C := by
    obtain ⟨C,hC,hb⟩ := (hQ.image (hp.continuous_iteratedFDeriv
      (by exact_mod_cast (show (j.val:ℕ∞) ≤ ⊤ from le_top)))).isBounded.exists_pos_norm_le
    exact ⟨C,hC,fun x hx ↦ hb _ ⟨x,hx,rfl⟩⟩
  choose b hb hbound using hb
  let D : ℝ := 1+∑ j, b j
  have hD : 1 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ ↦ (hb j).le))
  refine ⟨(k.factorial:ℝ)*D^k,by positivity,?_⟩
  intro N hN x hx
  have hphi : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i phi x‖ ≤ D := by
    intro i _ hi
    have h := (hbound ⟨i,by omega⟩ x hx).trans
      (Finset.single_le_sum (fun j _ ↦ (hb j).le) (Finset.mem_univ _))
    dsimp [D]
    linarith
  have he : oscillatorySeed S T N = fun z ↦ (waveExp phi N z).re := by
    funext z
    simp [oscillatorySeed,waveExp,Complex.exp_re,phi]
  rw [he]
  have hw : ContDiff ℝ ∞ (waveExp phi N) :=
    (Complex.contDiff_exp (𝕜 := ℝ)).comp (contDiff_const.mul hp)
  have h := (realPart_iterated_norm_le (waveExp phi N) x hw.contDiffAt k).trans
    (waveExp_derivative_bound hp k x hD hN hphi)
  simpa [phi] using h

end
end Yau.Jets

end OAI
