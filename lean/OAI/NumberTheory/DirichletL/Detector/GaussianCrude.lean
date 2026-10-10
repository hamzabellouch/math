import OAI.NumberTheory.DirichletL.Detector.GaussianTuple

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CubicEisenstein FourierBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gaussianAnnulus_norm_le_one (y : ℝ) : ‖gaussianAnnulus y‖≤1 := by
  rw [gaussianAnnulus_norm]
  change Real.smoothTransition (2-y)-Real.smoothTransition (2-2*y)≤1
  linarith [Real.smoothTransition.le_one (2-y),Real.smoothTransition.nonneg (2-2*y)]

lemma gaussianAnnulus_scaled_square (N T : ℝ) (hN : 0<N) (hT : 0<T) :
    N^2*‖gaussianAnnulus (N/T)‖≤4*T^2 := by
  by_cases hz : gaussianAnnulus (N/T)=0
  · rw [hz,norm_zero,mul_zero]
    positivity
  have hn : N/T<2 := by
    by_contra hh
    exact hz (gaussianAnnulus_large _ (le_of_not_gt hh))
  have hn' : N<2*T := (div_lt_iff₀ hT).mp hn
  calc
    _ ≤ N^2 := mul_le_of_le_one_right (sq_nonneg _) (gaussianAnnulus_norm_le_one _)
    _ ≤ _ := by nlinarith

lemma gaussianFixedWindow_spectral_identity (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (T t : ℝ) (hT : 0<T) (I J : Id) (hI : I≠0) (hJ : J≠0) :
    correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T I J=
      spectralSummand S D Ψ 2 I J*
        ((((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3:ℝ):ℂ)^2*
          (gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T)*
            logPhase t (Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T)))) := by
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hic : (Ideal.absNorm I:ℂ)≠0 := by exact_mod_cast hi.ne'
  have hjc : (Ideal.absNorm J:ℂ)≠0 := by exact_mod_cast hj.ne'
  unfold correctedSummand markedSummand CompletedGauss.summand spectralSummand fullIdealWeight
  rw [gaussianFixedWindow_Vstar_twist t _ (div_pos (mul_pos hi (pow_pos hj 3)) hT)]
  simp only [ite_eq_right hI,ite_eq_right hJ]
  norm_num only [show (3:ℂ)*2=6 by norm_num,Complex.cpow_neg,Complex.cpow_ofNat]
  push_cast
  field_simp

lemma gaussianFixedWindow_summand_crude (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (T t : ℝ) (hT : 0<T) (I J : Id) :
    ‖correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T I J‖≤
      4*T^2*rowMajorant 2 (I,J) := by
  by_cases hI : I=0
  · subst I
    simp only [correctedSummand,markedSummand,summand_zero_left,mul_zero,norm_zero]
    unfold rowMajorant
    positivity
  by_cases hJ : J=0
  · subst J
    simp only [correctedSummand,markedSummand,summand_zero_right,mul_zero,norm_zero]
    unfold rowMajorant
    positivity
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hN : 0<(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := mul_pos hi (pow_pos hj 3)
  rw [gaussianFixedWindow_spectral_identity S D Ψ T t hT I J hI hJ,
    norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN,
    norm_mul,logPhase_norm,mul_one]
  have hs : ‖spectralSummand S D Ψ 2 I J‖≤rowMajorant 2 (I,J) := by
    simpa only [Complex.ofReal_ofNat,Complex.ofReal_zero,zero_mul,add_zero] using
      spectralSummand_vertical_bound S D Ψ hΨ 2 0 (I,J)
  have hn := gaussianAnnulus_scaled_square _ T hN hT
  exact (mul_le_mul hs hn (by positivity) (by unfold rowMajorant;positivity)).trans_eq (by ring)

theorem gaussianFixedWindow_completed_crude :
    ∃C : ℝ,0<C ∧ ∀S : Finset Id,∀D : Id,∀Ψ : O→*ℂ,
      (∀n,‖Ψ n‖≤1)→∀T t : ℝ,0<T→
      ‖correctedCompletedT S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T‖≤C*T^2 := by
  let M : ℝ := ∑'p : Id×Id,rowMajorant 2 p
  have hM : 0≤M := tsum_nonneg (fun p=>by unfold rowMajorant;positivity)
  refine ⟨4*M+1,by positivity,?_⟩
  intro S D Ψ hΨ T t hT
  have hs := correctedSummand_summable S D Ψ _ (gaussianFixedWindow_twist_compact t) T hT
  change ‖∑'p : Id×Id,correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2‖≤_
  calc
    _ ≤ ∑'p : Id×Id,‖correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑'p : Id×Id,4*T^2*rowMajorant 2 p := hs.norm.tsum_le_tsum
      (fun p=>gaussianFixedWindow_summand_crude S D Ψ hΨ T t hT p.1 p.2)
      ((rowMajorant_summable 2 (by norm_num)).mul_left (4*T^2))
    _ = (4*M)*T^2 := by rw [tsum_mul_left];dsimp only [M];ring
    _ ≤ _ := by nlinarith [sq_nonneg T]

end SevenEighths.ProbePhysical
end

end OAI
