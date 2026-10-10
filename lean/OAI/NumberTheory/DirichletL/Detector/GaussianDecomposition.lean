import OAI.NumberTheory.DirichletL.Detector.GaussianWindows

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma annular_reassembly_summable {α : Type*} (a : α→ℂ) (N : α→ℝ)
    (ha : Summable a) (hN : ∀p,a p≠0→1≤N p) :
    Summable (fun q : α×ℕ=>gaussianAnnulus (N q.1/(2:ℝ)^q.2)*a q.1) := by
  have hs (p : α) : HasSum (fun j : ℕ=>‖gaussianAnnulus (N p/(2:ℝ)^j)*a p‖) ‖a p‖ := by
    by_cases hp : a p=0
    · simp only [hp,mul_zero,norm_zero]
      exact hasSum_zero
    · simpa only [norm_mul,one_mul] using (gaussianAnnulus_partition_norm (N p) (hN p hp)).mul_right ‖a p‖
  apply Summable.of_norm
  apply (summable_prod_of_nonneg (fun _=>norm_nonneg _)).mpr
  exact ⟨fun p=>(hs p).summable,by simpa only [fun p=>(hs p).tsum_eq] using ha.norm⟩

lemma annular_reassembly {α : Type*} (a : α→ℂ) (N : α→ℝ)
    (ha : Summable a) (hN : ∀p,a p≠0→1≤N p) :
    (∑'j : ℕ,∑'p : α,gaussianAnnulus (N p/(2:ℝ)^j)*a p)=∑'p,a p := by
  rw [Summable.tsum_comm (f:=fun p : α=>fun j : ℕ=>gaussianAnnulus (N p/(2:ℝ)^j)*a p)
    (annular_reassembly_summable a N ha hN)]
  apply tsum_congr
  intro p
  by_cases hp : a p=0
  · simp [hp]
  · simpa only [one_mul] using ((gaussianAnnulus_partition (N p) (hN p hp)).mul_right (a p)).tsum_eq

lemma gaussian_dyadic_correctedSummand (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (Z : ℝ) (hZ : 0<Z) (j : ℕ) (I J : Id) :
    correctedSummand S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) I J=
      gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)*
        correctedSummand S D Ψ gaussianCompletedProfile Z I J := by
  by_cases hI : I=0
  · subst I
    simp [correctedSummand,markedSummand,summand]
  by_cases hJ : J=0
  · subst J
    simp [correctedSummand,markedSummand,summand]
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hN := mul_pos hi (pow_pos hj 3)
  unfold correctedSummand markedSummand summand
  rw [gaussianDyadicProfile_Vstar _ _ _ (div_pos hN (by positivity)),
    gaussianCompleted_Vstar _ (div_pos hN hZ)]
  have he : (2:ℝ)^j*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/Z=
      (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z := by
    field_simp
  rw [he]
  ring

lemma gaussian_correctedSummand_norm_ge_one (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (Z : ℝ) (I J : Id)
    (h : correctedSummand S D Ψ gaussianCompletedProfile Z I J≠0) :
    1≤(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := by
  have hI : I≠0 := by intro he; subst I; simp [correctedSummand,markedSummand,summand] at h
  have hJ : J≠0 := by intro he; subst J; simp [correctedSummand,markedSummand,summand] at h
  have hi : 1≤Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : 1≤Ideal.absNorm J := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  exact_mod_cast one_le_mul_of_one_le_of_one_le hi (one_le_pow₀ hj)

theorem correctedGaussian_eq_tsum_dyadic (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (Z : ℝ) (hZ : 0<Z) :
    correctedCompletedT S D Ψ gaussianCompletedProfile Z=
      ∑'j : ℕ,correctedCompletedT S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) := by
  unfold correctedCompletedT
  simp_rw [gaussian_dyadic_correctedSummand S D Ψ Z hZ]
  exact (annular_reassembly _ _ (gaussian_correctedSummand_summable S D Ψ hΨ Z hZ)
    (fun p=>gaussian_correctedSummand_norm_ge_one S D Ψ Z p.1 p.2)).symm

end SevenEighths.ProbePhysical
end

end OAI
