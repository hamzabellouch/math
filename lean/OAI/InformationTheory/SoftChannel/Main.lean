import OAI.InformationTheory.SoftChannel.SoftInformation

namespace OAI

section

noncomputable section
open scoped BigOperators

namespace SoftChannel204

open LeanBlast
open Set

lemma production_eq {n : ℕ} (g : Cube n → ℝ) :
    production g = CourtadeKumar.dissipation g := by
  unfold production numberOperator
  change CourtadeKumar.cubeAverage
    (fun x => Real.artanh (g x) * ((1/2:ℝ) * ∑ i, (g x-g (flip i x)))) = _
  have h : (fun x => Real.artanh (g x) * ((1/2:ℝ) * ∑ i, (g x-g (flip i x)))) =
      (fun x => ∑ i, Real.artanh (g x) * CourtadeKumar.cubeDerivative i g x) := by
    funext x
    simp only [CourtadeKumar.cubeDerivative, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change Real.artanh (g x) * (1/2*(g x-g (flip i x))) = Real.artanh (g x) * ((g x-g (flip i x))/2)
    ring
  rw [h,CourtadeKumar.cubeAverage_sum]
  rfl

lemma S_eq_L {x : ℝ} (hx : 0 < x) :
    S (L-x)=CourtadeKumar.L x := by
  change (if CourtadeKumar.ell-x < 0 then 0 else CourtadeKumar.rGap (CourtadeKumar.ell-x)) =
    (if 0 < x ∧ x < CourtadeKumar.ell then CourtadeKumar.rGap (CourtadeKumar.ell-x) else 0)
  rcases lt_trichotomy x CourtadeKumar.ell with h | h | h
  · rw [ite_eq_right (by linarith),ite_eq_left ⟨hx,h⟩]
  · rw [h,sub_self,ite_eq_right (lt_irrefl 0),CourtadeKumar.rGap_zero,ite_eq_right (by simp)]
  · rw [ite_eq_left (by linarith),ite_eq_right (fun hh => (not_lt_of_ge h.le) hh.2)]

lemma reserve_eq {m I : ℝ} (hm : |m| < 1) (hI : I < H m) :
    reserve m I=CourtadeKumar.meanReserve m I := by
  unfold reserve CourtadeKumar.meanReserve
  rw [S_eq_L (div_pos (sub_pos.mpr hI) (CourtadeKumar.scalar_meanVariance_pos hm))]
  rfl

lemma softJoint_eq {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) :
    softJoint ρ g=CourtadeKumar.softJointNat ρ g := by
  funext b y
  unfold softJoint CourtadeKumar.softJointNat
  change CourtadeKumar.cubeAverage _=CourtadeKumar.cubeAverage _
  congr 1
  funext x
  cases b <;> simp only [sign,CourtadeKumar.signProbability,Bool.false_eq_true,ite_false,ite_true]
  · change (1 + -1*g x)/2*kernel ρ x y = (1-g x)/2*kernel ρ x y
    ring
  · change (1 + 1*g x)/2*kernel ρ x y = (1+g x)/2*kernel ρ x y
    ring

theorem softContraction : SoftContraction := by
  intro n u hu ρ hρ
  exact CourtadeKumar.all_soft_contraction u hu hρ

theorem softAttainment : SoftAttainment := by
  intro n i a ha ρ _
  exact CourtadeKumar.all_soft_coordinate_attainment i a ha ρ

theorem softInformationIdentity : SoftInformationIdentity := by
  intro n u hu ρ hρ
  rw [softJoint_eq]
  exact CourtadeKumar.soft_information_identity u hu hρ

theorem refinedBoolean : RefinedBoolean := by
  intro n f ρ hρ
  have hρa : |ρ| ∈ Icc (0:ℝ) 1 := ⟨abs_nonneg _, abs_le.mpr hρ⟩
  have hm : avg (sign ∘ f) ∈ Icc (-1:ℝ) 1 :=
    ⟨CourtadeKumar.cubeAverage_mono (fun x => (CourtadeKumar.signEncoding_closed f x).1) |>.trans'
        (CourtadeKumar.cubeAverage_const n (-1)).ge,
     (CourtadeKumar.cubeAverage_mono (fun x => (CourtadeKumar.signEncoding_closed f x).2)).trans
        (CourtadeKumar.cubeAverage_const n 1).le⟩
  exact ⟨CourtadeKumar.bool_information_identity f hρ,
    CourtadeKumar.refined_boolean_bound f hρ,
    CourtadeKumar.refined_curve_le hm hρa,
    fun hm0 hm1 hρ0 => CourtadeKumar.refined_curve_strict hm0 hm1 ⟨hρ0,hρa.2⟩⟩

theorem booleanAttainment : BooleanAttainment := by
  intro n i ρ hρ
  change CourtadeKumar.mutualInformationNat (CourtadeKumar.boolJointNat ρ (CourtadeKumar.dictator i)) = _ ∧
    CourtadeKumar.mutualInformationNat (CourtadeKumar.boolJointNat ρ (CourtadeKumar.complementDictator i)) = _
  rw [CourtadeKumar.bool_information_identity _ hρ,CourtadeKumar.bool_information_identity _ hρ,
    CourtadeKumar.informationDeficit_noise_dictator,CourtadeKumar.informationDeficit_noise_complementDictator]
  exact ⟨(CourtadeKumar.psi_abs_soft ρ).symm,(CourtadeKumar.psi_abs_soft ρ).symm⟩

theorem bitsConversion : BitsConversion := by
  intro n f ε hε
  have h : psi (1-2*ε)/L=1-binaryEntropyBits ε :=
    (CourtadeKumar.one_sub_binaryEntropy_eq_psi ε).symm
  refine ⟨h,?_⟩
  rw [← h]
  apply div_le_div_of_nonneg_right _ CourtadeKumar.ell_pos.le
  have hρ : (1-2*ε) ∈ Icc (-1:ℝ) 1 := by constructor <;> linarith [hε.1,hε.2]
  have hb := (refinedBoolean n f (1-2*ε) hρ).2.1.trans (refinedBoolean n f (1-2*ε) hρ).2.2.1
  rwa [abs_of_nonneg (by linarith [hε.2] : 0 ≤ 1-2*ε)] at hb

theorem sharpProduction : SharpProduction := by
  intro n g hg
  refine ⟨?_,le_max_right _ _⟩
  unfold hybrid
  have hm : |avg g| < 1 := abs_lt.mpr (CourtadeKumar.IsInterior.cubeAverage hg)
  have hI : info g < H (avg g) := CourtadeKumar.IsInterior.information_lt_entropy hg
  rw [reserve_eq hm hI,production_eq]
  exact CourtadeKumar.all_soft_max_production g hg

theorem fullMain : FullMain :=
  ⟨softContraction,softAttainment,softInformationIdentity,refinedBoolean,
    booleanAttainment,bitsConversion,sharpProduction⟩

end SoftChannel204
end
end

end OAI
