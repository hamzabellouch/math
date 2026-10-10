import OAI.InformationTheory.SoftChannel.Contraction

namespace OAI

section

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LeanBlast.CourtadeKumar

def softJointNat {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (b : Bool) (y : Cube n) : ℝ :=
  cubeAverage (fun x => signProbability (g x) b * noiseKernel ρ x y)

def boolJointNat {n : ℕ} (ρ : ℝ) (f : Cube n → Bool) (b : Bool) (y : Cube n) : ℝ :=
  cubeAverage (fun x => if f x=b then noiseKernel ρ x y else 0)

universe u v

def mutualInformationNat {A : Type u} {B : Type v} [Fintype A] [Fintype B] (p : A → B → ℝ) : ℝ :=
  ∑ a, ∑ b, if 0 < p a b then p a b * Real.log (p a b / ((∑ y, p a y)*(∑ x, p x b))) else 0

lemma noiseKernel_nonneg_closed {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Icc (-1) 1) (x y : Cube n) :
    0 ≤ noiseKernel ρ x y := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith [hρ.1,hρ.2]

lemma signProbability_nonneg_soft {v : ℝ} (hv : v ∈ Icc (-1) 1) (b : Bool) :
    0 ≤ signProbability v b := by
  cases b <;> simp only [signProbability, Bool.false_eq_true, ite_false, ite_true] <;> linarith [hv.1,hv.2]

lemma softJointNat_nonneg {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Icc (-1) 1)
    (g : Cube n → ℝ) (hg : IsClosedSoft g) (b : Bool) (y : Cube n) :
    0 ≤ softJointNat ρ g b y :=
  cubeAverage_nonneg (fun x => mul_nonneg (signProbability_nonneg_soft (hg x) b) (noiseKernel_nonneg_closed hρ x y))

lemma softJointNat_posterior {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (b : Bool) (y : Cube n) :
    softJointNat ρ g b y=signProbability (noiseOperator ρ g y) b / (2:ℝ)^n := by
  unfold softJointNat cubeAverage
  simp_rw [noiseKernel_symm ρ _ y,mul_comm (signProbability _ b)]
  change noiseOperator ρ (fun x => signProbability (g x) b) y / (2:ℝ)^n = _
  rw [noiseOperator_signProbability]

lemma softJointNat_left {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (b : Bool) :
    (∑ y, softJointNat ρ g b y)=signProbability (cubeAverage g) b := by
  simp_rw [softJointNat_posterior]
  rw [← Finset.sum_div]
  change cubeAverage (fun y => signProbability (noiseOperator ρ g y) b)=_
  rw [cubeAverage_signProbability,cubeAverage_noiseOperator]

lemma softJointNat_right {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (y : Cube n) :
    (∑ b, softJointNat ρ g b y)=1/(2:ℝ)^n := by
  simp_rw [softJointNat_posterior]
  rw [← Finset.sum_div,sum_signProbability]

lemma softJointNat_total {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) :
    (∑ b, ∑ y, softJointNat ρ g b y)=1 := by
  simp_rw [softJointNat_left]
  exact sum_signProbability _

lemma softJointNat_xlogx_bool {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (y : Cube n) :
    (∑ b, xlogx (softJointNat ρ g b y))=xlogx (((2:ℝ)^n)⁻¹)-
      entropy (noiseOperator ρ g y)/(2:ℝ)^n := by
  simp_rw [softJointNat_posterior,div_eq_mul_inv,xlogx_mul]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,
    sum_signProbability,sum_xlogx_signProbability]
  ring

theorem soft_information_identity {n : ℕ} (g : Cube n → ℝ) (hg : IsClosedSoft g)
    {ρ : ℝ} (hρ : ρ ∈ Icc (-1) 1) :
    mutualInformationNat (softJointNat ρ g)=informationDeficit (noiseOperator ρ g) := by
  unfold mutualInformationNat
  rw [finite_kl_eq_entropy_sums _ (softJointNat_nonneg hρ g hg)]
  have hj : (∑ b, ∑ y, xlogx (softJointNat ρ g b y))=
      (2:ℝ)^n*xlogx (((2:ℝ)^n)⁻¹)-entropyAverage (noiseOperator ρ g) := by
    rw [Finset.sum_comm]
    simp_rw [softJointNat_xlogx_bool]
    simp [Finset.sum_sub_distrib,entropyAverage,cubeAverage,Finset.sum_div]
  rw [hj]
  simp_rw [softJointNat_left,softJointNat_right]
  rw [sum_xlogx_signProbability]
  simp only [Finset.sum_const,Finset.card_univ,card_cube,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  unfold informationDeficit
  rw [cubeAverage_noiseOperator]
  simp only [one_div]
  ring

lemma boolJointNat_eq_soft {n : ℕ} (ρ : ℝ) (f : Cube n → Bool) :
    boolJointNat ρ f=softJointNat ρ (signEncoding f) := by
  funext b y
  unfold boolJointNat softJointNat
  congr 1
  funext x
  rw [signProbability_signEncoding]
  split_ifs <;> simp

lemma signEncoding_closed {n : ℕ} (f : Cube n → Bool) : IsClosedSoft (signEncoding f) := by
  intro x
  cases hfx : f x <;> simp [signEncoding,hfx]

lemma information_signEncoding {n : ℕ} (f : Cube n → Bool) :
    informationDeficit (signEncoding f)=entropy (cubeAverage (signEncoding f)) := by
  rw [informationDeficit,entropyAverage_eq_zero_of_signValued _ (isSignValued_signEncoding f),sub_zero]

lemma bool_information_identity {n : ℕ} (f : Cube n → Bool)
    {ρ : ℝ} (hρ : ρ ∈ Icc (-1) 1) :
    mutualInformationNat (boolJointNat ρ f)=informationDeficit (noiseOperator ρ (signEncoding f)) := by
  rw [boolJointNat_eq_soft]
  exact soft_information_identity _ (signEncoding_closed f) hρ

lemma psi_abs_soft (v : ℝ) : psi |v|=psi v := by
  by_cases hv : 0 ≤ v
  · rw [abs_of_nonneg hv]
  · rw [abs_of_neg (lt_of_not_ge hv),psi_neg]

lemma psiInv_psi_abs {v : ℝ} (hv : |v| ≤ 1) : psiInv (psi v)=|v| := by
  rw [← psi_abs_soft v]
  exact psiInv_psi ⟨abs_nonneg _,hv⟩

lemma refined_curve_le {m ρ : ℝ} (hm : m ∈ Icc (-1) 1) (hρ : ρ ∈ Icc 0 1) :
    psi (ρ*psiInv (entropy m)) ≤ psi ρ := by
  have ha := psiInv_mem_Icc ⟨entropy_nonneg hm,entropy_le_ell m⟩
  have har : ρ*psiInv (entropy m) ≤ ρ := mul_le_of_le_one_right hρ.1 ha.2
  exact strictMonoOn_psi.monotoneOn ⟨mul_nonneg hρ.1 ha.1,har.trans hρ.2⟩ hρ har

lemma refined_curve_strict {m ρ : ℝ} (hm : 0 < |m|) (hm1 : |m| < 1) (hρ : ρ ∈ Ioc 0 1) :
    psi (ρ*psiInv (entropy m)) < psi ρ := by
  have hp : 0 < psi m := by rw [← psi_abs_soft]; exact psi_pos_of_pos hm hm1.le
  have he : entropy m < ell := by dsimp [entropy]; linarith
  have ha := psiInv_mem_Ico (entropy_nonneg (abs_le.mp hm1.le)) he
  have har : ρ*psiInv (entropy m)<ρ := mul_lt_of_lt_one_right hρ.1 ha.2
  exact strictMonoOn_psi ⟨mul_nonneg hρ.1.le ha.1,har.le.trans hρ.2⟩ ⟨hρ.1.le,hρ.2⟩ har

theorem refined_boolean_bound {n : ℕ} (f : Cube n → Bool)
    {ρ : ℝ} (hρ : ρ ∈ Icc (-1) 1) :
    mutualInformationNat (boolJointNat ρ f) ≤
      psi (|ρ| * psiInv (entropy (cubeAverage (signEncoding f)))) := by
  rw [bool_information_identity f hρ]
  have h := all_soft_contraction (signEncoding f) (signEncoding_closed f) hρ
  rwa [information_signEncoding] at h

lemma information_scaled_coordinate {n : ℕ} (i : Fin n) (a : ℝ) :
    informationDeficit (fun x => a*signEncoding (dictator i) x)=psi a := by
  have he : (fun x => a*signEncoding (dictator i) x)=noiseOperator a (signEncoding (dictator i)) := by
    funext x
    rw [noiseOperator_dictator]
  rw [he,informationDeficit_noise_dictator]

lemma information_noise_scaled_coordinate {n : ℕ} (i : Fin n) (a ρ : ℝ) :
    informationDeficit (noiseOperator ρ (fun x => a*signEncoding (dictator i) x))=psi (ρ*a) := by
  have he : noiseOperator ρ (fun x => a*signEncoding (dictator i) x)=
      fun x => (ρ*a)*signEncoding (dictator i) x := by
    funext x
    rw [noiseOperator_smul,noiseOperator_dictator]
    ring
  rw [he,information_scaled_coordinate]

theorem all_soft_coordinate_attainment {n : ℕ} (i : Fin n) (a : ℝ) (ha : |a| ≤ 1) (ρ : ℝ) :
    informationDeficit (noiseOperator ρ (fun x => a*signEncoding (dictator i) x))=
      psi (|ρ| * psiInv (informationDeficit (fun x => a*signEncoding (dictator i) x))) := by
  rw [information_noise_scaled_coordinate,information_scaled_coordinate,psiInv_psi_abs ha,← abs_mul,psi_abs_soft]

end LeanBlast.CourtadeKumar
end
end

end OAI
