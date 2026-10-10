import OAI.InformationTheory.BooleanNoise.FiniteNoise
import OAI.InformationTheory.BooleanNoise.Statement
import OAI.InformationTheory.BooleanNoise.EntropyScalars
import OAI.InformationTheory.BooleanNoise.InformationIdentity

namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem noiseOperator_dictator (u : ℝ) (i : Fin n) (x : Cube n) :
    noiseOperator u (signEncoding (dictator i)) x =
      u * signEncoding (dictator i) x := by
  let a : Fin n → Bool → ℝ :=
    fun j b => if j = i then (if b then 1 else -1) else 1
  have hprod : (fun y : Cube n => ∏ j, a j (y j)) = signEncoding (dictator i) := by
    funext y
    simp [a, signEncoding, dictator]
    rfl
  have hfactor (j : Fin n) :
      (∑ b : Bool, (if x j = b then (1 + u) / 2 else (1 - u) / 2) * a j b) =
        if j = i then u * signEncoding (dictator i) x else 1 := by
    by_cases hji : j = i
    · subst j
      cases hx : x i <;> simp [a, hx, signEncoding, dictator] <;> ring
    · cases hx : x j <;> simp [a, hji] <;> ring
  calc
    _ = noiseOperator u (fun y => ∏ j, a j (y j)) x := by rw [hprod]
    _ = ∏ j, ∑ b : Bool,
        (if x j = b then (1 + u) / 2 else (1 - u) / 2) * a j b :=
      noiseOperator_prod u a x
    _ = u * signEncoding (dictator i) x := by simp_rw [hfactor]; simp

theorem cubeAverage_dictator (i : Fin n) : cubeAverage (signEncoding (dictator i)) = 0 := by
  simpa only [noiseOperator_zero_correlation, zero_mul] using
    noiseOperator_dictator 0 i (fun _ => false)

theorem signEncoding_complementDictator (i : Fin n) :
    signEncoding (complementDictator i) = fun x => -signEncoding (dictator i) x := by
  funext x
  cases hx : x i <;> simp [signEncoding, complementDictator, dictator, hx]

theorem noiseOperator_complementDictator (u : ℝ) (i : Fin n) (x : Cube n) :
    noiseOperator u (signEncoding (complementDictator i)) x =
      u * signEncoding (complementDictator i) x := by
  rw [signEncoding_complementDictator, noiseOperator_neg, noiseOperator_dictator]
  ring

theorem cubeAverage_complementDictator (i : Fin n) :
    cubeAverage (signEncoding (complementDictator i)) = 0 := by
  rw [signEncoding_complementDictator, cubeAverage_neg, cubeAverage_dictator, neg_zero]

theorem isSignValued_signEncoding (f : Cube n → Bool) : IsSignValued (signEncoding f) := by
  intro x
  cases hx : f x <;> simp [signEncoding, hx]

@[simp] theorem entropyAverage_const (c : ℝ) :
    entropyAverage (fun _ : Cube n => c) = entropy c :=
  cubeAverage_const n (entropy c)

@[simp] theorem informationDeficit_const (c : ℝ) :
    informationDeficit (fun _ : Cube n => c) = 0 := by
  simp [informationDeficit]

theorem entropyAverage_neg (g : Cube n → ℝ) :
    entropyAverage (fun x => -g x) = entropyAverage g := by
  simp [entropyAverage]

theorem informationDeficit_neg (g : Cube n → ℝ) :
    informationDeficit (fun x => -g x) = informationDeficit g := by
  simp only [informationDeficit, cubeAverage_neg, entropy_neg, entropyAverage_neg]

@[simp] theorem informationDeficit_noise_const (u c : ℝ) :
    informationDeficit (noiseOperator u (fun _ : Cube n => c)) = 0 := by
  have h : noiseOperator u (fun _ : Cube n => c) = fun _ => c := by
    funext x
    exact noiseOperator_const u c x
  rw [h, informationDeficit_const]

@[simp] theorem informationDeficit_noise_zero (g : Cube n → ℝ) :
    informationDeficit (noiseOperator 0 g) = 0 := by
  have h : noiseOperator 0 g = fun _ => cubeAverage g := by
    funext x
    exact noiseOperator_zero_correlation g x
  rw [h, informationDeficit_const]

theorem informationDeficit_noise_one_le (g : Cube n → ℝ) (hg : IsSignValued g) :
    informationDeficit (noiseOperator 1 g) ≤ psi 1 := by
  have hnoise : noiseOperator 1 g = g := by
    funext x
    exact noiseOperator_one g x
  have he : entropyAverage g = 0 := by
    have hpoint : (fun x => entropy (g x)) = fun _ : Cube n => 0 := by
      funext x
      rcases hg x with h | h <;> simp [h]
    unfold entropyAverage
    rw [hpoint, cubeAverage_const]
  rw [hnoise, informationDeficit, he, sub_zero, psi_one]
  exact entropy_le_ell _

theorem informationDeficit_noise_dictator (u : ℝ) (i : Fin n) :
    informationDeficit (noiseOperator u (signEncoding (dictator i))) = psi u := by
  have he : entropyAverage (noiseOperator u (signEncoding (dictator i))) = entropy u := by
    have hpoint :
        (fun x => entropy (noiseOperator u (signEncoding (dictator i)) x)) =
          fun _ : Cube n => entropy u := by
      funext x
      rw [noiseOperator_dictator]
      cases hx : x i <;> simp [signEncoding, dictator, hx]
    unfold entropyAverage
    rw [hpoint, cubeAverage_const]
  rw [informationDeficit, cubeAverage_noiseOperator, cubeAverage_dictator,
    entropy_zero, he]
  simp [entropy]

theorem informationDeficit_noise_complementDictator (u : ℝ) (i : Fin n) :
    informationDeficit (noiseOperator u (signEncoding (complementDictator i))) = psi u := by
  rw [signEncoding_complementDictator]
  have h : noiseOperator u (fun x => -signEncoding (dictator i) x) =
      fun x => -noiseOperator u (signEncoding (dictator i)) x := by
    funext x
    exact noiseOperator_neg u (signEncoding (dictator i)) x
  rw [h, informationDeficit_neg, informationDeficit_noise_dictator]

theorem mutualInformation_dictator (ε : ℝ) (hε0 : 0 ≤ ε) (hεhalf : ε ≤ (1 : ℝ) / 2)
    (i : Fin n) : mutualInformation ε (dictator i) = 1 - binaryEntropy ε := by
  rw [mutualInformation_eq_informationDeficit ε (dictator i) hε0 hεhalf,
    informationDeficit_noise_dictator, one_sub_binaryEntropy_eq_psi]

theorem mutualInformation_complementDictator (ε : ℝ) (hε0 : 0 ≤ ε)
    (hεhalf : ε ≤ (1 : ℝ) / 2) (i : Fin n) :
    mutualInformation ε (complementDictator i) = 1 - binaryEntropy ε := by
  rw [mutualInformation_eq_informationDeficit ε (complementDictator i) hε0 hεhalf,
    informationDeficit_noise_complementDictator, one_sub_binaryEntropy_eq_psi]

theorem dictatorAttainment : DictatorAttainmentStatement := by
  intro n _ ε hε0 hεhalf i
  exact ⟨mutualInformation_dictator ε hε0 hεhalf i,
    mutualInformation_complementDictator ε hε0 hεhalf i⟩

theorem mutualInformation_zero_le (f : Cube n → Bool) : mutualInformation 0 f ≤ 1 := by
  rw [mutualInformation_eq_informationDeficit 0 f (by norm_num) (by norm_num)]
  simp only [mul_zero, sub_zero]
  apply (div_le_one ell_pos).mpr
  simpa only [psi_one] using
    informationDeficit_noise_one_le (signEncoding f) (isSignValued_signEncoding f)

theorem mutualInformation_half (f : Cube n → Bool) :
    mutualInformation ((1 : ℝ) / 2) f = 0 := by
  rw [mutualInformation_eq_informationDeficit _ f (by norm_num) (by norm_num)]
  norm_num

theorem courtadeKumar_zero (f : Cube n → Bool) :
    mutualInformation 0 f ≤ 1 - binaryEntropy 0 := by
  simpa only [binaryEntropy_zero, sub_zero] using mutualInformation_zero_le f

theorem courtadeKumar_half (f : Cube n → Bool) :
    mutualInformation ((1 : ℝ) / 2) f ≤ 1 - binaryEntropy ((1 : ℝ) / 2) := by
  rw [mutualInformation_half, one_sub_binaryEntropy_eq_psi]
  norm_num

end LeanBlast.CourtadeKumar

end

end OAI
