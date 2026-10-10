import OAI.Probability.InvariantIsing.Magnetic.MagneticScalarThird

namespace OAI

/-! Fourth spatial differentiation of the actual Gaussian field step.
The derivative is expressed in bounded tilted averages; no positive-variance
assumption is needed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldTiltSpatial (ζ : ℝ) (v : ℝ≥0) (F M A B : ℝ → ℝ) (z : ℝ) : ℝ :=
  fieldSpinTransition ζ v F B z + ζ *
    (fieldSpinTransition ζ v F (fun y => A y * M y) z -
      fieldSpinTransition ζ v F A z * fieldSpinTransition ζ v F M z)

lemma measurable_fieldTiltSpatial (ζ : ℝ) (v : ℝ≥0) {F M A B : ℝ → ℝ}
    (hF : Measurable F) (hM : Measurable M) (hA : Measurable A) (hB : Measurable B) :
    Measurable (fieldTiltSpatial ζ v F M A B) := by
  exact (measurable_fieldSpinTransition ζ v hF hB).add
    (((measurable_fieldSpinTransition ζ v hF (hA.mul hM)).sub
      ((measurable_fieldSpinTransition ζ v hF hA).mul
        (measurable_fieldSpinTransition ζ v hF hM))).const_mul ζ)

def fieldFourthTransform (ζ : ℝ) (v : ℝ≥0) (F M Q R S : ℝ → ℝ) (z : ℝ) : ℝ :=
  let T := fieldSpinTransition ζ v F
  let D := fieldTiltSpatial ζ v F M
  let q := fieldCurvatureTransform ζ v F M Q z
  let r := fieldThirdTransform ζ v F M Q R z
  D R S z + ζ * (D (fun y => Q y * M y) (fun y => R y * M y + Q y * Q y) z -
    (D Q R z * T M z + T Q z * q)) +
  ζ * ((D (fun y => 2 * M y * Q y) (fun y => 2 * Q y * Q y + 2 * M y * R y) z +
    ζ * (D (fun y => (M y) ^ 2 * M y) (fun y => 3 * (M y) ^ 2 * Q y) z -
      (D (fun y => (M y) ^ 2) (fun y => 2 * M y * Q y) z * T M z +
        T (fun y => (M y) ^ 2) z * q))) -
    2 * (q * q + T M z * r))

lemma hasDerivAt_fieldThirdTransform (ζ : ℝ) (v : ℝ≥0)
    {F M Q R S : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q) (hR : Measurable R) (hS : Measurable S)
    {K C D E : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ C)
    (bR : ∀ y, |R y| ≤ D) (bS : ∀ y, |S y| ≤ E)
    (dF : ∀ y, HasDerivAt F (M y) y)
    (dM : ∀ y, HasDerivAt M (Q y) y)
    (dQ : ∀ y, HasDerivAt Q (R y) y)
    (dR : ∀ y, HasDerivAt R (S y) y) (z : ℝ) :
    HasDerivAt (fieldThirdTransform ζ v F M Q R)
      (fieldFourthTransform ζ v F M Q R S z) z := by
  have bprod {A B : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
      (ba : ∀ y, |A y| ≤ a) (bb : ∀ y, |B y| ≤ b) (y : ℝ) :
      |A y * B y| ≤ a * b := by
    rw [abs_mul]
    exact mul_le_mul (ba y) (bb y) (abs_nonneg _) ha
  have bsq : ∀ y, |(M y) ^ 2| ≤ K ^ 2 := by
    intro y
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (bM y) 2
  have bQM := bprod hC bQ bM
  have b2MQ : ∀ y, |2 * M y * Q y| ≤ 2 * K * C := by
    intro y
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (bM y) (by norm_num)) (bQ y)
      (abs_nonneg _) (by positivity)
  have bM3 := bprod (sq_nonneg K) bsq bM
  have bQM' : ∀ y, |R y * M y + Q y * Q y| ≤ D * K + C * C := by
    intro y
    exact (abs_add_le _ _).trans (add_le_add (bprod hD bR bM y) (bprod hC bQ bQ y))
  have b2MQ' : ∀ y, |2 * Q y * Q y + 2 * M y * R y| ≤ 2 * C * C + 2 * K * D := by
    intro y
    rw [show 2 * Q y * Q y + 2 * M y * R y =
      2 * (Q y * Q y) + 2 * (M y * R y) by ring]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (bprod hC bQ bQ y) (by norm_num : (0 : ℝ) ≤ 2)
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (bprod hK bM bR y) (by norm_num : (0 : ℝ) ≤ 2)
  have bM3' : ∀ y, |3 * (M y) ^ 2 * Q y| ≤ 3 * K ^ 2 * C := by
    intro y
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (bsq y) (by norm_num)) (bQ y)
      (abs_nonneg _) (by positivity)
  have dQM (y : ℝ) : HasDerivAt (fun x => Q x * M x) (R y * M y + Q y * Q y) y :=
    (dQ y).mul (dM y)
  have d2MQ (y : ℝ) : HasDerivAt (fun x => 2 * M x * Q x)
      (2 * Q y * Q y + 2 * M y * R y) y := by
    convert ((dM y).const_mul 2).mul (dQ y) using 1
  have dM3 (y : ℝ) : HasDerivAt (fun x => (M x) ^ 2 * M x)
      (3 * (M y) ^ 2 * Q y) y := by
    convert ((dM y).pow 2).mul (dM y) using 1
    simp only [Pi.pow_apply]
    ring
  have dM2 (y : ℝ) : HasDerivAt (fun x => (M x) ^ 2) (2 * M y * Q y) y := by
    convert (dM y).pow 2 using 1
    ring
  have ht (A B : ℝ → ℝ) (ha : Measurable A) (hb : Measurable B)
      {a b : ℝ} (ha0 : 0 ≤ a) (ba : ∀ y, |A y| ≤ a) (bb : ∀ y, |B y| ≤ b)
      (dab : ∀ y, HasDerivAt A (B y) y) :
      HasDerivAt (fieldSpinTransition ζ v F A) (fieldTiltSpatial ζ v F M A B z) z :=
    hasDerivAt_fieldSpinTransition ζ v hF hG hM ha hb hK ha0 bM ba bb dF dab z
  have hm := ht M Q hM hQ hK bM bQ dM
  have hm' : HasDerivAt (fieldSpinTransition ζ v F M)
      (fieldCurvatureTransform ζ v F M Q z) z := by
    simpa only [fieldTiltSpatial, fieldCurvatureTransform, pow_two] using hm
  have hq := ht Q R hQ hR hC bQ bR dQ
  have hr := ht R S hR hS hD bR bS dR
  have hqm := ht _ _ (hQ.mul hM) ((hR.mul hM).add (hQ.mul hQ))
    (mul_nonneg hC hK) bQM bQM' dQM
  have h2mq := ht _ _ ((measurable_const.mul hM).mul hQ)
    (((measurable_const.mul hQ).mul hQ).add ((measurable_const.mul hM).mul hR))
    (by positivity) b2MQ b2MQ' d2MQ
  have hm3 := ht _ _ ((hM.pow_const 2).mul hM) ((measurable_const.mul (hM.pow_const 2)).mul hQ)
    (by positivity) bM3 bM3' dM3
  have hm2 := ht _ _ (hM.pow_const 2) ((measurable_const.mul hM).mul hQ)
    (sq_nonneg K) bsq b2MQ dM2
  have hcurv := hasDerivAt_fieldCurvatureTransform ζ v hF hG hM hQ hR hK hC bM bQ bR dF dM dQ z
  have hd := (hr.add ((hqm.sub (hq.mul hm')).const_mul ζ)).add
    (((h2mq.add ((hm3.sub (hm2.mul hm')).const_mul ζ)).sub
      ((hm'.mul hcurv).const_mul 2)).const_mul ζ)
  convert hd using 1
  · funext y
    change fieldThirdTransform ζ v F M Q R y =
      (fieldSpinTransition ζ v F R y + ζ *
        (fieldSpinTransition ζ v F (fun u => Q u * M u) y -
          fieldSpinTransition ζ v F Q y * fieldSpinTransition ζ v F M y)) +
      ζ * ((fieldSpinTransition ζ v F (fun u => 2 * M u * Q u) y + ζ *
        (fieldSpinTransition ζ v F (fun u => M u ^ 2 * M u) y -
          fieldSpinTransition ζ v F (fun u => M u ^ 2) y * fieldSpinTransition ζ v F M y)) -
        2 * (fieldSpinTransition ζ v F M y * fieldCurvatureTransform ζ v F M Q y))
    simp only [fieldThirdTransform]
    ring
  · rfl

lemma measurable_fieldFourthTransform (ζ : ℝ) (v : ℝ≥0)
    {F M Q R S : ℝ → ℝ} (hF : Measurable F) (hM : Measurable M)
    (hQ : Measurable Q) (hR : Measurable R) (hS : Measurable S) :
    Measurable (fieldFourthTransform ζ v F M Q R S) := by
  have hm := measurable_fieldSpinTransition ζ v hF hM
  have hq := measurable_fieldSpinTransition ζ v hF hQ
  have hm2 := measurable_fieldSpinTransition ζ v hF (hM.pow_const 2)
  have hc : Measurable (fieldCurvatureTransform ζ v F M Q) :=
    hq.add ((hm2.sub (hm.pow_const 2)).const_mul ζ)
  have hr := measurable_fieldThirdTransform ζ v hF hM hQ hR
  have h1 := measurable_fieldTiltSpatial ζ v hF hM hR hS
  have h2 := measurable_fieldTiltSpatial ζ v hF hM (hQ.mul hM)
    ((hR.mul hM).add (hQ.mul hQ))
  have h3 := measurable_fieldTiltSpatial ζ v hF hM hQ hR
  have h4 := measurable_fieldTiltSpatial ζ v hF hM (((measurable_const (a := (2 : ℝ))).mul hM).mul hQ)
    ((((measurable_const (a := (2 : ℝ))).mul hQ).mul hQ).add
      (((measurable_const (a := (2 : ℝ))).mul hM).mul hR))
  have h5 := measurable_fieldTiltSpatial ζ v hF hM ((hM.pow_const 2).mul hM)
    (((measurable_const (a := (3 : ℝ))).mul (hM.pow_const 2)).mul hQ)
  have h6 := measurable_fieldTiltSpatial ζ v hF hM (hM.pow_const 2)
    (((measurable_const (a := (2 : ℝ))).mul hM).mul hQ)
  exact (h1.add ((h2.sub ((h3.mul hm).add (hq.mul hc))).const_mul ζ)).add
    (((h4.add ((h5.sub ((h6.mul hm).add (hm2.mul hc))).const_mul ζ)).sub
      (((hc.mul hc).add (hm.mul hr)).const_mul 2)).const_mul ζ)

private def MagneticUniformBound (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C

private lemma magnetic_uniform_const (c : ℝ) : MagneticUniformBound (fun _ => c) :=
  ⟨|c|, abs_nonneg _, fun _ => le_rfl⟩

private lemma magnetic_uniform_add {f g : ℝ → ℝ}
    (hf : MagneticUniformBound f) (hg : MagneticUniformBound g) :
    MagneticUniformBound (fun x => f x + g x) := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  exact ⟨C + D, add_nonneg hC hD,
    fun x => (abs_add_le _ _).trans (add_le_add (hf x) (hg x))⟩

private lemma magnetic_uniform_sub {f g : ℝ → ℝ}
    (hf : MagneticUniformBound f) (hg : MagneticUniformBound g) :
    MagneticUniformBound (fun x => f x - g x) := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  exact ⟨C + D, add_nonneg hC hD,
    fun x => (abs_sub _ _).trans (add_le_add (hf x) (hg x))⟩

private lemma magnetic_uniform_mul {f g : ℝ → ℝ}
    (hf : MagneticUniformBound f) (hg : MagneticUniformBound g) :
    MagneticUniformBound (fun x => f x * g x) := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C * D, mul_nonneg hC hD, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hf x) (hg x) (abs_nonneg _) hC

lemma fieldFourthTransform_bounded (ζ : ℝ) (v : ℝ≥0)
    {F M Q R S : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    {K C D E : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (bM : ∀ y, |M y| ≤ K) (bQ : ∀ y, |Q y| ≤ C)
    (bR : ∀ y, |R y| ≤ D) (bS : ∀ y, |S y| ≤ E) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, |fieldFourthTransform ζ v F M Q R S z| ≤ B := by
  have mM : MagneticUniformBound M := ⟨K, hK, bM⟩
  have mQ : MagneticUniformBound Q := ⟨C, hC, bQ⟩
  have mR : MagneticUniformBound R := ⟨D, (abs_nonneg _).trans (bR 0), bR⟩
  have mS : MagneticUniformBound S := ⟨E, (abs_nonneg _).trans (bS 0), bS⟩
  have hT (A : ℝ → ℝ) (ha : MagneticUniformBound A) :
      MagneticUniformBound (fieldSpinTransition ζ v F A) := by
    obtain ⟨a, ha0, ha⟩ := ha
    exact ⟨a, ha0, fieldSpinTransition_bound ζ v hF hG ha⟩
  have hD (A B : ℝ → ℝ) (ha : MagneticUniformBound A) (hb : MagneticUniformBound B) :
      MagneticUniformBound (fieldTiltSpatial ζ v F M A B) := by
    obtain ⟨a, ha0, ha⟩ := ha
    obtain ⟨b, hb0, hb⟩ := hb
    exact ⟨b + 2 * |ζ| * a * K, by positivity,
      fieldSpinTransition_derivative_bound ζ v hF hG hK ha0 bM ha hb⟩
  have mM2 : MagneticUniformBound (fun y => (M y) ^ 2) := by
    simpa only [pow_two] using magnetic_uniform_mul mM mM
  have m2MQ := magnetic_uniform_mul (magnetic_uniform_mul (magnetic_uniform_const 2) mM) mQ
  have mQnew : MagneticUniformBound (fieldCurvatureTransform ζ v F M Q) := by
    have he : (fun z => fieldSpinTransition ζ v F Q z + ζ *
        (fieldSpinTransition ζ v F (fun y => M y ^ 2) z -
          fieldSpinTransition ζ v F M z * fieldSpinTransition ζ v F M z)) =
        fieldCurvatureTransform ζ v F M Q := by
      funext z
      simp only [fieldCurvatureTransform, pow_two]
    rw [← he]
    exact magnetic_uniform_add (hT Q mQ) (magnetic_uniform_mul (magnetic_uniform_const ζ)
      (magnetic_uniform_sub (hT _ mM2) (magnetic_uniform_mul (hT M mM) (hT M mM))))
  have mRnew : MagneticUniformBound (fieldThirdTransform ζ v F M Q R) := by
    have hb := fieldThirdTransform_bound ζ v hF hG hK hC bM bQ bR
    exact ⟨_, (abs_nonneg _).trans (hb 0), hb⟩
  have m1 := hD R S mR mS
  have m2 := hD _ _ (magnetic_uniform_mul mQ mM)
    (magnetic_uniform_add (magnetic_uniform_mul mR mM) (magnetic_uniform_mul mQ mQ))
  have m3 := hD Q R mQ mR
  have m4 := hD _ _ m2MQ
    (magnetic_uniform_add
      (magnetic_uniform_mul (magnetic_uniform_mul (magnetic_uniform_const 2) mQ) mQ)
      (magnetic_uniform_mul (magnetic_uniform_mul (magnetic_uniform_const 2) mM) mR))
  have m5 := hD _ _ (magnetic_uniform_mul mM2 mM)
    (magnetic_uniform_mul (magnetic_uniform_mul (magnetic_uniform_const 3) mM2) mQ)
  have m6 := hD _ _ mM2 m2MQ
  exact magnetic_uniform_add
    (magnetic_uniform_add m1 (magnetic_uniform_mul (magnetic_uniform_const ζ)
      (magnetic_uniform_sub m2
        (magnetic_uniform_add (magnetic_uniform_mul m3 (hT M mM))
          (magnetic_uniform_mul (hT Q mQ) mQnew)))))
    (magnetic_uniform_mul (magnetic_uniform_const ζ)
      (magnetic_uniform_sub
        (magnetic_uniform_add m4 (magnetic_uniform_mul (magnetic_uniform_const ζ)
          (magnetic_uniform_sub m5
            (magnetic_uniform_add (magnetic_uniform_mul m6 (hT M mM))
              (magnetic_uniform_mul (hT _ mM2) mQnew)))))
        (magnetic_uniform_mul (magnetic_uniform_const 2)
          (magnetic_uniform_add (magnetic_uniform_mul mQnew mQnew)
            (magnetic_uniform_mul (hT M mM) mRnew)))))

end InvariantIsing

end

end OAI
