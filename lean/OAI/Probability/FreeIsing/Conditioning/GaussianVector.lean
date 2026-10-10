import OAI.Probability.FreeIsing.Conditioning.Characteristic

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

namespace Problem367.ConditionalGaussianVector

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem map_restrict_eq_smul_of_condExp_inner_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → H} (hX : Measurable[mΩ] X)
    (ν : Measure H) [IsProbabilityMeasure ν]
    (hchar : ∀ t : H,
      P[(fun ω => Complex.exp ((⟪X ω, t⟫ : ℝ) * Complex.I)) | m] =ᵐ[P]
        fun _ => charFun ν t)
    {s : Set Ω} (hs : MeasurableSet[m] s) :
    Measure.map X (P.restrict s) = P s • ν := by
  let : IsFiniteMeasure (P s • ν) := ν.smul_finite (measure_ne_top P s)
  apply Measure.ext_of_charFun
  funext t
  have hi : Integrable (fun ω => Complex.exp ((⟪X ω, t⟫ : ℝ) * Complex.I)) P := by
    have hi := ConditionalCharacteristic.integrable_character (P := P)
      (show Measurable (fun ω => ⟪X ω, t⟫) by fun_prop) 1
    convert hi using 1
    funext ω
    simp [ConditionalCharacteristic.character]
  rw [charFun_apply, integral_map hX.aemeasurable (by fun_prop),
    charFun_apply, integral_smul_measure]
  rw [← setIntegral_condExp hm hi hs]
  calc
    (∫ ω in s, P[(fun ω => Complex.exp ((⟪X ω, t⟫ : ℝ) * Complex.I)) | m] ω ∂P) =
        ∫ _ in s, charFun ν t ∂P :=
      integral_congr_ae (ae_restrict_of_ae (hchar t))
    _ = _ := by simp [charFun_apply, measureReal_def]

theorem law_and_indep_of_condExp_inner_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → H} (hX : Measurable[mΩ] X)
    (ν : Measure H) [IsProbabilityMeasure ν]
    (hchar : ∀ t : H,
      P[(fun ω => Complex.exp ((⟪X ω, t⟫ : ℝ) * Complex.I)) | m] =ᵐ[P]
        fun _ => charFun ν t)
    {E : Type*} [MeasurableSpace E] {Y : Ω → E} (hY : Measurable[m] Y) :
    HasLaw X ν P ∧ IndepFun X Y P := by
  have hlaw : Measure.map X P = ν := by
    simpa using map_restrict_eq_smul_of_condExp_inner_character hm hX ν hchar
      (MeasurableSet.univ : MeasurableSet[m] Set.univ)
  refine ⟨⟨hX.aemeasurable, hlaw⟩, ?_⟩
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro a b ha hb
  have hrestrict := congrArg (fun μ : Measure H => μ a)
    (map_restrict_eq_smul_of_condExp_inner_character hm hX ν hchar (hY hb))
  rw [Measure.map_apply hX ha, Measure.restrict_apply (hX ha),
    Measure.smul_apply, smul_eq_mul, ← hlaw, Measure.map_apply hX ha] at hrestrict
  exact hrestrict.trans (mul_comm _ _)

end Hilbert

section FiniteVector

variable {ι : Type*} [Fintype ι]

theorem charFun_product_gaussian (v : ι → ℝ≥0) (t : EuclideanSpace ℝ ι) :
    charFun ((Measure.pi (fun i => gaussianReal 0 (v i))).map (WithLp.toLp 2)) t =
      Complex.exp (-((∑ i, (v i : ℝ) * (t i) ^ 2 : ℝ) : ℂ) / 2) := by
  simp_rw [charFun_pi, charFun_gaussianReal, ← Complex.exp_sum]
  simp [Finset.sum_div, neg_div, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow]

theorem product_gaussian_law_and_indep_of_condExp_linear_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → ι → ℝ} (hX : Measurable[mΩ] X)
    (v : ι → ℝ≥0)
    (hchar : ∀ a : ι → ℝ,
      P[(fun ω => Complex.exp (((∑ i, a i * X ω i : ℝ) : ℂ) * Complex.I)) | m] =ᵐ[P]
        fun _ => Complex.exp (-((∑ i, (v i : ℝ) * (a i) ^ 2 : ℝ) : ℂ) / 2))
    {E : Type*} [MeasurableSpace E] {Y : Ω → E} (hY : Measurable[m] Y) :
    HasLaw X (Measure.pi (fun i => gaussianReal 0 (v i))) P ∧ IndepFun X Y P := by
  let Z : Ω → EuclideanSpace ℝ ι := fun ω => WithLp.toLp 2 (X ω)
  let ν : Measure (EuclideanSpace ℝ ι) :=
    (Measure.pi (fun i => gaussianReal 0 (v i))).map (WithLp.toLp 2)
  have hZ : Measurable Z := (WithLp.measurable_toLp 2 _).comp hX
  have hν : IsProbabilityMeasure ν := inferInstance
  have hc : ∀ t : EuclideanSpace ℝ ι,
      P[(fun ω => Complex.exp ((⟪Z ω, t⟫ : ℝ) * Complex.I)) | m] =ᵐ[P]
        fun _ => charFun ν t := by
    intro t
    simpa only [Z, ν, PiLp.inner_apply, WithLp.ofLp_toLp, Real.inner_apply, mul_comm,
      charFun_product_gaussian] using hchar t.ofLp
  obtain ⟨hlaw, hind⟩ := law_and_indep_of_condExp_inner_character hm hZ ν hc hY
  constructor
  · refine ⟨hX.aemeasurable, ?_⟩
    apply (MeasurableEquiv.toLp 2 (ι → ℝ)).map_measurableEquiv_injective
    change (P.map X).map (WithLp.toLp 2) = ν
    rw [Measure.map_map (WithLp.measurable_toLp 2 _) hX]
    exact hlaw.map_eq
  · simpa only [Function.comp_def, Z, WithLp.ofLp_toLp, id_eq] using
      hind.comp (WithLp.measurable_ofLp 2 (ι → ℝ)) measurable_id

theorem condExp_linear_character_of_unit_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → ι → ℝ} (v : ℝ≥0)
    (hchar : ∀ a : ι → ℝ, (∑ i, (a i) ^ 2) = 1 → ∀ u : ℝ,
      P[ConditionalCharacteristic.character (fun ω => ∑ i, a i * X ω i) u | m] =ᵐ[P]
        fun _ => Complex.exp (-((v : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2)) :
    ∀ a : ι → ℝ,
      P[(fun ω => Complex.exp (((∑ i, a i * X ω i : ℝ) : ℂ) * Complex.I)) | m] =ᵐ[P]
        fun _ => Complex.exp (-((∑ i, (v : ℝ) * (a i) ^ 2 : ℝ) : ℂ) / 2) := by
  classical
  intro a
  by_cases hz : (∑ i, (a i) ^ 2) = 0
  · have ha : ∀ i, a i = 0 := by
      intro i
      have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (a j))).mp hz
      exact sq_eq_zero_iff.mp (hs i (Finset.mem_univ i))
    simpa [ha] using
      Filter.EventuallyEq.of_eq (condExp_const (μ := P) hm (1 : ℂ))
  let q : ℝ := Real.sqrt (∑ i, (a i) ^ 2)
  have hsq : 0 < ∑ i, (a i) ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg (a i))) (Ne.symm hz)
  have hq : 0 < q := Real.sqrt_pos.mpr hsq
  have hq2 : q ^ 2 = ∑ i, (a i) ^ 2 := Real.sq_sqrt hsq.le
  let b : ι → ℝ := fun i => a i / q
  have hb : (∑ i, (b i) ^ 2) = 1 := by
    simp only [b, div_pow, ← Finset.sum_div, hq2]
    exact div_self hz
  have heq : ConditionalCharacteristic.character (fun ω => ∑ i, b i * X ω i) q =
      (fun ω => Complex.exp (((∑ i, a i * X ω i : ℝ) : ℂ) * Complex.I)) := by
    funext ω
    have hs : q * (∑ i, b i * X ω i) = ∑ i, a i * X ω i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [b]
      field_simp
    simp only [ConditionalCharacteristic.character, ← Complex.ofReal_mul, hs]
  have h := hchar b hb q
  rw [heq] at h
  convert h using 1
  funext ω
  congr 1
  rw [← Complex.ofReal_pow, hq2, ← Finset.mul_sum]
  push_cast
  ring

theorem condExp_weighted_character_of_unit_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → ι → ℝ} (v : ℝ≥0)
    (hchar : ∀ a : ι → ℝ, (∑ i, (a i) ^ 2) = 1 → ∀ u : ℝ,
      P[ConditionalCharacteristic.character (fun ω => ∑ i, a i * X ω i) u | m] =ᵐ[P]
        fun _ => Complex.exp (-((v : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2)) :
    ∀ a : ι → ℝ,
      P[ConditionalCharacteristic.character (fun ω => ∑ i, a i * X ω i) 1 | m] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i, ((v : ℝ) : ℂ) * (a i : ℂ)^2) / 2) := by
  intro a
  have he : ConditionalCharacteristic.character (fun ω => ∑ i, a i * X ω i) 1 =
      (fun ω => Complex.exp (((∑ i, a i * X ω i : ℝ) : ℂ) * Complex.I)) := by
    funext ω
    simp [ConditionalCharacteristic.character]
  rw [he]
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow] using
    condExp_linear_character_of_unit_character hm v hchar a

theorem product_gaussian_law_and_indep_of_condExp_unit_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → ι → ℝ} (hX : Measurable[mΩ] X)
    (v : ℝ≥0)
    (hchar : ∀ a : ι → ℝ, (∑ i, (a i) ^ 2) = 1 → ∀ u : ℝ,
      P[ConditionalCharacteristic.character (fun ω => ∑ i, a i * X ω i) u | m] =ᵐ[P]
        fun _ => Complex.exp (-((v : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2))
    {E : Type*} [MeasurableSpace E] {Y : Ω → E} (hY : Measurable[m] Y) :
    HasLaw X (Measure.pi (fun _ : ι => gaussianReal 0 v)) P ∧ IndepFun X Y P := by
  exact product_gaussian_law_and_indep_of_condExp_linear_character hm hX
    (fun _ => v) (condExp_linear_character_of_unit_character hm v hchar) hY

end FiniteVector

section ArbitraryArray

variable {ι : Type*}

theorem infinite_product_gaussian_law_and_indep_of_condExp_linear_character
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → ι → ℝ} (hX : Measurable[mΩ] X)
    (v : ι → ℝ≥0)
    (hchar : ∀ (I : Finset ι) (a : I → ℝ),
      P[(fun ω => Complex.exp (((∑ i : I, a i * X ω i : ℝ) : ℂ) * Complex.I)) | m] =ᵐ[P]
        fun _ => Complex.exp (-((∑ i : I, (v i : ℝ) * (a i) ^ 2 : ℝ) : ℂ) / 2))
    {E : Type*} [MeasurableSpace E] {Y : Ω → E} (hY : Measurable[m] Y) :
    HasLaw X (Measure.infinitePi (fun i => gaussianReal 0 (v i))) P ∧
      iIndepFun (fun i ω => X ω i) P ∧ IndepFun X Y P := by
  classical
  have hfinite (I : Finset ι) :
      HasLaw (fun ω (i : I) => X ω i) (Measure.pi (fun i : I => gaussianReal 0 (v i))) P ∧
        IndepFun (fun ω (i : I) => X ω i) Y P :=
    product_gaussian_law_and_indep_of_condExp_linear_character hm
      (by fun_prop) (fun i : I => v i) (hchar I) hY
  have hcoordinate (i : ι) : HasLaw (fun ω => X ω i) (gaussianReal 0 (v i)) P := by
    let j : ({i} : Finset ι) := ⟨i, Finset.mem_singleton_self i⟩
    exact (measurePreserving_eval (fun k : ({i} : Finset ι) => gaussianReal 0 (v k)) j).fun_comp_hasLaw (hfinite {i}).1
  have hind : iIndepFun (fun i ω => X ω i) P := by
    apply iIndepFun_iff_finset.mpr
    intro I
    exact (iIndepFun_iff_hasLaw_pi_pi (fun i : I => hcoordinate i)).mpr (hfinite I).1
  refine ⟨hind.hasLaw_infinitePi hcoordinate hX.aemeasurable, hind, ?_⟩
  exact IndepFun.process_indepFun (fun i => (measurable_pi_apply i).comp hX)
    (hY.mono hm le_rfl) (fun I => (hfinite I).2)

end ArbitraryArray

end Problem367.ConditionalGaussianVector

end

end OAI
