import OAI.Probability.FreeIsing.Brownian.ArrayLaw
import OAI.Probability.FreeIsing.Brownian.Characterization
import OAI.Probability.FreeIsing.Conditioning.GaussianVector

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianArrayCharacterization

theorem isGaussianProcess_array_of_finite_coordinate_processes
    {ι T Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ι → T → Ω → ℝ}
    (h : ∀ I : Finset ι,
      IsGaussianProcess (fun t ω (i : I) => B i t ω) P) :
    IsGaussianProcess (fun p : (_ : ι) × T => B p.1 p.2) P := by
  classical
  constructor
  intro S
  let I : Finset ι := S.image Sigma.fst
  let J : Finset T := S.image Sigma.snd
  let L : (J → I → ℝ) →L[ℝ] (S → ℝ) :=
    { toFun x p := x
        ⟨p.1.2, Finset.mem_image_of_mem Sigma.snd p.2⟩
        ⟨p.1.1, Finset.mem_image_of_mem Sigma.fst p.2⟩
      map_add' x y := by rfl
      map_smul' c x := by rfl }
  exact (h I |>.hasGaussianLaw J).map L

open ConditionalCharacteristic ConditionalGaussianVector

theorem gaussianPi_law_and_indep_of_weighted_characters
    {ι Ω : Type*} [Fintype ι] {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    {X : Ω → ι → ℝ} (hX : Measurable X) (v : ι → ℝ≥0)
    (hchar : ∀ a : ι → ℝ,
      P[character (fun ω => ∑ i, a i * X ω i) 1 | m] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i, ((v i : ℝ) : ℂ) * (a i : ℂ)^2) / 2))
    {E : Type*} [MeasurableSpace E] {Y : Ω → E} (hY : Measurable[m] Y) :
    HasLaw X (Measure.pi (fun i => gaussianReal 0 (v i))) P ∧ IndepFun X Y P := by
  apply product_gaussian_law_and_indep_of_condExp_linear_character hm hX v _ hY
  intro a
  have hc : character (fun ω => ∑ i, a i * X ω i) 1 =
      fun ω => Complex.exp (((∑ i, a i * X ω i : ℝ) : ℂ) * Complex.I) := by
    funext ω
    simp [character]
  have h := hchar a
  rw [hc] at h
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow] using h

theorem isGaussianProcess_vector_of_conditional_weighted_characters
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ι → ℝ} (F : Filtration ℝ≥0 mΩ) (hX : Adapted F X)
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hchar : ∀ s t : ℝ≥0, s ≤ t → ∀ a : ι → ℝ,
      P[character (fun ω => ∑ i, a i * (X t ω i - X s ω i)) 1 | F s] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2)) :
    IsGaussianProcess X P := by
  have hm (s t : ℝ≥0) : Measurable (fun ω => X t ω - X s ω) :=
    hX.measurable.sub hX.measurable
  have hlaw (s t : ℝ≥0) (hst : s ≤ t) :
      HasLaw (fun ω => X t ω - X s ω)
        (Measure.pi (fun _ : ι => gaussianReal 0 (t - s))) P :=
    (gaussianPi_law_and_indep_of_weighted_characters (F.le s) (hm s t)
      (fun _ : ι => t - s) (hchar s t hst)
      (measurable_const : Measurable[F s] (fun _ : Ω => ()))).1
  have hi : HasIndepIncrements X P := by
    apply BrownianCharacterization.hasIndepIncrements_of_past_events_general F hX
    intro s t hst A hA S hS
    let Y : Ω → ℝ := A.indicator (fun _ => 1)
    have hY : Measurable[F s] Y := measurable_const.indicator hA
    have hind := (gaussianPi_law_and_indep_of_weighted_characters
      (F.le s) (hm s t) (fun _ : ι => t - s) (hchar s t hst) hY).2
    have hAe : Y ⁻¹' {1} = A := by
      ext ω
      by_cases hω : ω ∈ A <;> simp [Y, hω]
    have hh := (indepFun_iff_measure_inter_preimage_eq_mul.mp hind)
      S {1} hS (measurableSet_singleton 1)
    simpa only [hAe, Set.inter_comm, mul_comm] using hh
  apply hi.isGaussianProcess _ hzero
  change ∀ t : ℝ≥0, HasGaussianLaw (X t) P
  intro t
  have hg : HasGaussianLaw (id : (ι → ℝ) → (ι → ℝ))
      (Measure.pi (fun _ : ι => gaussianReal 0 (t - 0))) :=
    (iIndepFun_pi (X := fun _ : ι => id) (fun _ => aemeasurable_id)).hasGaussianLaw
      (fun i => (measurePreserving_eval (fun _ : ι => gaussianReal 0 (t - 0)) i).hasLaw.hasGaussianLaw)
  have : IsGaussian (Measure.pi (fun _ : ι => gaussianReal 0 (t - 0))) := by
    simpa only [Measure.map_id] using hg.isGaussian_map
  apply (hlaw 0 t bot_le).hasGaussianLaw.congr
  filter_upwards [hzero] with ω hω
  simp [hω]

theorem isGaussianProcess_array_of_conditional_finite_characters
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ι → ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : ∀ i, Adapted F (B i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, B i 0 ω = 0)
    (hchar : ∀ (I : Finset ι) (s t : ℝ≥0), s ≤ t → ∀ a : I → ℝ,
      P[character (fun ω => ∑ i : I, a i * (B i t ω - B i s ω)) 1 | F s] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i : I, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2)) :
    IsGaussianProcess (fun p : (_ : ι) × ℝ≥0 => B p.1 p.2) P := by
  classical
  apply isGaussianProcess_array_of_finite_coordinate_processes
  intro I
  apply isGaussianProcess_vector_of_conditional_weighted_characters F
  · intro t
    let : MeasurableSpace Ω := F t
    exact Measurable.of_eval (fun index : I => hB index t)
  · have hz : ∀ᵐ ω ∂P, ∀ i : I, B i 0 ω = 0 := ae_all_iff.mpr (fun i => hzero i)
    filter_upwards [hz] with ω hω
    exact funext hω
  · exact hchar I

theorem conditional_character_coordinate
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ι → ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hchar : ∀ (I : Finset ι) (s t : ℝ≥0), s ≤ t → ∀ a : I → ℝ,
      P[character (fun ω => ∑ i : I, a i * (B i t ω - B i s ω)) 1 | F s] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i : I, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2))
    (i : ι) (s t : ℝ≥0) (hst : s ≤ t) (u : ℝ) :
    P[character (fun ω => B i t ω - B i s ω) u | F s] =ᵐ[P]
      fun _ => charFun (gaussianReal 0 (t - s)) u := by
  classical
  have h := hchar {i} s t hst (fun _ => u)
  have hc : character (fun ω => u * (B i t ω - B i s ω)) 1 =
      character (fun ω => B i t ω - B i s ω) u := by
    funext ω
    simp [character, Complex.ofReal_mul]
  simpa [hc, charFun_gaussianReal, neg_div] using h

theorem preBrownian_coordinate_of_conditional_finite_characters
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ι → ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : ∀ i, Adapted F (B i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, B i 0 ω = 0)
    (hchar : ∀ (I : Finset ι) (s t : ℝ≥0), s ≤ t → ∀ a : I → ℝ,
      P[character (fun ω => ∑ i : I, a i * (B i t ω - B i s ω)) 1 | F s] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i : I, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2))
    (i : ι) : IsPreBrownianReal (B i) P := by
  classical
  exact BrownianCharacterization.isPreBrownianReal_of_conditional_charFun
    F (hB i).stronglyAdapted (hzero i) (conditional_character_coordinate F hchar i)

theorem law_finite_coordinates_of_conditional_finite_characters
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ι → ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : ∀ i, Adapted F (B i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, B i 0 ω = 0)
    (hchar : ∀ (I : Finset ι) (s t : ℝ≥0), s ≤ t → ∀ a : I → ℝ,
      P[character (fun ω => ∑ i : I, a i * (B i t ω - B i s ω)) 1 | F s] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i : I, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2))
    (I : Finset ι) (t : ℝ≥0) :
    HasLaw (fun ω (i : I) => B i t ω)
      (Measure.pi (fun _ : I => gaussianReal 0 t)) P := by
  classical
  have hm : Measurable (fun ω (i : I) => B i t ω - B i 0 ω) :=
    Measurable.of_eval (fun index => (hB index).measurable.sub (hB index).measurable)
  have hh := (gaussianPi_law_and_indep_of_weighted_characters
    (F.le 0) hm (fun _ : I => t - 0) (hchar I 0 t bot_le)
    (measurable_const : Measurable[F 0] (fun _ : Ω => ()))).1
  simp only [tsub_zero] at hh
  apply hh.congr
  have hz : ∀ᵐ ω ∂P, ∀ i : I, B i 0 ω = 0 := ae_all_iff.mpr (fun i => hzero i)
  filter_upwards [hz] with ω hω
  funext i
  simp [hω i]

theorem covariance_coordinate_ne_of_gaussianPi_law
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ι → ℝ} (v : ι → ℝ≥0)
    (hX : HasLaw X (Measure.pi (fun i => gaussianReal 0 (v i))) P)
    (i j : ι) (hij : i ≠ j) :
    cov[fun ω => X ω i, fun ω => X ω j; P] = 0 := by
  rw [hX.covariance_fun_comp (f := fun x : ι → ℝ => x i) (g := fun x : ι → ℝ => x j)
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable]
  exact (iIndepFun_pi (X := fun _ : ι => id) (fun _ => aemeasurable_id)).indepFun hij
    |>.covariance_eq_zero
      ((measurePreserving_eval (fun i => gaussianReal 0 (v i)) i).hasLaw.hasGaussianLaw.memLp_two)
      ((measurePreserving_eval (fun i => gaussianReal 0 (v i)) j).hasLaw.hasGaussianLaw.memLp_two)

theorem crossCovariance_of_conditional_finite_characters
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ι → ℝ≥0 → Ω → ℝ} (F : Filtration ℝ≥0 mΩ)
    (hB : ∀ i, Adapted F (B i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, B i 0 ω = 0)
    (hchar : ∀ (I : Finset ι) (s t : ℝ≥0), s ≤ t → ∀ a : I → ℝ,
      P[character (fun ω => ∑ i : I, a i * (B i t ω - B i s ω)) 1 | F s] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i : I, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2)) :
    ∀ i j, i ≠ j → ∀ s t, cov[B i s, B j t; P] = 0 := by
  classical
  have hb (i : ι) := preBrownian_coordinate_of_conditional_finite_characters F hB hzero hchar i
  have hL2 (i : ι) (t : ℝ≥0) : MemLp (B i t) 2 P :=
    (hb i).isGaussianProcess.hasGaussianLaw_eval t |>.memLp_two
  have hsame (i j : ι) (hij : i ≠ j) (t : ℝ≥0) : cov[B i t, B j t; P] = 0 := by
    let I : Finset ι := {i, j}
    let ii : I := ⟨i, by simp [I]⟩
    let jj : I := ⟨j, by simp [I]⟩
    have hne : ii ≠ jj := fun h => hij (congrArg Subtype.val h)
    exact covariance_coordinate_ne_of_gaussianPi_law (fun _ : I => t)
      (law_finite_coordinates_of_conditional_finite_characters F hB hzero hchar I t)
      ii jj hne
  have hordered (i j : ι) (hij : i ≠ j) (s t : ℝ≥0) (hst : s ≤ t) :
      cov[B i s, B j t; P] = 0 := by
    have hi : IndepFun (fun ω => B j t ω - B j s ω) (B i s) P :=
      indepFun_of_condExp_character (F.le s)
        ((hB j).measurable.sub (hB j).measurable) (gaussianReal 0 (t - s))
        (conditional_character_coordinate F hchar j s t hst) (hB i s)
    change IndepFun (B j t - B j s) (B i s) P at hi
    have heq : B j t = (B j t - B j s) + B j s := by
      funext ω
      simp
    rw [heq, covariance_add_right (hL2 i s) ((hL2 j t).sub (hL2 j s)) (hL2 j s),
      hi.symm.covariance_eq_zero (hL2 i s) ((hL2 j t).sub (hL2 j s)), hsame i j hij s,
      add_zero]
  intro i j hij s t
  rcases le_total s t with hst | hts
  · exact hordered i j hij s t hst
  · rw [covariance_comm]
    exact hordered j i hij.symm t s hts

theorem map_brownianArray_eq_infinitePi_of_conditional_finite_characters
    {ι Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'}
    {B : ι → ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ω' → ℝ}
    (F : Filtration ℝ≥0 mΩ) (hB : ∀ i, Adapted F (B i))
    (hzero : ∀ i, ∀ᵐ ω ∂P, B i 0 ω = 0)
    (hchar : ∀ (I : Finset ι) (s t : ℝ≥0), s ≤ t → ∀ a : I → ℝ,
      P[character (fun ω => ∑ i : I, a i * (B i t ω - B i s ω)) 1 | F s] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i : I, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2))
    (hC : IsPreBrownianReal C Q) (hmC : ∀ t, Measurable (C t)) :
    P.map (fun ω i t => B i t ω) =
      Measure.infinitePi (fun _ : ι => Q.map (fun ω t => C t ω)) := by
  have hb (i : ι) := preBrownian_coordinate_of_conditional_finite_characters F hB hzero hchar i
  apply map_brownianArray_eq_infinitePi_reference
    (isGaussianProcess_array_of_conditional_finite_characters F hB hzero hchar)
    (fun i _ => (hB i).measurable) (fun i t => (hb i).integral_eval t)
    _ (crossCovariance_of_conditional_finite_characters F hB hzero hchar) hC hmC
  intro i s t hst
  simpa only [min_eq_left hst] using (hb i).covariance_eval s t

theorem map_continuousBrownianArray_eq_infinitePi_of_conditional_finite_characters
    [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]
    [StandardBorelSpace C(ℝ≥0, ℝ)]
    {ι Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P] {Q : Measure Ω'}
    {X : ι → Ω → C(ℝ≥0, ℝ)} {Y : Ω' → C(ℝ≥0, ℝ)}
    (F : Filtration ℝ≥0 mΩ) (hX : ∀ i, Adapted F (fun t ω => X i ω t))
    (hzero : ∀ i, ∀ᵐ ω ∂P, X i ω 0 = 0)
    (hchar : ∀ (I : Finset ι) (s t : ℝ≥0), s ≤ t → ∀ a : I → ℝ,
      P[character (fun ω => ∑ i : I, a i * (X i ω t - X i ω s)) 1 | F s] =ᵐ[P]
        fun _ => Complex.exp (-(∑ i : I, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2))
    (hmY : Measurable Y) (hY : IsPreBrownianReal (fun t ω => Y ω t) Q) :
    P.map (fun ω i => X i ω) =
      Measure.infinitePi (fun _ : ι => Q.map Y) := by
  have hb (i : ι) := preBrownian_coordinate_of_conditional_finite_characters F hX hzero hchar i
  apply map_continuousBrownianArray_eq_infinitePi_reference
    (fun i => measurable_continuousPath_of_evaluations (fun _ => (hX i).measurable)) hmY
    (isGaussianProcess_array_of_conditional_finite_characters F hX hzero hchar)
    (fun i t => (hb i).integral_eval t) _
    (crossCovariance_of_conditional_finite_characters F hX hzero hchar) hY
  intro i s t hst
  simpa only [min_eq_left hst] using (hb i).covariance_eval s t

end Problem367.GaussianArrayCharacterization

end

end OAI
