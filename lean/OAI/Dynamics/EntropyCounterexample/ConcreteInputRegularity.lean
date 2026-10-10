import OAI.Dynamics.EntropyCounterexample.NormalizedPrediction
import OAI.Dynamics.EntropyCounterexample.SphereAngularInput
import OAI.Dynamics.EntropyCounterexample.LocalPredictionInput
import OAI.Dynamics.EntropyCounterexample.PredictionModelBridge

namespace OAI

noncomputable section

namespace Problem340.ConcreteInputRegularity

abbrev Ambient := AmbientPrediction.Ambient

def preparation (x : Ambient) : ℝ := preparationCoeff x.1

def predictedClock (n : ℕ) : Ambient → ℝ :=
  NormalizedPrediction.clock AmbientPrediction.predictor (n + 1)

def angular (n : ℕ) (x : Ambient) : ℂ :=
  SphereAngularInput.angularAmbient (2 ^ (n + 2)) x.2

def ambientInput (L : ℝ) (i : Fin 3) (x : Ambient) : ℂ :=
  ∑' n, predictionSummand preparation (readoutCoeff i) predictedClock angular L n x

theorem predictor_preserves_norm (x : Ambient) (hx : ‖x.2‖ = 1) :
    ‖(AmbientPrediction.predictor x).2‖ = 1 := by
  exact mem_sphere_zero_iff_norm.mp
    (SphereDoubling.ambientMap_mem_sphere ⟨x.2, mem_sphere_zero_iff_norm.mpr hx⟩)

theorem exists_contDiffOn_ambientInput_product :
    ∃ (B : ℝ) (W : Set SphereAmbient), 1 ≤ B ∧ IsOpen W ∧
      Metric.sphere (0 : SphereAmbient) 1 ⊆ W ∧
      ∀ L : ℝ, B < L → 2 < L → ∀ i : Fin 3,
        ContDiffOn ℝ 1 (ambientInput L i) (Set.univ ×ˢ W) := by
  obtain ⟨B, hB, hBbound⟩ := AmbientPrediction.exists_derivative_bound
  obtain ⟨U, K, hU, hsU, hK, hangular, hangularBound⟩ :=
    SphereAngularInput.exists_uniform_angular_neighborhood
  obtain ⟨A, hA, hAbound⟩ := exists_preparationCoeff_fderiv_bound
  obtain ⟨D, hD, hDbound⟩ := exists_readoutCoeff_fderiv_bound
  let V : Set Ambient := AmbientRetraction.cylinderDomain ∩ Prod.snd ⁻¹' U
  have hV : IsOpen V := AmbientRetraction.isOpen_cylinderDomain.inter
    (hU.preimage continuous_snd)
  have hVsub : AmbientPrediction.cylinder ⊆ V := by
    intro x hx
    refine ⟨?_, hsU hx.2⟩
    change (1 / 2 : ℝ) < ‖x.2‖
    rw [mem_sphere_zero_iff_norm.mp hx.2]
    norm_num
  have hpred : ContDiff ℝ 1 AmbientPrediction.predictor :=
    AmbientPrediction.contDiff_predictor
  have hnormBound : ∀ x : Ambient, ‖x.2‖ = 1 →
      ‖fderiv ℝ AmbientPrediction.predictor x‖ ≤ B := by
    intro x hx
    exact hBbound x ⟨Set.mem_univ _, mem_sphere_zero_iff_norm.mpr hx⟩
  let W : Set SphereAmbient := {z | (0, z) ∈ V}
  have hW : IsOpen W := hV.preimage (continuous_const.prodMk continuous_id)
  have hsW : Metric.sphere (0 : SphereAmbient) 1 ⊆ W :=
    fun z hz => hVsub ⟨Set.mem_univ _, hz⟩
  have hVW : V = Set.univ ×ˢ W := by
    ext x
    simp [V, W, AmbientRetraction.cylinderDomain]
  refine ⟨B, W, hB, hW, hsW, ?_⟩
  intro L hBL hL i
  rw [← hVW]
  apply contDiffOn_predictionInput hV (A := A) (D := D) (J := 4) (K := K)
    (B := B) (by linarith) (by linarith) (by norm_num) (by linarith)
    (by linarith) hBL hL
  · exact (preparationCoeff_contDiff.comp contDiff_fst).contDiffOn
  · exact readoutCoeff_contDiff i
  · intro n
    exact (NormalizedPrediction.contDiffOn_clock hpred predictor_preserves_norm
      (n + 1)).mono (fun _ hx => hx.1)
  · intro n
    exact ((hangular (2 ^ (n + 2))).of_le (by norm_num)).comp
      contDiffOn_snd (fun _ hx => hx.2)
  · intro x _
    change ‖preparationCoeff x.1‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (preparationCoeff_nonneg x.1)]
    exact preparationCoeff_le_one x.1
  · intro n x _
    rw [Real.norm_eq_abs, abs_of_nonneg (readoutCoeff_nonneg i _)]
    exact readoutCoeff_le_one i _
  · intro n x _
    exact SphereAngularInput.norm_angularAmbient_le_one _ _
  · intro x _
    have hh := norm_fderiv_comp_le
      ((preparationCoeff_contDiff (n := 1)).differentiable_one x.1)
      (differentiableAt_fst (p := x))
    change ‖fderiv ℝ preparation x‖ ≤ A
    apply hh.trans
    calc
      ‖fderiv ℝ preparationCoeff x.1‖ * ‖fderiv ℝ Prod.fst x‖
          ≤ A * 1 := mul_le_mul (hAbound x.1)
            (by rw [fderiv_fst]; exact ContinuousLinearMap.norm_fst_le ℝ ℝ SphereAmbient)
            (norm_nonneg _) (by linarith)
      _ = A := mul_one A
  · intro n x _
    exact hDbound i _
  · intro n x hx
    exact NormalizedPrediction.norm_fderiv_clock_le_scaled hpred predictor_preserves_norm
      (by linarith) hnormBound (n + 1) x hx.1
  · intro n x hx
    have hd : DifferentiableAt ℝ
        (SphereAngularInput.angularAmbient (2 ^ (n + 2))) x.2 :=
      (((hangular (2 ^ (n + 2))).of_le (by norm_num)).contDiffAt
        (hU.mem_nhds hx.2)).differentiableAt one_ne_zero
    have hh := norm_fderiv_comp_le hd (differentiableAt_snd (p := x))
    change ‖fderiv ℝ (angular n) x‖ ≤ K * (1 + 2 ^ (n + 2))
    apply hh.trans
    have hb : ‖fderiv ℝ (SphereAngularInput.angularAmbient (2 ^ (n + 2))) x.2‖ ≤
        K * (1 + (2 : ℝ) ^ (n + 2)) := by
      have := hangularBound (2 ^ (n + 2)) x.2 hx.2
      push_cast at this
      linarith [norm_nonneg (SphereAngularInput.angularAmbient (2 ^ (n + 2)) x.2)]
    calc
      _ ≤ (K * (1 + (2 : ℝ) ^ (n + 2))) * 1 := mul_le_mul hb
        (by rw [fderiv_snd]; exact ContinuousLinearMap.norm_snd_le ℝ ℝ SphereAmbient)
        (norm_nonneg _) (by positivity)
      _ = K * (1 + 2 ^ (n + 2)) := mul_one _

theorem exists_contDiffOn_ambientInput :
    ∃ (B : ℝ) (V : Set Ambient), 1 ≤ B ∧ IsOpen V ∧
      AmbientPrediction.cylinder ⊆ V ∧
      ∀ L : ℝ, B < L → 2 < L → ∀ i : Fin 3,
        ContDiffOn ℝ 1 (ambientInput L i) V := by
  obtain ⟨B, W, hB, hW, hsW, hreg⟩ := exists_contDiffOn_ambientInput_product
  exact ⟨B, Set.univ ×ˢ W, hB, isOpen_univ.prod hW,
    fun x hx => ⟨Set.mem_univ _, hsW hx.2⟩, hreg⟩

theorem ambientInput_eq_zero_of_preparation_eq_zero
    (L : ℝ) (i : Fin 3) (x : Ambient) (h : preparationCoeff x.1 = 0) :
    ambientInput L i x = 0 := by
  simp [ambientInput, predictionSummand, preparation, h]

theorem ambientInput_eq_zero_of_not_mem (L : ℝ) (i : Fin 3) (x : Ambient)
    (hx : x.1 ∉ Set.Ioo (8 : ℝ) 12) : ambientInput L i x = 0 := by
  apply ambientInput_eq_zero_of_preparation_eq_zero
  by_contra h
  exact hx (preparationCoeff_support ▸ h)

open scoped OnePoint

theorem horizontal_sphereOfComplex (z : ℂ) :
    SphereAngularInput.horizontal (sphereOfComplex z).val =
      (2 / (‖z‖ ^ 2 + 1) : ℝ) • z := by
  calc
    _ = (2 / (‖z‖ ^ 2 + 1) : ℝ) • ((z.re : ℂ) + (z.im : ℂ) * Complex.I) := by
      simp only [SphereAngularInput.horizontal, sphereOfComplex_val_zero,
        sphereOfComplex_val_one, Complex.real_smul]
      push_cast
      ring
    _ = _ := by rw [Complex.re_add_im]

theorem phase_complexSphereHomeomorph (z : OnePoint ℂ) :
    SphereAngularInput.phase (complexSphereHomeomorph z).val = Construction.phase z := by
  induction z using OnePoint.rec with
  | infty =>
      simp [SphereAngularInput.phase, SphereAngularInput.horizontal,
        chartNorthPole, chartNorthVector, Fin.ext_iff]
  | coe z =>
      rw [complexSphereHomeomorph_coe,
        SphereAngularInput.phase_eq_of_positive_scale
          (by positivity : (0 : ℝ) < 2 / (‖z‖ ^ 2 + 1))
          (horizontal_sphereOfComplex z)]
      simp [NormedSpace.normalize, Construction.phase_coe, Complex.real_smul,
        div_eq_mul_inv, mul_comm]

theorem cutoff_complexSphereHomeomorph (z : OnePoint ℂ) :
    SphereCutoffs.preparationCutoffAmbient (complexSphereHomeomorph z).val =
      SphereCutoffs.onePointPreparationCutoff z := by
  induction z using OnePoint.rec with
  | infty =>
      change SphereCutoffs.preparationCutoffAmbient chartNorthPole.val = 0
      apply SphereCutoffs.preparationCutoffAmbient_eq_zero_of_high
      norm_num [chartNorthPole, chartNorthVector, PiLp.single_apply, Fin.ext_iff]
  | coe z =>
      simp [SphereCutoffs.preparationCutoffAmbient,
        SphereCutoffs.affinePreparationCutoff, SphereCutoffs.affineHeight]

theorem angular_modelEmbedding (n : ℕ) (t : ℝ) (z : OnePoint ℂ) :
    angular n (PredictionModelBridge.modelEmbedding (t, z)) =
      (SphereCutoffs.onePointPreparationCutoff z : ℂ) *
        Construction.phase z ^ (2 ^ (n + 2)) := by
  change SphereAngularInput.angularAmbient _ (complexSphereHomeomorph z).val = _
  rw [SphereAngularInput.angularAmbient, phase_complexSphereHomeomorph,
    cutoff_complexSphereHomeomorph]

theorem predictedClock_modelEmbedding (D : Construction.SphereData)
    (hgate : D.gate = SphereCutoffs.onePointClockGate)
    (n : ℕ) (t : ℝ) (z : OnePoint ℂ) :
    predictedClock n (PredictionModelBridge.modelEmbedding (t, z)) =
      Construction.predictedClock D (n + 1) t z := by
  have hx : ‖(PredictionModelBridge.modelEmbedding (t, z)).2‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (complexSphereHomeomorph z).property
  have hn := NormalizedPrediction.clock_eq_original_on_sphere
    (G := AmbientPrediction.predictor) predictor_preserves_norm hx (n + 1)
  exact hn.trans (PredictionModelBridge.predictedClock_eq D hgate (n + 1) t z).symm

theorem summand_modelEmbedding (D : Construction.SphereData)
    (hgate : D.gate = SphereCutoffs.onePointClockGate)
    (hcutoff : D.cutoff = SphereCutoffs.onePointPreparationCutoff)
    (i : Fin 3) (n : ℕ) (t : ℝ) (z : OnePoint ℂ) :
    predictionSummand preparation (readoutCoeff i) predictedClock angular D.L n
        (PredictionModelBridge.modelEmbedding (t, z)) =
      ((preparationCoeff t / 10 : ℝ) : ℂ) * Construction.inputTerm D i n t z := by
  rw [predictionSummand, predictedClock_modelEmbedding D hgate,
    angular_modelEmbedding]
  simp only [preparation, PredictionModelBridge.modelEmbedding, Construction.inputTerm,
    hcutoff, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_ofNat]
  ring

theorem ambientInput_modelEmbedding (D : Construction.SphereData)
    (hgate : D.gate = SphereCutoffs.onePointClockGate)
    (hcutoff : D.cutoff = SphereCutoffs.onePointPreparationCutoff)
    (i : Fin 3) (t : ℝ) (z : OnePoint ℂ) :
    ambientInput D.L i (PredictionModelBridge.modelEmbedding (t, z)) =
      Construction.baseInput D i t z := by
  unfold ambientInput Construction.baseInput
  rw [← tsum_mul_left]
  exact tsum_congr (fun n => summand_modelEmbedding D hgate hcutoff i n t z)

theorem continuous_modelEmbedding : Continuous PredictionModelBridge.modelEmbedding :=
  continuous_fst.prodMk (continuous_subtype_val.comp
    (complexSphereHomeomorph.continuous.comp continuous_snd))

theorem exists_regular_baseInput :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ D : Construction.SphereData,
      D.gate = SphereCutoffs.onePointClockGate →
      D.cutoff = SphereCutoffs.onePointPreparationCutoff →
      B < D.L → 2 < D.L → ∀ i : Fin 3,
      ContDiff ℝ 1 (fun x : ℝ × ℂ =>
        Construction.baseInput D i x.1 (x.2 : OnePoint ℂ)) ∧
      Continuous (fun x : ℝ × OnePoint ℂ => Construction.baseInput D i x.1 x.2) := by
  obtain ⟨B, V, hB, hV, hsub, hreg⟩ := exists_contDiffOn_ambientInput
  refine ⟨B, hB, ?_⟩
  intro D hgate hcutoff hBL hL i
  have hinput := hreg D.L hBL hL i
  constructor
  · have hc : ContDiffOn ℝ 1
        (ambientInput D.L i ∘ PredictionModelBridge.affineEmbedding) Set.univ :=
      hinput.comp PredictionModelBridge.contDiff_affineEmbedding.contDiffOn
        (fun x _ => hsub (PredictionModelBridge.affineEmbedding_mem_cylinder x))
    have heq : (ambientInput D.L i ∘ PredictionModelBridge.affineEmbedding) =
        (fun x : ℝ × ℂ => Construction.baseInput D i x.1 (x.2 : OnePoint ℂ)) := by
      funext x
      exact ambientInput_modelEmbedding D hgate hcutoff i x.1 (x.2 : OnePoint ℂ)
    rw [heq, contDiffOn_univ] at hc
    exact hc
  · have hc : Continuous (ambientInput D.L i ∘ PredictionModelBridge.modelEmbedding) :=
      hinput.continuousOn.comp_continuous continuous_modelEmbedding
        (fun x => hsub (PredictionModelBridge.modelEmbedding_mem_cylinder x))
    have heq : (ambientInput D.L i ∘ PredictionModelBridge.modelEmbedding) =
        (fun x : ℝ × OnePoint ℂ => Construction.baseInput D i x.1 x.2) := by
      funext x
      exact ambientInput_modelEmbedding D hgate hcutoff i x.1 x.2
    rwa [heq] at hc

end Problem340.ConcreteInputRegularity

end

end OAI
