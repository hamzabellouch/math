import OAI.Probability.GaussianReplacement.Tilt

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory




lemma sphere_own_density_moment {d m r : ℕ}
    (hdim : AdmissibleDimensions d m r 1) (hd : 2 ≤ d) :
    ∫⁻ z : Rows (m+r) d × Sphere d,
      exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d))
      ∂(gaussianRows (m+r) d).prod (uniformSphere d) ≤
        momentConstant 9 d (3*4^d) (3*4^d) := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  have hB : (0:ℝ) < 3*4^d := by positivity
  have hG := uniformSphere_growth (show 1 ≤ d by omega) (show m+r ≤ d-1 by have := hdim.2.2.2.1; omega)
  have hD := uniformSphere_growth (show 1 ≤ d by omega) (le_refl (d-1))
  have ha : ∀ᵐ (s : Sphere d) ∂uniformSphere d,
      (∫⁻ G, exactDensity (uniformSphere d) G (label G (s:Vector d))
        ∂gaussianRows (m+r) d) ≤ momentConstant 9 d (3*4^d) (3*4^d) := by
    filter_upwards [ae_target_cube_limit (k:=m+r) (uniformSphere d)] with s hs
    have hfin := extended_ae_finite hdim (uniformSphere d) _ _ hB hB hG hD s
    have he : ∀ᵐ G ∂gaussianRows (m+r) d,
        exactDensity (uniformSphere d) G (label G (s:Vector d)) =
          extendedCubeDensity (uniformSphere d) G (label G (s:Vector d)) := by
      filter_upwards [hs,hfin] with G hG hf
      exact exactDensity_eq_of_tendsto _ _ _ hG.1 hf.ne
    have hm := exact_mixed_moment_of_ae hdim (uniformSphere d) _ _ hB hB hG hD s he
    simpa only [pow_one, gaussianRows, ←lintegral_pi_append (stdGaussian (Vector d)) m r
      _ (measurable_fixed_exact (uniformSphere d) s)] using hm
  rw [lintegral_prod_symm _ (measurable_own_exact (uniformSphere d)).aemeasurable]
  exact (lintegral_mono_ae ha).trans_eq (by simp)

lemma sphere_moment_log_bound {d : ℕ} (hd : 1 ≤ d) :
    Real.log (1+(momentConstant 9 d (3*4^d) (3*4^d)).toReal) ≤ 20*d := by
  have hB : (0:ℝ) < 3*4^d := by positivity
  have he : (momentConstant 9 d (3*4^d) (3*4^d)).toReal =
      Real.exp (9*d)*(3*4^d) := by
    simp [momentConstant,ENNReal.toReal_ofReal (by positivity :
      0 ≤ Real.exp (9*d)*(3*4^d))]
  rw [he]
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hpow : (1:ℝ) ≤ 4^d := one_le_pow₀ (by norm_num)
  have hexp : (1:ℝ) ≤ Real.exp (9*d) := Real.one_le_exp_iff.mpr (by positivity)
  have ht : 1 ≤ Real.exp (9*d)*(3*4^d) := by nlinarith
  have hl := Real.log_le_log (by positivity : 0<1+Real.exp (9*d)*(3*4^d))
    (show 1+Real.exp (9*d)*(3*4^d) ≤ 2*(Real.exp (9*d)*(3*4^d)) by linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by positivity),
    Real.log_mul (Real.exp_ne_zero _) hB.ne',Real.log_exp,
    Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),Real.log_pow] at hl
  have h2 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 2)
  have h3 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 3)
  have h4 := Real.log_le_self (by norm_num : (0:ℝ) ≤ 4)
  nlinarith

lemma sphere_label_entropy_finite {d m r : ℕ}
    (hdim : AdmissibleDimensions d m r 1) (hd : 2 ≤ d) :
    Integrable (fun z : Rows (m+r) d × Sphere d =>
      Real.log (exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d))).toReal)
      ((gaussianRows (m+r) d).prod (uniformSphere d)) ∧
    (∫ z : Rows (m+r) d × Sphere d,
      Real.log (exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d))).toReal
      ∂(gaussianRows (m+r) d).prod (uniformSphere d)) ≤ 20*d := by
  classical
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
  let μ := (gaussianRows (m+r) d).prod (uniformSphere d)
  let f : Rows (m+r) d × Sphere d → ℝ≥0∞ :=
    fun z => exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d))
  have hf : Measurable f := measurable_own_exact _
  have hmoment := sphere_own_density_moment hdim hd
  have ht : ∫⁻ z, f z ∂μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmoment
  have hJ := log_one_add_jensen μ f hf (fun z => exactDensity_ne_top _ _ _) ht
  have hM := ENNReal.toReal_mono (show momentConstant 9 d (3*4^d) (3*4^d) ≠ ∞ from ENNReal.ofReal_ne_top) hmoment
  have hMlog := Real.log_le_log (by positivity : 0<1+(∫⁻ z, f z ∂μ).toReal)
    (show 1+(∫⁻ z, f z ∂μ).toReal ≤ 1+(momentConstant 9 d (3*4^d) (3*4^d)).toReal from by dsimp [f,μ]; linarith)
  have hb := sphere_moment_log_bound (show 1 ≤ d by omega)
  have hJ' : ∫⁻ z, ENNReal.ofReal (Real.log (1+(f z).toReal)) ∂μ ≤ ENNReal.ofReal (20*d) :=
    hJ.trans (ENNReal.ofReal_le_ofReal (hMlog.trans hb))
  obtain ⟨⟨hiL,hbL⟩,hiP,_⟩ := log_bound_consequences μ f hf (20*d) (by positivity) hJ'
  have hB : (0:ℝ) < 3*4^d := by positivity
  have hAC := ae_labelLaw_ac_of_growth hdim (uniformSphere d) _ _ hB hB
    (uniformSphere_growth (show 1 ≤ d by omega) (show m+r ≤ d-1 by have := hdim.2.2.2.1; omega))
    (uniformSphere_growth (show 1 ≤ d by omega) (le_refl (d-1)))
  let c : Sphere d := Classical.choice inferInstance
  obtain ⟨hi,_⟩ := projection_cover_entropy (uniformSphere d) hAC hiP
    (Finset.singleton_nonempty c) (show (0:ℝ)<1 by norm_num)
    (ae_of_all _ (fun s => ⟨c,Finset.mem_singleton_self c,by
      have hdist := (norm_sub_le (s:Vector d) (c:Vector d))
      simpa only [Subtype.dist_eq,dist_eq_norm,norm_eq_of_mem_sphere s,norm_eq_of_mem_sphere c,one_add_one_eq_two,mul_one] using hdist⟩))
  refine ⟨hi,?_⟩
  apply (integral_mono hi hiL (fun z => ?_)).trans hbL
  exact (le_max_left _ _).trans (logPositive_le_log_one_add (f z))




def conditionalReferenceKL {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure (A×B)) (ν : Measure B) : ℝ≥0∞ := klDiv P (P.fst.prod ν)

lemma conditionalReferenceKL_chain {C A B : Type*} [MeasurableSpace C]
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (P : Measure (C×(A×B))) [IsProbabilityMeasure P]
    (ν : Measure A) (π : Measure B) [IsProbabilityMeasure ν] [IsProbabilityMeasure π] :
    conditionalReferenceKL P (ν.prod π) =
      conditionalReferenceKL (P.map (Prod.map id Prod.fst)) ν +
      conditionalReferenceKL (P.map MeasurableEquiv.prodAssoc.symm) π := by
  let R := P.map MeasurableEquiv.prodAssoc.symm
  let : IsProbabilityMeasure R := inferInstance
  have hRf : R.fst = P.map (Prod.map id Prod.fst) := by
    rw [Measure.fst,Measure.map_map measurable_fst MeasurableEquiv.prodAssoc.symm.measurable]
    rfl
  have hff : R.fst.fst = P.fst := by
    rw [hRf,Measure.fst,Measure.map_map measurable_fst (measurable_id.prodMap measurable_fst)]
    rfl
  have hr : (P.fst.prod (ν.prod π)).map MeasurableEquiv.prodAssoc.symm =
      (P.fst.prod ν).prod π := by rw [←Measure.prodAssoc_prod,MeasurableEquiv.map_symm_map]
  unfold conditionalReferenceKL
  rw [←klDiv_map_equiv P (P.fst.prod (ν.prod π)) MeasurableEquiv.prodAssoc.symm,hr,
    klDiv_prod_chain R (P.fst.prod ν) π]
  rw [←hff,hRf]

lemma conditionalReferenceKL_add_condition {C A B : Type*} [MeasurableSpace C]
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace A] [StandardBorelSpace B]
    [Nonempty A] [Nonempty B]
    (P : Measure (C×(A×B))) [IsProbabilityMeasure P]
    (π : Measure B) [IsProbabilityMeasure π] :
    conditionalReferenceKL (P.map MeasurableEquiv.prodAssoc.symm) π =
      conditionalReferenceKL (P.map (Prod.map id Prod.snd)) π +
      conditionalMutualInformation P := by
  let μ := P.fst
  let κ := P.condKernel
  have hP : μ ⊗ₘ κ = P := P.disintegrate P.condKernel
  have hfst : (P.map MeasurableEquiv.prodAssoc.symm).fst = μ ⊗ₘ κ.fst := by
    rw [←hP]
    exact fst_map_assoc_compProd μ κ
  have hsnd : P.map (Prod.map id Prod.snd) = μ ⊗ₘ κ.snd := by
    rw [Kernel.snd_eq,Measure.compProd_map measurable_snd,hP]
  have href : (μ ⊗ₘ (κ.fst ×ₖ Kernel.const C π)).map MeasurableEquiv.prodAssoc.symm =
      (μ ⊗ₘ κ.fst).prod π := by
    rw [compProd_prod_assoc]
    have he : (Kernel.const C π).comap Prod.fst measurable_fst = Kernel.const (C×A) π := rfl
    rw [he,Measure.compProd_const]
  have h := conditionalKL_chain μ κ π
  rw [hP] at h
  have hc := conditionalMutualInformation_compProd μ κ
  simp only [hP] at hc
  unfold conditionalReferenceKL
  rw [hfst,←href,klDiv_map_equiv,h,←hc,hsnd,Measure.fst_compProd]

lemma conditionalMutualInformation_symm {C A B : Type*} [MeasurableSpace C]
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace A] [StandardBorelSpace B]
    [Nonempty A] [Nonempty B]
    (P : Measure (C×(A×B))) [IsProbabilityMeasure P] :
    conditionalMutualInformation (P.map (Prod.map id Prod.swap)) =
      conditionalMutualInformation P := by
  let μ := P.fst
  let κ := P.condKernel
  have hP : μ ⊗ₘ κ = P := P.disintegrate P.condKernel
  have hmap : P.map (Prod.map id Prod.swap) = μ ⊗ₘ κ.map Prod.swap := by
    rw [Measure.compProd_map measurable_swap,hP]
  have hfst : (κ.map Prod.swap).fst = κ.snd := by
    rw [Kernel.fst_eq,Kernel.snd_eq,←Kernel.map_comp_right _ measurable_swap measurable_fst]
    rfl
  have hsnd : (κ.map Prod.swap).snd = κ.fst := by
    rw [Kernel.fst_eq,Kernel.snd_eq,←Kernel.map_comp_right _ measurable_swap measurable_snd]
    rfl
  have href : μ ⊗ₘ (κ.snd ×ₖ κ.fst) =
      (μ ⊗ₘ (κ.fst ×ₖ κ.snd)).map (Prod.map id Prod.swap) := by
    rw [←Measure.compProd_map measurable_swap,Kernel.map_prod_swap]
  have : IsMarkovKernel (κ.map Prod.swap) := Kernel.IsMarkovKernel.map κ measurable_swap
  have hc := conditionalMutualInformation_compProd μ (κ.map Prod.swap)
  simp only [hfst,hsnd,href,Measure.compProd_map measurable_swap] at hc
  have he := klDiv_map_equiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ κ.snd))
    ((MeasurableEquiv.refl C).prodCongr MeasurableEquiv.prodComm)
  change klDiv ((μ ⊗ₘ κ).map (Prod.map id Prod.swap))
    ((μ ⊗ₘ (κ.fst ×ₖ κ.snd)).map (Prod.map id Prod.swap)) = _ at he
  rw [he,←conditionalMutualInformation_compProd μ κ] at hc
  simpa only [hP] using hc

lemma conditionalReferenceKL_finite_condition {C A B : Type*} [MeasurableSpace C]
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    [Countable A] [MeasurableSingletonClass A] [Nonempty A]
    (P : Measure (C×(A×B))) [IsProbabilityMeasure P]
    (π : Measure B) [IsProbabilityMeasure π]
    (hbase : conditionalReferenceKL (P.map (Prod.map id Prod.snd)) π ≠ ∞)
    (hH : shannonEntropy (P.map (fun z => z.2.1)) ≠ ∞) :
    conditionalReferenceKL (P.map MeasurableEquiv.prodAssoc.symm) π ≠ ∞ ∧
    (conditionalReferenceKL (P.map MeasurableEquiv.prodAssoc.symm) π).toReal ≤
      (conditionalReferenceKL (P.map (Prod.map id Prod.snd)) π).toReal +
      (shannonEntropy (P.map (fun z => z.2.1))).toReal := by
  let Q := P.map (Prod.map id Prod.swap)
  let : IsProbabilityMeasure Q := inferInstance
  have hQ : (Q.map MeasurableEquiv.prodAssoc.symm).snd = P.map (fun z => z.2.1) := by
    simp only [Q,Measure.snd,Measure.map_map measurable_snd MeasurableEquiv.prodAssoc.symm.measurable,
      Measure.map_map (measurable_snd.comp MeasurableEquiv.prodAssoc.symm.measurable)
        (measurable_id.prodMap measurable_swap)]
    rfl
  obtain ⟨hc,hcb⟩ := conditionalMutualInformation_le_entropy Q (by rwa [hQ])
  rw [hQ,conditionalMutualInformation_symm P] at hcb
  rw [conditionalMutualInformation_symm P] at hc
  rw [conditionalReferenceKL_add_condition P π]
  exact ⟨ENNReal.add_ne_top.mpr ⟨hbase,hc⟩,by rw [ENNReal.toReal_add hbase hc]; linarith⟩



def gaussianLabels (k : ℕ) : Measure (Fin k → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)

instance gaussianLabels_probability (k : ℕ) : IsProbabilityMeasure (gaussianLabels k) := by
  unfold gaussianLabels
  infer_instance

lemma gaussianLabels_density (k : ℕ) :
    (volume : Measure (Fin k → ℝ)).withDensity
      (fun y => ENNReal.ofReal (gaussianProductPDF 1 0 y)) = gaussianLabels k := by
  symm
  apply Measure.pi_eq
  intro t ht
  rw [withDensity_apply _ (MeasurableSet.univ_pi ht)]
  simp only [gaussianProductPDF,radiusVariance,one_pow,Pi.zero_apply]
  change (∫⁻ y in Set.univ.pi t, ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (y i))) = _
  rw [←ofReal_integral_eq_lintegral_ofReal]
  · change ENNReal.ofReal (∫ y, ∏ i, gaussianPDFReal 0 1 (y i)
        ∂(Measure.pi (fun _ : Fin k => (volume : Measure ℝ))).restrict (Set.univ.pi t)) = _
    rw [Measure.restrict_pi_pi,integral_fintype_prod_eq_prod,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun _ => (gaussianPDFReal_pos 0 1 _ (by norm_num)).le))]
    congr 1
    funext i
    rw [gaussianReal_apply 0 (by norm_num : (1:ℝ≥0) ≠ 0)]
    exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).integrableOn
      (ae_of_all _ (fun x => (gaussianPDFReal_pos 0 1 x (by norm_num)).le))
  · exact (Integrable.fintype_prod (fun _ : Fin k => integrable_gaussianPDFReal 0 1)).integrableOn
  · exact ae_of_all _ (fun y => Finset.prod_nonneg (fun i _ => (gaussianPDFReal_pos 0 1 (y i) (by norm_num)).le))

lemma log_gaussianLabelsPDF {k : ℕ} (y : Fin k → ℝ) :
    Real.log (gaussianProductPDF 1 0 y) = -(k:ℝ)*Real.log (normalizer 1) -
      (∑ i, (y i)^2)/2 := by
  simpa using log_gaussianProductPDF (k:=k) (show (0:ℝ)<1 by norm_num) (0:Fin k→ℝ) y

lemma projectionSquare_sphere_joint_integrable {d k : ℕ}
    (ρ : Measure (Sphere d)) [IsProbabilityMeasure ρ] :
    Integrable (fun z : Rows k d × Sphere d => projectionSquare z.1 (z.2:Vector d))
      ((gaussianRows k d).prod ρ) := by
  have hm : Measurable (fun z : Rows k d × Sphere d => projectionSquare z.1 (z.2:Vector d)) := by
    unfold projectionSquare label
    fun_prop
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun s => projectionSquare_integrable (s:Vector d)),?_⟩
  have he : (fun s : Sphere d => ∫ G, ‖projectionSquare G (s:Vector d)‖ ∂gaussianRows k d) =
      fun _ => (k:ℝ) := by
    funext s
    simp_rw [Real.norm_eq_abs,abs_of_nonneg (projectionSquare_nonneg _ _)]
    rw [projectionSquare_integral,norm_eq_of_mem_sphere s]
    simp
  rw [he]
  exact integrable_const _

lemma projectionSquare_sphere_joint_integral {d k : ℕ}
    (ρ : Measure (Sphere d)) [IsProbabilityMeasure ρ] :
    (∫ z : Rows k d × Sphere d, projectionSquare z.1 (z.2:Vector d)
      ∂(gaussianRows k d).prod ρ) = k := by
  rw [integral_prod_symm _ (projectionSquare_sphere_joint_integrable ρ)]
  simp only [projectionSquare_integral,norm_eq_of_mem_sphere,
    one_pow,mul_one,integral_const,probReal_univ,one_smul]

lemma gaussian_log_reference_projection {d k : ℕ}
    (ρ : Measure (Sphere d)) [IsProbabilityMeasure ρ] :
    Integrable (fun z : Rows k d×(Fin k→ℝ) =>
      Real.log (gaussianProductPDF 1 0 z.2)) (projectionJoint ρ (gaussianRows k d)) ∧
    (∫ z : Rows k d×(Fin k→ℝ), Real.log (gaussianProductPDF 1 0 z.2)
      ∂projectionJoint ρ (gaussianRows k d)) =
      -(k:ℝ)*(Real.log (normalizer 1)+1/2) := by
  have hf : Measurable (fun z : Rows k d×(Fin k→ℝ) => Real.log (gaussianProductPDF 1 0 z.2)) := by
    unfold gaussianProductPDF
    fun_prop
  have hm : Measurable (fun z : Rows k d×Sphere d => (z.1,label z.1 (z.2:Vector d))) :=
    measurable_fst.prodMk measurable_own_label
  have hi : Integrable (fun z : Rows k d×Sphere d =>
      Real.log (gaussianProductPDF 1 0 (label z.1 (z.2:Vector d))))
      ((gaussianRows k d).prod ρ) := by
    simp_rw [log_gaussianLabelsPDF]
    exact (integrable_const _).sub ((projectionSquare_sphere_joint_integrable ρ).div_const 2)
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mpr hi,?_⟩
  rw [projectionJoint,integral_map hm.aemeasurable hf.aestronglyMeasurable]
  simp_rw [log_gaussianLabelsPDF]
  change (∫ z : Rows k d×Sphere d, -(k:ℝ)*Real.log (normalizer 1) - projectionSquare z.1 (z.2:Vector d)/2 ∂(gaussianRows k d).prod ρ) = _
  rw [integral_sub (integrable_const _) ((projectionSquare_sphere_joint_integrable ρ).div_const 2),
    integral_const,integral_div,projectionSquare_sphere_joint_integral]
  simp only [probReal_univ,one_smul]
  ring

lemma sphere_projection_reference_finite {d m r : ℕ}
    (hdim : AdmissibleDimensions d m r 1) (hd : 2 ≤ d) :
    klDiv (projectionJoint (uniformSphere d) (gaussianRows (m+r) d))
      ((gaussianRows (m+r) d).prod (gaussianLabels (m+r))) ≠ ∞ ∧
    (klDiv (projectionJoint (uniformSphere d) (gaussianRows (m+r) d))
      ((gaussianRows (m+r) d).prod (gaussianLabels (m+r)))).toReal ≤
      20*d + (m+r:ℕ)*(Real.log (normalizer 1)+1/2) := by
  let : IsProbabilityMeasure (uniformSphere d) := uniformSphere_probability_of_pos (by omega)
  let P := projectionJoint (uniformSphere d) (gaussianRows (m+r) d)
  let Q := (gaussianRows (m+r) d).prod (gaussianLabels (m+r))
  let Λ := (gaussianRows (m+r) d).prod (volume : Measure (Fin (m+r)→ℝ))
  let p : Rows (m+r) d×(Fin (m+r)→ℝ) → ℝ≥0∞ := fun z => exactDensity (uniformSphere d) z.1 z.2
  let g : Rows (m+r) d×(Fin (m+r)→ℝ) → ℝ := fun z => gaussianProductPDF 1 0 z.2
  have hp : Measurable p := measurable_exactDensity _
  have hg : Measurable g := by unfold g gaussianProductPDF; fun_prop
  have hQ : Λ.withDensity (fun z => ENNReal.ofReal (g z)) = Q := by
    have hs : Measurable (fun y : Fin (m+r)→ℝ => ENNReal.ofReal (gaussianProductPDF 1 0 y)) := by unfold gaussianProductPDF; fun_prop
    dsimp [Λ,g,Q]
    rw [←prod_withDensity_right hs,gaussianLabels_density]
  have hB : (0:ℝ) < 3*4^d := by positivity
  have hAC := ae_labelLaw_ac_of_growth hdim (uniformSphere d) _ _ hB hB
    (uniformSphere_growth (show 1 ≤ d by omega) (show m+r ≤ d-1 by have := hdim.2.2.2.1; omega))
    (uniformSphere_growth (show 1 ≤ d by omega) (le_refl (d-1)))
  obtain ⟨hPQ,he⟩ := llr_of_two_densities P Q Λ p hp
    (projectionJoint_withDensity _ _ hAC) g hg (fun z => gaussianProductPDF_pos (by norm_num) _ _) hQ
  obtain ⟨hpi,hpb⟩ := sphere_label_entropy_finite hdim hd
  have hpm : Measurable (fun z : Rows (m+r) d×Sphere d => (z.1,label z.1 (z.2:Vector d))) :=
    measurable_fst.prodMk measurable_own_label
  have hpi' : Integrable (fun z => Real.log (p z).toReal) P :=
    (integrable_map_measure hp.ennreal_toReal.log.aestronglyMeasurable hpm.aemeasurable).mpr hpi
  obtain ⟨hgi,hge⟩ := gaussian_log_reference_projection (k:=m+r) (uniformSphere d)
  have hll : Integrable (llr P Q) P := (hpi'.sub hgi).congr he.symm
  refine ⟨klDiv_ne_top hPQ hll,?_⟩
  rw [toReal_klDiv_of_measure_eq hPQ (by simp),integral_congr_ae he,integral_sub hpi' hgi,hge]
  have hpint : (∫ z, Real.log (p z).toReal ∂P) =
      ∫ z : Rows (m+r) d×Sphere d, Real.log (exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d))).toReal
      ∂(gaussianRows (m+r) d).prod (uniformSphere d) :=
    integral_map hpm.aemeasurable hp.ennreal_toReal.log.aestronglyMeasurable
  rw [hpint]
  linarith




lemma weighted_log_integral {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (w g : T → ℝ)
    (hw : ∀ t, 0 < w t) (hg : ∀ t, 0 < g t)
    (hwi : Integrable w μ) (hgi : Integrable g μ)
    (hli : Integrable (fun t => w t * (Real.log (g t) - Real.log (w t))) μ)
    (hA : 0 < ∫ t, w t ∂μ) (hM : 0 < ∫ t, g t ∂μ) :
    (∫ t, w t * (Real.log (g t) - Real.log (w t)) ∂μ) ≤
      (∫ t, w t ∂μ) * (Real.log (∫ t, g t ∂μ) - Real.log (∫ t, w t ∂μ)) := by
  let A := ∫ t, w t ∂μ
  let M := ∫ t, g t ∂μ
  change 0 < A at hA
  change 0 < M at hM
  have hp (t : T) : w t * (Real.log (g t) - Real.log (w t)) ≤
      w t * (Real.log M - Real.log A) + (A/M)*g t - w t := by
    have hh := Real.log_le_sub_one_of_pos (div_pos (div_pos (hg t) (hw t)) (div_pos hM hA))
    rw [Real.log_div (div_ne_zero (hg t).ne' (hw t).ne') (div_ne_zero hM.ne' hA.ne'),
      Real.log_div (hg t).ne' (hw t).ne',Real.log_div hM.ne' hA.ne'] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (hw t).le
    have he : w t * ((g t / w t) / (M / A) - 1) = (A/M)*g t - w t := by
      field_simp [hA.ne',hM.ne',(hw t).ne']
    rw [he] at hh'
    nlinarith
  have hi : Integrable (fun t => w t*(Real.log M-Real.log A)+(A/M)*g t-w t) μ :=
    ((hwi.mul_const _).add (hgi.const_mul (A/M))).sub hwi
  have hb := integral_mono hli hi hp
  have hv : (∫ t, w t * (Real.log M-Real.log A) + (A/M)*g t - w t ∂μ) =
      A * (Real.log M-Real.log A) + (A/M)*M - A := by
    calc
      _ = (∫ t, w t * (Real.log M-Real.log A) + (A/M)*g t ∂μ) - A :=
        integral_sub ((hwi.mul_const _).add (hgi.const_mul _)) hwi
      _ = A * (Real.log M-Real.log A) + (A/M)*M - A := by
        rw [integral_add (hwi.mul_const (Real.log M-Real.log A)) (hgi.const_mul (A/M))]
        simp only [integral_mul_const, integral_const_mul, A, M]
  rw [hv,div_mul_cancel₀ _ hM.ne'] at hb
  linarith

def regularizedReciprocal {d : ℕ} (e : ℝ) (s t : Sphere d) : ℝ :=
  (max (dist s t) e)⁻¹

def regularizedScale {d : ℕ} (μ : Measure (Sphere d)) (e : ℝ) (s : Sphere d) : ℝ :=
  ∫ t, regularizedReciprocal e s t ∂μ

lemma sphere_subtype_dist_le_two {d : ℕ} (s t : Sphere d) : dist s t ≤ 2 := by
  simpa only [Subtype.dist_eq,dist_eq_norm,norm_eq_of_mem_sphere s,
    norm_eq_of_mem_sphere t,one_add_one_eq_two] using norm_sub_le (s:Vector d) (t:Vector d)

lemma regularizedReciprocal_pos {d : ℕ} {e : ℝ} (he : 0 < e) (s t : Sphere d) :
    0 < regularizedReciprocal e s t := inv_pos.mpr (he.trans_le (le_max_right _ _))

lemma regularizedReciprocal_bounds {d : ℕ} {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (s t : Sphere d) : 1/2 ≤ regularizedReciprocal e s t ∧ regularizedReciprocal e s t ≤ e⁻¹ := by
  have hmax : 0 < max (dist s t) e := he.trans_le (le_max_right _ _)
  constructor
  · simp only [one_div,regularizedReciprocal]
    change (2:ℝ)⁻¹ ≤ (max (dist s t) e)⁻¹
    exact (inv_le_inv₀ (by norm_num) hmax).mpr (max_le (sphere_subtype_dist_le_two s t) (by linarith))
  · exact (inv_le_inv₀ hmax he).mpr (le_max_right _ _)

lemma integrable_regularizedReciprocal {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (s : Sphere d) : Integrable (regularizedReciprocal e s) μ := by
  apply (integrable_const (e⁻¹)).mono' (by unfold regularizedReciprocal; fun_prop)
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs,abs_of_pos (regularizedReciprocal_pos he s t)]
  exact (inv_le_inv₀ (he.trans_le (le_max_right _ _)) he).mpr (le_max_right _ _)

lemma regularizedScale_bounds {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (s : Sphere d) :
    1/2 ≤ regularizedScale μ e s ∧ regularizedScale μ e s ≤ e⁻¹ := by
  have hi := integrable_regularizedReciprocal μ he s
  constructor
  · simpa [regularizedScale] using integral_mono (integrable_const (1/2:ℝ)) hi
      (fun t => (regularizedReciprocal_bounds he he1 s t).1)
  · simpa [regularizedScale] using integral_mono hi (integrable_const (e⁻¹))
      (fun t => (regularizedReciprocal_bounds he he1 s t).2)

lemma log_regularizedReciprocal {d : ℕ} (e : ℝ) (s t : Sphere d) :
    Real.log (regularizedReciprocal e s t) = -Real.log (max (dist s t) e) := Real.log_inv _



end CurrentProjection

end

end OAI
