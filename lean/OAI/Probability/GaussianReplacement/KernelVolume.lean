import OAI.Probability.GaussianReplacement.KernelGeometry

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

section KernelVolume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E] [nontrivialE : Nontrivial E]

abbrev KernelHistory (r n : ℕ) (E : Type*) := Fin n → ((Fin r → E) × E)

def kernelInverseVolume {r n : ℕ} (h : KernelHistory r n E) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (‖gramSchmidt ℝ (fun j => (h j).2) i‖⁻¹)

omit nontrivialE in
lemma measurable_kernelInverseVolume (r n : ℕ) :
    Measurable (kernelInverseVolume (E:=E) (r:=r) (n:=n)) := by
  apply Finset.measurable_prod
  intro i _
  exact (((measurable_gramSchmidt (E:=E) i).comp
    (Measurable.of_eval fun j => (measurable_pi_apply j).snd)).norm.inv).ennreal_ofReal

lemma measurable_snoc_history {A : Type*} [MeasurableSpace A] (n : ℕ) :
    Measurable (fun z : (Fin n → A) × A => Fin.snoc (α:=fun _ => A) z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  induction i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using measurable_snd
  | cast j => simpa only [Fin.snoc_castSucc, Function.comp_def] using (measurable_pi_apply j).comp measurable_fst

omit measurableSpaceE borelSpaceE nontrivialE in
lemma kernelInverseVolume_snoc {r n : ℕ} (h : KernelHistory r n E)
    (z : (Fin r → E) × E) :
    kernelInverseVolume (Fin.snoc h z) = kernelInverseVolume h *
      ENNReal.ofReal ((Metric.infDist z.2 (rowSpan (fun j => (h j).2) : Set E))⁻¹) := by
  unfold kernelInverseVolume
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    congr 3
    rw [gramSchmidt_castSucc]
    simp only [Fin.snoc_castSucc]
  · congr 2
    rw [norm_gramSchmidt_eq_infDist, image_Iio_last]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, rowSpan]

omit nontrivialE in
lemma measurableSet_kernel_nondegenerate (r n : ℕ) :
    MeasurableSet {h : KernelHistory r n E |
      ∀ i, gramSchmidt ℝ (fun j => (h j).2) i ≠ 0} := by
  simp_rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_eq_fun ((measurable_gramSchmidt (E:=E) i).comp
    (Measurable.of_eval fun j => (measurable_pi_apply j).snd)) measurable_const).compl

omit measurableSpaceE borelSpaceE nontrivialE in
lemma kernel_nondegenerate_snoc {r n : ℕ} (h : KernelHistory r n E)
    (z : (Fin r → E) × E)
    (hh : ∀ i, gramSchmidt ℝ (fun j => (h j).2) i ≠ 0)
    (hz : 0 < Metric.infDist z.2 (rowSpan (fun j => (h j).2) : Set E)) :
    ∀ i, gramSchmidt ℝ (fun j => (Fin.snoc (α:=fun _ => (Fin r → E) × E) h z j).2) i ≠ 0 := by
  intro i
  induction i using Fin.lastCases with
  | last =>
    apply norm_ne_zero_iff.mp
    rw [norm_gramSchmidt_eq_infDist, image_Iio_last]
    simpa only [Fin.snoc_castSucc, Fin.snoc_last, rowSpan] using hz.ne'
  | cast j =>
    simpa only [gramSchmidt_castSucc, Fin.snoc_castSucc] using hh j




def kernelHistoryLaw {r : ℕ}
    (ν : (n : ℕ) → Kernel (KernelHistory r n E) ((Fin r → E) × E)) :
    (n : ℕ) → Measure (KernelHistory r n E)
  | 0 => Measure.dirac (fun i => Fin.elim0 i)
  | n+1 => ((kernelHistoryLaw ν n) ⊗ₘ ν n).map (fun z => Fin.snoc z.1 z.2)

instance kernelHistoryLaw_probability {r : ℕ}
    (ν : (n : ℕ) → Kernel (KernelHistory r n E) ((Fin r → E) × E))
    [∀ n, IsMarkovKernel (ν n)] (n : ℕ) : IsProbabilityMeasure (kernelHistoryLaw ν n) := by
  induction n with
  | zero => dsimp [kernelHistoryLaw]; infer_instance
  | succ n ih =>
    let := ih
    rw [kernelHistoryLaw]
    exact (Measure.isProbabilityMeasure_map_iff
      (measurable_snoc_history n).aemeasurable).mpr inferInstance

lemma kernelHistory_step {r n : ℕ} (hr : r ≤ Module.finrank ℝ E)
    (hd : Module.finrank ℝ E ≤ 8*r) (hn : 2*n ≤ r) (hmargin : 2 ≤ r-n)
    (μ : Measure (KernelHistory r n E)) [IsProbabilityMeasure μ]
    (ν : Kernel (KernelHistory r n E) ((Fin r → E) × E)) [IsMarkovKernel ν]
    (hrows : ∀ᵐ h ∂μ, (ν h).fst = Measure.pi (fun _ => stdGaussian E))
    (hsupport : ∀ᵐ h ∂μ, ∀ᵐ z ∂ν h, ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ) :
    (∫⁻ z, kernelInverseVolume (Fin.snoc z.1 z.2) ∂(μ ⊗ₘ ν)) ≤
      ENNReal.ofReal (5*kernelSmallBallConstant) * ∫⁻ h, kernelInverseVolume h ∂μ := by
  rw [Measure.lintegral_compProd (μ:=μ) (κ:=ν)
    (f:=fun z => kernelInverseVolume (Fin.snoc z.1 z.2))
    ((measurable_kernelInverseVolume (E:=E) r (n+1)).comp (measurable_snoc_history n))]
  calc
    _ ≤ ∫⁻ h, kernelInverseVolume h * ENNReal.ofReal (5*kernelSmallBallConstant) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hrows, hsupport] with h hh hs
      have hp : Module.finrank ℝ (rowSpan (fun j => (h j).2)) ≤ n :=
        (finrank_range_le_card (R:=ℝ) (fun j => (h j).2)).trans_eq (Fintype.card_fin n)
      have hi := (kernel_selected_inverse_step hr hd (rowSpan (fun j => (h j).2))
        (by omega) (by omega) (ν h) hh hs).1
      simp_rw [kernelInverseVolume_snoc]
      rw [lintegral_const_mul' _ _ (by
        apply ENNReal.prod_ne_top
        intro i _
        exact ENNReal.ofReal_ne_top)]
      exact mul_le_mul' le_rfl hi
    _ = _ := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]

lemma kernelHistory_step_nondegenerate {r n : ℕ} (hr : r ≤ Module.finrank ℝ E)
    (hd : Module.finrank ℝ E ≤ 8*r) (hn : 2*n ≤ r) (hmargin : 2 ≤ r-n)
    (μ : Measure (KernelHistory r n E)) [IsProbabilityMeasure μ]
    (ν : Kernel (KernelHistory r n E) ((Fin r → E) × E)) [IsMarkovKernel ν]
    (hrows : ∀ᵐ h ∂μ, (ν h).fst = Measure.pi (fun _ => stdGaussian E))
    (hsupport : ∀ᵐ h ∂μ, ∀ᵐ z ∂ν h, ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ)
    (hprev : ∀ᵐ h ∂μ, ∀ i, gramSchmidt ℝ (fun j => (h j).2) i ≠ 0) :
    ∀ᵐ z ∂(μ ⊗ₘ ν), ∀ i, gramSchmidt ℝ (fun j => (Fin.snoc (α:=fun _ => (Fin r → E) × E) z.1 z.2 j).2) i ≠ 0 := by
  apply Measure.ae_compProd_of_ae_ae
    ((measurableSet_kernel_nondegenerate r (n+1)).preimage (measurable_snoc_history n))
  filter_upwards [hrows, hsupport, hprev] with h hh hs hp
  have hdimp : Module.finrank ℝ (rowSpan (fun j => (h j).2)) ≤ n :=
    (finrank_range_le_card (R:=ℝ) (fun j => (h j).2)).trans_eq (Fintype.card_fin n)
  filter_upwards [(kernel_selected_inverse_step hr hd (rowSpan (fun j => (h j).2))
    (by omega) (by omega) (ν h) hh hs).2] with z hz
  exact kernel_nondegenerate_snoc h z hp hz



theorem independent_kernel_inverse_volume {r q : ℕ}
    (hr : r ≤ Module.finrank ℝ E) (hd : Module.finrank ℝ E ≤ 8*r)
    (hq : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (ν : (n : ℕ) → Kernel (KernelHistory r n E) ((Fin r → E) × E))
    [∀ n, IsMarkovKernel (ν n)]
    (hrows : ∀ n < q, ∀ᵐ h ∂kernelHistoryLaw ν n,
      (ν n h).fst = Measure.pi (fun _ => stdGaussian E))
    (hsupport : ∀ n < q, ∀ᵐ h ∂kernelHistoryLaw ν n,
      ∀ᵐ z ∂ν n h, ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ) :
    (∫⁻ h, kernelInverseVolume h ∂kernelHistoryLaw ν q) ≤
      ENNReal.ofReal (5*kernelSmallBallConstant)^q ∧
    ∀ᵐ h ∂kernelHistoryLaw ν q, ∀ i, gramSchmidt ℝ (fun j => (h j).2) i ≠ 0 := by
  have hmain : ∀ n, n ≤ q →
      (∫⁻ h, kernelInverseVolume h ∂kernelHistoryLaw ν n) ≤
        ENNReal.ofReal (5*kernelSmallBallConstant)^n ∧
      ∀ᵐ h ∂kernelHistoryLaw ν n, ∀ i, gramSchmidt ℝ (fun j => (h j).2) i ≠ 0 := by
    intro n
    induction n with
    | zero =>
      intro _
      constructor
      · simp [kernelHistoryLaw, kernelInverseVolume]
      · exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
    | succ n ih =>
      intro hnq
      have hi := ih (by omega)
      constructor
      · rw [kernelHistoryLaw, lintegral_map (measurable_kernelInverseVolume r (n+1))
          (measurable_snoc_history n)]
        apply (kernelHistory_step hr hd (by omega)
          (hmargin.trans (Nat.sub_le_sub_left (by omega) r))
          (kernelHistoryLaw ν n) (ν n) (hrows n (by omega)) (hsupport n (by omega))).trans
        calc
          _ ≤ ENNReal.ofReal (5*kernelSmallBallConstant) *
              ENNReal.ofReal (5*kernelSmallBallConstant)^n := mul_le_mul' le_rfl hi.1
          _ = _ := by rw [pow_succ']
      · rw [kernelHistoryLaw, ae_map_iff (measurable_snoc_history n).aemeasurable
          (measurableSet_kernel_nondegenerate r (n+1))]
        exact kernelHistory_step_nondegenerate hr hd (by omega) (by omega)
          (kernelHistoryLaw ν n) (ν n) (hrows n (by omega)) (hsupport n (by omega)) hi.2
  exact hmain q le_rfl

end KernelVolume



section KernelPiVolume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E] [nontrivialE : Nontrivial E]

lemma independent_kernel_inverse_volume_pi {r q : ℕ}
    (hr : r ≤ Module.finrank ℝ E) (hd : Module.finrank ℝ E ≤ 8*r)
    (hq : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (Q : Measure ((Fin r → E) × E)) [IsProbabilityMeasure Q]
    (hrows : Q.fst = Measure.pi (fun _ => stdGaussian E))
    (hsupport : ∀ᵐ z ∂Q, ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ) :
    (∫⁻ h : KernelHistory r q E, kernelInverseVolume h ∂Measure.pi (fun _ => Q)) ≤
      ENNReal.ofReal (5*kernelSmallBallConstant)^q ∧
    ∀ᵐ h : KernelHistory r q E ∂Measure.pi (fun _ => Q),
      ∀ i, gramSchmidt ℝ (fun j => (h j).2) i ≠ 0 := by
  induction q with
  | zero =>
    constructor
    · simp [kernelInverseVolume]
    · exact Filter.Eventually.of_forall fun _ i => Fin.elim0 i
  | succ q ih =>
    have hi := ih (by omega) (by omega)
    have hp (h : KernelHistory r q E) : Module.finrank ℝ (rowSpan (fun j => (h j).2)) ≤ q :=
      (finrank_range_le_card (R:=ℝ) (fun j => (h j).2)).trans_eq (Fintype.card_fin q)
    have hstep (h : KernelHistory r q E) :=
      kernel_selected_inverse_step hr hd (rowSpan (fun j => (h j).2))
        (by have := hp h; omega) (by have := hp h; omega) Q hrows hsupport
    constructor
    · rw [lintegral_pi_snoc Q _ (measurable_kernelInverseVolume r (q+1))]
      calc
        _ ≤ ∫⁻ h : KernelHistory r q E, kernelInverseVolume h *
            ENNReal.ofReal (5*kernelSmallBallConstant) ∂Measure.pi (fun _ => Q) := by
          apply lintegral_mono
          intro h
          simp_rw [kernelInverseVolume_snoc]
          rw [lintegral_const_mul' _ _ (by
            apply ENNReal.prod_ne_top
            intro i _
            exact ENNReal.ofReal_ne_top)]
          exact mul_le_mul' le_rfl (hstep h).1
        _ = (∫⁻ h : KernelHistory r q E, kernelInverseVolume h ∂Measure.pi (fun _ => Q)) *
            ENNReal.ofReal (5*kernelSmallBallConstant) :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (5*kernelSmallBallConstant)^q *
            ENNReal.ofReal (5*kernelSmallBallConstant) := mul_le_mul' hi.1 le_rfl
        _ = _ := (pow_succ _ _).symm
    · rw [ae_pi_snoc Q (measurableSet_kernel_nondegenerate r (q+1))]
      filter_upwards [hi.2] with h hh
      filter_upwards [(hstep h).2] with z hz
      exact kernel_nondegenerate_snoc h z hh hz

omit finiteDimensionalRealE measurableSpaceE borelSpaceE nontrivialE in
lemma span_image_diagonal_smul {ι : Type*} (v : ι → E) (c : ι → ℝ)
    (hc : ∀ i, c i ≠ 0) (I : Set ι) :
    Submodule.span ℝ ((fun i => c i • v i) '' I) = Submodule.span ℝ (v '' I) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have h := Submodule.smul_mem (Submodule.span ℝ ((fun i => c i • v i) '' I))
      (c i)⁻¹ (Submodule.subset_span ⟨i, hi, rfl⟩)
    rw [inv_smul_smul₀ (hc i)] at h
    exact h

omit measurableSpaceE borelSpaceE nontrivialE in
lemma gramSchmidt_diagonal_smul {n : ℕ} (v : Fin n → E) (c : Fin n → ℝ)
    (hc : ∀ i, c i ≠ 0) (j : Fin n) :
    gramSchmidt ℝ (fun i => c i • v i) j = c j • gramSchmidt ℝ v j := by
  rw [gramSchmidt_eq_sub_starProjection, gramSchmidt_eq_sub_starProjection,
    span_image_diagonal_smul v c hc, map_smul, smul_sub]

omit measurableSpaceE borelSpaceE nontrivialE in
lemma kernelInverseVolume_normalization {r n : ℕ}
    (h : KernelHistory r n E) (hn : ∀ i, (h i).2 ≠ 0) :
    kernelInverseVolume h =
      (∏ i, ENNReal.ofReal (‖(h i).2‖⁻¹)) *
        kernelInverseVolume (fun i => ((h i).1, ‖(h i).2‖⁻¹ • (h i).2)) := by
  unfold kernelInverseVolume
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [gramSchmidt_diagonal_smul _ _ (fun j => inv_ne_zero (norm_ne_zero_iff.mpr (hn j))),
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_inv,
    inv_inv, ←mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hn i)), one_mul]

end KernelPiVolume



section KernelNormalizedMoment
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E] [nontrivialE : Nontrivial E]

def normalizeKernelVector {r : ℕ} (z : (Fin r → E) × E) : (Fin r → E) × E :=
  (z.1, ‖z.2‖⁻¹ • z.2)

omit nontrivialE in
lemma measurable_normalizeKernelVector (r : ℕ) :
    Measurable (normalizeKernelVector (E:=E) (r:=r)) := by
  unfold normalizeKernelVector
  fun_prop

omit finiteDimensionalRealE measurableSpaceE borelSpaceE nontrivialE in
lemma normalizeKernelVector_support {r : ℕ} (z : (Fin r → E) × E)
    (hz : z.2 ≠ 0 ∧ z.2 ∈ (rowSpan z.1)ᗮ) :
    ‖(normalizeKernelVector z).2‖ = 1 ∧
      (normalizeKernelVector z).2 ∈ (rowSpan (normalizeKernelVector z).1)ᗮ := by
  constructor
  · simp [normalizeKernelVector, norm_smul,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz.1)]
  · exact Submodule.smul_mem _ _ hz.2

omit nontrivialE in
lemma gaussian_single_kernel_bound {q : ℕ} (v : Fin q → E)
    (hv : LinearIndependent ℝ v) (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ t, φ t = 1) :
    ∫⁻ x, ∏ i, φ ⟪v i,x⟫ ∂stdGaussian E ≤
      ∏ i, ENNReal.ofReal (‖gramSchmidt ℝ v i‖⁻¹) := by
  rw [← lintegral_map (show Measurable (fun z : Fin q → ℝ => ∏ i, φ (z i)) by fun_prop)
    (show Measurable (fun x : E => fun i => ⟪v i,x⟫) by fun_prop)]
  calc
    _ ≤ ∫⁻ z : Fin q → ℝ, ∏ i, φ (z i)
        ∂(ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹) • volume) :=
      lintegral_mono' (gaussian_pairings_le v hv) (fun _ => le_rfl)
    _ = _ := by
      rw [lintegral_smul_measure, volume_pi, lintegral_fin_prod volume q
        (fun _ => φ) (fun _ => hφ)]
      simp only [hφ1, Finset.prod_const_one, smul_eq_mul, mul_one]
      rw [←Finset.prod_inv_distrib]
      exact ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)




lemma kernel_normalized_projection_moment {r q : ℕ}
    (hr : r ≤ Module.finrank ℝ E) (hd : Module.finrank ℝ E ≤ 8*r)
    (hq : 2*q ≤ r) (hmargin : 2 ≤ r-q)
    (Q : Measure ((Fin r → E) × E)) [IsProbabilityMeasure Q]
    (hrows : Q.fst = Measure.pi (fun _ => stdGaussian E))
    (hsupport : ∀ᵐ z ∂Q, z.2 ≠ 0 ∧ z.2 ∈ (rowSpan z.1)ᗮ)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ t, φ t = 1) :
    ∫⁻ x, (∫⁻ z, ENNReal.ofReal ‖z.2‖ * φ ⟪z.2,x⟫ ∂Q)^q
      ∂stdGaussian E ≤ ENNReal.ofReal (5*kernelSmallBallConstant)^q := by
  let T := normalizeKernelVector (E:=E) (r:=r)
  have hT : Measurable T := measurable_normalizeKernelVector r
  let Q' := Q.map T
  have : IsProbabilityMeasure Q' := inferInstance
  have hrows' : Q'.fst = Measure.pi (fun _ => stdGaussian E) := by
    change (Q.map T).map Prod.fst = _
    rw [Measure.map_map measurable_fst hT]
    exact hrows
  have hs' : ∀ᵐ z ∂Q', ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ := by
    change ∀ᵐ z ∂Q.map T, ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ
    have hm : MeasurableSet {z : (Fin r → E) × E | z.2 ∈ (rowSpan z.1)ᗮ} := by
      have he : {z : (Fin r → E) × E | z.2 ∈ (rowSpan z.1)ᗮ} =
          {z | rowProjectionL z.1 z.2 = 0} := by
        ext z
        simp only [Set.mem_ofPred_eq, rowProjectionL_eq, Submodule.starProjection_apply_eq_zero_iff]
      rw [he]
      exact measurableSet_eq_fun (measurable_rowProjection_pair r) measurable_const
    apply (ae_map_iff hT.aemeasurable (show MeasurableSet
      {z : (Fin r → E) × E | ‖z.2‖=1 ∧ z.2 ∈ (rowSpan z.1)ᗮ} from
      (measurableSet_eq_fun measurable_snd.norm (measurable_const (a:= (1:ℝ)))).inter hm)).mpr
    exact hsupport.mono fun z hz => normalizeKernelVector_support z hz
  have hvol := independent_kernel_inverse_volume_pi hr hd hq hmargin Q' hrows' hs'
  have hmap : (Measure.pi (fun _ : Fin q => Q)).map (fun h i => T (h i)) =
      Measure.pi (fun _ : Fin q => Q') := Measure.pi_map_pi (fun _ => hT.aemeasurable)
  have hprodT : Measurable (fun h : KernelHistory r q E => fun i => T (h i)) := by fun_prop
  have hnondeg : ∀ᵐ h : KernelHistory r q E ∂Measure.pi (fun _ => Q),
      ∀ i, gramSchmidt ℝ (fun j => (T (h j)).2) i ≠ 0 := by
    have ht := hvol.2
    rw [← hmap, ae_map_iff hprodT.aemeasurable (measurableSet_kernel_nondegenerate r q)] at ht
    exact ht
  have hnonzero : ∀ᵐ h : KernelHistory r q E ∂Measure.pi (fun _ => Q),
      ∀ i, (h i).2 ≠ 0 := by
    refine ae_all_iff.mpr fun i => ?_
    exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin q => Q) i).ae
      (hsupport.mono fun _ hz => hz.1)
  have hf : Measurable (fun z : ((Fin r → E) × E) × E =>
      ENNReal.ofReal ‖z.1.2‖ * φ ⟪z.1.2,z.2⟫) := by fun_prop
  have hpow (x : E) := lintegral_pow_pi Q
    (fun z => ENNReal.ofReal ‖z.2‖ * φ ⟪z.2,x⟫)
    (hf.comp (measurable_id.prodMk measurable_const)) q
  calc
    _ = ∫⁻ h : KernelHistory r q E, ∫⁻ x, ∏ i,
        (ENNReal.ofReal ‖(h i).2‖ * φ ⟪(h i).2,x⟫)
        ∂stdGaussian E ∂Measure.pi (fun _ => Q) := by
      simp_rw [hpow]
      rw [lintegral_lintegral_swap (by fun_prop)]
    _ ≤ ∫⁻ h : KernelHistory r q E, kernelInverseVolume (fun i => T (h i))
        ∂Measure.pi (fun _ => Q) := by
      apply lintegral_mono_ae
      filter_upwards [hnondeg, hnonzero] with h hn hz
      have hgs (i : Fin q) : gramSchmidt ℝ (fun j => (h j).2) i ≠ 0 := by
        have hi := hn i
        change gramSchmidt ℝ (fun j => ‖(h j).2‖⁻¹ • (h j).2) i ≠ 0 at hi
        rw [gramSchmidt_diagonal_smul _ _ (fun j => inv_ne_zero (norm_ne_zero_iff.mpr (hz j)))] at hi
        exact fun hh => hi (by rw [hh, smul_zero])
      have hli : LinearIndependent ℝ (fun i => (h i).2) := by
        apply Matrix.linearIndependent_of_det_gram_ne_zero
        rw [det_gram_eq_prod_gramSchmidt]
        exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (hgs i))
      simp_rw [Finset.prod_mul_distrib]
      rw [lintegral_const_mul _ (by fun_prop)]
      calc
        _ ≤ (∏ i, ENNReal.ofReal ‖(h i).2‖) * kernelInverseVolume h :=
          mul_le_mul' le_rfl (gaussian_single_kernel_bound _ hli φ hφ hφ1)
        _ = kernelInverseVolume (fun i => T (h i)) := by
          rw [kernelInverseVolume_normalization h hz, ←mul_assoc, ←Finset.prod_mul_distrib]
          have hc (i : Fin q) : ENNReal.ofReal ‖(h i).2‖ * ENNReal.ofReal ‖(h i).2‖⁻¹ = 1 := by
            rw [←ENNReal.ofReal_mul (norm_nonneg _), mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hz i))]
            exact ENNReal.ofReal_one
          simp only [hc, Finset.prod_const_one, one_mul]
          rfl
    _ = ∫⁻ h : KernelHistory r q E, kernelInverseVolume h ∂Measure.pi (fun _ => Q') := by
      rw [←hmap, lintegral_map (measurable_kernelInverseVolume r q) hprodT]
    _ ≤ _ := hvol.1

end KernelNormalizedMoment



end CurrentProjection

end

end OAI
