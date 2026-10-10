import OAI.InformationTheory.SecretKey.Sampling

namespace OAI

noncomputable section

namespace ZeroKey

section

open MeasureTheory ProbabilityTheory Set Function unitInterval

universe v4286_0 v4286_1

theorem exists_local_instrument_sampler {O : Type v4286_0} {M : Type v4286_1} [MeasurableSpace O]
    [StandardBorelSpace O] [Nonempty O] [MeasurableSpace M]
    (alice : ℕ → Bool)
    (κA κB : (n : ℕ) → Kernel ((Fin n → (O ⊕ Unit)) × (Fin n → M)) O)
    [∀ n, IsMarkovKernel (κA n)] [∀ n, IsMarkovKernel (κB n)]
    (sendA sendB : (n : ℕ) → ((Fin n → (O ⊕ Unit)) × (Fin n → M)) × O → M)
    (ha : ∀ n, Measurable (sendA n)) (hb : ∀ n, Measurable (sendB n)) :
    ∃ p : LocalOutcomeSampler O M,
      p.alice = alice ∧ p.sendA = sendA ∧ p.sendB = sendB ∧
      (∀ n s, volume.map (fun u => p.sampleA n (s,u)) = κA n s) ∧
      (∀ n s, volume.map (fun u => p.sampleB n (s,u)) = κB n s) := by
  have hA (n : ℕ) := sample_instrument_kernel (κA n)
  have hB (n : ℕ) := sample_instrument_kernel (κB n)
  choose fA hfA hlawA hrestA using hA
  choose fB hfB hlawB hrestB using hB
  exact ⟨⟨alice,fun n pair => fA n pair.1 pair.2,
    fun n pair => fB n pair.1 pair.2,sendA,sendB,hfA,hfB,ha,hb⟩,
    rfl,rfl,rfl,hlawA,hlawB⟩

namespace LocalOutcomeSampler

universe v4306_0 v4306_1

variable {O : Type v4306_0} {M : Type v4306_1} [inst4306_0 : MeasurableSpace O] [inst4306_1 : MeasurableSpace M]
  (p : LocalOutcomeSampler O M)

def instrumentKernel
    (κA κB : (n : ℕ) → Kernel ((Fin n → (O ⊕ Unit)) × (Fin n → M)) O)
    (n : ℕ) : Kernel (Fin n → O) O :=
  if p.alice n then
    (κA n).comap (fun x => (p.extractPrivate true n x,p.publicFrom n x))
      ((p.measurable_extractPrivate true n).prodMk (p.measurable_publicFrom n)) else
    (κB n).comap (fun x => (p.extractPrivate false n x,p.publicFrom n x))
      ((p.measurable_extractPrivate false n).prodMk (p.measurable_publicFrom n))

instance instrumentKernel_markov
    (κA κB : (n : ℕ) → Kernel ((Fin n → (O ⊕ Unit)) × (Fin n → M)) O)
    [∀ n, IsMarkovKernel (κA n)] [∀ n, IsMarkovKernel (κB n)] (n : ℕ) :
    IsMarkovKernel (p.instrumentKernel κA κB n) := by
  unfold instrumentKernel
  split <;> infer_instance

lemma causal_step_law
    (κA κB : (n : ℕ) → Kernel ((Fin n → (O ⊕ Unit)) × (Fin n → M)) O)
    (ha : ∀ n s, volume.map (fun u => p.sampleA n (s,u)) = κA n s)
    (hb : ∀ n s, volume.map (fun u => p.sampleB n (s,u)) = κB n s) :
    ∀ n s, volume.map (fun u => p.causal.step n (s,u)) = p.instrumentKernel κA κB n s := by
  intro n s
  change volume.map (fun u => if p.alice n then
    p.sampleA n ((p.extractPrivate true n s,p.publicFrom n s),u) else
    p.sampleB n ((p.extractPrivate false n s,p.publicFrom n s),u)) = _
  unfold instrumentKernel
  split <;> simp_all only [Kernel.comap_apply]

end LocalOutcomeSampler

end

section

open MeasureTheory Matrix Filter

open scoped ComplexOrder MatrixOrder

universe v4357_0 v4357_1

variable {Ω : Type v4357_0} {ι : Type v4357_1} [inst4357_0 : MeasurableSpace Ω] [inst4357_1 : Fintype ι] [inst4357_2 : DecidableEq ι]

namespace PositiveMatrixMeasure

open scoped Matrix.Norms.L2Operator in
lemma integrable_density (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω) :
    Integrable (W.density μ) μ := by
  have hh : Integrable (fun t i j => (W.entry i j).rnDeriv μ t) μ := by
    apply integrable_pi_iff.mpr; intro i
    apply integrable_pi_iff.mpr; intro j
    exact W.integrable_entry μ i j
  let L : (ι → ι → ℂ) →L[ℂ] Matrix ι ι ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℂ).toLinearMap
  exact L.integrable_comp hh

end PositiveMatrixMeasure

end

section

open MeasureTheory Matrix Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator ProbabilityTheory ENNReal NNReal Topology

universe v4623_0 v4623_1

variable {Ω : Type v4623_0} {ι : Type v4623_1} {mΩ : MeasurableSpace Ω} [inst4623_0 : Fintype ι] [inst4623_1 : DecidableEq ι]
  {μ : Measure Ω} [inst4623_2 : IsFiniteMeasure μ] {F : Filtration ℕ mΩ}

theorem positive_matrix_martingale_extension (W : ℕ → Ω → Matrix ι ι ℂ)
    (hr : ∀ i j, Martingale (fun n ω => (W n ω i j).re) F μ)
    (hi : ∀ i j, Martingale (fun n ω => (W n ω i j).im) F μ)
    (hp : ∀ n, ∀ᵐ ω ∂μ, (W n ω).PosSemidef)
    (ht : ∀ n, ∀ᵐ ω ∂μ, (trace (W n ω)).re ≤ 1) :
    ∃ V : PositiveMatrixMeasure Ω ι, ∀ n S, MeasurableSet[F n] S →
      V.value S = fun i j => ∫ ω in S, W n ω i j ∂μ := by
  have hbound (n : ℕ) (i j : ι) : ∀ᵐ ω ∂μ, ‖W n ω i j‖ ≤ 1 := by
    filter_upwards [hp n,ht n] with ω hω htω
    exact (psd_entry_norm_le_trace hω i j).trans htω
  have hbr (i j : ι) (n : ℕ) : ∀ᵐ ω ∂μ, ‖(W n ω i j).re‖ ≤ 1 :=
    (hbound n i j).mono (fun ω hω => (show ‖(W n ω i j).re‖ ≤ ‖W n ω i j‖ from by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (W n ω i j)).trans hω)
  have hbi (i j : ι) (n : ℕ) : ∀ᵐ ω ∂μ, ‖(W n ω i j).im‖ ≤ 1 :=
    (hbound n i j).mono (fun ω hω => (show ‖(W n ω i j).im‖ ≤ ‖W n ω i j‖ from by simpa only [Real.norm_eq_abs] using Complex.abs_im_le_norm (W n ω i j)).trans hω)
  choose gr hgr htr hcr using (fun i j => bounded_martingale_limit (hr i j) (hbr i j))
  choose gi hgi hti hci using (fun i j => bounded_martingale_limit (hi i j) (hbi i j))
  let G : Ω → Matrix ι ι ℂ := fun ω i j => (gr i j ω : ℂ) + (gi i j ω : ℂ)*Complex.I
  have hG (i j : ι) : Integrable (fun ω => G ω i j) μ :=
    ((hgr i j).ofReal).add (((hgi i j).ofReal).mul_const Complex.I)
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => W n ω) atTop (𝓝 (G ω)) := by
    have htr' := ae_all_iff.mpr (fun i => ae_all_iff.mpr (htr i))
    have hti' := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hti i))
    filter_upwards [htr',hti'] with ω hωr hωi
    have hc : Tendsto (fun n i j => W n ω i j) atTop (𝓝 (fun i j => G ω i j)) := by
      apply tendsto_pi_nhds.mpr; intro i
      apply tendsto_pi_nhds.mpr; intro j
      have hh := (Complex.continuous_ofReal.continuousAt.tendsto.comp (hωr i j)).add
        ((Complex.continuous_ofReal.continuousAt.tendsto.comp (hωi i j)).mul_const Complex.I)
      simpa only [Function.comp_apply, Pi.add_apply, Complex.re_add_im] using hh
    have hcM : Continuous (Matrix.of : (ι → ι → ℂ) → Matrix ι ι ℂ) :=
      continuous_matrix (fun i j => continuous_apply_apply i j)
    exact hcM.continuousAt.tendsto.comp hc
  have hGp : ∀ᵐ ω ∂μ, (G ω).PosSemidef := by
    filter_upwards [hlim,ae_all_iff.mpr hp] with ω hω hh
    exact (isClosed_Ici.mem_of_tendsto hω (Eventually.of_forall (fun n => (hh n).nonneg))).posSemidef
  refine ⟨positiveMatrixMeasureOfDensity hG hGp, ?_⟩
  intro n S hS
  rw [positiveMatrixMeasureOfDensity_value hG hGp S (F.le n S hS)]
  have hc (i j : ι) : Integrable (fun ω => W n ω i j) μ := by
    have hh := ((hr i j).integrable n).ofReal.add (((hi i j).integrable n).ofReal.mul_const Complex.I)
    have hefun : (fun ω => W n ω i j) =
        ((fun ω => ((W n ω i j).re : ℂ)) + (fun ω => ((W n ω i j).im : ℂ)*Complex.I)) :=
      funext (fun ω => (Complex.re_add_im (W n ω i j)).symm)
    rw [hefun]
    exact hh
  have he (i j : ι) : (∫ ω in S, G ω i j ∂μ) = ∫ ω in S, W n ω i j ∂μ := by
    apply Complex.ext
    · change RCLike.re (∫ ω in S, G ω i j ∂μ) = RCLike.re (∫ ω in S, W n ω i j ∂μ)
      rw [← integral_re (hG i j).integrableOn, ← integral_re (hc i j).integrableOn]
      have heG : (fun ω => RCLike.re (G ω i j)) = gr i j := by
        funext ω
        change ((gr i j ω : ℂ) + (gi i j ω : ℂ)*Complex.I).re = _
        simp
      rw [heG]
      calc
        _ = ∫ ω in S, μ[gr i j | F n] ω ∂μ :=
          (setIntegral_condExp (F.le n) (hgr i j) hS).symm
        _ = _ := integral_congr_ae (ae_restrict_of_ae (hcr i j n).symm)
    · change RCLike.im (∫ ω in S, G ω i j ∂μ) = RCLike.im (∫ ω in S, W n ω i j ∂μ)
      rw [← integral_im (hG i j).integrableOn, ← integral_im (hc i j).integrableOn]
      have heG : (fun ω => RCLike.im (G ω i j)) = gi i j := by
        funext ω
        change ((gr i j ω : ℂ) + (gi i j ω : ℂ)*Complex.I).im = _
        simp
      rw [heG]
      calc
        _ = ∫ ω in S, μ[gi i j | F n] ω ∂μ :=
          (setIntegral_condExp (F.le n) (hgi i j) hS).symm
        _ = _ := integral_congr_ae (ae_restrict_of_ae (hci i j n).symm)
  exact Matrix.ext (fun i j => (integral_matrix_entry (integrable_matrix_of_entries hG).integrableOn i j).trans (he i j))

end

section

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

section ReferenceAlgebra

universe v4714_0 v4714_1 v4714_2

variable {ι : Type v4714_0} {κ : Type v4714_1} {η : Type v4714_2} [inst4714_0 : Fintype ι] [inst4714_1 : Fintype κ] [inst4714_2 : Fintype η]
  [inst4714_3 : DecidableEq ι] [inst4714_4 : DecidableEq κ] [inst4714_5 : DecidableEq η]

omit inst4714_2 inst4714_3 inst4714_5 in
lemma keepReference_pos [Fintype η] [DecidableEq ι] [DecidableEq η] {U : Matrix (ι × η) (ι × η) ℂ} (hU : U.PosSemidef) :
    (keepReference U).PosSemidef := by
  have he : keepReference U = ∑ i, U.submatrix (fun x => (i,x)) (fun x => (i,x)) := by
    ext x y; simp [keepReference,Matrix.sum_apply]
  rw [he]
  exact Matrix.posSemidef_sum _ (fun i _ => hU.submatrix _)

omit inst4714_3 inst4714_5 in
lemma trace_keepReference [DecidableEq ι] [DecidableEq η] (U : Matrix (ι × η) (ι × η) ℂ) :
    trace (keepReference U) = trace U := by
  simp only [trace,diag,keepReference,Fintype.sum_prod_type]
  exact Finset.sum_comm

end ReferenceAlgebra

universe v4805_0 v4805_1

variable {a b : ℕ} {η : Type v4805_0} {κ : Type v4805_1} [inst4805_0 : Fintype η] [inst4805_1 : Fintype κ]
  [inst4805_2 : DecidableEq η] [inst4805_3 : DecidableEq κ]

def localAction (L : Mat a →ₗ[ℂ] Mat b)
    (U : Matrix (Fin a × η) (Fin a × η) ℂ) : Matrix (Fin b × η) (Fin b × η) ℂ :=
  fun p q => L (fun i j => U (i,p.2) (j,q.2)) p.1 q.1

lemma localAction_refFilter (L : Mat a →ₗ[ℂ] Mat b) (K : Matrix κ η ℂ)
    (U : Matrix (Fin a × η) (Fin a × η) ℂ) :
    localAction L (referenceFilter K U) = referenceFilter K (localAction L U) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  rw [referenceFilter_apply]
  change L (fun u v => referenceFilter K U (u,x) (v,y)) i j = _
  have he : (fun u v => referenceFilter K U (u,x) (v,y) : Mat a) =
      ∑ s, ∑ t, (K x s * star (K y t)) • (fun u v => U (u,s) (v,t) : Mat a) := by
    apply Matrix.ext; intro u v
    rw [referenceFilter_apply]

    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro t _
    ring
  have hm : L (∑ s, ∑ t, (K x s * star (K y t)) • (fun u v => U (u,s) (v,t) : Mat a)) =
      ∑ s, ∑ t, (K x s * star (K y t)) • L (fun u v => U (u,s) (v,t)) := by
    exact map_sum L _ _ |>.trans (Finset.sum_congr rfl (fun s _ =>
      (map_sum L _ _).trans (Finset.sum_congr rfl (fun t _ => L.map_smul _ _))))
  have hh := congrArg (fun F : Mat b => F i j) ((congrArg L he).trans hm)
  refine hh.trans ?_

  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro t _

  unfold localAction
  ring

omit inst4805_2 in
lemma localAction_positive [DecidableEq η] (L : Mat a →ₗ[ℂ] Mat b) (hL : CompletelyPositive L)
    {U : Matrix (Fin a × η) (Fin a × η) ℂ} (hU : U.PosSemidef) :
    (localAction L U).PosSemidef :=
  (cp_amplifyIndex hL (U.submatrix Prod.swap Prod.swap) (hU.submatrix Prod.swap)).submatrix Prod.swap

end

namespace PositiveMatrixMeasure

open MeasureTheory Matrix Filter

open scoped ComplexOrder MatrixOrder

universe v4860_0 v4860_1

variable {Ω : Type v4860_0} {ι : Type v4860_1} [inst4860_0 : MeasurableSpace Ω] [inst4860_1 : Fintype ι] [inst4860_2 : DecidableEq ι]

lemma traceMeasure_real (W : PositiveMatrixMeasure Ω ι) (S : Set Ω) (hS : MeasurableSet S) :
    W.traceMeasure.real S = (trace (W.value S)).re := by
  rw [traceMeasure,SignedMeasure.toMeasureOfZeroLE_real_apply _ _ _ hS,
    Set.univ_inter,traceSigned_apply]

lemma value_zero_of_traceMeasure_zero (W : PositiveMatrixMeasure Ω ι)
    (S : Set Ω) (hS : MeasurableSet S) (h : W.traceMeasure S=0) : W.value S=0 := by
  have hr : (trace (W.value S)).re=0 := by
    rw [← W.traceMeasure_real S hS,Measure.real,h,ENNReal.toReal_zero]
  apply (W.positive S hS).trace_eq_zero_iff.mp
  apply Complex.ext
  · exact hr
  · exact (RCLike.nonneg_iff.mp (W.positive S hS).trace_nonneg).2

universe v4900_0

def sum {β : Type v4900_0} [Fintype β] (W : β → PositiveMatrixMeasure Ω ι) :
    PositiveMatrixMeasure Ω ι where
  entry i j := ∑ k, (W k).entry i j
  positive S hS := by
    have he : (fun i j => (∑ k, (W k).entry i j) S) = ∑ k, (W k).value S := by
      ext i j; simp [value,Matrix.sum_apply]
    rw [he]
    exact Matrix.posSemidef_sum _ (fun k _ => (W k).positive S hS)

universe v4909_0

omit inst4860_2 in
lemma sum_value [DecidableEq ι] {β : Type v4909_0} [Fintype β] (W : β → PositiveMatrixMeasure Ω ι) (S : Set Ω) :
    (sum W).value S = ∑ k, (W k).value S := by
  ext i j; simp [value,sum,Matrix.sum_apply]

universe v4913_0

lemma value_zero_of_sum_trace_zero {β : Type v4913_0} [Fintype β]
    (W : β → PositiveMatrixMeasure Ω ι) (S : Set Ω) (hS : MeasurableSet S)
    (h : (sum W).traceMeasure S=0) (k : β) : (W k).value S=0 := by
  have he := value_zero_of_traceMeasure_zero (sum W) S hS h
  rw [sum_value] at he
  have ht : ∑ l, (Matrix.trace ((W l).value S)).re=0 := by
    have hh := congrArg (fun M : Matrix ι ι ℂ => (trace M).re) he
    simpa [Matrix.trace_sum,Complex.re_sum] using hh
  have hp (l : β) : 0 ≤ (Matrix.trace ((W l).value S)).re :=
    (RCLike.nonneg_iff.mp ((W l).positive S hS).trace_nonneg).1
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hp l)).mp ht k (Finset.mem_univ k)
  apply ((W k).positive S hS).trace_eq_zero_iff.mp
  exact Complex.ext hz (RCLike.nonneg_iff.mp ((W k).positive S hS).trace_nonneg).2

universe v4940_0

lemma sum_trace_density_one {β : Type v4940_0} [Fintype β]
    (W : β → PositiveMatrixMeasure Ω ι) :
    ∀ᵐ t ∂(sum W).traceMeasure, ∑ k, (trace ((W k).density (sum W).traceMeasure t)).re = 1 := by
  let μ := (sum W).traceMeasure
  have hi (k : β) : Integrable (fun t => (trace ((W k).density μ t)).re) μ :=
    ((W k).integrable_trace_density μ).re
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (integrable_finsetSum _ (fun k _ => hi k))
    (integrable_const (1:ℝ))
  intro S hS _
  rw [integral_finsetSum _ (fun k _ => (hi k).integrableOn)]
  simp only [integral_const,smul_eq_mul,mul_one]
  have hf (k : β) : (∫ t in S, (trace ((W k).density μ t)).re ∂μ) =
      (trace ((W k).value S)).re := by
    change (∫ t in S, RCLike.re (trace ((W k).density μ t)) ∂μ) = _
    rw [integral_re ((W k).integrable_trace_density μ).integrableOn,
      integral_trace_density _ μ (fun T hT h => value_zero_of_sum_trace_zero W T hT h k) S hS]
    rfl
  simp_rw [hf]
  simp only [Measure.real,Measure.restrict_apply_univ]
  change _ = μ.real S
  rw [show μ.real S=(trace ((sum W).value S)).re from (sum W).traceMeasure_real S hS,
    sum_value,Matrix.trace_sum,Complex.re_sum]

lemma integrable_test_density (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω)
    (T : Matrix ι ι ℂ) : Integrable (fun t => trace (T * W.density μ t)) μ := by
  unfold trace diag
  simp only [Matrix.mul_apply]
  apply integrable_finsetSum; intro i _
  apply integrable_finsetSum; intro j _
  exact (W.integrable_entry μ j i).const_mul _

lemma integral_test_density (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω) [SigmaFinite μ]
    (hAC : ∀ S, MeasurableSet S → μ S=0 → W.value S=0)
    (T : Matrix ι ι ℂ) (S : Set Ω) (hS : MeasurableSet S) :
    (∫ t in S, trace (T * W.density μ t) ∂μ) = trace (T * W.value S) := by
  change (∫ t in S, ∑ i, ∑ j, T i j * W.density μ t j i ∂μ) =
    ∑ i, ∑ j, T i j * W.value S j i
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => ((W.integrable_entry μ j i).const_mul (T i j)).integrableOn))]
  apply Finset.sum_congr rfl; intro i _
  rw [integral_finsetSum _ (fun j _ =>
    ((W.integrable_entry μ j i).const_mul (T i j)).integrableOn)]
  apply Finset.sum_congr rfl; intro j _
  rw [integral_const_mul,W.integral_density_entry μ hAC S hS j i]

end PositiveMatrixMeasure

open Matrix MeasureTheory

open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

universe v5030_0 v5030_1 v5030_2

lemma referenceFilter_pos {ι : Type v5030_0} {η : Type v5030_1} {κ : Type v5030_2} [Fintype ι] [Fintype η]
    [Fintype κ] [DecidableEq ι] (K : Matrix κ η ℂ)
    {U : Matrix (ι × η) (ι × η) ℂ} (hU : U.PosSemidef) :
    (referenceFilter K U).PosSemidef :=
  hU.mul_mul_conjTranspose_same _

section InstrumentAlgebra

universe v5037_0

variable {a b : ℕ} {η : Type v5037_0} [inst5037_0 : Fintype η] [inst5037_1 : DecidableEq η]

omit inst5037_0 inst5037_1 in
lemma localAction_product [Fintype η] [DecidableEq η] (L : Mat a →ₗ[ℂ] Mat b)
    (A : Mat a) (B : Matrix η η ℂ) :
    localAction L (A ⊗ₖ B) = L A ⊗ₖ B := by
  ext ⟨i,x⟩ ⟨j,y⟩
  change L (fun u v => A u v * B x y) i j = L A i j * B x y
  have he : (fun u v => A u v * B x y : Mat a) = B x y • A := by
    ext u v; simp [smul_eq_mul,mul_comm]
  rw [he,map_smul]
  simp [smul_eq_mul,mul_comm]

omit inst5037_0 inst5037_1 in
lemma keepReference_localAction [Fintype η] [DecidableEq η] (L : Mat a →ₗ[ℂ] Mat b)
    (hL : ∀ A, trace (L A) = trace A)
    (U : Matrix (Fin a × η) (Fin a × η) ℂ) :
    keepReference (localAction L U) = keepReference U := by
  ext x y
  exact hL (fun i j => U (i,x) (j,y))

lemma trace_localAction (L : Mat a →ₗ[ℂ] Mat b)
    (hL : ∀ A, trace (L A) = trace A)
    (U : Matrix (Fin a × η) (Fin a × η) ℂ) :
    trace (localAction L U) = trace U := by
  rw [← trace_keepReference,keepReference_localAction L hL,trace_keepReference]

end InstrumentAlgebra

universe v5068_0

structure QuantumInstrument (O : Type v5068_0) [MeasurableSpace O] (a b : ℕ) where
  operation : Set O → Mat a →ₗ[ℂ] Mat b
  coefficient : Fin b → Fin b → Fin a → Fin a → ComplexMeasure O
  operation_coefficient : ∀ S i j x y,
    operation S (matrixUnit x y) i j = coefficient i j x y S
  completelyPositive : ∀ S, MeasurableSet S → CompletelyPositive (operation S)
  totalTrace : ∀ U, trace (operation Set.univ U) = trace U

namespace PositiveMatrixMeasure

universe v5077_0 v5077_1 v5077_2

variable {O : Type v5077_0} {ι : Type v5077_1} {η : Type v5077_2} [inst5077_0 : MeasurableSpace O] [inst5077_1 : Fintype ι] [inst5077_2 : Fintype η]
  [inst5077_3 : DecidableEq ι] [inst5077_4 : DecidableEq η]

def retainReference (W : PositiveMatrixMeasure O (ι × η)) : PositiveMatrixMeasure O η where
  entry x y := ∑ i, W.entry (i,x) (i,y)
  positive S hS := by
    have hp : (keepReference (W.value S)).PosSemidef := keepReference_pos (W.positive S hS)
    have he : (fun x y : η => (∑ i, W.entry (i,x) (i,y)) S) =
        keepReference (W.value S) := by
      ext x y
      simp only [_root_.sum_apply,keepReference,value]
    rw [he]
    exact hp

lemma retainReference_value (W : PositiveMatrixMeasure O (ι × η)) (S : Set O) :
    W.retainReference.value S = keepReference (W.value S) := by
  ext x y; simp [retainReference,value,keepReference,_root_.sum_apply]

universe v5109_0 v5109_1

lemma pushforward_filter {T : Type v5109_0} {κ : Type v5109_1} [MeasurableSpace T] [Fintype κ] [DecidableEq κ]
    (W : PositiveMatrixMeasure O η) (f : O → T) (hf : Measurable f)
    (K : Matrix κ η ℂ) (S : Set T) (hS : MeasurableSet S) :
    ((W.filter K).pushforward f hf).value S =
      ((W.pushforward f hf).filter K).value S := by
  rw [pushforward_value _ _ _ S hS,filter_value,filter_value,pushforward_value _ _ _ S hS]

lemma normalized_density (W : PositiveMatrixMeasure O η) :
    ∀ᵐ t ∂W.traceMeasure, Density (W.density W.traceMeasure t) := by
  let μ := W.traceMeasure
  have hAC := W.value_zero_of_traceMeasure_zero
  have htrace : ∀ᵐ t ∂μ, (trace (W.density μ t)).re = 1 := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
      (W.integrable_trace_density μ).re (integrable_const (1 : ℝ))
    intro S hS _
    change (∫ t in S, RCLike.re (trace (W.density μ t)) ∂μ) = _
    rw [integral_re ((W.integrable_trace_density μ).integrableOn),
      W.integral_trace_density μ hAC S hS,integral_const]
    simp only [smul_eq_mul,mul_one]
    change (trace (W.value S)).re = (μ.restrict S).real Set.univ
    simpa only [Measure.real,Measure.restrict_apply_univ] using (W.traceMeasure_real S hS).symm
  filter_upwards [htrace,density_posSemidef_ae W μ hAC] with t ht hp
  refine ⟨hp,?_⟩
  exact Complex.ext ht (RCLike.nonneg_iff.mp hp.trace_nonneg).2

end PositiveMatrixMeasure

namespace QuantumInstrument

universe v5136_0

variable {O : Type v5136_0} [inst5136_0 : MeasurableSpace O] {a b : ℕ}
  (J : QuantumInstrument O a b)

lemma operation_apply (S : Set O) (U : Mat a) (i j : Fin b) :
    J.operation S U i j = ∑ x, ∑ y, U x y * J.coefficient i j x y S := by
  have hh := congrArg (fun X : Mat b => X i j)
    (congrArg (J.operation S) (matrix_sum_units U))
  rw [map_sum] at hh
  simp only [map_sum,map_smul,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    J.operation_coefficient] at hh
  exact hh

universe v5151_0

def withReference {η : Type v5151_0} [Fintype η] [DecidableEq η]
    (U : Matrix (Fin a × η) (Fin a × η) ℂ) (hU : U.PosSemidef) :
    PositiveMatrixMeasure O (Fin b × η) where
  entry p q := ∑ x, ∑ y, U (x,p.2) (y,q.2) • J.coefficient p.1 q.1 x y
  positive S hS := by
    have he : (fun p q : Fin b × η =>
        (∑ x, ∑ y, U (x,p.2) (y,q.2) • J.coefficient p.1 q.1 x y) S) =
        localAction (J.operation S) U := by
      ext ⟨i,r⟩ ⟨j,s⟩
      simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
      exact (J.operation_apply S _ i j).symm
    rw [he]
    exact localAction_positive _ (J.completelyPositive S hS) hU

universe v5165_0

lemma withReference_value {η : Type v5165_0} [Fintype η] [DecidableEq η]
    (U : Matrix (Fin a × η) (Fin a × η) ℂ) (hU : U.PosSemidef) (S : Set O) :
    (J.withReference U hU).value S = localAction (J.operation S) U := by
  ext ⟨i,r⟩ ⟨j,s⟩
  change (∑ x, ∑ y, U (x,r) (y,s) • J.coefficient i j x y) S = _
  simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  exact (J.operation_apply S _ i j).symm

universe v5173_0

lemma total_reference_unchanged {η : Type v5173_0} [Fintype η] [DecidableEq η]
    (U : Matrix (Fin a × η) (Fin a × η) ℂ) (hU : U.PosSemidef) :
    keepReference ((J.withReference U hU).value Set.univ) = keepReference U := by
  rw [J.withReference_value]
  exact keepReference_localAction _ J.totalTrace U

universe v5179_0

lemma normalized_outcome_measure {η : Type v5179_0} [Fintype η] [DecidableEq η]
    (U : Matrix (Fin a × η) (Fin a × η) ℂ) (hU : Density U) :
    IsProbabilityMeasure (J.withReference U hU.1).traceMeasure := by
  constructor
  apply (ENNReal.toReal_eq_one_iff _).mp
  change (J.withReference U hU.1).traceMeasure.real Set.univ = 1
  rw [(J.withReference U hU.1).traceMeasure_real Set.univ MeasurableSet.univ,
    J.withReference_value,trace_localAction _ J.totalTrace,hU.2]
  rfl

universe v5191_0 v5191_1

lemma withReference_filter {η : Type v5191_0} {κ : Type v5191_1} [Fintype η] [Fintype κ]
    [DecidableEq η] [DecidableEq κ]
    (U : Matrix (Fin a × η) (Fin a × η) ℂ) (hU : U.PosSemidef)
    (K : Matrix κ η ℂ) (S : Set O) :
    (J.withReference (referenceFilter K U) (referenceFilter_pos K hU)).value S =
      referenceFilter K ((J.withReference U hU).value S) := by
  rw [J.withReference_value,J.withReference_value,localAction_refFilter]

universe v5200_0

def referenceLaw {η : Type v5200_0} [Fintype η] [DecidableEq η]
    (U : Matrix (Fin a × η) (Fin a × η) ℂ) (hU : U.PosSemidef) :
    PositiveMatrixMeasure O η := (J.withReference U hU).retainReference

universe v5204_0

lemma referenceLaw_value {η : Type v5204_0} [Fintype η] [DecidableEq η]
    (U : Matrix (Fin a × η) (Fin a × η) ℂ) (hU : U.PosSemidef) (S : Set O) :
    (J.referenceLaw U hU).value S = keepReference (localAction (J.operation S) U) := by
  rw [referenceLaw,PositiveMatrixMeasure.retainReference_value,J.withReference_value]

universe v5209_0 v5209_1

lemma referenceLaw_filter {η : Type v5209_0} {κ : Type v5209_1} [Fintype η] [Fintype κ]
    [DecidableEq η] [DecidableEq κ]
    (U : Matrix (Fin a × η) (Fin a × η) ℂ) (hU : U.PosSemidef)
    (K : Matrix κ η ℂ) (S : Set O) :
    (J.referenceLaw (referenceFilter K U) (referenceFilter_pos K hU)).value S =
      ((J.referenceLaw U hU).filter K).value S := by
  rw [J.referenceLaw_value,localAction_refFilter,keepReference_filter,
    PositiveMatrixMeasure.filter_value,J.referenceLaw_value]

universe v5221_0

lemma reference_test_born {η : Type v5221_0} [Fintype η] [DecidableEq η]
    (U : Matrix (Fin a × η) (Fin a × η) ℂ) (hU : U.PosSemidef)
    (E : Matrix η η ℂ) (hE : E.PosSemidef) (S : Set O) (hS : MeasurableSet S) :
    (J.referenceLaw (referenceFilter (CFC.sqrt E) U)
      (referenceFilter_pos _ hU)).traceMeasure.real S =
      (trace (E * (J.referenceLaw U hU).value S)).re := by
  rw [PositiveMatrixMeasure.traceMeasure_real _ S hS,J.referenceLaw_filter,
    PositiveMatrixMeasure.filter_value,(CFC.sqrt_nonneg E).posSemidef.isHermitian.eq,
    Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self E hE.nonneg]

universe v5235_0

theorem reference_posterior_mean {η : Type v5235_0} [Fintype η] [DecidableEq η]
    (U : Matrix (Fin a × η) (Fin a × η) ℂ) (hU : Density U) :
    let W := J.withReference U hU.1
    (∀ᵐ o ∂W.traceMeasure, Density (W.density W.traceMeasure o)) ∧
    ∀ x y, (∫ o, keepReference (W.density W.traceMeasure o) x y ∂W.traceMeasure) =
      keepReference U x y := by
  dsimp only
  refine ⟨(J.withReference U hU.1).normalized_density,?_⟩
  intro x y
  let W := J.withReference U hU.1
  have he : (∫ o, keepReference (W.density W.traceMeasure o) x y ∂W.traceMeasure) =
      keepReference (W.value Set.univ) x y := by
    change (∫ o, ∑ i, W.density W.traceMeasure o (i,x) (i,y) ∂W.traceMeasure) = _
    rw [integral_finsetSum _ (fun i _ => W.integrable_entry W.traceMeasure (i,x) (i,y))]
    change (∑ i, ∫ o, W.density W.traceMeasure o (i,x) (i,y) ∂W.traceMeasure) = _
    change (∑ i, ∫ o, W.density W.traceMeasure o (i,x) (i,y) ∂W.traceMeasure) =
      ∑ i, W.value Set.univ (i,x) (i,y)
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Measure.restrict_univ] using W.integral_density_entry W.traceMeasure
      W.value_zero_of_traceMeasure_zero Set.univ MeasurableSet.univ (i,x) (i,y)
  rw [he]
  exact congrArg (fun A : Matrix η η ℂ => A x y) (J.total_reference_unchanged U hU.1)

end QuantumInstrument

end ZeroKey

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace ZeroKey

universe v5273_0

variable {O : Type v5273_0} [inst5273_0 : MeasurableSpace O]

universe v5311_0

variable {ι : Type v5311_0} [inst5311_0 : Fintype ι] [inst5311_1 : DecidableEq ι]

variable (P : Measure (ℕ → O)) [inst5327_0 : IsProbabilityMeasure P]
    (K : (n : ℕ) → Kernel (Fin n → O) O) [inst5327_1 : ∀ n, IsMarkovKernel (K n)]
    (hP : ∀ n, P.map (historyPrefix (n+1)) =
      ((P.map (historyPrefix n)) ⊗ₘ K n).map
        (fun pair : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) pair.1 pair.2))
    (U : (n : ℕ) → (Fin n → O) → Matrix ι ι ℂ)
    (hU : ∀ n s, Density (U n s)) (hm : ∀ n, Measurable (U n))
    (hmean : ∀ n s i j,
      (∫ o, U (n+1) (Fin.snoc (α := fun _ : Fin (n+1) => O) s o) i j ∂K n s) = U n s i j)

include hP hU hm hmean in
theorem instrument_history_reference_extension :
    ∃ V : PositiveMatrixMeasure (ℕ → O) ι, ∀ n S,
      MeasurableSet[historyFiltration n] S →
      V.value S = fun i j => ∫ x in S, U n (historyPrefix n x) i j ∂P := by
  apply positive_matrix_martingale_extension (fun n x => U n (historyPrefix n x))
  · exact reference_history_martingale_re P K hP U hU hm hmean
  · exact reference_history_martingale_im P K hP U hU hm hmean
  · intro n; exact Filter.Eventually.of_forall (fun x => (hU n _).1)
  · intro n; exact Filter.Eventually.of_forall (fun x => by simp only [(hU n _).2,Complex.one_re,le_refl])

end ZeroKey

end

end OAI
