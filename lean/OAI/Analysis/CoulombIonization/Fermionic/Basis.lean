import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.GlobalDensityBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
namespace CoulombPauli
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]

omit [SigmaFinite μ] in
lemma tensor_add_left (u w : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    tensor (u+w) v = tensor u v + tensor w v := by
  apply Lp.ext
  filter_upwards [tensor_ae (u+w) v, tensor_ae u v, tensor_ae w v,
    Lp.coeFn_add (tensor u v) (tensor w v),
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_add u w)] with z h1 h2 h3 h4 h5
  simp only [h1,h2,h3,h4,h5,Pi.add_apply,add_mul]

omit [SigmaFinite μ] in
lemma tensor_smul_left (c : ℂ) (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    tensor (c • u) v = c • tensor u v := by
  apply Lp.ext
  filter_upwards [tensor_ae (c • u) v, tensor_ae u v,
    Lp.coeFn_smul c (tensor u v),
    Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_smul c u)] with z h1 h2 h3 h4
  simp only [h1,h2,h3,h4,Pi.smul_apply,smul_eq_mul,mul_assoc]

def tensorRight (v : Lp ℂ 2 ν) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearMap.mkContinuous
    ({ toFun := fun u => tensor u v
       map_add' := fun u w => tensor_add_left u w v
       map_smul' := fun c u => tensor_smul_left c u v } :
        Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 (μ.prod ν))
    ‖v‖ (fun u => by
      change ‖tensor u v‖ ≤ ‖v‖ * ‖u‖
      rw [tensor_norm, mul_comm])

lemma tensorRight_apply (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) : tensorRight v u = tensor u v := rfl

lemma tensor_adjoint_exchange (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν)
    (ψ : Lp ℂ 2 (μ.prod ν)) :
    inner ℂ v ((tensorLeft u).adjoint ψ) = inner ℂ u ((tensorRight v).adjoint ψ) := by
  rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
  rfl

omit [SigmaFinite μ] [SigmaFinite ν] in
lemma hilbertBasis_inner_eq_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ι : Type*} (b : HilbertBasis ι ℂ H) (u : H)
    (h : ∀ i, inner ℂ (b i) u = 0) : u = 0 := by
  apply b.repr.injective
  ext i
  simp [b.repr_apply_apply, h]

variable {ι κ : Type*}

lemma tensor_orthonormal (a : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν)) :
    Orthonormal ℂ (fun p : ι × κ => tensor (a p.1) (b p.2)) := by
  classical
  rw [orthonormal_iff_ite]
  intro p q
  rw [tensor_inner, orthonormal_iff_ite.mp a.orthonormal,
    orthonormal_iff_ite.mp b.orthonormal]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
    simp [h1,h2,Prod.ext_iff]

lemma tensor_basis_total (a : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν)) :
    (Submodule.span ℂ (Set.range (fun p : ι × κ => tensor (a p.1) (b p.2))))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro ψ hψ
  change ψ = 0
  have hij (i : ι) (j : κ) : inner ℂ (tensor (a i) (b j)) ψ = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self (i,j))) hψ
  have hleft (i : ι) : (tensorLeft (a i)).adjoint ψ = 0 := by
    apply hilbertBasis_inner_eq_zero b
    intro j
    rw [ContinuousLinearMap.adjoint_inner_right,tensorLeft_apply]
    exact hij i j
  apply eq_zero_of_tensor_orthogonal
  intro u v
  have hr : (tensorRight v).adjoint ψ = 0 := by
    apply hilbertBasis_inner_eq_zero a
    intro i
    rw [← tensor_adjoint_exchange, hleft, inner_zero_right]
  rw [← tensorRight_apply, ← ContinuousLinearMap.adjoint_inner_right, hr, inner_zero_right]

def tensorBasis (a : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν)) : HilbertBasis (ι × κ) ℂ (Lp ℂ 2 (μ.prod ν)) :=
  HilbertBasis.mkOfOrthogonalEqBot (tensor_orthonormal a b) (tensor_basis_total a b)

lemma tensorBasis_apply (a : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν)) (p : ι × κ) :
    tensorBasis a b p = tensor (a p.1) (b p.2) := by
  simp [tensorBasis]

omit [SigmaFinite μ] [SigmaFinite ν] in
lemma basis_parseval {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ι ℂ H) (u : H) :
    HasSum (fun i => ‖inner ℂ (b i) u‖^2) (‖u‖^2) := by
  have hh := (b.hasSum_inner_mul_inner u u).mapL Complex.reCLM
  convert hh using 1
  · ext i
    simp only [Complex.reCLM_apply, ← inner_conj_symm u (b i),
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  · simp only [Complex.reCLM_apply, inner_self_eq_norm_sq_to_K,
      ← RCLike.ofReal_pow]
    rfl

lemma tensorRight_parseval (a : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (b : HilbertBasis κ ℂ (Lp ℂ 2 ν)) (ψ : Lp ℂ 2 (μ.prod ν)) :
    ∑' j, ENNReal.ofReal (‖(tensorRight (b j)).adjoint ψ‖^2) =
      ENNReal.ofReal (‖ψ‖^2) := by
  have hs (j : κ) := basis_parseval a ((tensorRight (b j)).adjoint ψ)
  have hsb := basis_parseval (tensorBasis a b) ψ
  calc
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (tensor (a i) (b j)) ψ‖^2) := by
      congr 1; funext j
      rw [← (hs j).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hs j).summable]
      simp only [ContinuousLinearMap.adjoint_inner_right, tensorRight_apply]
    _ = ∑' p : ι × κ, ENNReal.ofReal (‖inner ℂ (tensor (a p.1) (b p.2)) ψ‖^2) := by
      rw [ENNReal.tsum_comm]
      exact ENNReal.tsum_prod.symm
    _ = _ := by
      simp_rw [← tensorBasis_apply]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsb.summable, hsb.tsum_eq]

omit [SigmaFinite μ] [SigmaFinite ν] in
lemma hilbertBasis_countable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [SeparableSpace H] (b : HilbertBasis ι ℂ H) : Countable ι := by
  classical
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (b i) (1/2 : ℝ)) (Metric.ball (b j) (1/2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have h := norm_inner_le_norm (𝕜 := ℂ) (b i) (b i - b j)
    have hi := b.orthonormal.norm_eq_one i
    have hii := orthonormal_iff_ite.mp b.orthonormal i i
    have hij' := orthonormal_iff_ite.mp b.orthonormal i j
    have h' : (1 : ℝ) ≤ ‖b i - b j‖ := by
      simpa [inner_sub_right, hii, hij', hi, hij] using h
    norm_num only [dist_eq_norm] at ⊢
    exact h'
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨b i, Metric.mem_ball_self (by norm_num)⟩)

end CoulombPauli

open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal

namespace CoulombPackets
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def windowed (g : 𝓢(V, ℝ)) (v : 𝓢(V, ℂ)) (z : V) : 𝓢(V, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x => (g (x-z) : ℂ)) v

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma windowed_apply (g : 𝓢(V, ℝ)) (v : 𝓢(V, ℂ)) (z x : V) :
    windowed g v z x = (g (x-z) : ℂ) * v x := by
  have hg : (fun x => (g (x-z) : ℂ)).HasTemperateGrowth := by
    have ht := (g.compSubConstCLM ℝ z).hasTemperateGrowth
    simpa only [SchwartzMap.compSubConstCLM_apply, Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.hasTemperateGrowth.comp ht
  exact SchwartzMap.smulLeftCLM_apply_apply hg v x

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma norm_windowed (g : 𝓢(V, ℝ)) (v : 𝓢(V, ℂ)) (z x : V) :
    ‖windowed g v z x‖^2 = g (x-z)^2 * ‖v x‖^2 := by
  rw [windowed_apply, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]

lemma integrable_shift_product (g : 𝓢(V, ℝ)) (v : 𝓢(V, ℂ)) :
    Integrable (fun p : V × V => g (p.2-p.1)^2 * ‖v p.2‖^2) (volume.prod volume) := by
  have hg : Integrable (fun x => g x^2) := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (g.memLp 2).aestronglyMeasurable).1 (g.memLp 2)
  have hv : Integrable (fun x => ‖v x‖^2) :=
    (memLp_two_iff_integrable_sq_norm (v.memLp 2).aestronglyMeasurable).1 (v.memLp 2)
  have he : MeasurePreserving (fun p : V × V => (p.2-p.1,p.2)) (volume.prod volume) (volume.prod volume) := by
    simpa only [Function.comp_def, Prod.map_apply, neg_sub, id_eq] using
      ((Measure.measurePreserving_neg (volume : Measure V)).prod
        (MeasurePreserving.id (volume : Measure V))).comp
        (measurePreserving_sub_prod (volume : Measure V) volume)
  exact he.integrable_comp_of_integrable (hg.mul_prod hv)

lemma integrated_plancherel (g : 𝓢(V, ℝ)) (v : 𝓢(V, ℂ)) :
    (∫ z : V, ∫ ξ : V, ‖𝓕 (windowed g v z) ξ‖^2) =
      (∫ x : V, g x^2) * (∫ x : V, ‖v x‖^2) := by
  simp_rw [SchwartzMap.integral_norm_sq_fourier, norm_windowed]
  rw [integral_integral_swap (integrable_shift_product g v)]
  simp_rw [integral_mul_const]
  have h (x : V) := integral_sub_left_eq_self (fun y : V => g y^2) volume x
  simp_rw [h]
  rw [integral_const_mul]

def frameFunction (g : 𝓢(V, ℝ)) (v : 𝓢(V, ℂ)) (p : V × V) : ℂ :=
  𝓕 (windowed g v p.1) p.2

lemma frameFunction_stronglyMeasurable (g : 𝓢(V, ℝ)) (v : 𝓢(V, ℂ)) :
    StronglyMeasurable (frameFunction g v) := by
  have h : Continuous (fun q : (V × V) × V =>
      Real.fourierChar (-inner ℝ q.2 q.1.2) • ((g (q.2-q.1.1) : ℂ) * v q.2)) := by
    exact (Real.continuous_fourierChar.comp ((continuous_snd.inner
      (continuous_snd.comp continuous_fst)).neg)).smul
      (((Complex.continuous_ofReal.comp (g.continuous.comp
        (continuous_snd.sub (continuous_fst.comp continuous_fst)))).mul
        (v.continuous.comp continuous_snd)))
  convert (h.stronglyMeasurable.integral_prod_right' (ν := volume)) using 1
  ext p
  simp only [frameFunction, SchwartzMap.fourier_coe, Real.fourier_eq, windowed_apply]

lemma frameFunction_memLp (g : 𝓢(V, ℝ)) (v : 𝓢(V, ℂ)) :
    MemLp (frameFunction g v) 2 (volume.prod volume) := by
  apply (memLp_two_iff_integrable_sq_norm
    (frameFunction_stronglyMeasurable g v).aestronglyMeasurable).2
  apply (integrable_prod_iff
    ((frameFunction_stronglyMeasurable g v).norm.pow 2).aestronglyMeasurable).2
  constructor
  · refine Filter.Eventually.of_forall fun z => ?_
    change Integrable (fun ξ : V => ‖𝓕 (windowed g v z) ξ‖^2) volume
    exact (memLp_two_iff_integrable_sq_norm
      ((𝓕 (windowed g v z)).memLp 2 volume).aestronglyMeasurable).1
      ((𝓕 (windowed g v z)).memLp 2 volume)
  · have h := (integrable_shift_product g v).integral_prod_left
    change Integrable (fun z : V => ∫ ξ : V, |‖𝓕 (windowed g v z) ξ‖^2|) volume
    simpa only [abs_sq, SchwartzMap.integral_norm_sq_fourier, norm_windowed] using h

lemma l2_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : Lp ℂ 2 μ) : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def]
  simp only [inner_self_eq_norm_sq_to_K]
  change (∫ x, (‖u x‖ : ℂ)^2 ∂μ).re = _
  simp_rw [← Complex.ofReal_pow]
  rw [integral_complex_ofReal]
  rfl

lemma frame_norm_sq (g : 𝓢(V, ℝ)) (v : 𝓢(V, ℂ)) :
    ‖(frameFunction_memLp g v).toLp (frameFunction g v)‖^2 =
      (∫ x : V, g x^2) * ‖v.toLp 2 volume‖^2 := by
  rw [l2_norm_sq, l2_norm_sq]
  calc
    _ = ∫ p : V × V, ‖frameFunction g v p‖^2 ∂(volume.prod volume) := by
      apply integral_congr_ae
      filter_upwards [(frameFunction_memLp g v).coeFn_toLp] with p hp
      rw [hp]
    _ = (∫ x : V, g x^2) * (∫ x : V, ‖v x‖^2) := by
      rw [integral_prod _ ((memLp_two_iff_integrable_sq_norm
        (frameFunction_memLp g v).aestronglyMeasurable).1 (frameFunction_memLp g v))]
      exact integrated_plancherel g v
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [v.coeFn_toLp 2 volume] with x hx
      rw [hx]

def frameLinear (g : 𝓢(V, ℝ)) :
    𝓢(V, ℂ) →ₗ[ℂ] Lp ℂ 2 ((volume : Measure V).prod (volume : Measure V)) where
  toFun v := (frameFunction_memLp g v).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(frameFunction_memLp g (u+v)).coeFn_toLp,
      (frameFunction_memLp g u).coeFn_toLp, (frameFunction_memLp g v).coeFn_toLp,
      Lp.coeFn_add ((frameFunction_memLp g u).toLp _)
        ((frameFunction_memLp g v).toLp _)] with p h1 h2 h3 h4
    simp only [h1, h4, Pi.add_apply, h2, h3]
    simp only [frameFunction, windowed, map_add, FourierTransform.fourier_add,
      add_apply]
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [(frameFunction_memLp g (c • v)).coeFn_toLp,
      (frameFunction_memLp g v).coeFn_toLp,
      Lp.coeFn_smul c ((frameFunction_memLp g v).toLp _)] with p h1 h2 h3
    simp only [RingHom.id_apply, h1, h3, Pi.smul_apply, h2]
    simp only [frameFunction, windowed, map_smul, FourierTransform.fourier_smul,
      smul_apply]

lemma frameLinear_norm (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (v : 𝓢(V, ℂ)) : ‖frameLinear g v‖ = ‖v.toLp 2 volume‖ := by
  have h := frame_norm_sq g v
  rw [hg, one_mul] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

def frame (g : 𝓢(V, ℝ)) : Lp ℂ 2 (volume : Measure V) →L[ℂ]
    Lp ℂ 2 ((volume : Measure V).prod (volume : Measure V)) :=
  (frameLinear g).extendOfNorm (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

lemma frame_toLp (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1) (v : 𝓢(V, ℂ)) :
    frame g (v.toLp 2 volume) = frameLinear g v := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  · exact ⟨1, fun v => by simpa using (frameLinear_norm g hg v).le⟩

lemma frame_norm (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1)
    (v : Lp ℂ 2 (volume : Measure V)) : ‖frame g v‖ = ‖v‖ := by
  refine (SchwartzMap.denseRange_toLpCLM (μ := (volume : Measure V))
      (F := ℂ) (p := 2) ENNReal.ofNat_ne_top).induction_on v ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro u
    rw [SchwartzMap.toLpCLM_apply, frame_toLp g hg]
    exact frameLinear_norm g hg u

def frameIsometry (g : 𝓢(V, ℝ)) (hg : ∫ x : V, g x^2 = 1) :
    Lp ℂ 2 (volume : Measure V) →ₗᵢ[ℂ] Lp ℂ 2 ((volume : Measure V).prod (volume : Measure V)) where
  toLinearMap := (frame g).toLinearMap
  norm_map' := frame_norm g hg

end CoulombPackets

end

end OAI
