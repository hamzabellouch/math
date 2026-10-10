import Mathlib
import OAI.Probability.ParisiFinite.Law

namespace OAI

/-! Scalar Phase. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter

namespace ClassicalGaussian
variable {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def scalarPhase (t x : ℝ) : ℂ := Complex.exp (Complex.I*((t*x : ℝ):ℂ))

@[simp] theorem norm_scalarPhase (t x : ℝ) : ‖scalarPhase t x‖=1 := by
  simp [scalarPhase,Complex.norm_exp,Complex.mul_re]

theorem continuous_scalarPhase (t : ℝ) : Continuous (scalarPhase t) := by
  unfold scalarPhase
  fun_prop

theorem memLp_phase_smul {q : Ω → ℝ} (hq : AEStronglyMeasurable q μ)
    (t : ℝ) (ψ : Lp E 2 μ) :
    MemLp (fun x=>scalarPhase t (q x) • ψ x) 2 μ := by
  apply (Lp.memLp ψ).congr_norm
    (((continuous_scalarPhase t).comp_aestronglyMeasurable hq).smul (Lp.aestronglyMeasurable ψ))
  exact Eventually.of_forall fun x=>by
    change ‖ψ x‖=‖scalarPhase t (q x) • ψ x‖
    simp only [norm_smul,norm_scalarPhase,one_mul]

 

def phaseMultiplier {q : Ω → ℝ} (hq : AEStronglyMeasurable q μ)
    (t : ℝ) : Lp E 2 μ →ₗᵢ[ℂ] Lp E 2 μ where
  toFun ψ := (memLp_phase_smul μ hq t ψ).toLp (fun x=>scalarPhase t (q x) • ψ x)
  map_add' ψ φ := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_phase_smul μ hq t (ψ+φ)),
      Lp.coeFn_add ψ φ,
      Lp.coeFn_add ((memLp_phase_smul μ hq t ψ).toLp _) ((memLp_phase_smul μ hq t φ).toLp _),
      MemLp.coeFn_toLp (memLp_phase_smul μ hq t ψ),
      MemLp.coeFn_toLp (memLp_phase_smul μ hq t φ)] with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h2 h3
    rw [h1,h2,h3,h4,h5,smul_add]
  map_smul' c ψ := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_phase_smul μ hq t (c • ψ)),
      Lp.coeFn_smul c ψ,
      Lp.coeFn_smul c ((memLp_phase_smul μ hq t ψ).toLp _),
      MemLp.coeFn_toLp (memLp_phase_smul μ hq t ψ)] with x h1 h2 h3 h4
    simp only [Pi.smul_apply] at h2 h3
    simp only [RingHom.id_apply]
    rw [h1,h2,h3,h4,smul_comm]
  norm_map' ψ := by
    change ‖(memLp_phase_smul μ hq t ψ).toLp (fun x=>scalarPhase t (q x) • ψ x)‖=‖ψ‖
    rw [Lp.norm_toLp,Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (memLp_phase_smul μ hq t ψ).aestronglyMeasurable
      (Lp.aestronglyMeasurable ψ)
    exact Eventually.of_forall fun x=>by simp only [norm_smul,norm_scalarPhase,one_mul]

theorem phaseMultiplier_ae {q : Ω → ℝ} (hq : AEStronglyMeasurable q μ)
    (t : ℝ) (ψ : Lp E 2 μ) :
    (phaseMultiplier μ hq t ψ : Ω → E)=ᵐ[μ] fun x=>scalarPhase t (q x) • ψ x :=
  MemLp.coeFn_toLp (memLp_phase_smul μ hq t ψ)

@[simp] theorem scalarPhase_zero (x : ℝ) : scalarPhase 0 x=1 := by
  simp [scalarPhase]

theorem scalarPhase_add (t u x : ℝ) :
    scalarPhase (t+u) x=scalarPhase t x*scalarPhase u x := by
  simp only [scalarPhase,add_mul,Complex.ofReal_add,mul_add,Complex.exp_add]

@[simp] theorem phaseMultiplier_zero {q : Ω → ℝ} (hq : AEStronglyMeasurable q μ)
    (ψ : Lp E 2 μ) : phaseMultiplier μ hq 0 ψ=ψ := by
  apply Lp.ext
  filter_upwards [phaseMultiplier_ae μ hq 0 ψ] with x hx
  simpa only [scalarPhase_zero,one_smul] using hx

theorem phaseMultiplier_add {q : Ω → ℝ} (hq : AEStronglyMeasurable q μ)
    (t u : ℝ) (ψ : Lp E 2 μ) :
    phaseMultiplier μ hq (t+u) ψ=phaseMultiplier μ hq t (phaseMultiplier μ hq u ψ) := by
  apply Lp.ext
  filter_upwards [phaseMultiplier_ae μ hq (t+u) ψ,
    phaseMultiplier_ae μ hq t (phaseMultiplier μ hq u ψ),
    phaseMultiplier_ae μ hq u ψ] with x h1 h2 h3
  rw [h1,h2,h3,scalarPhase_add,mul_smul]

 
def phaseUnitary {q : Ω → ℝ} (hq : AEStronglyMeasurable q μ)
    (t : ℝ) : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 μ :=
  LinearIsometryEquiv.ofSurjective (phaseMultiplier μ hq t) (by
    intro ψ
    refine ⟨phaseMultiplier μ hq (-t) ψ,?_⟩
    rw [←phaseMultiplier_add,add_neg_cancel,phaseMultiplier_zero])

@[simp] theorem phaseUnitary_apply {q : Ω → ℝ} (hq : AEStronglyMeasurable q μ)
    (t : ℝ) (ψ : Lp E 2 μ) : phaseUnitary μ hq t ψ=phaseMultiplier μ hq t ψ := rfl

theorem L2_norm_sq_integral (ψ : Lp E 2 μ) :
    ‖ψ‖^2=∫x,‖ψ x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜:=ℂ),L2.inner_def,←integral_re (L2.integrable_inner ψ ψ)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x=>(norm_sq_eq_re_inner (𝕜:=ℂ) (ψ x)).symm

 

theorem phaseMultiplier_tendsto [IsFiniteMeasure μ]
    {q : ℕ → Ω → ℝ} (hq : ∀n,MemLp (q n) 2 μ)
    (ht : Tendsto (fun n=>∫x,q n x^2 ∂μ) atTop (𝓝 0)) (t : ℝ) (ψ : Lp E 2 μ) :
    Tendsto (fun n=>phaseMultiplier μ (hq n).aestronglyMeasurable t ψ) atTop (𝓝 ψ) := by
  have hρ : Integrable (fun x=>‖ψ x‖^2) μ := (Lp.memLp ψ).integrable_norm_pow'
  have h := phase_weighted_L2_tendsto μ hq ht t (fun x=>‖ψ x‖^2) hρ
  have he (n : ℕ) : ‖phaseMultiplier μ (hq n).aestronglyMeasurable t ψ-ψ‖^2=
      ∫x,|‖ψ x‖^2| *phaseError t (q n x) ∂μ := by
    rw [L2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (phaseMultiplier μ (hq n).aestronglyMeasurable t ψ) ψ,
      phaseMultiplier_ae μ (hq n).aestronglyMeasurable t ψ] with x h1 h2
    simp only [Pi.sub_apply] at h1
    rw [h1,h2,show scalarPhase t (q n x) • ψ x-ψ x=
      (scalarPhase t (q n x)-1) • ψ x by rw [sub_smul,one_smul]]
    rw [norm_smul,mul_pow,abs_of_nonneg (sq_nonneg _)]
    exact mul_comm _ _
  have hn : Tendsto (fun n=>‖phaseMultiplier μ (hq n).aestronglyMeasurable t ψ-ψ‖)
      atTop (𝓝 0) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
    simp only [←he,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero,Function.comp_def] at hs
    exact hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end ClassicalGaussian

 

open scoped Topology
open Filter MeasureTheory

namespace StrongIsometryContexts
variable {α E F G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] {l : Filter α}

 

theorem apply_varying {U : α → E →ₗᵢ[ℂ] F} {V : E →ₗᵢ[ℂ] F}
    (hU : ∀x,Tendsto (fun n=>U n x) l (𝓝 (V x)))
    {x : α → E} {x₀ : E} (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun n=>U n (x n)) l (𝓝 (V x₀)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have h := (tendsto_iff_dist_tendsto_zero.mp hx).add
    (tendsto_iff_dist_tendsto_zero.mp (hU x₀))
  apply squeeze_zero (fun n=>dist_nonneg) _ (by simpa only [zero_add] using h)
  intro n
  calc
    dist (U n (x n)) (V x₀)≤dist (U n (x n)) (U n x₀)+dist (U n x₀) (V x₀) :=
      dist_triangle _ _ _
    _=dist (x n) x₀+dist (U n x₀) (V x₀) := by rw [(U n).dist_map]

theorem comp {U : α → F →ₗᵢ[ℂ] G} {V : F →ₗᵢ[ℂ] G}
    (hU : ∀x,Tendsto (fun n=>U n x) l (𝓝 (V x)))
    {A : α → E →ₗᵢ[ℂ] F} {B : E →ₗᵢ[ℂ] F}
    (hA : ∀x,Tendsto (fun n=>A n x) l (𝓝 (B x))) (x : E) :
    Tendsto (fun n=>(U n).comp (A n) x) l (𝓝 (V.comp B x)) :=
  apply_varying hU (hA x)

 
def word (U : ι → E →ₗᵢ[ℂ] E) : List ι → E →ₗᵢ[ℂ] E
  | [] => LinearIsometry.id
  | a::w => (word U w).comp (U a)

 

theorem word_tendsto (w : List ι) {U : α → ι → E →ₗᵢ[ℂ] E} {V : ι → E →ₗᵢ[ℂ] E}
    (h : ∀a x,Tendsto (fun n=>U n a x) l (𝓝 (V a x))) (x : E) :
    Tendsto (fun n=>word (U n) w x) l (𝓝 (word V w x)) := by
  induction w generalizing x with
  | nil => exact tendsto_const_nhds
  | cons a w ih => exact comp (fun y=>ih y) (h a) x

 

theorem phase_in_context {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {q : ℕ → Ω → ℝ} (hq : ∀n,MemLp (q n) 2 μ)
    (ht : Tendsto (fun n=>∫x,q n x^2 ∂μ) atTop (𝓝 0)) (t : ℝ)
    (A B : Lp H 2 μ →ₗᵢ[ℂ] Lp H 2 μ) (ψ : Lp H 2 μ) :
    Tendsto (fun n=>B (ClassicalGaussian.phaseMultiplier μ (hq n).aestronglyMeasurable t (A ψ)))
      atTop (𝓝 (B (A ψ))) :=
  B.continuous.continuousAt.tendsto.comp
    (ClassicalGaussian.phaseMultiplier_tendsto μ hq ht t (A ψ))

end StrongIsometryContexts

 

open scoped BigOperators Topology RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace ClassicalGaussian.Shifted
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*}

def form (s : Finset ι) (d e : ι → E) (g : E) : ℝ :=
  ∑i∈s,centeredQuadratic E (d i) (e i) g

def kernel (s : Finset ι) (d e : ι → E) : E →L[ℝ] E :=
  ∑i∈s,InnerProductSpace.rankOne ℝ (d i) (e i)

def kernelSq (s : Finset ι) (d e : ι → E) : ℝ :=
  ∑i∈s,‖d i‖^2*‖e i‖^2

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kernelSq_nonneg (s : Finset ι) (d e : ι → E) : 0≤kernelSq E s d e :=
  Finset.sum_nonneg fun _ _=>mul_nonneg (sq_nonneg _) (sq_nonneg _)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kernelSq_swap (s : Finset ι) (d e : ι → E) :
    kernelSq E s e d=kernelSq E s d e := by
  simp only [kernelSq,mul_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem field_kernel (s : Finset ι) (d e : ι → E) (m g : E) :
    field E (kernel E s d e m) g=∑i∈s,field E (e i) m*field E (d i) g := by
  simp [kernel,field,sum_apply,InnerProductSpace.rankOne_apply,sum_inner,real_inner_smul_left]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem form_translate (s : Finset ι) (d e : ι → E) (m g : E) :
    form E s d e (g+m)=form E s d e g+
      field E (kernel E s d e m) g+field E (kernel E s e d m) g+
      ⟪m,kernel E s d e m⟫ := by
  rw [field_kernel,field_kernel]
  have hc : ⟪m,kernel E s d e m⟫=∑i∈s,field E (d i) m*field E (e i) m := by
    simp [kernel,sum_apply,InnerProductSpace.rankOne_apply,inner_sum,real_inner_smul_right,field,real_inner_comm,mul_comm]
  rw [hc]
  simp only [form,centeredQuadratic,field,inner_add_right,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem memLp_form (s : Finset ι) (d e : ι → E) :
    MemLp (form E s d e) 2 (stdGaussian E) :=
  memLp_finsetSum s (fun i _=>memLp_centeredQuadratic E (d i) (e i))

theorem memLp_form_translate (s : Finset ι) (d e : ι → E) (m : E) :
    MemLp (fun g=>form E s d e (g+m)) 2 (stdGaussian E) := by
  have h := (((memLp_form E s d e).add (memLp_field E (kernel E s d e m))).add
    (memLp_field E (kernel E s e d m))).add (memLp_const ⟪m,kernel E s d e m⟫)
  exact MemLp.ae_eq (Filter.Eventually.of_forall fun g=>(form_translate E s d e m g).symm) h

theorem form_second_moment_le (s : Finset ι) (d e : ι → E)
    (ho : ∀i∈s,∀j∈s,i≠j → ⟪d i,d j⟫=0 ∧ ⟪d i,e j⟫=0) :
    (∫g,form E s d e g^2 ∂stdGaussian E)≤2*kernelSq E s d e := by
  change (∫g,(∑i∈s,centeredQuadratic E (d i) (e i) g)^2 ∂stdGaussian E)≤_
  rw [quadratic_sum_variance E s d e ho]
  simp only [kernelSq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have h := sq_le_sq₀ (abs_nonneg ⟪d i,e i⟫)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr (abs_real_inner_le_norm (d i) (e i))
  simp only [sq_abs,mul_pow] at h
  nlinarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kernel_apply_sq_le (s : Finset ι) (d e : ι → E)
    (ho : ∀i∈s,∀j∈s,i≠j → ⟪d i,d j⟫=0) (m : E) :
    ‖kernel E s d e m‖^2≤kernelSq E s d e*‖m‖^2 :=
  OrthogonalKernels.rankOne_sum_apply_sq_le s d e ho m

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem kernel_pairing_sq_le (s : Finset ι) (d e : ι → E)
    (ho : ∀i∈s,∀j∈s,i≠j → ⟪d i,d j⟫=0) (m : E) :
    ⟪m,kernel E s d e m⟫^2≤kernelSq E s d e*‖m‖^4 := by
  have hh := sq_le_sq₀ (abs_nonneg ⟪m,kernel E s d e m⟫)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr
      (abs_real_inner_le_norm m (kernel E s d e m))
  simp only [sq_abs,mul_pow] at hh
  have hb := mul_le_mul_of_nonneg_left (kernel_apply_sq_le E s d e ho m) (sq_nonneg ‖m‖)
  nlinarith

 

theorem translated_second_moment_le (s : Finset ι) (d e : ι → E)
    (ho : ∀i∈s,∀j∈s,i≠j → ⟪d i,d j⟫=0 ∧ ⟪d i,e j⟫=0)
    (he : ∀i∈s,∀j∈s,i≠j → ⟪e i,e j⟫=0) (m : E) :
    (∫g,form E s d e (g+m)^2 ∂stdGaussian E)≤
      kernelSq E s d e*(8+8*‖m‖^2+4*‖m‖^4) := by
  let A := kernel E s d e m
  let B := kernel E s e d m
  let c := ⟪m,A⟫
  have hQ := (memLp_form E s d e).integrable_sq
  have hA := (memLp_field E A).integrable_sq
  have hB := (memLp_field E B).integrable_sq
  have hC : Integrable (fun _ : E=>c^2) (stdGaussian E) := integrable_const _
  have hb : (∫g,form E s d e (g+m)^2 ∂stdGaussian E)≤
      ∫g,4*(form E s d e g^2+field E A g^2+field E B g^2+c^2) ∂stdGaussian E := by
    apply integral_mono ((memLp_form_translate E s d e m).integrable_sq)
      (((hQ.add hA).add hB).add hC |>.const_mul 4)
    intro g
    dsimp only [Pi.add_apply]
    rw [form_translate]
    change (form E s d e g+field E A g+field E B g+c)^2≤_
    nlinarith [sq_nonneg (form E s d e g-field E A g),
      sq_nonneg (form E s d e g-field E B g),sq_nonneg (form E s d e g-c),
      sq_nonneg (field E A g-field E B g),sq_nonneg (field E A g-c),
      sq_nonneg (field E B g-c)]
  have hInt := integral_add ((hQ.add hA).add hB) hC
  have hInt2 := integral_add (hQ.add hA) hB
  have hInt3 := integral_add hQ hA
  simp only [Pi.add_apply] at hInt hInt2 hInt3
  rw [integral_const_mul,hInt,hInt2,hInt3] at hb
  have haa : (∫g,field E A g^2 ∂stdGaussian E)=‖A‖^2 := by
    simpa only [pow_two,real_inner_self_eq_norm_sq] using field_covariance E A A
  have hbb : (∫g,field E B g^2 ∂stdGaussian E)=‖B‖^2 := by
    simpa only [pow_two,real_inner_self_eq_norm_sq] using field_covariance E B B
  rw [haa,hbb,integral_const,probReal_univ,one_smul] at hb
  have hsm := form_second_moment_le E s d e ho
  have hao := kernel_apply_sq_le E s d e (fun i hi j hj hn=>(ho i hi j hj hn).1) m
  have hbo := kernel_apply_sq_le E s e d he m
  rw [kernelSq_swap] at hbo
  have hco := kernel_pairing_sq_le E s d e (fun i hi j hj hn=>(ho i hi j hj hn).1) m
  dsimp only [A,B,c] at hb
  nlinarith

end ClassicalGaussian.Shifted

 

open scoped BigOperators Topology RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter

namespace GaussianCoherent.Quadratic
variable {κ ι : Type*} [Fintype κ]

abbrev RealMode (κ : Type*) [Fintype κ] := EuclideanSpace ℝ κ

 

theorem coordinate_preserving : MeasurePreserving (WithLp.toLp 2 : (κ → ℝ) → RealMode κ)
    (GaussianFourier.law κ) (stdGaussian (RealMode κ)) := by
  refine ⟨by fun_prop,?_⟩
  exact map_pi_eq_stdGaussian

def symbol (s : Finset ι) (d e : ι → RealMode κ) (g : κ → ℝ) : ℝ :=
  ClassicalGaussian.Shifted.form (RealMode κ) s d e (WithLp.toLp 2 g)

theorem memLp_symbol (s : Finset ι) (d e : ι → RealMode κ) :
    MemLp (symbol s d e) 2 (GaussianFourier.law κ) :=
  (ClassicalGaussian.Shifted.memLp_form (RealMode κ) s d e).comp_measurePreserving
    coordinate_preserving

theorem symbol_second_moment_le (s : Finset ι) (d e : ι → RealMode κ)
    (ho : ∀i∈s,∀j∈s,i≠j → ⟪d i,d j⟫=0 ∧ ⟪d i,e j⟫=0) :
    (∫g,symbol s d e g^2 ∂GaussianFourier.law κ)≤
      2*ClassicalGaussian.Shifted.kernelSq (RealMode κ) s d e := by
  have hl : HasLaw (WithLp.toLp 2 : (κ → ℝ) → RealMode κ)
      (stdGaussian (RealMode κ)) (GaussianFourier.law κ) :=
    ⟨coordinate_preserving.measurable.aemeasurable,coordinate_preserving.map_eq⟩
  have he := hl.integral_comp
    ((ClassicalGaussian.Shifted.memLp_form (RealMode κ) s d e).integrable_sq.aestronglyMeasurable)
  rw [show (∫g,symbol s d e g^2 ∂GaussianFourier.law κ)=
      ∫g,ClassicalGaussian.Shifted.form (RealMode κ) s d e g^2 ∂stdGaussian (RealMode κ) from he]
  exact ClassicalGaussian.Shifted.form_second_moment_le (RealMode κ) s d e ho

 

def unitary (s : Finset ι) (d e : ι → RealMode κ) (t : ℝ) :
    CoherentFock.Space (Mode κ) ≃ₗᵢ[ℂ] CoherentFock.Space (Mode κ) :=
  gaussianUnitary.trans ((ClassicalGaussian.phaseUnitary (GaussianFourier.law κ)
    (memLp_symbol s d e).aestronglyMeasurable t).trans gaussianUnitary.symm)

@[simp] theorem gaussian_unitary_apply (s : Finset ι) (d e : ι → RealMode κ)
    (t : ℝ) (ψ : CoherentFock.Space (Mode κ)) :
    gaussianUnitary (unitary s d e t ψ)=
      ClassicalGaussian.phaseMultiplier (GaussianFourier.law κ)
        (memLp_symbol s d e).aestronglyMeasurable t (gaussianUnitary ψ) := by
  simp only [unitary,LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.apply_symm_apply,
    ClassicalGaussian.phaseUnitary_apply]

 

theorem unitary_coherent_ae (s : Finset ι) (d e : ι → RealMode κ)
    (t : ℝ) (v : Mode κ) :
    (gaussianUnitary (unitary s d e t (CoherentFock.coherent v)) : (κ → ℝ) → ℂ)=ᵐ[GaussianFourier.law κ]
      fun g=>ClassicalGaussian.scalarPhase t (symbol s d e g)*wave v g := by
  rw [gaussian_unitary_apply,gaussianUnitary_coherent]
  filter_upwards [ClassicalGaussian.phaseMultiplier_ae (GaussianFourier.law κ)
    (memLp_symbol s d e).aestronglyMeasurable t (vector v),vector_ae v] with g h1 h2
  rw [h1,h2,smul_eq_mul]

@[simp] theorem unitary_zero (s : Finset ι) (d e : ι → RealMode κ)
    (ψ : CoherentFock.Space (Mode κ)) : unitary s d e 0 ψ=ψ := by
  apply gaussianUnitary.injective
  rw [gaussian_unitary_apply,ClassicalGaussian.phaseMultiplier_zero]

theorem unitary_add (s : Finset ι) (d e : ι → RealMode κ) (t u : ℝ)
    (ψ : CoherentFock.Space (Mode κ)) :
    unitary s d e (t+u) ψ=unitary s d e t (unitary s d e u ψ) := by
  apply gaussianUnitary.injective
  simp only [gaussian_unitary_apply,ClassicalGaussian.phaseMultiplier_add]

 

theorem unitary_tendsto {s : ℕ → Finset ι} {d e : ℕ → ι → RealMode κ}
    (ho : ∀n,∀i∈s n,∀j∈s n,i≠j → ⟪d n i,d n j⟫=0 ∧ ⟪d n i,e n j⟫=0)
    (hk : Tendsto (fun n=>ClassicalGaussian.Shifted.kernelSq (RealMode κ) (s n) (d n) (e n))
      atTop (𝓝 0)) (t : ℝ) (ψ : CoherentFock.Space (Mode κ)) :
    Tendsto (fun n=>unitary (s n) (d n) (e n) t ψ) atTop (𝓝 ψ) := by
  have hq : Tendsto (fun n=>∫g,symbol (s n) (d n) (e n) g^2 ∂GaussianFourier.law κ)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>integral_nonneg fun g=>sq_nonneg _)
      (fun n=>symbol_second_moment_le (s n) (d n) (e n) (ho n))
    simpa only [mul_zero] using hk.const_mul 2
  have hh := ClassicalGaussian.phaseMultiplier_tendsto (GaussianFourier.law κ)
    (fun n=>memLp_symbol (s n) (d n) (e n)) hq t (gaussianUnitary ψ)
  have hh' := gaussianUnitary.symm.continuous.continuousAt.tendsto.comp hh
  simpa only [Function.comp_def,unitary,LinearIsometryEquiv.trans_apply,
    ClassicalGaussian.phaseUnitary_apply,LinearIsometryEquiv.symm_apply_apply] using hh'

end GaussianCoherent.Quadratic

 

open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Complex

namespace GaussianFourier
open scoped _root_.GaussianFourier
variable {κ : Type*} [Fintype κ]

def dot (a g : κ → ℝ) : ℝ := ∑k,a k*g k

theorem integrable_real_exp_dot (a : κ → ℝ) :
    Integrable (fun g=>Real.exp (dot a g)) (law κ) := by
  have h := (integrable_exp_sum (fun k=>(a k:ℂ))).re
  convert h using 1
  funext g
  simp only [dot,←Complex.ofReal_mul,←Complex.ofReal_sum,←Complex.ofReal_exp]
  rfl

theorem integral_real_exp_dot (a : κ → ℝ) :
    (∫g,Real.exp (dot a g) ∂law κ)=Real.exp (∑k,a k^2/2) := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (integral_exp_sum (fun k=>(a k:ℂ)))
  rw [←integral_re (integrable_exp_sum (fun k=>(a k:ℂ)))] at h
  simp only [←Complex.ofReal_mul,←Complex.ofReal_sum,←Complex.ofReal_exp,
    ←Complex.ofReal_pow,←Complex.ofReal_div,←Complex.ofReal_ofNat] at h
  exact h

theorem linear_eq_dot (L : (κ → ℝ) →L[ℝ] ℝ) :
    ∃a : κ → ℝ,∀g,L g=dot a g := by
  classical
  refine ⟨fun k=>L (Pi.single k 1),fun g=>?_⟩
  have hg : g=∑k,g k • Pi.single k (1:ℝ) := by
    funext j
    simp [Pi.single_apply]
  conv_lhs => rw [hg,map_sum]
  simp only [map_smul,smul_eq_mul,dot]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm]

theorem charFunDual_eq_dot (L : (κ → ℝ) →L[ℝ] ℝ) (b : κ → ℝ)
    (hb : ∀g,L g=dot b g) :
    charFunDual (law κ) L=Complex.exp (∑k,((b k:ℂ)*I)^2/2) := by
  rw [charFunDual_apply]
  convert integral_exp_sum (fun k=>(b k:ℂ)*I) using 1
  congr 1
  funext g
  congr 1
  rw [hb]
  simp only [dot,Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

 

theorem tilted_dot_eq_map_add (a : κ → ℝ) :
    (law κ).tilted (dot a)=(law κ).map (fun g=>g+a) := by
  have := isProbabilityMeasure_tilted (integrable_real_exp_dot a)
  apply Measure.ext_of_charFunDual
  funext L
  obtain ⟨b,hb⟩ := linear_eq_dot L
  rw [charFunDual_map_add_const,charFunDual_eq_dot L b hb,hb]
  rw [charFunDual_apply,integral_tilted,integral_real_exp_dot]
  have hp (g : κ → ℝ) :
      (Real.exp (dot a g)/Real.exp (∑k,a k^2/2)) • Complex.exp ((L g:ℂ)*I)=
        Complex.exp (-((∑k,a k^2/2:ℝ):ℂ))*
          Complex.exp (∑k,((a k:ℂ)+(b k:ℂ)*I)*(g k:ℂ)) := by
    rw [←Real.exp_sub,Complex.real_smul,Complex.ofReal_exp]
    simp only [←Complex.exp_add]
    rw [hb]
    congr 1
    simp only [Complex.ofReal_sub,Complex.ofReal_sum,Complex.ofReal_mul,dot,
      Finset.sum_mul,Finset.sum_add_distrib,add_mul]
    simp only [mul_comm,mul_left_comm]
    ring
  simp_rw [hp]
  rw [integral_const_mul,integral_exp_sum,←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [dot,Complex.ofReal_sum,Complex.ofReal_mul,←Finset.sum_neg_distrib,
    ←Finset.sum_add_distrib,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  ring

 

theorem integral_exp_dot_mul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : κ → ℝ) (f : (κ → ℝ) → F)
    (hf : AEStronglyMeasurable f ((law κ).map (fun g=>g+a))) :
    (∫g,Real.exp (dot a g-∑k,a k^2/2) • f g ∂law κ)=
      ∫g,f (g+a) ∂law κ := by
  calc
    _=∫g,f g ∂(law κ).tilted (dot a) := by
      rw [integral_tilted,integral_real_exp_dot]
      simp only [Real.exp_sub]
    _=∫g,f g ∂(law κ).map (fun g=>g+a) := by rw [tilted_dot_eq_map_add]
    _=_ := by rw [integral_map (by fun_prop) hf]

end GaussianFourier

 

open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open MeasureTheory ProbabilityTheory Complex

namespace GaussianCoherent
variable {κ : Type*} [Fintype κ]

 
def realShift (v : Mode κ) : κ → ℝ := fun k=> -2*(v k).im

theorem realShift_complex (v : Mode κ) (k : κ) :
    I*(v k-conj (v k))=(realShift v k:ℂ) := by
  apply Complex.ext <;> simp [realShift,Complex.mul_re,Complex.mul_im]; ring

theorem offset_shift (v : Mode κ) :
    conj (offset v)+offset v= -((∑k,realShift v k^2/2:ℝ):ℂ) := by
  have h := exponent_pair v v
  simp_rw [realShift_complex] at h
  rw [inner_self_eq_norm_sq_to_K] at h
  push_cast at h ⊢
  linear_combination h

 

theorem norm_wave_sq (v : Mode κ) (g : κ → ℝ) :
    ‖wave v g‖^2=Real.exp (GaussianFourier.dot (realShift v) g-
      ∑k,realShift v k^2/2) := by
  have h := wave_pair v v g
  rw [offset_shift] at h
  simp_rw [realShift_complex] at h
  rw [←Complex.exp_add] at h
  have hx : -((∑k,realShift v k^2/2:ℝ):ℂ)+
      (∑k,(realShift v k:ℂ)*(g k:ℂ))=
      ((GaussianFourier.dot (realShift v) g-∑k,realShift v k^2/2:ℝ):ℂ) := by
    unfold GaussianFourier.dot
    push_cast
    ring
  rw [hx,←Complex.ofReal_exp,Complex.conj_mul'] at h
  have hh := congrArg Complex.re h
  simpa only [←Complex.ofReal_pow,Complex.ofReal_re] using hh

theorem coherent_tilt_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : Mode κ) (f : (κ → ℝ) → F)
    (hf : AEStronglyMeasurable f ((GaussianFourier.law κ).map (fun g=>g+realShift v))) :
    (∫g,‖wave v g‖^2 • f g ∂GaussianFourier.law κ)=
      ∫g,f (g+realShift v) ∂GaussianFourier.law κ := by
  simp_rw [norm_wave_sq]
  exact GaussianFourier.integral_exp_dot_mul _ _ hf

end GaussianCoherent

 

open scoped BigOperators Topology RealInnerProductSpace
open MeasureTheory ProbabilityTheory Filter

namespace GaussianCoherent.Quadratic
variable {κ ι : Type*} [Fintype κ]

theorem continuous_symbol (s : Finset ι) (d e : ι → RealMode κ) :
    Continuous (symbol s d e) := by
  unfold symbol ClassicalGaussian.Shifted.form ClassicalGaussian.centeredQuadratic
    ClassicalGaussian.field
  fun_prop

theorem memLp_symbol_translate (s : Finset ι) (d e : ι → RealMode κ) (m : κ → ℝ) :
    MemLp (fun g=>symbol s d e (g+m)) 2 (GaussianFourier.law κ) := by
  simpa only [symbol,WithLp.toLp_add,Function.comp_def] using
    (ClassicalGaussian.Shifted.memLp_form_translate (RealMode κ) s d e (WithLp.toLp 2 m)).comp_measurePreserving
      coordinate_preserving

theorem translated_symbol_second_moment_le (s : Finset ι) (d e : ι → RealMode κ)
    (ho : ∀i∈s,∀j∈s,i≠j → ⟪d i,d j⟫=0 ∧ ⟪d i,e j⟫=0)
    (he : ∀i∈s,∀j∈s,i≠j → ⟪e i,e j⟫=0) (m : κ → ℝ) :
    (∫g,symbol s d e (g+m)^2 ∂GaussianFourier.law κ)≤
      ClassicalGaussian.Shifted.kernelSq (RealMode κ) s d e*
        (8+8*‖WithLp.toLp 2 m‖^2+4*‖WithLp.toLp 2 m‖^4) := by
  have hl : HasLaw (WithLp.toLp 2 : (κ → ℝ) → RealMode κ)
      (stdGaussian (RealMode κ)) (GaussianFourier.law κ) :=
    ⟨coordinate_preserving.measurable.aemeasurable,coordinate_preserving.map_eq⟩
  have hh := hl.integral_comp
    ((ClassicalGaussian.Shifted.memLp_form_translate (RealMode κ) s d e (WithLp.toLp 2 m)).integrable_sq.aestronglyMeasurable)
  calc
    _=∫g,ClassicalGaussian.Shifted.form (RealMode κ) s d e (g+WithLp.toLp 2 m)^2 ∂stdGaussian (RealMode κ) := by
      simpa only [symbol,WithLp.toLp_add,Function.comp_def] using hh
    _≤_ := ClassicalGaussian.Shifted.translated_second_moment_le (RealMode κ) s d e ho he _

 

theorem coherent_error_integral (s : Finset ι) (d e : ι → RealMode κ)
    (t : ℝ) (v : Mode κ) :
    ‖unitary s d e t (CoherentFock.coherent v)-CoherentFock.coherent v‖^2=
      ∫g,ClassicalGaussian.phaseError t (symbol s d e (g+realShift v)) ∂GaussianFourier.law κ := by
  have hn := gaussianUnitary.norm_map
    (unitary s d e t (CoherentFock.coherent v)-CoherentFock.coherent v)
  rw [map_sub,gaussian_unitary_apply,gaussianUnitary_coherent] at hn
  rw [←hn,ClassicalGaussian.L2_norm_sq_integral]
  calc
    _=∫g,‖wave v g‖^2 • ClassicalGaussian.phaseError t (symbol s d e g) ∂GaussianFourier.law κ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub
          (ClassicalGaussian.phaseMultiplier (GaussianFourier.law κ)
            (memLp_symbol s d e).aestronglyMeasurable t (vector v)) (vector v),
        ClassicalGaussian.phaseMultiplier_ae (GaussianFourier.law κ)
          (memLp_symbol s d e).aestronglyMeasurable t (vector v),vector_ae v] with g h1 h2 h3
      simp only [Pi.sub_apply] at h1
      rw [h1,h2,h3,smul_eq_mul]
      rw [show ClassicalGaussian.scalarPhase t (symbol s d e g)*wave v g-wave v g=
        (ClassicalGaussian.scalarPhase t (symbol s d e g)-1)*wave v g by ring]
      rw [norm_mul,mul_pow,smul_eq_mul]
      exact mul_comm _ _
    _=_ := coherent_tilt_integral v _
      ((ClassicalGaussian.continuous_phaseError t).comp (continuous_symbol s d e)).aestronglyMeasurable

 

theorem coherent_error_sq_le (s : Finset ι) (d e : ι → RealMode κ)
    (ho : ∀i∈s,∀j∈s,i≠j → ⟪d i,d j⟫=0 ∧ ⟪d i,e j⟫=0)
    (he : ∀i∈s,∀j∈s,i≠j → ⟪e i,e j⟫=0) (t : ℝ) (v : Mode κ) :
    ‖unitary s d e t (CoherentFock.coherent v)-CoherentFock.coherent v‖^2≤
      t^2*ClassicalGaussian.Shifted.kernelSq (RealMode κ) s d e*
       (8+8*‖WithLp.toLp 2 (realShift v)‖^2+4*‖WithLp.toLp 2 (realShift v)‖^4) := by
  rw [coherent_error_integral]
  calc
    _≤t^2*∫g,symbol s d e (g+realShift v)^2 ∂GaussianFourier.law κ :=
      ClassicalGaussian.integral_phaseError_le (GaussianFourier.law κ)
        (memLp_symbol_translate s d e (realShift v)) t
    _≤_ := by
      have h := mul_le_mul_of_nonneg_left
        (translated_symbol_second_moment_le s d e ho he (realShift v)) (sq_nonneg t)
      simpa only [mul_assoc] using h

end GaussianCoherent.Quadratic

end

end OAI
