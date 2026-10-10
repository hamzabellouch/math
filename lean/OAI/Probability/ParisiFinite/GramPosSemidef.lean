import Mathlib

namespace OAI

/-! Gram Pos Semidef. -/

noncomputable section

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped Topology
open Filter
open scoped BigOperators Matrix
open scoped Matrix Matrix.Norms.L2Operator
open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter

namespace CoherentFock
variable {ι : Type*} {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem gram_posSemidef (v : ι → E) :
    (Matrix.of (fun i j => ⟪v i, v j⟫_ℂ)).PosSemidef := by
  refine ⟨?_, fun c => ?_⟩
  · ext i j
    change conj ⟪v j,v i⟫_ℂ = ⟪v i,v j⟫_ℂ
    exact inner_conj_symm _ _
  · have he : c.sum (fun i a => c.sum fun j b => star a * ⟪v i,v j⟫_ℂ * b) =
        ⟪c.sum (fun i a => a • v i), c.sum (fun i a => a • v i)⟫_ℂ := by
      rw [Finsupp.sum_inner]
      apply Finsupp.sum_congr
      intro i hi
      rw [Finsupp.inner_sum]
      apply Finsupp.sum_congr
      intro j hj
      simp only [inner_smul_left,inner_smul_right,Complex.star_def]
      ring
    change 0 ≤ c.sum (fun i a => c.sum fun j b => star a * ⟪v i,v j⟫_ℂ * b)
    rw [he]
    exact RCLike.nonneg_iff.mpr ⟨inner_self_nonneg,inner_self_im _⟩

theorem ones_posSemidef : (Matrix.of (fun _ _ : ι => (1 : ℂ))).PosSemidef := by
  simpa using (gram_posSemidef (fun _ : ι => (1 : ℂ)))

theorem entry_pow_posSemidef {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (n : ℕ) :
    (Matrix.of (fun i j => M i j ^ n)).PosSemidef := by
  induction n with
  | zero => simpa using (ones_posSemidef (ι := ι))
  | succ n ih =>
    have hh : ((Matrix.of (fun i j => M i j ^ n)).hadamard M).PosSemidef := ih.hadamard hM
    convert! hh using 1

theorem entry_exp_posSemidef {M : Matrix ι ι ℂ} (hM : M.PosSemidef) :
    (Matrix.of (fun i j => Complex.exp (M i j))).PosSemidef := by
  have hp (N : ℕ) : (Matrix.of (fun i j => ∑ k ∈ Finset.range N,
      (k.factorial : ℝ)⁻¹ • M i j ^ k)).PosSemidef := by
    induction N with
    | zero =>
      convert! (Matrix.PosSemidef.zero (n := ι) (R := ℂ)) using 1
    | succ N ih =>
      convert!
        ih.add ((entry_pow_posSemidef hM N).smul (by positivity : (0:ℝ) ≤ (N.factorial : ℝ)⁻¹)) using 1
      ext i j
      simp [Finset.sum_range_succ]
  have ht (i j : ι) : Tendsto (fun N => ∑ k ∈ Finset.range N,
      (k.factorial : ℝ)⁻¹ • M i j ^ k) atTop (𝓝 (Complex.exp (M i j))) := by
    simpa [Complex.exp_eq_exp_ℂ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (M i j)).tendsto_sum_nat
  refine ⟨?_,fun c => ?_⟩
  · ext i j
    change conj (Complex.exp (M j i)) = Complex.exp (M i j)
    rw [← Complex.exp_conj]
    congr 1
    exact congrFun (congrFun hM.isHermitian i) j
  · have hc : Tendsto (fun N => c.sum fun i a => c.sum fun j b =>
        star a * (∑ k ∈ Finset.range N, (k.factorial : ℝ)⁻¹ • M i j ^ k) * b)
        atTop (𝓝 (c.sum fun i a => c.sum fun j b => star a * Complex.exp (M i j) * b)) := by
      apply tendsto_finsetSum
      intro i hi
      apply tendsto_finsetSum
      intro j hj
      exact (tendsto_const_nhds.mul (ht i j)).mul tendsto_const_nhds
    rw [Complex.nonneg_iff]
    constructor
    · exact ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp hc)
        (.of_forall fun N => (Complex.nonneg_iff.mp ((hp N).2 c)).1)
    · have hz : Tendsto (fun N => (c.sum fun i a => c.sum fun j b =>
          star a * (∑ k ∈ Finset.range N, (k.factorial : ℝ)⁻¹ • M i j ^ k) * b).im)
          atTop (𝓝 (0 : ℝ)) := by
        convert! tendsto_const_nhds using 1
        funext N
        exact (Complex.nonneg_iff.mp ((hp N).2 c)).2.symm
      exact (tendsto_nhds_unique hz (Complex.continuous_im.tendsto _ |>.comp hc))

 
def kernel (d e : E) : ℂ :=
  Complex.exp ((-(‖d‖^2 : ℝ)/2 : ℝ) + ⟪d,e⟫_ℂ + (-(‖e‖^2 : ℝ)/2 : ℝ))

theorem kernel_posSemidef : (Matrix.of (kernel (E := E))).PosSemidef := by
  let v : E → E := id
  have h := entry_exp_posSemidef (gram_posSemidef v)
  let w : E → ℂ := fun d => Complex.exp ((-(‖d‖^2 : ℝ)/2 : ℝ) : ℂ)
  have hw := gram_posSemidef w
  have hh : (Matrix.hadamard (Matrix.of fun i j => ⟪w i,w j⟫_ℂ)
    (Matrix.of fun i j => Complex.exp ⟪v i,v j⟫_ℂ)).PosSemidef := hw.hadamard h
  convert! hh using 1
  ext d e
  simp only [kernel,w,v,Matrix.hadamard_apply,Matrix.of_apply,RCLike.inner_apply',
    ← Complex.exp_conj,← Complex.exp_add,Complex.conj_ofReal,id_eq]
  congr 1
  ring

def PreSpace (E : Type*) := E →₀ ℂ
instance : AddCommGroup (PreSpace E) := inferInstanceAs (AddCommGroup (E →₀ ℂ))
instance : Module ℂ (PreSpace E) := inferInstanceAs (Module ℂ (E →₀ ℂ))

def toFinsupp : PreSpace E ≃ₗ[ℂ] (E →₀ ℂ) := LinearEquiv.refl ℂ _

 

abbrev core : PreInnerProductSpace.Core ℂ (PreSpace E) where
  inner x y := (toFinsupp x).sum fun d a => (toFinsupp y).sum fun e b =>
    conj a * kernel d e * b
  conj_inner_symm x y := by
    classical
    simp only [Finsupp.sum,map_sum, map_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    have hk := congrFun (congrFun (kernel_posSemidef (E := E)).isHermitian d) e
    simp only [Matrix.conjTranspose_apply,Matrix.of_apply,Complex.star_def] at hk
    simp only [Complex.conj_conj]
    rw [hk]
    ring
  re_inner_nonneg x := (Complex.nonneg_iff.mp ((kernel_posSemidef (E := E)).2 (toFinsupp x))).1
  add_left x y z := by
    classical
    simp [map_add,Finsupp.sum_add_index, add_mul,Finsupp.sum_add]
  smul_left x y r := by
    classical
    simp [map_smul,Finsupp.sum_smul_index,map_mul,mul_assoc,Finsupp.mul_sum]

instance : SeminormedAddCommGroup (PreSpace E) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := core (E := E))
instance : InnerProductSpace ℂ (PreSpace E) := InnerProductSpace.ofCore (core (E := E))

abbrev Space (E : Type*) [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] :=
  UniformSpace.Completion (PreSpace E)

def coherent (d : E) : Space E :=
  ↑(toFinsupp.symm (Finsupp.single d 1) : PreSpace E)

@[simp] theorem inner_coherent (d e : E) :
    ⟪coherent d, coherent e⟫_ℂ = kernel d e := by
  classical
  rw [coherent,coherent,UniformSpace.Completion.inner_coe]
  change (Finsupp.single d (1:ℂ)).sum (fun d a =>
    (Finsupp.single e (1:ℂ)).sum fun e b => conj a * kernel d e * b) = _
  simp

@[simp] theorem kernel_self (d : E) : kernel d d = 1 := by
  unfold kernel
  rw [inner_self_eq_norm_sq_to_K]
  convert! Complex.exp_zero using 1
  congr 1
  push_cast
  ring!

@[simp] theorem norm_coherent (d : E) : ‖coherent d‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),inner_coherent,kernel_self]
  norm_num

theorem kernel_eq (d e : E) : kernel d e =
    Complex.exp (((-‖d-e‖^2/2 : ℝ) : ℂ) + ((⟪d,e⟫_ℂ).im : ℂ) * Complex.I) := by
  unfold kernel
  congr 1
  apply Complex.ext
  · simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero]
    rw [norm_sub_sq (𝕜 := ℂ)]
    change _ = -(‖d‖^2 - 2*(⟪d,e⟫_ℂ).re+‖e‖^2)/2+0
    ring
  · simp only [Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,mul_one,zero_add,add_zero]

theorem norm_kernel (d e : E) : ‖kernel d e‖ = Real.exp (-‖d-e‖^2/2) := by
  rw [kernel_eq,Complex.norm_exp]
  congr 1
  simp only [Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]

def phase (d e : E) : ℂ := Complex.exp ((-(⟪d,e⟫_ℂ).im : ℝ) * Complex.I)

@[simp] theorem norm_phase (d e : E) : ‖phase d e‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

@[simp] theorem phase_zero_left (e : E) : phase 0 e = 1 := by simp [phase]
@[simp] theorem phase_zero_right (d : E) : phase d 0 = 1 := by simp [phase]

 
theorem phase_cocycle (d e f : E) :
    phase e f * phase d (e+f) = phase d e * phase (d+e) f := by
  simp only [phase,← Complex.exp_add,inner_add_left,inner_add_right,Complex.add_im]
  congr 1
  push_cast
  ring

theorem kernel_translate (d e f : E) :
    conj (phase d e) * kernel (d+e) (d+f) * phase d f = kernel e f := by
  simp only [phase,kernel,← Complex.exp_conj,← Complex.exp_add]
  congr 1
  have hdd : ⟪d,d⟫_ℂ = ((‖d‖^2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp only [inner_add_left,inner_add_right,hdd]
  apply Complex.ext
  · simp only [Complex.add_re,Complex.mul_re,Complex.conj_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero]
    rw [norm_add_sq (𝕜 := ℂ),norm_add_sq (𝕜 := ℂ)]
    have hs := inner_re_symm (𝕜 := ℂ) d e
    change (⟪d,e⟫_ℂ).re = (⟪e,d⟫_ℂ).re at hs
    dsimp only [RCLike.re_to_complex] at *
    linarith
  · simp only [Complex.add_im,Complex.mul_im,Complex.conj_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add]
    have hs := inner_im_symm (𝕜 := ℂ) d e
    change (⟪d,e⟫_ℂ).im = -(⟪e,d⟫_ℂ).im at hs
    linarith

 
def basis (e : E) : PreSpace E := toFinsupp.symm (Finsupp.single e 1)

@[simp] theorem inner_basis (d e : E) : ⟪basis d,basis e⟫_ℂ = kernel d e := by
  classical
  change (Finsupp.single d (1:ℂ)).sum (fun d a =>
    (Finsupp.single e (1:ℂ)).sum fun e b => conj a * kernel d e * b) = _
  simp

@[simp] theorem coe_basis (e : E) : (↑(basis e) : Space E) = coherent e := rfl

def preWLinear (d : E) : PreSpace E →ₗ[ℂ] PreSpace E :=
  (Finsupp.linearCombination ℂ fun e => phase d e • basis (d+e)).comp toFinsupp.toLinearMap

@[simp] theorem preWLinear_basis (d e : E) :
    preWLinear d (basis e) = phase d e • basis (d+e) := by
  classical
  simp [preWLinear,basis]

theorem inner_preW (d : E) (x y : PreSpace E) :
    ⟪preWLinear d x,preWLinear d y⟫_ℂ = ⟪x,y⟫_ℂ := by
  classical
  change ⟪(toFinsupp x).sum (fun e a => a • phase d e • basis (d+e)),
    (toFinsupp y).sum (fun f b => b • phase d f • basis (d+f))⟫_ℂ =
    (toFinsupp x).sum (fun e a => (toFinsupp y).sum fun f b => conj a * kernel e f * b)
  rw [Finsupp.sum_inner]
  apply Finsupp.sum_congr
  intro e he
  rw [Finsupp.inner_sum]
  apply Finsupp.sum_congr
  intro f hf
  simp only [inner_smul_left,inner_smul_right,inner_basis]
  calc
    _ = conj ((toFinsupp x) e) *
        (conj (phase d e) * kernel (d+e) (d+f) * phase d f) * (toFinsupp y) f := by ring
    _ = _ := by rw [kernel_translate]

def preW (d : E) : PreSpace E →ₗᵢ[ℂ] PreSpace E where
  toLinearMap := preWLinear d
  norm_map' x := by rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),inner_preW,
    ← norm_eq_sqrt_re_inner (𝕜 := ℂ)]

 
def W (d : E) : Space E →L[ℂ] Space E := (preW d).toContinuousLinearMap.completion

@[simp] theorem W_coe (d : E) (x : PreSpace E) : W d ↑x = ↑(preWLinear d x) :=
  ContinuousLinearMap.completion_apply_coe _ _

@[simp] theorem W_coherent (d e : E) : W d (coherent e) = phase d e • coherent (d+e) := by
  rw [← coe_basis,W_coe,preWLinear_basis,UniformSpace.Completion.coe_smul,coe_basis]

@[simp] theorem norm_W (d : E) (x : Space E) : ‖W d x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq ((W d).continuous.norm) continuous_norm) fun y => ?_
  rw [W_coe,UniformSpace.Completion.norm_coe,UniformSpace.Completion.norm_coe]
  exact (preW d).norm_map y

theorem inner_W (d : E) (x y : Space E) : ⟪W d x,W d y⟫_ℂ = ⟪x,y⟫_ℂ := by
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq (((W d).continuous.comp continuous_fst).inner
      ((W d).continuous.comp continuous_snd)) (continuous_fst.inner continuous_snd)) ?_
  intro x y
  rw [W_coe,W_coe,UniformSpace.Completion.inner_coe,
    UniformSpace.Completion.inner_coe,inner_preW]

omit [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] in
 
theorem sum_basis (x : PreSpace E) :
    (toFinsupp x).sum (fun e a => a • basis e) = x := by
  classical
  apply toFinsupp.injective
  simp only [Finsupp.sum,map_sum,map_smul,basis,LinearEquiv.apply_symm_apply,
    Finsupp.smul_single,smul_eq_mul,mul_one]
  exact Finsupp.sum_single _

 
theorem ext_coherent {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {A B : Space E →L[ℂ] F} (h : ∀ e, A (coherent e) = B (coherent e)) : A = B := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq A.continuous B.continuous) fun y => ?_
  rw [← sum_basis y]
  change (A.comp UniformSpace.Completion.toComplL) _ =
    (B.comp UniformSpace.Completion.toComplL) _
  simp only [Finsupp.sum,map_sum,map_smul,ContinuousLinearMap.comp_apply,
    UniformSpace.Completion.coe_toComplL,coe_basis]
  apply Finset.sum_congr rfl
  intro e he
  rw [h]

@[simp] theorem W_zero : W (0 : E) = ContinuousLinearMap.id ℂ (Space E) := by
  apply ext_coherent
  intro e
  simp

 
theorem W_mul (d e : E) : (W d).comp (W e) = phase d e • W (d+e) := by
  apply ext_coherent
  intro f
  simp only [ContinuousLinearMap.comp_apply,W_coherent,map_smul,
    smul_apply,smul_smul,phase_cocycle,add_assoc]

@[simp] theorem phase_neg_left (d : E) : phase (-d) d = 1 := by
  have h : (⟪d,d⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) d
  simp only [phase,inner_neg_left,Complex.neg_im,h,neg_zero,
    Complex.ofReal_zero,zero_mul,Complex.exp_zero]

@[simp] theorem phase_neg_right (d : E) : phase d (-d) = 1 := by
  have h : (⟪d,d⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) d
  simp only [phase,inner_neg_right,Complex.neg_im,h,neg_zero,
    Complex.ofReal_zero,zero_mul,Complex.exp_zero]

 
def weyl (d : E) : Space E ≃ₗᵢ[ℂ] Space E where
  toFun := W d
  invFun := W (-d)
  left_inv x := by
    have h := congrArg (fun A : Space E →L[ℂ] Space E => A x) (W_mul (-d) d)
    simpa using h
  right_inv x := by
    have h := congrArg (fun A : Space E →L[ℂ] Space E => A x) (W_mul d (-d))
    simpa using h
  map_add' := (W d).map_add
  map_smul' := (W d).map_smul
  norm_map' := norm_W d

@[simp] theorem weyl_apply (d : E) (x : Space E) : weyl d x = W d x := rfl

 
theorem norm_inner_translated_coherent (d e x y : E) :
    ‖⟪W d (coherent x),W e (coherent y)⟫_ℂ‖ = Real.exp (-‖(d+x)-(e+y)‖^2/2) := by
  simp only [W_coherent,inner_smul_left,inner_smul_right,inner_coherent,
    norm_mul,RCLike.norm_conj,norm_phase,one_mul,norm_kernel]

 theorem continuous_kernel : Continuous (fun x : E × E => kernel x.1 x.2) := by
  unfold kernel
  fun_prop

 theorem continuous_phase : Continuous (fun x : E × E => phase x.1 x.2) := by
  unfold phase
  fun_prop

 theorem norm_sub_coherent (d e : E) :
    ‖coherent d - coherent e‖ = Real.sqrt (2-2*(kernel d e).re) := by
  rw [← Real.sqrt_sq (norm_nonneg (coherent d-coherent e)),norm_sub_sq (𝕜 := ℂ),
    norm_coherent,norm_coherent,inner_coherent]
  congr 1
  change (1:ℝ)^2 - 2*(kernel d e).re + 1^2 = 2 - 2*(kernel d e).re
  ring

 theorem continuous_coherent : Continuous (coherent (E := E)) := by
  rw [continuous_iff_continuousAt]
  intro d
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [norm_sub_coherent]
  have h : Continuous (fun x : E => kernel x d) :=
    continuous_kernel.comp (continuous_id.prodMk continuous_const)
  have hs : Continuous (fun x : E => Real.sqrt (2-2*(kernel x d).re)) := by
    fun_prop
  simpa using hs.tendsto d

section SecondQuantization
variable {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace ℂ E']

 
def preGammaLinear (T : E →ₗᵢ[ℂ] E') : PreSpace E →ₗ[ℂ] PreSpace E' :=
  (Finsupp.linearCombination ℂ fun e => basis (T e)).comp toFinsupp.toLinearMap

@[simp] theorem preGammaLinear_basis (T : E →ₗᵢ[ℂ] E') (e : E) :
    preGammaLinear T (basis e) = basis (T e) := by
  classical
  simp [preGammaLinear,basis]

@[simp] theorem kernel_map (T : E →ₗᵢ[ℂ] E') (d e : E) : kernel (T d) (T e) = kernel d e := by
  simp [kernel]

@[simp] theorem phase_map (T : E →ₗᵢ[ℂ] E') (d e : E) : phase (T d) (T e) = phase d e := by
  simp [phase]

theorem inner_preGamma (T : E →ₗᵢ[ℂ] E') (x y : PreSpace E) :
    ⟪preGammaLinear T x,preGammaLinear T y⟫_ℂ = ⟪x,y⟫_ℂ := by
  classical
  change ⟪(toFinsupp x).sum (fun e a => a • basis (T e)),
    (toFinsupp y).sum (fun f b => b • basis (T f))⟫_ℂ =
    (toFinsupp x).sum (fun e a => (toFinsupp y).sum fun f b => conj a * kernel e f * b)
  rw [Finsupp.sum_inner]
  apply Finsupp.sum_congr
  intro e he
  rw [Finsupp.inner_sum]
  apply Finsupp.sum_congr
  intro f hf
  simp only [inner_smul_left,inner_smul_right,inner_basis,kernel_map]
  ring

def preGamma (T : E →ₗᵢ[ℂ] E') : PreSpace E →ₗᵢ[ℂ] PreSpace E' where
  toLinearMap := preGammaLinear T
  norm_map' x := by rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),inner_preGamma,
    ← norm_eq_sqrt_re_inner (𝕜 := ℂ)]

def Gamma (T : E →ₗᵢ[ℂ] E') : Space E →L[ℂ] Space E' :=
  (preGamma T).toContinuousLinearMap.completion

@[simp] theorem Gamma_coe (T : E →ₗᵢ[ℂ] E') (x : PreSpace E) :
    Gamma T ↑x = ↑(preGammaLinear T x) := ContinuousLinearMap.completion_apply_coe _ _

@[simp] theorem Gamma_coherent (T : E →ₗᵢ[ℂ] E') (e : E) :
    Gamma T (coherent e) = coherent (T e) := by
  rw [← coe_basis,Gamma_coe,preGammaLinear_basis,coe_basis]

@[simp] theorem norm_Gamma (T : E →ₗᵢ[ℂ] E') (x : Space E) : ‖Gamma T x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq ((Gamma T).continuous.norm) continuous_norm) fun y => ?_
  rw [Gamma_coe,UniformSpace.Completion.norm_coe,UniformSpace.Completion.norm_coe]
  exact (preGamma T).norm_map y

 
theorem Gamma_W (T : E →ₗᵢ[ℂ] E') (d : E) :
    (Gamma T).comp (W d) = (W (T d)).comp (Gamma T) := by
  apply ext_coherent
  intro e
  simp only [ContinuousLinearMap.comp_apply,W_coherent,Gamma_coherent,map_smul,
    phase_map,map_add]

end SecondQuantization

@[simp] theorem Gamma_id : Gamma ((LinearIsometry.id : E →ₗᵢ[ℂ] E)) = ContinuousLinearMap.id ℂ (Space E) := by
  apply ext_coherent
  intro e
  simp

theorem Gamma_comp {E' E'' : Type*}
    [SeminormedAddCommGroup E'] [InnerProductSpace ℂ E']
    [SeminormedAddCommGroup E''] [InnerProductSpace ℂ E'']
    (T : E →ₗᵢ[ℂ] E') (S : E' →ₗᵢ[ℂ] E'') :
    (Gamma S).comp (Gamma T) = Gamma (S.comp T) := by
  apply ext_coherent
  intro e
  simp

 
def secondQuantization {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace ℂ E']
    (T : E ≃ₗᵢ[ℂ] E') : Space E ≃ₗᵢ[ℂ] Space E' where
  toFun := Gamma T.toLinearIsometry
  invFun := Gamma T.symm.toLinearIsometry
  left_inv x := by
    have h := congrArg (fun A : Space E →L[ℂ] Space E => A x)
      (Gamma_comp T.toLinearIsometry T.symm.toLinearIsometry)
    have hc : T.symm.toLinearIsometry.comp T.toLinearIsometry = (LinearIsometry.id : E →ₗᵢ[ℂ] E) := by
      ext e
      simp
    simpa [hc] using h
  right_inv x := by
    have h := congrArg (fun A : Space E' →L[ℂ] Space E' => A x)
      (Gamma_comp T.symm.toLinearIsometry T.toLinearIsometry)
    have hc : T.toLinearIsometry.comp T.symm.toLinearIsometry = (LinearIsometry.id : E' →ₗᵢ[ℂ] E') := by
      ext e
      simp
    simpa [hc] using h
  map_add' := (Gamma T.toLinearIsometry).map_add
  map_smul' := (Gamma T.toLinearIsometry).map_smul
  norm_map' := norm_Gamma T.toLinearIsometry

 
theorem coe_eq_sum (x : PreSpace E) : (↑x : Space E) =
    (toFinsupp x).sum (fun e a => a • coherent e) := by
  classical
  have h := congrArg (UniformSpace.Completion.toComplL : PreSpace E →L[ℂ] Space E)
    (sum_basis x)
  simpa only [Finsupp.sum,map_sum,map_smul,UniformSpace.Completion.coe_toComplL,coe_basis]
    using h.symm

theorem tendsto_norm_separated (d e x y : E) (hne : 0 < ‖d-e‖) :
    Tendsto (fun r : ℝ => ‖(r • d+x)-(r • e+y)‖) atTop atTop := by
  have h : Tendsto (fun r : ℝ => ‖d-e‖*r-‖x-y‖) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop ((b+‖x-y‖)/‖d-e‖)] with r hr
    have hh := (div_le_iff₀ hne).mp hr
    linarith
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
  have hl := norm_sub_norm_le (r • (d-e)) (-(x-y))
  simp only [norm_smul,Real.norm_of_nonneg hr,norm_neg,sub_neg_eq_add] at hl
  have heq : r • (d-e)+(x-y) = (r • d+x)-(r • e+y) := by module
  rw [heq] at hl
  simpa only [mul_comm] using hl

 
theorem tendsto_inner_translated_coherent (d e x y : E) (hne : 0 < ‖d-e‖) :
    Tendsto (fun r : ℝ => ⟪W (r • d) (coherent x),W (r • e) (coherent y)⟫_ℂ)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_inner_translated_coherent]
  have ht := (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp
    (tendsto_norm_separated d e x y hne)
  have hh := ht.const_mul_atTop (by positivity : (0:ℝ) < (2:ℝ)⁻¹)
  convert! Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hh) using 1
  funext r
  congr 1
  dsimp only [Function.comp_def]
  ring

 
theorem tendsto_inner_translated_pre (d e : E) (hne : 0 < ‖d-e‖) (x y : PreSpace E) :
    Tendsto (fun r : ℝ => ⟪W (r • d) (↑x),W (r • e) (↑y)⟫_ℂ) atTop (𝓝 0) := by
  classical
  simp_rw [coe_eq_sum,Finsupp.sum,map_sum,map_smul,sum_inner,inner_sum,
    inner_smul_left,inner_smul_right]
  convert! (tendsto_finsetSum (toFinsupp x).support fun a ha =>
    tendsto_finsetSum (toFinsupp y).support fun b hb =>
      tendsto_const_nhds.mul (tendsto_const_nhds.mul
        (tendsto_inner_translated_coherent d e a b hne))) using 1
  simp

 
theorem inner_translate_approx (d e : E) (x x' y y' : Space E) :
    ‖⟪W d x,W e y⟫_ℂ‖ ≤ ‖x-x'‖ * ‖y‖ + ‖x'‖ * ‖y-y'‖ + ‖⟪W d x',W e y'⟫_ℂ‖ := by
  have heq : ⟪W d x,W e y⟫_ℂ =
      ⟪W d (x-x'),W e y⟫_ℂ + ⟪W d x',W e (y-y')⟫_ℂ + ⟪W d x',W e y'⟫_ℂ := by
    simp only [map_sub,inner_sub_left,inner_sub_right]
    ring
  rw [heq]
  calc
    _ ≤ ‖⟪W d (x-x'),W e y⟫_ℂ‖ + ‖⟪W d x',W e (y-y')⟫_ℂ‖ + ‖⟪W d x',W e y'⟫_ℂ‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      gcongr
      · simpa only [norm_W] using norm_inner_le_norm (W d (x-x')) (W e y)
      · simpa only [norm_W] using norm_inner_le_norm (W d x') (W e (y-y'))

 

theorem tendsto_inner_translated (d e : E) (hne : 0 < ‖d-e‖) (x y : Space E) :
    Tendsto (fun r : ℝ => ⟪W (r • d) x,W (r • e) y⟫_ℂ) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero,Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x',hx⟩ := Metric.denseRange_iff.mp
    (UniformSpace.Completion.denseRange_coe (α := PreSpace E)) x
    (ε/(4*(‖y‖+1))) (by positivity)
  obtain ⟨y',hy⟩ := Metric.denseRange_iff.mp
    (UniformSpace.Completion.denseRange_coe (α := PreSpace E)) y
    (ε/(4*(‖(↑x' : Space E)‖+1))) (by positivity)
  rw [dist_eq_norm,lt_div_iff₀ (by positivity)] at hx hy
  have hx' : ‖x-(↑x' : Space E)‖ * ‖y‖ < ε/4 := by
    nlinarith [norm_nonneg (x-(↑x' : Space E))]
  have hy' : ‖(↑x' : Space E)‖ * ‖y-(↑y' : Space E)‖ < ε/4 := by
    nlinarith [norm_nonneg (y-(↑y' : Space E))]
  have ht := tendsto_inner_translated_pre d e hne x' y'
  have he : ∀ᶠ r : ℝ in atTop, ‖⟪W (r • d) (↑x'),W (r • e) (↑y')⟫_ℂ‖ < ε/2 := by
    have ht' : Tendsto (fun r : ℝ => ‖⟪W (r • d) (↑x'),W (r • e) (↑y')⟫_ℂ‖)
        atTop (𝓝 (0:ℝ)) := by simpa using ht.norm
    exact ht'.eventually_lt_const (half_pos hε)
  filter_upwards [he] with r hr
  rw [dist_zero_right,Real.norm_of_nonneg (norm_nonneg _)]
  have hb := inner_translate_approx (r • d) (r • e) x (↑x') y (↑y')
  linarith

theorem continuous_W_coherent (x : E) : Continuous (fun d : E => W d (coherent x)) := by
  have hp : Continuous (fun d : E => phase d x) :=
    continuous_phase.comp (continuous_id.prodMk continuous_const)
  have hc : Continuous (fun d : E => coherent (d+x)) :=
    continuous_coherent.comp (continuous_id.add continuous_const)
  simp_rw [W_coherent]
  convert! hp.smul hc using 1

theorem continuous_W_coe (x : PreSpace E) : Continuous (fun d : E => W d (↑x)) := by
  classical
  simp only [coe_eq_sum,Finsupp.sum,map_sum,map_smul]
  apply continuous_finsetSum
  intro e he
  exact (continuous_const (y := (toFinsupp x) e)).smul (continuous_W_coherent e)

 
theorem continuous_W (x : Space E) : Continuous (fun d : E => W d x) := by
  rw [continuous_iff_continuousAt]
  intro d
  rw [ContinuousAt,Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x',hx⟩ := Metric.denseRange_iff.mp
    (UniformSpace.Completion.denseRange_coe (α := PreSpace E)) x (ε/4) (by positivity)
  have he := Metric.tendsto_nhds.mp ((continuous_W_coe x').tendsto d) (ε/2) (by positivity)
  filter_upwards [he] with a ha
  have h1 : dist (W a x) (W a (↑x')) = dist x (↑x' : Space E) :=
    (weyl a).isometry.dist_eq _ _
  have h2 : dist (W d (↑x')) (W d x) = dist x (↑x' : Space E) := by
    rw [← weyl_apply,← weyl_apply,(weyl d).isometry.dist_eq,dist_comm]
  have ht1 := dist_triangle (W a x) (W a (↑x')) (W d x)
  have ht2 := dist_triangle (W a (↑x')) (W d (↑x')) (W d x)
  rw [h1] at ht1
  rw [h2] at ht2
  linarith

 
theorem tendsto_W {α : Type*} {l : Filter α} {ds : α → E} {xs : α → Space E}
    {d : E} {x : Space E} (hd : Tendsto ds l (𝓝 d)) (hx : Tendsto xs l (𝓝 x)) :
    Tendsto (fun a => W (ds a) (xs a)) l (𝓝 (W d x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he1 := Metric.tendsto_nhds.mp hx (ε/2) (by positivity)
  have he2 := Metric.tendsto_nhds.mp (((continuous_W x).tendsto d).comp hd)
    (ε/2) (by positivity)
  filter_upwards [he1,he2] with a ha hb
  have heq : dist (W (ds a) (xs a)) (W (ds a) x) = dist (xs a) x :=
    (weyl (ds a)).isometry.dist_eq _ _
  have ht := dist_triangle (W (ds a) (xs a)) (W (ds a) x) (W d x)
  rw [heq] at ht
  dsimp only [Function.comp_def] at hb
  linarith

end CoherentFock

end

end OAI
