import OAI.Algebra.Determinantal.SchurDifferentials

namespace OAI

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι κ T : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

noncomputable def dirMatrix (A : T → Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ) (x h : T) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
  Matrix.of fun i j => fderiv ℂ (fun y => A y i j) x h

noncomputable def kernelRemaining
    (a : T → ℂ) (β γ : T → ι → ℂ) (E : T → Matrix ι ι ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T)
    (z : (ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) : ℂ × (κ → ℂ) :=
  (a (ψ z.1) + β (ψ z.1) ⬝ᵥ z.2.1,
    fun i => normalized z.2.2 ⬝ᵥ
      (dirMatrix (fun y => block (a y) (β y) (γ y) (E y)) (ψ z.1) (h i)
        *ᵥ normalized z.2.1))

omit [Fintype κ] in
 theorem kernelRemaining_solved
    {a : T → ℂ} {β γ : T → ι → ℂ} {E : T → Matrix ι ι ℂ}
    {ψ : (ℂ × (κ → ℂ)) → T} {h : κ → T} {x : ℂ × (κ → ℂ)}
    (ha : DifferentiableAt ℂ a (ψ x))
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) (ψ x))
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) (ψ x))
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) (ψ x))
    (hx : (E (ψ x)).det ≠ 0) :
    kernelRemaining a β γ E ψ h
        (x, graphKernels (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ) x) =
      polarPair (fun y => scalar (a y) (β y) (γ y) (E y)) ψ h x := by
  apply Prod.ext
  · simp [kernelRemaining, graphKernels, polarPair, scalar, right,
      dotProduct_neg, sub_eq_add_neg]
  · ext i
    exact (differential_scalar ha hβ hγ hE hx (h i)).symm

omit [Fintype ι] [DecidableEq ι] in
 theorem contDiff_block {a : T → ℂ} {β γ : T → ι → ℂ}
    {E : T → Matrix ι ι ℂ} {n : WithTop ℕ∞}
    (ha : ContDiff ℂ n a)
    (hβ : ∀ i, ContDiff ℂ n (fun y => β y i))
    (hγ : ∀ i, ContDiff ℂ n (fun y => γ y i))
    (hE : ∀ i j, ContDiff ℂ n (fun y => E y i j)) (i j : Unit ⊕ ι) :
    ContDiff ℂ n (fun y => block (a y) (β y) (γ y) (E y) i j) := by
  cases i <;> cases j <;> simp only [block, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.of_apply]
  · exact ha
  · exact hβ _
  · exact hγ _
  · exact hE _ _

omit [DecidableEq ι] in
 theorem differentiableAt_kernelRemaining
    {a : T → ℂ} {β γ : T → ι → ℂ} {E : T → Matrix ι ι ℂ}
    {ψ : (ℂ × (κ → ℂ)) → T} {h : κ → T} {x : ℂ × (κ → ℂ)}
    {w : (ι → ℂ) × (ι → ℂ)}
    (ha : ContDiff ℂ 2 a)
    (hβ : ∀ i, ContDiff ℂ 2 (fun y => β y i))
    (hγ : ∀ i, ContDiff ℂ 2 (fun y => γ y i))
    (hE : ∀ i j, ContDiff ℂ 2 (fun y => E y i j))
    (hψ : DifferentiableAt ℂ ψ x) :
    DifferentiableAt ℂ (kernelRemaining a β γ E ψ h) (x,w) := by
  have hψ' : DifferentiableAt ℂ (fun z : ((ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) => ψ z.1) (x,w) :=
    hψ.comp (x,w) (ContinuousLinearMap.fst ℂ (ℂ × (κ → ℂ)) ((ι → ℂ) × (ι → ℂ))).differentiableAt
  have hnorm (j : Unit ⊕ ι) (b : Bool) :
      DifferentiableAt ℂ (fun z : ((ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) => normalized (if b then z.2.1 else z.2.2) j) (x,w) := by
    cases j <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, normalized, Sum.elim_inl,
      Sum.elim_inr] <;> fun_prop
  have hdir (i j : Unit ⊕ ι) (l : κ) :
      DifferentiableAt ℂ (fun z : ((ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) =>
        dirMatrix (fun y => block (a y) (β y) (γ y) (E y)) (ψ z.1) (h l) i j) (x,w) := by
    have hc := (contDiff_block ha hβ hγ hE i j).contDiffAt (x := ψ x)
    have hd := (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
    exact (hd.clm_apply (differentiableAt_const (h l))).comp (x,w) hψ'
  apply DifferentiableAt.prodMk
  · change DifferentiableAt ℂ (fun z : ((ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) => a (ψ z.1) + ∑ j, β (ψ z.1) j * z.2.1 j) (x,w)
    apply DifferentiableAt.add ((ha.differentiable (by norm_num) _).comp (x,w) hψ')
    apply DifferentiableAt.fun_sum
    intro j _
    apply DifferentiableAt.mul (((hβ j).differentiable (by norm_num) _).comp (x,w) hψ')
    fun_prop
  · apply differentiableAt_pi.mpr
    intro l
    change DifferentiableAt ℂ (fun z : ((ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) => ∑ i, normalized z.2.2 i *
      ∑ j, dirMatrix (fun y => block (a y) (β y) (γ y) (E y)) (ψ z.1) (h l) i j *
        normalized z.2.1 j) (x,w)
    apply DifferentiableAt.fun_sum
    intro i _
    apply DifferentiableAt.mul (hnorm i false)
    apply DifferentiableAt.fun_sum
    intro j _
    exact (hdir i j l).mul (hnorm j true)

 theorem simple_kernel_lift
    {a : T → ℂ} {β γ : T → ι → ℂ} {E : T → Matrix ι ι ℂ}
    {ψ : (ℂ × (κ → ℂ)) → T} {h : κ → T} {x : ℂ × (κ → ℂ)}
    (ha : ContDiff ℂ 2 a)
    (hβ : ∀ i, ContDiff ℂ 2 (fun y => β y i))
    (hγ : ∀ i, ContDiff ℂ 2 (fun y => γ y i))
    (hE : ∀ i j, ContDiff ℂ 2 (fun y => E y i j))
    (hψ : DifferentiableAt ℂ ψ x) (hx : (E (ψ x)).det ≠ 0)
    (hz : polarPair (fun y => (block (a y) (β y) (γ y) (E y)).det) ψ h x = 0)
    (hsimple : (fderiv ℂ (polarPair
      (fun y => (block (a y) (β y) (γ y) (E y)).det) ψ h) x).IsInvertible) :
    let g := graphKernels (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ)
    let R := kernelRemaining a β γ E ψ h
    let J := auxiliary (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ)
    (R (x,g x),J (x,g x)) = 0 ∧
      (fderiv ℂ (fun z => (R z,J z)) (x,g x)).IsInvertible := by
  let S := fun y => scalar (a y) (β y) (γ y) (E y)
  let g := graphKernels (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ)
  let R := kernelRemaining a β γ E ψ h
  let J := auxiliary (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ)
  have hdE : ∀ i j y, DifferentiableAt ℂ (fun z => E z i j) y :=
    fun i j => (hE i j).differentiable (by norm_num)
  have hdb : ∀ i y, DifferentiableAt ℂ (fun z => β z i) y :=
    fun i => (hβ i).differentiable (by norm_num)
  have hdg : ∀ i y, DifferentiableAt ℂ (fun z => γ z i) y :=
    fun i => (hγ i).differentiable (by norm_num)
  have hda := ha.differentiable (by norm_num)
  have hevent : ∀ᶠ y in 𝓝 (ψ x), (E y).det ≠ 0 :=
    (differentiableAt_det (fun i j => hdE i j (ψ x))).continuousAt.eventually_ne hx
  have hFS : (fun y => (block (a y) (β y) (γ y) (E y)).det) =ᶠ[𝓝 (ψ x)]
      (fun y => (E y).det * S y) := by
    filter_upwards [hevent] with y hy
    exact det_block _ _ _ _ hy
  obtain ⟨hSz,hSs⟩ := simple_polarPair_unit (contDiff_det hE).contDiffAt
    (contDiffAt_scalar ha hβ hγ hE hx) hψ hFS hx hz hsimple
  have hRG : (fun y => R (y,g y)) =ᶠ[𝓝 x] polarPair S ψ h := by
    filter_upwards [hψ.continuousAt.eventually hevent] with y hy
    exact kernelRemaining_solved (hda _) (fun i => hdb i _) (fun i => hdg i _)
      (fun i j => hdE i j _) hy
  change (R (x,g x),J (x,g x)) = 0 ∧ _
  constructor
  · apply Prod.ext
    · exact hRG.eq_of_nhds.trans hSz
    · exact auxiliary_solved _ _ _ _ hx
  · apply simple_kernel_elimination (β := β ∘ ψ) (γ := γ ∘ ψ) (E := E ∘ ψ)
      (fun i => (hdb i _).comp x hψ) (fun i => (hdg i _).comp x hψ)
      (fun i j => (hdE i j _).comp x hψ) hx
      (differentiableAt_kernelRemaining ha hβ hγ hE hψ)
    rwa [hRG.fderiv_eq]
end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix
variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype σ]

noncomputable def affineValue
    (A₀ : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (A : σ → Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ) (y : σ → ℂ) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
  Matrix.of fun i j => A₀ i j + ∑ v, A v i j * y v

omit [Fintype ι] [DecidableEq ι] in
 theorem affineValue_contDiff
    (A₀ : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (A : σ → Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (i j : Unit ⊕ ι) : ContDiff ℂ 2 (fun y => affineValue A₀ A y i j) := by
  unfold affineValue
  simp only [Matrix.of_apply]
  fun_prop

omit [Fintype ι] [DecidableEq ι] in
 theorem block_entries (M : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ) :
    block (M (.inl ()) (.inl ())) (fun j => M (.inl ()) (.inr j))
      (fun i => M (.inr i) (.inl ())) (fun i j => M (.inr i) (.inr j)) = M := by
  ext i j
  cases i <;> cases j <;> rfl

 theorem simple_affine_kernel_lift
    (A₀ : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (A : σ → Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    {ψ : (ℂ × (κ → ℂ)) → (σ → ℂ)} {h : κ → (σ → ℂ)}
    {x : ℂ × (κ → ℂ)} (hψ : DifferentiableAt ℂ ψ x)
    (hx : ((affineValue A₀ A (ψ x)).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hz : polarPair (fun y => (affineValue A₀ A y).det) ψ h x = 0)
    (hsimple : (fderiv ℂ (polarPair
      (fun y => (affineValue A₀ A y).det) ψ h) x).IsInvertible) :
    let F := affineValue A₀ A
    let a := fun y => F y (.inl ()) (.inl ())
    let β := fun y j => F y (.inl ()) (.inr j)
    let γ := fun y i => F y (.inr i) (.inl ())
    let E := fun y => (F y).submatrix Sum.inr Sum.inr
    let g := graphKernels (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ)
    let R := kernelRemaining a β γ E ψ h
    let J := auxiliary (β ∘ ψ) (γ ∘ ψ) (E ∘ ψ)
    (R (x,g x),J (x,g x)) = 0 ∧
      (fderiv ℂ (fun z => (R z,J z)) (x,g x)).IsInvertible := by
  dsimp only
  apply simple_kernel_lift
    (affineValue_contDiff A₀ A _ _)
    (fun j => affineValue_contDiff A₀ A _ _)
    (fun i => affineValue_contDiff A₀ A _ _)
    (fun i j => affineValue_contDiff A₀ A _ _) hψ hx
  · simpa only [block_entries] using hz
  · simpa only [block_entries] using hsimple
end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis
open Matrix
variable {I J : Type*} [Fintype I] [DecidableEq I] [Finite J]

noncomputable def dotLinear (v : I → ℂ) : (I → ℂ) →ₗ[ℂ] ℂ where
  toFun f := f ⬝ᵥ v
  map_add' := by intros; apply add_dotProduct
  map_smul' := by intros; simp [smul_dotProduct]

 theorem exists_common_functional (v : J → I → ℂ) (hv : ∀ j, v j ≠ 0) :
    ∃ f : I → ℂ, ∀ j, f ⬝ᵥ v j ≠ 0 := by
  classical
  let p (j : J) := LinearMap.ker (dotLinear (v j))
  have hp (j : J) : p j ≠ ⊤ := by
    intro h
    apply hv j
    funext i
    have hi : Pi.single i 1 ∈ p j := h ▸ Submodule.mem_top
    change (Pi.single i 1 : I → ℂ) ⬝ᵥ v j = 0 at hi
    simpa only [single_dotProduct, one_mul, Pi.zero_apply] using hi
  obtain ⟨f,hf⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  exact ⟨f,hf⟩

 theorem det_updateRow_one (i : I) (f : I → ℂ) :
    ((1 : Matrix I I ℂ).updateRow i f).det = f i := by
  have hsum : (∑ k, f k • (1 : Matrix I I ℂ) k) = f := by
    ext j
    simp [Matrix.one_apply, Finset.sum_apply, Pi.smul_apply]
  simpa only [hsum, Matrix.det_one, smul_eq_mul, mul_one] using
    (Matrix.det_updateRow_sum (1 : Matrix I I ℂ) i f)

 theorem exists_common_kernel_chart (i₀ : I) (A : J → Matrix I I ℂ)
    (hA : ∀ j, (A j).adjugate ≠ 0) :
    ∃ S : Matrix I I ℂ, S.det ≠ 0 ∧
      ∀ j, ∃ r, (A j * S).adjugate i₀ r ≠ 0 := by
  classical
  have hv : ∀ j, ∃ r, (fun i => (A j).adjugate i r) ≠ 0 := by
    intro j
    by_contra! hz
    exact hA j (by funext i r; exact congrFun (hz r) i)
  choose r hr using hv
  let v : Option J → I → ℂ
    | none => Pi.single i₀ 1
    | some j => fun i => (A j).adjugate i (r j)
  have hv' : ∀ j, v j ≠ 0 := by
    rintro (_|j)
    · intro h
      have := congrFun h i₀
      simp [v] at this
    · exact hr j
  obtain ⟨f,hf⟩ := exists_common_functional v hv'
  have hf₀ : f i₀ ≠ 0 := by
    simpa only [v, dotProduct_single, mul_one] using hf none
  let T : Matrix I I ℂ := (1 : Matrix I I ℂ).updateRow i₀ f
  have hT : T.det ≠ 0 := by simpa only [T, det_updateRow_one] using hf₀
  let S : Matrix I I ℂ := T⁻¹
  have hST : S * T = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hT)
  have hS : S.det ≠ 0 := by
    have he := congrArg Matrix.det hST
    rw [Matrix.det_mul, Matrix.det_one] at he
    exact left_ne_zero_of_mul_eq_one he
  have hadj : S.adjugate = S.det • T := by
    calc
      S.adjugate = S.adjugate * (S*T) := by rw [hST, Matrix.mul_one]
      _ = (S.adjugate*S)*T := (Matrix.mul_assoc _ _ _).symm
      _ = S.det • T := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  refine ⟨S,hS,?_⟩
  intro j
  refine ⟨r j,?_⟩
  rw [Matrix.adjugate_mul_distrib, hadj, Matrix.smul_mul]
  change S.det * (T * (A j).adjugate) i₀ (r j) ≠ 0
  apply mul_ne_zero hS
  simpa only [Matrix.mul_apply, T, Matrix.updateRow_self, v, dotProduct] using hf (some j)
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def determinantMultilinear :
    ContinuousMultilinearMap ℂ (fun _ : I => I → ℂ) ℂ :=
  { Matrix.detRowAlternating.toMultilinearMap with
    cont := continuous_id.matrix_det }

 theorem determinantDifferential (M H : I → I → ℂ) :
    fderiv ℂ (fun M : I → I → ℂ => (Matrix.of M).det) M H =
      ∑ i, ∑ j, (Matrix.of M).adjugate j i * H i j := by
  have hd := (determinantMultilinear (I := I)).hasFDerivAt M
  have he : fderiv ℂ (fun M : I → I → ℂ => (Matrix.of M).det) M =
      (determinantMultilinear (I := I)).linearDeriv M := hd.fderiv
  rw [he, ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro i _
  change ((Matrix.of M).updateRow i (H i)).det = _
  rw [← Matrix.det_transpose, ← Matrix.updateCol_transpose]
  change (Matrix.of M).transpose.cramer (H i) i = _
  rw [Matrix.cramer_eq_adjugate_mulVec, ← Matrix.adjugate_transpose]
  rfl

 theorem differentiableAt_determinant (M : I → I → ℂ) :
    DifferentiableAt ℂ (fun M : I → I → ℂ => (Matrix.of M).det) M :=
  ((determinantMultilinear (I := I)).hasFDerivAt M).differentiableAt

 theorem adjugate_ne_zero_of_differential
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : E → I → I → ℂ} {x : E} (hA : DifferentiableAt ℂ A x)
    (hd : fderiv ℂ (fun y => (Matrix.of (A y)).det) x ≠ 0) :
    (Matrix.of (A x)).adjugate ≠ 0 := by
  intro hz
  apply hd
  change fderiv ℂ ((fun M : I → I → ℂ => (Matrix.of M).det) ∘ A) x = 0
  rw [fderiv_comp x (differentiableAt_determinant (A x)) hA]
  ext v
  simp only [ContinuousLinearMap.comp_apply, _root_.zero_apply]
  rw [determinantDifferential, hz]
  simp
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Matrix
open scoped Topology
variable {V E W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

 theorem first_derivative_ne_zero_of_invertible
    {P : (ℂ × W) → (ℂ × W)} {x : ℂ × W}
    (hP : DifferentiableAt ℂ P x) (hs : (fderiv ℂ P x).IsInvertible) :
    fderiv ℂ (fun y => (P y).1) x ≠ 0 := by
  intro hz
  obtain ⟨v,hv⟩ := hs.bijective.surjective (1,0)
  have hh := congrArg (fun L : (ℂ × W) →L[ℂ] ℂ => L v) hz
  rw [(hP.hasFDerivAt.fst).fderiv] at hh
  change (fderiv ℂ P x v).1 = 0 at hh
  rw [hv] at hh
  exact one_ne_zero hh

variable {I J : Type*} [Fintype I] [DecidableEq I] [Finite J]

 theorem selected_simple_common_kernel_chart
    (i₀ : I) (A : E → I → I → ℂ) (ψ : (ℂ × W) → E)
    (P : (ℂ × W) → (ℂ × W)) (x : J → (ℂ × W))
    (hA : ∀ j, DifferentiableAt ℂ A (ψ (x j)))
    (hψ : ∀ j, DifferentiableAt ℂ ψ (x j))
    (hP : ∀ j, DifferentiableAt ℂ P (x j))
    (hfirst : ∀ y, (P y).1 = (Matrix.of (A (ψ y))).det)
    (hsimple : ∀ j, (fderiv ℂ P (x j)).IsInvertible) :
    ∃ S : Matrix I I ℂ, S.det ≠ 0 ∧
      ∀ j, ∃ r, (Matrix.of (A (ψ (x j))) * S).adjugate i₀ r ≠ 0 := by
  apply exists_common_kernel_chart
  intro j
  apply adjugate_ne_zero_of_differential ((hA j).comp (x j) (hψ j))
  have hn := first_derivative_ne_zero_of_invertible (hP j) (hsimple j)
  simpa only [Function.comp_apply, hfirst] using hn
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Matrix

 def unitSumOptionEquiv (α : Type*) : Unit ⊕ α ≃ Option α where
  toFun := Sum.elim (fun _ => none) some
  invFun := fun o => o.elim (Sum.inl ()) Sum.inr
  left_inv := by
    rintro (u|a)
    · cases u; rfl
    · rfl
  right_inv := by rintro (_|a) <;> rfl

noncomputable def pivotEquiv {n : ℕ} (i : Fin (n+1)) : Unit ⊕ Fin n ≃ Fin (n+1) :=
  (unitSumOptionEquiv (Fin n)).trans (finSuccEquiv' i).symm

@[simp] theorem pivotEquiv_inl {n : ℕ} (i : Fin (n+1)) :
    pivotEquiv i (Sum.inl ()) = i := rfl
@[simp] theorem pivotEquiv_inr {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    pivotEquiv i (Sum.inr j) = i.succAbove j := rfl

 theorem det_submatrix_two_equiv {I J R : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [CommRing R]
    (er ec : I ≃ J) (M : Matrix J J R) :
    (M.submatrix er ec).det = (Equiv.Perm.sign (ec.symm.trans er) : ℤ) * M.det := by
  exact Matrix.det_reindex er.symm ec.symm M

 theorem determinant_pivot_scalar {n : ℕ} (i r : Fin (n+1)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ,
      (M.submatrix (pivotEquiv r) (pivotEquiv i)).det = c*M.det := by
  let c : ℂ := (Equiv.Perm.sign ((pivotEquiv i).symm.trans (pivotEquiv r)) : ℤ)
  refine ⟨c, ?_, fun M => det_submatrix_two_equiv _ _ _⟩
  exact Int.cast_ne_zero.mpr (Units.ne_zero _)

 theorem pivot_minor_ne_zero {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (i r : Fin (n+1)) (h : M.adjugate i r ≠ 0) :
    ((M.submatrix (pivotEquiv r) (pivotEquiv i)).submatrix Sum.inr Sum.inr).det ≠ 0 := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at h
  have he : (M.submatrix (pivotEquiv r) (pivotEquiv i)).submatrix Sum.inr Sum.inr =
      M.submatrix r.succAbove i.succAbove := by ext a b; rfl
  rw [he]
  exact (mul_ne_zero_iff.mp h).2
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix
variable {ι κ T : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

noncomputable def matrixKernelSystem
    (F : T → Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T)
    (z : (ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) :=
  (kernelRemaining (fun y => F y (.inl ()) (.inl ()))
      (fun y j => F y (.inl ()) (.inr j)) (fun y i => F y (.inr i) (.inl ()))
      (fun y => (F y).submatrix Sum.inr Sum.inr) ψ h z,
    auxiliary (fun y j => F (ψ y) (.inl ()) (.inr j))
      (fun y i => F (ψ y) (.inr i) (.inl ()))
      (fun y => (F (ψ y)).submatrix Sum.inr Sum.inr) z)

noncomputable def matrixKernelPoint
    (F : T → Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (x : ℂ × (κ → ℂ)) :=
  (x, graphKernels (fun y j => F (ψ y) (.inl ()) (.inr j))
      (fun y i => F (ψ y) (.inr i) (.inl ()))
      (fun y => (F (ψ y)).submatrix Sum.inr Sum.inr) x)

 theorem simple_matrix_kernel_lift
    (F : T → Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (hF : ∀ i j, ContDiff ℂ 2 (fun y => F y i j))
    {ψ : (ℂ × (κ → ℂ)) → T} {h : κ → T} {x : ℂ × (κ → ℂ)}
    (hψ : DifferentiableAt ℂ ψ x)
    (hx : ((F (ψ x)).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hz : polarPair (fun y => (F y).det) ψ h x = 0)
    (hsimple : (fderiv ℂ (polarPair (fun y => (F y).det) ψ h) x).IsInvertible) :
    matrixKernelSystem F ψ h (matrixKernelPoint F ψ x) = 0 ∧
      (fderiv ℂ (matrixKernelSystem F ψ h) (matrixKernelPoint F ψ x)).IsInvertible := by
  apply simple_kernel_lift (hF _ _) (fun j => hF _ _) (fun i => hF _ _)
    (fun i j => hF _ _) hψ hx
  · simpa only [block_entries] using hz
  · simpa only [block_entries] using hsimple
end PermanentBorder.PolarAnalysis.Schur

end OAI
