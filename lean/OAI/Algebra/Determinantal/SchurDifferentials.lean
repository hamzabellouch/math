import OAI.Algebra.Determinantal.KernelCharts

namespace OAI

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

 theorem differentiableAt_right {γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ} {x : V}
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (i : ι) :
    DifferentiableAt ℂ (fun y => right (γ y) (E y) i) x := by
  simp only [right, Pi.neg_apply, mulVec, dotProduct]
  exact (DifferentiableAt.fun_sum (fun j _ =>
    (differentiableAt_inverse hE hx i j).mul (hγ j))).neg

 theorem differentiableAt_left {β : V → ι → ℂ} {E : V → Matrix ι ι ℂ} {x : V}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (i : ι) :
    DifferentiableAt ℂ (fun y => left (β y) (E y) i) x := by
  simp only [left, Pi.neg_apply, vecMul, dotProduct]
  exact (DifferentiableAt.fun_sum (fun j _ =>
    (hβ j).mul (differentiableAt_inverse hE hx j i))).neg

 theorem differentiableAt_scalar {a : V → ℂ} {β γ : V → ι → ℂ}
    {E : V → Matrix ι ι ℂ} {x : V}
    (ha : DifferentiableAt ℂ a x)
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) :
    DifferentiableAt ℂ (fun y => scalar (a y) (β y) (γ y) (E y)) x := by
  simp only [scalar, mulVec, dotProduct]
  exact ha.sub (DifferentiableAt.fun_sum (fun j _ => (hβ j).mul
    (DifferentiableAt.fun_sum (fun l _ => (differentiableAt_inverse hE hx j l).mul (hγ l)))))

omit [Fintype ι] [DecidableEq ι] in
 theorem differential_mulVec {κ : Type*} [Fintype κ]
    {A : V → Matrix ι κ ℂ} {p : V → κ → ℂ} {x : V}
    (hA : ∀ i j, DifferentiableAt ℂ (fun y => A y i j) x)
    (hp : ∀ i, DifferentiableAt ℂ (fun y => p y i) x) (h : V) (i : ι) :
    fderiv ℂ (fun y => (A y *ᵥ p y) i) x h =
      ((Matrix.of fun i j => fderiv ℂ (fun y => A y i j) x h) *ᵥ p x) i +
      (A x *ᵥ (fun j => fderiv ℂ (fun y => p y j) x h)) i := by
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hA i j).hasFDerivAt.mul (hp j).hasFDerivAt)
  have heq : fderiv ℂ (fun y => (A y *ᵥ p y) i) x =
      ∑ j, ((A x i j) • fderiv ℂ (fun y => p y j) x +
        (p x j) • fderiv ℂ (fun y => A y i j) x) := by
    convert! hd.fderiv using 1
  rw [heq]
  simp only [_root_.sum_apply, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul, mulVec, dotProduct,
    Finset.sum_add_distrib, Matrix.of_apply]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

 theorem differential_scalar {a : V → ℂ} {β γ : V → ι → ℂ}
    {E : V → Matrix ι ι ℂ} {x : V}
    (ha : DifferentiableAt ℂ a x)
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (h : V) :
    fderiv ℂ (fun y => scalar (a y) (β y) (γ y) (E y)) x h =
      normalized (left (β x) (E x)) ⬝ᵥ
        ((Matrix.of fun i j => fderiv ℂ (fun y => block (a y) (β y) (γ y) (E y) i j) x h)
          *ᵥ normalized (right (γ x) (E x))) := by
  let A := fun y => block (a y) (β y) (γ y) (E y)
  let p := fun y => normalized (right (γ y) (E y))
  let b := normalized (left (β x) (E x))
  let S := fun y => scalar (a y) (β y) (γ y) (E y)
  have hA : ∀ i j, DifferentiableAt ℂ (fun y => A y i j) x := by
    intro i j
    cases i <;> cases j <;> simp only [A, block, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.of_apply]
    · exact ha
    · exact hβ _
    · exact hγ _
    · exact hE _ _
  have hp : ∀ i, DifferentiableAt ℂ (fun y => p y i) x := by
    intro i
    cases i with
    | inl u => exact differentiableAt_const _
    | inr i => exact differentiableAt_right hγ hE hx i
  have hevent : ∀ᶠ y in 𝓝 x, (E y).det ≠ 0 :=
    (differentiableAt_det hE).continuousAt.eventually_ne hx
  have heq (i : Unit ⊕ ι) :
      (fun y => (A y *ᵥ p y) i) =ᶠ[𝓝 x] (fun y => Sum.elim (fun _ => S y) (fun _ => 0) i) := by
    filter_upwards [hevent] with y hy
    exact congr_fun (solved_right (a y) (β y) (γ y) (E y) hy) i
  let dA : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
    Matrix.of fun i j => fderiv ℂ (fun y => A y i j) x h
  let dp : Unit ⊕ ι → ℂ := fun j => fderiv ℂ (fun y => p y j) x h
  have hd : dA *ᵥ p x + A x *ᵥ dp =
      Sum.elim (fun _ => fderiv ℂ S x h) (fun _ => 0) := by
    ext i
    change (dA *ᵥ p x) i + (A x *ᵥ dp) i = _
    rw [← differential_mulVec hA hp h i]
    rw [(heq i).fderiv_eq]
    cases i <;> simp
  have hb : b ᵥ* A x = Sum.elim (fun _ => S x) (fun _ => 0) :=
    solved_left (a x) (β x) (γ x) (E x) hx
  have hz : b ⬝ᵥ (A x *ᵥ dp) = 0 := by
    rw [dotProduct_mulVec, hb]
    simp [dotProduct, dp, p, normalized, Fintype.sum_sum_type]
  have hd' := congrArg (fun z => b ⬝ᵥ z) hd
  rw [dotProduct_add, hz, add_zero] at hd'
  change fderiv ℂ S x h = b ⬝ᵥ (dA *ᵥ p x)
  simpa [dotProduct, b, normalized, Fintype.sum_sum_type] using hd'.symm
end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def auxiliaryLinear (E : Matrix ι ι ℂ) :
    ((ι → ℂ) × (ι → ℂ)) →L[ℂ] ((ι → ℂ) × (ι → ℂ)) :=
  ((E.mulVecLin.toContinuousLinearMap).comp (ContinuousLinearMap.fst ℂ _ _)).prod
    ((E.vecMulLinear.toContinuousLinearMap).comp (ContinuousLinearMap.snd ℂ _ _))

omit [DecidableEq ι] in
@[simp] theorem auxiliaryLinear_apply (E : Matrix ι ι ℂ) (w : (ι → ℂ) × (ι → ℂ)) :
    auxiliaryLinear E w = (E *ᵥ w.1, w.2 ᵥ* E) := rfl

 theorem auxiliaryLinear_invertible (E : Matrix ι ι ℂ) (hE : E.det ≠ 0) :
    (auxiliaryLinear E).IsInvertible := by
  have hu := isUnit_iff_ne_zero.mpr hE
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := auxiliaryLinear E⁻¹)
  · apply ContinuousLinearMap.ext
    intro w
    apply Prod.ext <;> simp [mulVec_mulVec, vecMul_vecMul, mul_nonsing_inv E hu,
      nonsing_inv_mul E hu]
  · apply ContinuousLinearMap.ext
    intro w
    apply Prod.ext <;> simp [mulVec_mulVec, vecMul_vecMul, mul_nonsing_inv E hu,
      nonsing_inv_mul E hu]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def auxiliary (β γ : V → ι → ℂ) (E : V → Matrix ι ι ℂ)
    (z : V × ((ι → ℂ) × (ι → ℂ))) : ((ι → ℂ) × (ι → ℂ)) :=
  (γ z.1 + E z.1 *ᵥ z.2.1, β z.1 + z.2.2 ᵥ* E z.1)

noncomputable def graphKernels (β γ : V → ι → ℂ) (E : V → Matrix ι ι ℂ)
    (x : V) : ((ι → ℂ) × (ι → ℂ)) :=
  (right (γ x) (E x), left (β x) (E x))

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
 theorem auxiliary_solved (β γ : V → ι → ℂ) (E : V → Matrix ι ι ℂ)
    (x : V) (hx : (E x).det ≠ 0) :
    auxiliary β γ E (x,graphKernels β γ E x) = 0 := by
  have hu := isUnit_iff_ne_zero.mpr hx
  apply Prod.ext <;> simp [auxiliary, graphKernels, right, left, mulVec_neg, neg_vecMul,
    mulVec_mulVec, vecMul_vecMul, mul_nonsing_inv (E x) hu, nonsing_inv_mul (E x) hu]

 theorem differentiableAt_graphKernels {β γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ} {x : V}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) : DifferentiableAt ℂ (graphKernels β γ E) x := by
  apply DifferentiableAt.prodMk
  · exact differentiableAt_pi.mpr (differentiableAt_right hγ hE hx)
  · exact differentiableAt_pi.mpr (differentiableAt_left hβ hE hx)

omit [DecidableEq ι] in
 theorem differentiableAt_auxiliary {β γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ}
    {x : V} {w : (ι → ℂ) × (ι → ℂ)}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x) :
    DifferentiableAt ℂ (auxiliary β γ E) (x,w) := by
  apply DifferentiableAt.prodMk
  · apply differentiableAt_pi.mpr
    intro i
    change DifferentiableAt ℂ (fun z => γ z.1 i + ∑ j, E z.1 i j * z.2.1 j) (x,w)
    apply DifferentiableAt.add ((hγ i).comp (x,w) (ContinuousLinearMap.fst ℂ V ((ι → ℂ) × (ι → ℂ))).differentiableAt)
    apply DifferentiableAt.fun_sum
    intro j _
    apply DifferentiableAt.mul ((hE i j).comp (x,w) (ContinuousLinearMap.fst ℂ V ((ι → ℂ) × (ι → ℂ))).differentiableAt)
    fun_prop
  · apply differentiableAt_pi.mpr
    intro j
    change DifferentiableAt ℂ (fun z => β z.1 j + ∑ i, z.2.2 i * E z.1 i j) (x,w)
    apply DifferentiableAt.add ((hβ j).comp (x,w) (ContinuousLinearMap.fst ℂ V ((ι → ℂ) × (ι → ℂ))).differentiableAt)
    apply DifferentiableAt.fun_sum
    intro i _
    apply DifferentiableAt.mul _ ((hE i j).comp (x,w) (ContinuousLinearMap.fst ℂ V ((ι → ℂ) × (ι → ℂ))).differentiableAt)
    fun_prop

omit [DecidableEq ι] in
 theorem fderiv_auxiliary_inr {β γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ}
    {x : V} {w : (ι → ℂ) × (ι → ℂ)}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x) :
    fderiv ℂ (auxiliary β γ E) (x,w) ∘L ContinuousLinearMap.inr ℂ V _ =
      auxiliaryLinear (E x) := by
  have hd := (differentiableAt_auxiliary (w := w) hβ hγ hE).hasFDerivAt.comp w
    ((hasFDerivAt_const x w).prodMk (hasFDerivAt_id w))
  have hf : HasFDerivAt (fun v => auxiliary β γ E (x,v)) (auxiliaryLinear (E x)) w := by
    convert! (auxiliaryLinear (E x)).hasFDerivAt.const_add (γ x,β x) using 1
  convert! hd.unique hf using 1

 theorem simple_kernel_elimination [FiniteDimensional ℂ V]
    {β γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ} {x : V}
    {R : V × ((ι → ℂ) × (ι → ℂ)) → V}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0)
    (hR : DifferentiableAt ℂ R (x,graphKernels β γ E x))
    (hs : (fderiv ℂ (fun y => R (y,graphKernels β γ E y)) x).IsInvertible) :
    (fderiv ℂ (fun z => (R z,auxiliary β γ E z))
      (x,graphKernels β γ E x)).IsInvertible := by
  apply PermanentBorder.PolarAnalysis.simple_after_elimination hR
    (differentiableAt_auxiliary hβ hγ hE) (differentiableAt_graphKernels hβ hγ hE hx)
  · have he := (differentiableAt_det hE).continuousAt.eventually_ne hx
    filter_upwards [he] with y hy
    exact auxiliary_solved β γ E y hy
  · rw [fderiv_auxiliary_inr hβ hγ hE]
    exact auxiliaryLinear_invertible _ hx
  · exact hs
end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

 theorem differential_det_block {a : V → ℂ} {β γ : V → ι → ℂ}
    {E : V → Matrix ι ι ℂ} {x : V}
    (ha : DifferentiableAt ℂ a x)
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (h : V) :
    fderiv ℂ (fun y => (block (a y) (β y) (γ y) (E y)).det) x h =
      (E x).det *
        (normalized (left (β x) (E x)) ⬝ᵥ
          ((Matrix.of fun i j => fderiv ℂ (fun y => block (a y) (β y) (γ y) (E y) i j) x h)
            *ᵥ normalized (right (γ x) (E x)))) +
      fderiv ℂ (fun y => (E y).det) x h * scalar (a x) (β x) (γ x) (E x) := by
  have hevent : ∀ᶠ y in 𝓝 x, (E y).det ≠ 0 :=
    (differentiableAt_det hE).continuousAt.eventually_ne hx
  have heq : (fun y => (block (a y) (β y) (γ y) (E y)).det) =ᶠ[𝓝 x]
      (fun y => (E y).det * scalar (a y) (β y) (γ y) (E y)) := by
    filter_upwards [hevent] with y hy
    exact det_block _ _ _ _ hy
  rw [heq.fderiv_eq, fderiv_fun_mul (differentiableAt_det hE)
      (differentiableAt_scalar ha hβ hγ hE hx)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [differential_scalar ha hβ hγ hE hx h]
  ring

 theorem contDiff_det {E : V → Matrix ι ι ℂ} {n : WithTop ℕ∞}
    (hE : ∀ i j, ContDiff ℂ n (fun y => E y i j)) :
    ContDiff ℂ n (fun y => (E y).det) := by
  classical
  simp only [Matrix.det_apply]
  fun_prop

 theorem contDiff_adjugate {E : V → Matrix ι ι ℂ} {n : WithTop ℕ∞}
    (hE : ∀ i j, ContDiff ℂ n (fun y => E y i j)) (i j : ι) :
    ContDiff ℂ n (fun y => (E y).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  apply contDiff_det
  intro u v
  by_cases hu : u = j
  · subst u
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simpa only [Matrix.updateRow_ne hu] using hE u v

 theorem contDiffAt_inverse {E : V → Matrix ι ι ℂ} {n : WithTop ℕ∞} {x : V}
    (hE : ∀ i j, ContDiff ℂ n (fun y => E y i j))
    (hx : (E x).det ≠ 0) (i j : ι) :
    ContDiffAt ℂ n (fun y => (E y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((contDiff_det hE).contDiffAt.inv hx).mul (contDiff_adjugate hE i j).contDiffAt

 theorem contDiffAt_scalar {a : V → ℂ} {β γ : V → ι → ℂ}
    {E : V → Matrix ι ι ℂ} {n : WithTop ℕ∞} {x : V}
    (ha : ContDiff ℂ n a)
    (hβ : ∀ i, ContDiff ℂ n (fun y => β y i))
    (hγ : ∀ i, ContDiff ℂ n (fun y => γ y i))
    (hE : ∀ i j, ContDiff ℂ n (fun y => E y i j))
    (hx : (E x).det ≠ 0) :
    ContDiffAt ℂ n (fun y => scalar (a y) (β y) (γ y) (E y)) x := by
  simp only [scalar, mulVec, dotProduct]
  exact ha.contDiffAt.sub (ContDiffAt.sum (fun j _ => (hβ j).contDiffAt.mul
    (ContDiffAt.sum (fun l _ => (contDiffAt_inverse hE hx j l).mul (hγ l).contDiffAt))))
end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis
section Multiplier
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem simple_unit_multiplier_iff {T : E → (F →L[ℂ] F)} {g : E → F} {x : E}
    (hT : DifferentiableAt ℂ T x) (hg : DifferentiableAt ℂ g x)
    (hz : g x = 0) (hu : (T x).IsInvertible) :
    (fderiv ℂ (fun y => T y (g y)) x).IsInvertible ↔ (fderiv ℂ g x).IsInvertible := by
  rw [fderiv_clm_apply hT hg, hz, map_zero, add_zero]
  obtain ⟨e,he⟩ := hu
  rw [← he]
  exact ContinuousLinearMap.isInvertible_equiv_comp

noncomputable def triangularMultiplier (c : ℂ) (d : F) : (ℂ × F) →L[ℂ] (ℂ × F) :=
  c • ContinuousLinearMap.id ℂ (ℂ × F) +
    (ContinuousLinearMap.inr ℂ ℂ F).comp ((ContinuousLinearMap.fst ℂ ℂ F).smulRight d)

@[simp] theorem triangularMultiplier_apply (c : ℂ) (d : F) (z : ℂ × F) :
    triangularMultiplier c d z = (c * z.1, c • z.2 + z.1 • d) := by
  apply Prod.ext <;> simp [triangularMultiplier]

 theorem triangularMultiplier_invertible (c : ℂ) (d : F) (hc : c ≠ 0) :
    (triangularMultiplier c d).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := triangularMultiplier c⁻¹ (-((c⁻¹*c⁻¹) • d)))
  · ext z <;> simp [smul_smul, hc]
  · ext z <;> simp [smul_smul, hc]

 theorem differentiableAt_triangularMultiplier {c : E → ℂ} {d : E → F} {x : E}
    (hc : DifferentiableAt ℂ c x) (hd : DifferentiableAt ℂ d x) :
    DifferentiableAt ℂ (fun y => triangularMultiplier (c y) (d y)) x := by
  apply DifferentiableAt.add (hc.smul_const _) ?_
  apply (differentiableAt_const (c := ContinuousLinearMap.inr ℂ ℂ F)).clm_comp
  exact ((ContinuousLinearMap.smulRightL ℂ (ℂ × F) F
    (ContinuousLinearMap.fst ℂ ℂ F)).differentiableAt.comp x hd)

theorem simple_triangular_system_iff {c : E → ℂ} {d : E → F}
    {s : E → ℂ} {g : E → F} {x : E}
    (hc : DifferentiableAt ℂ c x) (hd : DifferentiableAt ℂ d x)
    (hs : DifferentiableAt ℂ s x) (hg : DifferentiableAt ℂ g x)
    (hcx : c x ≠ 0) (hsx : s x = 0) (hgx : g x = 0) :
    (fderiv ℂ (fun y => (c y * s y, c y • g y + s y • d y)) x).IsInvertible ↔
      (fderiv ℂ (fun y => (s y,g y)) x).IsInvertible := by
  simpa only [triangularMultiplier_apply] using
    simple_unit_multiplier_iff (differentiableAt_triangularMultiplier hc hd)
      (hs.prodMk hg) (by simp [hsx,hgx]) (triangularMultiplier_invertible _ _ hcx)
end Multiplier
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology
variable {T V : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {κ : Type*} [Fintype κ]

noncomputable def polarPair (F : T → ℂ) (ψ : V → T) (h : κ → T) (x : V) : ℂ × (κ → ℂ) :=
  (F (ψ x), fun i => fderiv ℂ F (ψ x) (h i))

 theorem differentiableAt_polarPair {F : T → ℂ} {ψ : V → T} {h : κ → T} {x : V}
    (hF : ContDiffAt ℂ 2 F (ψ x)) (hψ : DifferentiableAt ℂ ψ x) :
    DifferentiableAt ℂ (polarPair F ψ h) x := by
  apply DifferentiableAt.prodMk
  · exact (hF.differentiableAt (by norm_num)).comp x hψ
  · apply differentiableAt_pi.mpr
    intro i
    have hd : DifferentiableAt ℂ (fderiv ℂ F) (ψ x) :=
      (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
    exact (hd.clm_apply (differentiableAt_const (h i))).comp x hψ

 theorem simple_polarPair_unit {F c S : T → ℂ} {ψ : V → T} {h : κ → T} {x : V}
    (hc : ContDiffAt ℂ 2 c (ψ x)) (hS : ContDiffAt ℂ 2 S (ψ x))
    (hψ : DifferentiableAt ℂ ψ x)
    (hFS : F =ᶠ[𝓝 (ψ x)] (fun y => c y * S y)) (hcx : c (ψ x) ≠ 0)
    (hz : polarPair F ψ h x = 0)
    (hsimple : (fderiv ℂ (polarPair F ψ h) x).IsInvertible) :
    polarPair S ψ h x = 0 ∧ (fderiv ℂ (polarPair S ψ h) x).IsInvertible := by
  let U : V → ((ℂ × (κ → ℂ)) →L[ℂ] (ℂ × (κ → ℂ))) :=
    fun y => triangularMultiplier (c (ψ y)) (fun i => fderiv ℂ c (ψ y) (h i))
  have hg := differentiableAt_polarPair (h := h) hS hψ
  have hU : DifferentiableAt ℂ U x := by
    apply differentiableAt_triangularMultiplier
    · exact (hc.differentiableAt (by norm_num)).comp x hψ
    · exact (differentiableAt_polarPair (h := h) hc hψ).snd
  have hu : (U x).IsInvertible := triangularMultiplier_invertible _ _ hcx
  have he : polarPair F ψ h =ᶠ[𝓝 x] (fun y => U y (polarPair S ψ h y)) := by
    have hlocal : ∀ᶠ z in 𝓝 (ψ x),
        (F z,fun i => fderiv ℂ F z (h i)) =
          triangularMultiplier (c z) (fun i => fderiv ℂ c z (h i))
            (S z,fun i => fderiv ℂ S z (h i)) := by
      filter_upwards [hFS, hFS.fderiv (𝕜 := ℂ), hc.eventually (by norm_num), hS.eventually (by norm_num)]
        with z h0 h1 hc' hS'
      rw [h1, fderiv_fun_mul (hc'.differentiableAt (by norm_num))
        (hS'.differentiableAt (by norm_num)), triangularMultiplier_apply]
      apply Prod.ext h0
      ext i
      simp
    exact hψ.continuousAt.eventually hlocal
  have hsz : polarPair S ψ h x = 0 := by
    apply hu.bijective.injective
    rw [map_zero, ← he.eq_of_nhds, hz]
  refine ⟨hsz, ?_⟩
  apply (simple_unit_multiplier_iff hU hg hsz hu).mp
  rwa [← he.fderiv_eq]
end PermanentBorder.PolarAnalysis

end OAI
