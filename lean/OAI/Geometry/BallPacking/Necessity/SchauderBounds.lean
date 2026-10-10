import Mathlib
import OAI.Geometry.BallPacking.Necessity.MarkedProfiles

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped Manifold
open MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open MeasureTheory
open scoped Topology
open Finset
open scoped ContDiff Classical
open scoped BoundedContinuousFunction
open Topology
open scoped NNReal

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance schauderBoundsInst1 (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst2 (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst3 (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance schauderBoundsInst4 (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 theorem compactCRInverse_leftInverse (R : ℝ) (u : C1HolderSpace E ((1:ℝ)/3))
    (g : CompactHolderSpace E R)
    (hc : HasCompactSupport (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)))
    (hCR : ∀ x : ℂ,
      fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) x Complex.I -
        Complex.I • fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) x 1 =
          compactHolderValue R g x) :
    compactCRInverse R g = u := by
  let f : ℂ → E := holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)
  let v : ℂ → E := compactCRInverseValue R g
  have hf : ContDiff ℝ 1 f := c1Holder_contDiff _ _
  have hv : ContDiff ℝ 1 v := compactCRInverse_contDiff _ _
  have hd : Differentiable ℂ (fun x => f x-v x) := by
    intro x
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    refine ⟨(hf.differentiable (by simp) x).sub (hv.differentiable (by simp) x),?_⟩
    change fderiv ℝ (f-v) x Complex.I = Complex.I • fderiv ℝ (f-v) x 1
    rw [fderiv_sub (hf.differentiable (by simp) x) (hv.differentiable (by simp) x)]
    simp only [sub_apply,smul_sub]
    have hu := hCR x
    have hg := compactCRInverse_rightInverse R g x
    change fderiv ℝ f x Complex.I - Complex.I • fderiv ℝ f x 1 = _ at hu
    change fderiv ℝ v x Complex.I - Complex.I • fderiv ℝ v x 1 = _ at hg
    exact sub_eq_sub_iff_sub_eq_sub.mp (hu.trans hg.symm)
  have ht : Tendsto (fun x => f x-v x) (cocompact ℂ) (𝓝 (0:E)) := by
    have hf0 : f =ᶠ[cocompact ℂ] 0 := by
      simpa only [Filter.coclosedCompact_eq_cocompact] using hasCompactSupport_iff_eventuallyEq.mp hc
    have htf : Tendsto f (cocompact ℂ) (𝓝 (0:E)) := tendsto_const_nhds.congr' hf0.symm
    simpa only [sub_zero] using htf.sub (compactCRInverse_tendsto_zero R g)
  have he := hd.eq_const_of_tendsto_cocompact ht
  apply c1HolderValue_injective
  apply holderValue_injective
  apply BoundedContinuousFunction.ext
  intro x
  have hx := congrFun he x
  change f x-v x=0 at hx
  exact (sub_eq_zero.mp hx).symm

 theorem compactCR_coercivity (R : ℝ) (u : C1HolderSpace E ((1:ℝ)/3))
    (g : CompactHolderSpace E R)
    (hc : HasCompactSupport (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)))
    (hCR : ∀ x : ℂ,
      fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) x Complex.I -
        Complex.I • fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) x 1 =
          compactHolderValue R g x) :
    ‖u‖ ≤ ‖compactCRInverse (E := E) R‖*‖g‖ := by
  rw [←compactCRInverse_leftInverse R u g hc hCR]
  exact (compactCRInverse (E := E) R).le_opNorm g

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance schauderBoundsInst5 (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst6 (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst7 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ F α) := inferInstance
local instance schauderBoundsInst8 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ F α) := inferInstance
local instance schauderBoundsInst9 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace F R) := inferInstance
local instance schauderBoundsInst10 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace F R) := inferInstance

def c1HolderDx : C1HolderSpace E ((1:ℝ)/3) →L[ℝ] HolderSpace ℂ E ((1:ℝ)/3) :=
  (holderJetEval ((1:ℝ)/3) 1).comp (c1HolderDeriv ((1:ℝ)/3))

@[simp] theorem c1HolderDx_value (u : C1HolderSpace E ((1:ℝ)/3)) (z : ℂ) :
    holderValue ((1:ℝ)/3) (c1HolderDx u) z =
      fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z 1 := by
  rw [c1Holder_fderiv]
  rfl

def compactHolderApply (R : ℝ) (A : CompactHolderSpace (E →L[ℝ] E) R)
    (v : HolderSpace ℂ E ((1:ℝ)/3)) : CompactHolderSpace E R :=
  ⟨holderApply ((1:ℝ)/3) A.val v,by
    intro z hz
    change (holderValue ((1:ℝ)/3) A.val z) (holderValue ((1:ℝ)/3) v z)=0
    rw [A.property z hz]
    rfl⟩

omit [CompleteSpace E] in
@[simp] theorem compactHolderApply_value [CompleteSpace E] (R : ℝ) (A : CompactHolderSpace (E →L[ℝ] E) R)
    (v : HolderSpace ℂ E ((1:ℝ)/3)) (z : ℂ) :
    compactHolderValue R (compactHolderApply R A v) z =
      compactHolderValue R A z (holderValue ((1:ℝ)/3) v z) := rfl

omit [CompleteSpace E] in
 theorem compactHolderApply_norm [CompleteSpace E] (R : ℝ) (A : CompactHolderSpace (E →L[ℝ] E) R)
    (v : HolderSpace ℂ E ((1:ℝ)/3)) :
    ‖compactHolderApply R A v‖ ≤ 2*‖A‖*‖v‖ :=
  holderApply_norm ((1:ℝ)/3) A.val v

 theorem compactHolderApply_c1_norm (R : ℝ) (A : CompactHolderSpace (E →L[ℝ] E) R)
    (b : CompactHolderSpace E R) (u : C1HolderSpace E ((1:ℝ)/3)) :
    ‖compactHolderApply R A (c1HolderDx u)+b‖ ≤
      2*‖A‖*‖c1HolderDx (E := E)‖*‖u‖+‖b‖ := by
    calc
      ‖compactHolderApply R A (c1HolderDx u)+b‖ ≤ ‖compactHolderApply R A (c1HolderDx u)‖+‖b‖ := norm_add_le _ _
      _ ≤ 2*‖A‖*‖c1HolderDx u‖+‖b‖ :=
        add_le_add (compactHolderApply_norm R A (c1HolderDx u)) le_rfl
      _ ≤ 2*‖A‖*(‖c1HolderDx (E := E)‖*‖u‖)+‖b‖ :=
        add_le_add (mul_le_mul_of_nonneg_left ((c1HolderDx (E := E)).le_opNorm u)
          (mul_nonneg (by norm_num) (norm_nonneg A))) le_rfl
      _ = _ := by ring

private theorem absorb_half (U C A D B : ℝ) (hU : 0 ≤ U)
    (h : U ≤ C*(2*A*D*U+B)) (hsmall : 2*C*A*D ≤ 1/2) :
    U ≤ 2*C*B := by
  have hm := mul_le_mul_of_nonneg_right hsmall hU
  nlinarith only [h,hm]

 theorem small_principal_coercivity (R : ℝ) (u : C1HolderSpace E ((1:ℝ)/3))
    (A : CompactHolderSpace (E →L[ℝ] E) R) (b : CompactHolderSpace E R)
    (hc : HasCompactSupport (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)))
    (hCR : ∀ z : ℂ,
      fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z Complex.I -
        Complex.I • fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z 1 =
        compactHolderValue R A z
          (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z 1) +
        compactHolderValue R b z)
    (hsmall : 2*‖compactCRInverse (E := E) R‖*‖A‖*‖c1HolderDx (E := E)‖ ≤ 1/2) :
    ‖u‖ ≤ 2*‖compactCRInverse (E := E) R‖*‖b‖ := by
  let g : CompactHolderSpace E R := compactHolderApply R A (c1HolderDx u)+b
  have hg := compactHolderApply_c1_norm R A b u
  have hgCR : ∀ z : ℂ,
      fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z Complex.I -
        Complex.I • fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z 1 =
          compactHolderValue R g z := by
    intro z
    have hgv : compactHolderValue R g z =
        compactHolderValue R A z (holderValue ((1:ℝ)/3) (c1HolderDx u) z)+
        compactHolderValue R b z := rfl
    rw [hgv,c1HolderDx_value]
    exact hCR z
  have h := (compactCR_coercivity R u g hc hgCR).trans
    (mul_le_mul_of_nonneg_left hg (norm_nonneg _))
  exact absorb_half ‖u‖ ‖compactCRInverse (E := E) R‖ ‖A‖ ‖c1HolderDx (E := E)‖
    ‖b‖ (norm_nonneg u) h hsmall

end

section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance schauderBoundsInst11 (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst12 (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst13 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ F α) := inferInstance
local instance schauderBoundsInst14 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ F α) := inferInstance
local instance schauderBoundsInst15 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace F R) := inferInstance
local instance schauderBoundsInst16 (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace F R) := inferInstance

 theorem compactSmoothHolder_interpolation {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℂ → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ z, ‖f z‖ ≤ M) (hd : ∀ z, ‖fderiv ℝ f z‖ ≤ L) :
    ‖compactSmoothHolder ((1:ℝ)/3) (by norm_num) (by norm_num) f hf hc‖ ≤
      max M ((2*M)^((2:ℝ)/3)*L^((1:ℝ)/3)) := by
  refine holder_third_interpolation
    (compactSmoothHolder ((1:ℝ)/3) (by norm_num) (by norm_num) f hf hc) hM hL ?_ ?_
  · intro z
    rw [compactSmoothHolder_apply]
    exact hb z
  have hLip : LipschitzWith ⟨L,hL⟩ f :=
    lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp)) (fun z => by
      exact_mod_cast hd z)
  intro x y
  simp only [compactSmoothHolder_apply]
  have hh := hLip.dist_le_mul x y
  rw [dist_eq_norm,dist_eq_norm] at hh
  rw [dist_eq_norm]
  exact hh

 theorem c1Holder_fderiv_holder (u : C1HolderSpace E ((1:ℝ)/3)) (x y : ℂ) :
    ‖fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) x -
      fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) y‖ ≤
      ‖u‖*‖x-y‖^((1:ℝ)/3) := by
  rw [c1Holder_fderiv,c1Holder_fderiv]
  have he := holderSpace_estimate ((1:ℝ)/3) (by norm_num) (c1HolderDeriv ((1:ℝ)/3) u) x y
  have hn : ‖c1HolderDeriv ((1:ℝ)/3) u‖ ≤ ‖u‖ := le_max_right _ _
  rw [dist_eq_norm] at he
  exact he.trans (mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg (norm_nonneg _) _))

 theorem small_principal_smooth_estimate (R : ℝ)
    (f : ℂ → E) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (A : ℂ → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A)
    (b : ℂ → E) (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hAs : tsupport A ⊆ Metric.closedBall (0:ℂ) R)
    (hbs : tsupport b ⊆ Metric.closedBall (0:ℂ) R)
    (hCR : ∀ z, fderiv ℝ f z Complex.I - Complex.I • fderiv ℝ f z 1 =
      A z (fderiv ℝ f z 1)+b z)
    (M L B K : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hAv : ∀ z, ‖A z‖ ≤ M) (hAD : ∀ z, ‖fderiv ℝ A z‖ ≤ L)
    (hbv : ∀ z, ‖b z‖ ≤ B) (hbD : ∀ z, ‖fderiv ℝ b z‖ ≤ K)
    (hsmall : 2*‖compactCRInverse (E := E) R‖*(max M ((2*M)^((2:ℝ)/3)*L^((1:ℝ)/3)))*‖c1HolderDx (E := E)‖ ≤ 1/2) :
    ∀ x y, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤
      (2*‖compactCRInverse (E := E) R‖*(max B ((2*B)^((2:ℝ)/3)*K^((1:ℝ)/3))))*‖x-y‖^((1:ℝ)/3) := by
  let u := compactSmoothC1Holder ((1:ℝ)/3) (by norm_num) (by norm_num) f hf hfc
  let AA : CompactHolderSpace (E →L[ℝ] E) R :=
    ⟨compactSmoothHolder ((1:ℝ)/3) (by norm_num) (by norm_num) A hA hAc,by
      intro z hz
      apply image_eq_zero_of_notMem_tsupport
      intro h
      have := hAs h
      simp only [Metric.mem_closedBall,dist_zero_right] at this
      exact (not_le_of_gt hz) this⟩
  let bb : CompactHolderSpace E R :=
    ⟨compactSmoothHolder ((1:ℝ)/3) (by norm_num) (by norm_num) b hb hbc,by
      intro z hz
      apply image_eq_zero_of_notMem_tsupport
      intro h
      have := hbs h
      simp only [Metric.mem_closedBall,dist_zero_right] at this
      exact (not_le_of_gt hz) this⟩
  have hAAn : ‖AA‖ ≤ max M ((2*M)^((2:ℝ)/3)*L^((1:ℝ)/3)) := compactSmoothHolder_interpolation A hA hAc M L hM hL hAv hAD
  have hbbn : ‖bb‖ ≤ max B ((2*B)^((2:ℝ)/3)*K^((1:ℝ)/3)) := compactSmoothHolder_interpolation b hb hbc B K hB hK hbv hbD
  have hsm : 2*‖compactCRInverse (E := E) R‖*‖AA‖*‖c1HolderDx (E := E)‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hAAn (mul_nonneg (by norm_num) (norm_nonneg _))) (norm_nonneg _)).trans hsmall
  have hu := small_principal_coercivity R u AA bb hfc hCR hsm
  intro x y
  exact (c1Holder_fderiv_holder u x y).trans
    (mul_le_mul_of_nonneg_right (hu.trans
      (mul_le_mul_of_nonneg_left hbbn (mul_nonneg (by norm_num) (norm_nonneg _))))
      (Real.rpow_nonneg (norm_nonneg _) _))

end

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_fderiv_smul_bound {χ : E → ℝ} {f : E → F} {z : E}
    (hχ : DifferentiableAt ℝ χ z) (hf : DifferentiableAt ℝ f z) :
    ‖fderiv ℝ (fun x => χ x • f x) z‖ ≤
      |χ z| *‖fderiv ℝ f z‖+‖fderiv ℝ χ z‖*‖f z‖ := by
  change ‖fderiv ℝ (χ • f) z‖ ≤ _
  rw [fderiv_smul hχ hf]
  exact (norm_add_le _ _).trans_eq (by
    rw [norm_smul,Real.norm_eq_abs,ContinuousLinearMap.norm_smulRight_apply])

theorem norm_fderiv_apply_bound {A : E → F →L[ℝ] G} {f : E → F} {z : E}
    (hA : DifferentiableAt ℝ A z) (hf : DifferentiableAt ℝ f z) :
    ‖fderiv ℝ (fun x => A x (f x)) z‖ ≤
      ‖A z‖*‖fderiv ℝ f z‖+‖fderiv ℝ A z‖*‖f z‖ := by
  rw [fderiv_clm_apply hA hf]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (A z).opNorm_comp_le _
  · exact ((fderiv ℝ A z).flip.le_opNorm (f z)).trans_eq (by rw [ContinuousLinearMap.opNorm_flip])

theorem cutoff_smul_bounds {χ : E → ℝ} {f : E → F}
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    {S : Set E} (hS : tsupport χ ⊆ S)
    {C D M L : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hχv : ∀ z, |χ z| ≤ C) (hχD : ∀ z, ‖fderiv ℝ χ z‖ ≤ D)
    (hfv : ∀ z ∈ S, ‖f z‖ ≤ M) (hfD : ∀ z ∈ S, ‖fderiv ℝ f z‖ ≤ L) :
    (∀ z, ‖χ z • f z‖ ≤ C*M) ∧
      ∀ z, ‖fderiv ℝ (fun x => χ x • f x) z‖ ≤ C*L+D*M := by
  constructor
  · intro z
    by_cases hz : z ∈ tsupport χ
    · rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hχv z) (hfv z (hS hz)) (norm_nonneg _) hC
    · rw [image_eq_zero_of_notMem_tsupport hz,zero_smul,norm_zero]
      exact mul_nonneg hC hM
  · intro z
    by_cases hz : z ∈ tsupport χ
    · apply (norm_fderiv_smul_bound (hχ.differentiable (by simp) z)
        (hf.differentiable (by simp) z)).trans
      exact add_le_add
        (mul_le_mul (hχv z) (hfD z (hS hz)) (norm_nonneg _) hC)
        (mul_le_mul (hχD z) (hfv z (hS hz)) (norm_nonneg _) hD)
    · have hz' : z ∉ tsupport (fun x => χ x • f x) :=
        fun hh => hz (tsupport_smul_subset_left χ f hh)
      rw [fderiv_of_notMem_tsupport ℝ hz',norm_zero]
      exact add_nonneg (mul_nonneg hC hL) (mul_nonneg hD hM)

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def cutoffCRRemainder (χ : ℂ → ℝ) (A : ℂ → E →L[ℝ] E) (u : ℂ → E) (z : ℂ) : E :=
  fderiv ℝ χ z Complex.I • u z - Complex.I • (fderiv ℝ χ z 1 • u z) -
    A z (fderiv ℝ χ z 1 • u z)

theorem cutoffCR_equation (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (A : ℂ → E →L[ℝ] E) (u : ℂ → E) (hu : ContDiff ℝ ∞ u)
    (hCR : ∀ z ∈ tsupport χ, fderiv ℝ u z Complex.I - Complex.I • fderiv ℝ u z 1 =
      A z (fderiv ℝ u z 1)) (z : ℂ) :
    fderiv ℝ (fun w => χ w • u w) z Complex.I -
      Complex.I • fderiv ℝ (fun w => χ w • u w) z 1 =
      A z (fderiv ℝ (fun w => χ w • u w) z 1)+cutoffCRRemainder χ A u z := by
  change fderiv ℝ (χ • u) z Complex.I - Complex.I • fderiv ℝ (χ • u) z 1 =
    A z (fderiv ℝ (χ • u) z 1)+cutoffCRRemainder χ A u z
  rw [fderiv_smul (hχ.differentiable (by simp) z) (hu.differentiable (by simp) z)]
  by_cases hz : z ∈ tsupport χ
  · simp only [add_apply,smul_apply,
      ContinuousLinearMap.smulRight_apply,map_add,map_smul,smul_add,cutoffCRRemainder]
    rw [sub_eq_iff_eq_add.mp (hCR z hz),smul_add,smul_comm (χ z) Complex.I]
    abel
  · rw [image_eq_zero_of_notMem_tsupport hz]
    simp only [ContinuousLinearMap.smulRight_apply,zero_smul,zero_add,cutoffCRRemainder,
      fderiv_of_notMem_tsupport ℝ hz,zero_apply,map_zero,smul_zero,sub_zero,add_zero]

def scalarDirection (χ : ℂ → ℝ) (w : ℂ) (z : ℂ) : ℝ := fderiv ℝ χ z w

theorem scalarDirection_smooth (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (w : ℂ) :
    ContDiff ℝ ∞ (scalarDirection χ w) :=
  (hχ.fderiv_right (by simp)).clm_apply contDiff_const

theorem scalarDirection_support (χ : ℂ → ℝ) (w : ℂ) :
    tsupport (scalarDirection χ w) ⊆ tsupport χ := by
  apply closure_minimal (support_subset_iff'.mpr ?_) (isClosed_tsupport χ)
  intro z hz
  simp only [scalarDirection,fderiv_of_notMem_tsupport ℝ hz,zero_apply]

theorem scalarDirection_norm (χ : ℂ → ℝ) (w z : ℂ) :
    |scalarDirection χ w z| ≤ ‖fderiv ℝ χ z‖*‖w‖ :=
  (fderiv ℝ χ z).le_opNorm w

theorem scalarDirection_fderiv_norm (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (w z : ℂ) :
    ‖fderiv ℝ (scalarDirection χ w) z‖ ≤ ‖fderiv ℝ (fderiv ℝ χ) z‖*‖w‖ := by
  change ‖fderiv ℝ (fun y => fderiv ℝ χ y w) z‖ ≤ _
  have hd : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right (by simp)
  have hh := norm_fderiv_apply_bound (A := fderiv ℝ χ) (f := fun _ : ℂ => w)
    (hd.differentiable (by simp) z) (differentiableAt_const (c := w))
  simpa only [fderiv_const_apply,norm_zero,mul_zero,zero_add] using hh

theorem cutoffCRRemainder_smooth (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (A : ℂ → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A)
    (u : ℂ → E) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (cutoffCRRemainder χ A u) :=
  (((scalarDirection_smooth χ hχ Complex.I).smul hu).sub
    (((scalarDirection_smooth χ hχ 1).smul hu).const_smul Complex.I)).sub
      (hA.clm_apply ((scalarDirection_smooth χ hχ 1).smul hu))

theorem cutoffCRRemainder_support (χ : ℂ → ℝ) (A : ℂ → E →L[ℝ] E) (u : ℂ → E) :
    tsupport (cutoffCRRemainder χ A u) ⊆ tsupport χ := by
  apply closure_minimal (support_subset_iff'.mpr ?_) (isClosed_tsupport χ)
  intro z hz
  simp only [cutoffCRRemainder,fderiv_of_notMem_tsupport ℝ hz,
    zero_apply,zero_smul,smul_zero,map_zero,sub_zero]

theorem cutoff_direction_product_bounds (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (u : ℂ → E) (hu : ContDiff ℝ ∞ u)
    {D L : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hχD : ∀ z, ‖fderiv ℝ χ z‖ ≤ D)
    (hχDD : ∀ z, ‖fderiv ℝ (fderiv ℝ χ) z‖ ≤ D)
    (huv : ∀ z ∈ tsupport χ, ‖u z‖ ≤ 1)
    (huD : ∀ z ∈ tsupport χ, ‖fderiv ℝ u z‖ ≤ L)
    (w : ℂ) (hw : ‖w‖=1) :
    (∀ z, ‖scalarDirection χ w z • u z‖ ≤ D) ∧
      ∀ z, ‖fderiv ℝ (fun x => scalarDirection χ w x • u x) z‖ ≤ D*(L+1) := by
  have h1 : ∀ z, |scalarDirection χ w z| ≤ D := fun z => by
    simpa only [hw,mul_one] using (scalarDirection_norm χ w z).trans
      (mul_le_mul_of_nonneg_right (hχD z) (norm_nonneg w))
  have h2 : ∀ z, ‖fderiv ℝ (scalarDirection χ w) z‖ ≤ D := fun z => by
    simpa only [hw,mul_one] using (scalarDirection_fderiv_norm χ hχ w z).trans
      (mul_le_mul_of_nonneg_right (hχDD z) (norm_nonneg w))
  have hh := cutoff_smul_bounds (scalarDirection_smooth χ hχ w) hu
    (scalarDirection_support χ w) hD hD (show (0:ℝ) ≤ 1 by norm_num) hL h1 h2 huv huD
  simpa only [mul_one,mul_add] using hh

theorem cutoffCRRemainder_bounds (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (A : ℂ → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A)
    (u : ℂ → E) (hu : ContDiff ℝ ∞ u)
    {D L K : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hχD : ∀ z, ‖fderiv ℝ χ z‖ ≤ D)
    (hχDD : ∀ z, ‖fderiv ℝ (fderiv ℝ χ) z‖ ≤ D)
    (huv : ∀ z ∈ tsupport χ, ‖u z‖ ≤ 1)
    (huD : ∀ z ∈ tsupport χ, ‖fderiv ℝ u z‖ ≤ L)
    (hAv : ∀ z, ‖A z‖ ≤ 1) (hAD : ∀ z, ‖fderiv ℝ A z‖ ≤ K) :
    (∀ z, ‖cutoffCRRemainder χ A u z‖ ≤ 3*D) ∧
      ∀ z, ‖fderiv ℝ (cutoffCRRemainder χ A u) z‖ ≤ 3*D*(L+1)+K*D := by
  let qI : ℂ → E := fun z => scalarDirection χ Complex.I z • u z
  let q1 : ℂ → E := fun z => scalarDirection χ 1 z • u z
  have hqIs : ContDiff ℝ ∞ qI := (scalarDirection_smooth χ hχ Complex.I).smul hu
  have hq1s : ContDiff ℝ ∞ q1 := (scalarDirection_smooth χ hχ 1).smul hu
  have hqI := cutoff_direction_product_bounds χ hχ u hu hD hL hχD hχDD huv huD
    Complex.I Complex.norm_I
  have hq1 := cutoff_direction_product_bounds χ hχ u hu hD hL hχD hχDD huv huD
    1 (norm_one : ‖(1:ℂ)‖=1)
  change (∀ z, ‖qI z‖ ≤ D) ∧ ∀ z, ‖fderiv ℝ qI z‖ ≤ D*(L+1) at hqI
  change (∀ z, ‖q1 z‖ ≤ D) ∧ ∀ z, ‖fderiv ℝ q1 z‖ ≤ D*(L+1) at hq1
  have hg : cutoffCRRemainder χ A u = qI - Complex.I • q1 - fun z => A z (q1 z) := rfl
  have ha (z : ℂ) : ‖A z (q1 z)‖ ≤ D := by
    exact ((A z).le_opNorm _).trans ((mul_le_mul (hAv z) (hq1.1 z)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul D))
  have haD (z : ℂ) : ‖fderiv ℝ (fun x => A x (q1 x)) z‖ ≤ D*(L+1)+K*D := by
    apply (norm_fderiv_apply_bound (hA.differentiable (by simp) z)
      (hq1s.differentiable (by simp) z)).trans
    have h1 := mul_le_mul (hAv z) (hq1.2 z) (norm_nonneg _) (show (0:ℝ) ≤ 1 by norm_num)
    have h2 := mul_le_mul (hAD z) (hq1.1 z) (norm_nonneg _) hK
    simpa only [one_mul] using add_le_add h1 h2
  constructor
  · intro z
    rw [hg]
    change ‖qI z-Complex.I • q1 z-A z (q1 z)‖ ≤ _
    have hh := (norm_sub_le (qI z-Complex.I • q1 z) (A z (q1 z))).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
    rw [norm_smul Complex.I (q1 z),Complex.norm_I,one_mul] at hh
    linarith [hqI.1 z,hq1.1 z,ha z]
  · intro z
    rw [hg,fderiv_sub (f := qI - Complex.I • q1) (g := fun z => A z (q1 z)) ((hqIs.sub (hq1s.const_smul Complex.I)).differentiable (by simp) z)
      ((hA.clm_apply hq1s).differentiable (by simp) z),
      fderiv_sub (f := qI) (g := Complex.I • q1) (hqIs.differentiable (by simp) z)
        ((hq1s.const_smul Complex.I).differentiable (by simp) z),
      fderiv_const_smul (hq1s.differentiable (by simp) z) Complex.I]
    have hh := (norm_sub_le (fderiv ℝ qI z-Complex.I • fderiv ℝ q1 z)
      (fderiv ℝ (fun x => A x (q1 x)) z)).trans (add_le_add (norm_sub_le _ _) le_rfl)
    rw [norm_smul Complex.I (fderiv ℝ q1 z),Complex.norm_I,one_mul] at hh
    nlinarith only [hh,hqI.2 z,hq1.2 z,haD z]

end

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance schauderBoundsInst17 (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst18 (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance schauderBoundsInst19 (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace F R) := inferInstance
local instance schauderBoundsInst20 (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace F R) := inferInstance

def localSchauderBound (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R D L K : ℝ) : ℝ :=
  2*‖compactCRInverse (E := E) R‖*
    max (3*D) ((2*(3*D))^((2:ℝ)/3)*(3*D*(L+1)+K*D)^((1:ℝ)/3))

theorem cutoff_smallCR_schauder (R : ℝ)
    (χ : ℂ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Metric.closedBall (0:ℂ) R)
    (A : ℂ → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A)
    (hAs : tsupport A ⊆ Metric.closedBall (0:ℂ) R)
    (u : ℂ → E) (hu : ContDiff ℝ ∞ u)
    {D L K M : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (hχD : ∀ z, ‖fderiv ℝ χ z‖ ≤ D)
    (hχDD : ∀ z, ‖fderiv ℝ (fderiv ℝ χ) z‖ ≤ D)
    (huv : ∀ z ∈ tsupport χ, ‖u z‖ ≤ 1)
    (huD : ∀ z ∈ tsupport χ, ‖fderiv ℝ u z‖ ≤ L)
    (hAv : ∀ z, ‖A z‖ ≤ M) (hAD : ∀ z, ‖fderiv ℝ A z‖ ≤ K)
    (hCR : ∀ z ∈ tsupport χ, fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1 =
      A z (fderiv ℝ u z 1))
    (hsmall : 2*‖compactCRInverse (E := E) R‖*
      max M ((2*M)^((2:ℝ)/3)*K^((1:ℝ)/3))*‖c1HolderDx (E := E)‖ ≤ 1/2) :
    ∀ x y, ‖fderiv ℝ (fun z => χ z • u z) x-fderiv ℝ (fun z => χ z • u z) y‖ ≤
      localSchauderBound E R D L K*‖x-y‖^((1:ℝ)/3) := by
  let b := cutoffCRRemainder χ A u
  have hbs : tsupport b ⊆ tsupport χ := cutoffCRRemainder_support χ A u
  have hbc : HasCompactSupport b := hχc.of_isClosed_subset (isClosed_tsupport b) hbs
  have hbb := cutoffCRRemainder_bounds χ hχ A hA u hu hD hL hK hχD hχDD huv huD
    (fun z => (hAv z).trans hM1) hAD
  exact small_principal_smooth_estimate R (fun z => χ z • u z) (hχ.smul hu)
    hχc.smul_right A hA hAc b (cutoffCRRemainder_smooth χ hχ A hA u hu) hbc hAs
    (hbs.trans hχs) (cutoffCR_equation χ hχ A u hu hCR)
    M K (3*D) (3*D*(L+1)+K*D) hM hK (by positivity) (by positivity)
    hAv hAD hbb.1 hbb.2 hsmall

end HigherDimensionalBallPacking.Rigidity

end

end OAI
