import OAI.InformationTheory.PhotonNumber.SpectralForms
import OAI.InformationTheory.PhotonNumber.SpectralLog
import OAI.InformationTheory.PhotonNumber.Continuity

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace EnsembleL2

section
open scoped BigOperators ComplexConjugate
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def secondMoment (v : I → E) (Z : E →L[ℂ] E) : ℝ := ∑' i, ‖Z (v i)‖^2

theorem shifted_secondMoment (v : I → E) (hv : HasSum (fun i => ‖v i‖^2) 1)
    (Z : E →L[ℂ] E) (c : ℂ) :
    secondMoment v (Z-c • ContinuousLinearMap.id ℂ E)=
      secondMoment v Z-2*(c*conj (mean v Z)).re+‖c‖^2 := by
  have hm := ((mean_hasSum v hv.summable Z).mapL Complex.conjCLE.toContinuousLinearMap).mul_left c
  change HasSum (fun i => c*conj (inner ℂ (v i) (Z (v i)))) (c*conj (mean v Z)) at hm
  have hr := (hm.mapL Complex.reCLM).mul_left 2
  have hh := ((image_summable v hv.summable Z).hasSum.sub hr).add (hv.mul_left (‖c‖^2))
  have he (i : I) : ‖(Z-c • ContinuousLinearMap.id ℂ E) (v i)‖^2 =
      ‖Z (v i)‖^2-2*(c*conj (inner ℂ (v i) (Z (v i)))).re+‖c‖^2*‖v i‖^2 := by
    simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply, norm_sub_sq (𝕜 := ℂ),
      inner_smul_right, inner_conj_symm, norm_smul, mul_pow]
    rfl
  have hs : HasSum (fun i => ‖(Z-c • ContinuousLinearMap.id ℂ E) (v i)‖^2)
      (secondMoment v Z-2*(c*conj (mean v Z)).re+‖c‖^2) := by
    simpa only [he, secondMoment, Complex.reCLM_apply, Complex.conjCLE_apply, mul_one] using hh
  exact hs.tsum_eq

theorem center_secondMoment (v : I → E) (hv : HasSum (fun i => ‖v i‖^2) 1)
    (Z : E →L[ℂ] E) :
    secondMoment v (center v Z)=secondMoment v Z-‖mean v Z‖^2 := by
  rw [center, shifted_secondMoment v hv Z, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]
  ring

theorem mean_square_le (v : I → E) (hv : HasSum (fun i => ‖v i‖^2) 1)
    (Z : E →L[ℂ] E) : ‖mean v Z‖^2 ≤ secondMoment v Z := by
  have hp : 0 ≤ secondMoment v (center v Z) := tsum_nonneg (fun _ => sq_nonneg _)
  rw [center_secondMoment v hv Z] at hp
  linarith

def mixture (v : I → E) (w : J → E) (t : ℝ) : I ⊕ J → E :=
  Sum.elim (fun i => (Real.sqrt t : ℂ) • v i) (fun j => (Real.sqrt (1-t) : ℂ) • w j)

theorem mixture_norm_left (v : I → E) (w : J → E) {t : ℝ} (ht : 0 ≤ t) (i : I) :
    ‖mixture v w t (.inl i)‖^2=t*‖v i‖^2 := by
  simp only [mixture, Sum.elim_inl, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg t), mul_pow, Real.sq_sqrt ht]

theorem mixture_norm_right (v : I → E) (w : J → E) {t : ℝ} (ht : t ≤ 1) (j : J) :
    ‖mixture v w t (.inr j)‖^2=(1-t)*‖w j‖^2 := by
  simp only [mixture, Sum.elim_inr, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg (1-t)), mul_pow, Real.sq_sqrt (sub_nonneg.mpr ht)]

theorem mixture_hasSum (v : I → E) (w : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1) :
    HasSum (fun k => ‖mixture v w t k‖^2) 1 := by
  have h₁ : HasSum ((fun k => ‖mixture v w t k‖^2) ∘ Sum.inl) t := by
    simpa only [Function.comp_def, mixture_norm_left v w ht.1, mul_one] using hv.mul_left t
  have h₂ : HasSum ((fun k => ‖mixture v w t k‖^2) ∘ Sum.inr) (1-t) := by
    simpa only [Function.comp_def, mixture_norm_right v w ht.2, mul_one] using hw.mul_left (1-t)
  simpa only [add_sub_cancel] using h₁.sum h₂

theorem mixture_mean (v : I → E) (w : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2)) (Z : E →L[ℂ] E) :
    mean (mixture v w t) Z=(t:ℂ)*mean v Z+((1-t:ℝ):ℂ)*mean w Z := by
  have he {a : ℝ} (ha : 0 ≤ a) (x : E) :
      inner ℂ ((Real.sqrt a:ℂ) • x) (Z ((Real.sqrt a:ℂ) • x))=(a:ℂ)*inner ℂ x (Z x) := by
    simp only [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt ha]
  have h₁ : HasSum ((fun k => inner ℂ (mixture v w t k) (Z (mixture v w t k))) ∘ Sum.inl)
      ((t:ℂ)*mean v Z) := by
    simpa only [Function.comp_def, mixture, Sum.elim_inl, he ht.1] using
      (mean_hasSum v hv Z).mul_left (t:ℂ)
  have h₂ : HasSum ((fun k => inner ℂ (mixture v w t k) (Z (mixture v w t k))) ∘ Sum.inr)
      (((1-t:ℝ):ℂ)*mean w Z) := by
    simpa only [Function.comp_def, mixture, Sum.elim_inr, he (sub_nonneg.mpr ht.2)] using
      (mean_hasSum w hw Z).mul_left ((1-t:ℝ):ℂ)
  exact (h₁.sum h₂).tsum_eq

theorem mixture_secondMoment (v : I → E) (w : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2)) (Z : E →L[ℂ] E) :
    secondMoment (mixture v w t) Z=t*secondMoment v Z+(1-t)*secondMoment w Z := by
  have h₁ : HasSum ((fun k => ‖Z (mixture v w t k)‖^2) ∘ Sum.inl) (t*secondMoment v Z) := by
    simpa only [Function.comp_def, mixture, Sum.elim_inl, map_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt ht.1, secondMoment] using
      (image_summable v hv Z).hasSum.mul_left t
  have h₂ : HasSum ((fun k => ‖Z (mixture v w t k)‖^2) ∘ Sum.inr) ((1-t)*secondMoment w Z) := by
    simpa only [Function.comp_def, mixture, Sum.elim_inr, map_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (sub_nonneg.mpr ht.2), secondMoment] using
      (image_summable w hw Z).hasSum.mul_left (1-t)
  exact (h₁.sum h₂).tsum_eq
end

open scoped BigOperators
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem complex_mixture_square (t : ℝ) (a b : ℂ) :
    t*‖a‖^2+(1-t)*‖b‖^2-‖(t:ℂ)*a+((1-t:ℝ):ℂ)*b‖^2 = t*(1-t)*‖a-b‖^2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem mixture_variance (v : I → E) (w : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1) (Z : E →L[ℂ] E) :
    secondMoment (mixture v w t) (center (mixture v w t) Z)=
      t*secondMoment v (center v Z)+(1-t)*secondMoment w (center w Z)+
        t*(1-t)*‖mean v Z-mean w Z‖^2 := by
  rw [center_secondMoment _ (mixture_hasSum v w ht hv hw),
    mixture_secondMoment v w ht hv.summable hw.summable,
    mixture_mean v w ht hv.summable hw.summable,
    center_secondMoment v hv, center_secondMoment w hw]
  linear_combination complex_mixture_square t (mean v Z) (mean w Z)

theorem mixture_variance_left (v : I → E) (w : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1) (Z : E →L[ℂ] E) :
    t*secondMoment v (center v Z) ≤ secondMoment (mixture v w t) (center (mixture v w t) Z) := by
  rw [mixture_variance v w ht hv hw Z]
  have h₁ : 0 ≤ (1-t)*secondMoment w (center w Z) :=
    mul_nonneg (sub_nonneg.mpr ht.2) (tsum_nonneg (fun _ => sq_nonneg _))
  have h₂ := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg ‖mean v Z-mean w Z‖)
  linarith

theorem mixture_between_variance (v : I → E) (w : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1) (Z : E →L[ℂ] E) :
    t*(1-t)*‖mean v Z-mean w Z‖^2 ≤ secondMoment (mixture v w t) (center (mixture v w t) Z) := by
  rw [mixture_variance v w ht hv hw Z]
  have h₁ : 0 ≤ t*secondMoment v (center v Z) :=
    mul_nonneg ht.1 (tsum_nonneg (fun _ => sq_nonneg _))
  have h₂ : 0 ≤ (1-t)*secondMoment w (center w Z) :=
    mul_nonneg (sub_nonneg.mpr ht.2) (tsum_nonneg (fun _ => sq_nonneg _))
  linarith
end EnsembleL2

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

def ensemble (i : S.I) : E := (Real.sqrt (S.p i) : ℂ) • S.basis i

theorem ensemble_norm (i : S.I) : ‖S.ensemble i‖^2=S.p i := by
  simp only [ensemble, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), S.basis.orthonormal.norm_eq_one i, mul_one]
  exact Real.sq_sqrt (S.pos i).le

theorem ensemble_hasSum : HasSum (fun i => ‖S.ensemble i‖^2) 1 := by
  simpa only [S.ensemble_norm] using S.sum

theorem image_ensemble_norm (Z : E →L[ℂ] E) (i : S.I) :
    ‖Z (S.ensemble i)‖^2=S.p i*‖Z (S.basis i)‖^2 := by
  simp only [ensemble, map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (S.pos i).le]

theorem minus_quad_ensemble (Z : E →L[ℂ] E) :
    S.quad minus Z=∑' i, ‖Z (S.ensemble i)‖^2 := by
  simp only [quad, S.minus_entry Z, S.image_ensemble_norm Z]
  have hs := BKM.weighted_column_summable S.basis S.p (fun i => (S.pos i).le) S.sum.summable Z
  rw [hs.tsum_prod, ← hs.tsum_comm]
  simp only [tsum_mul_left, (BKM.hasSum_column S.basis Z _).tsum_eq]

theorem plus_quad_ensemble (Z : E →L[ℂ] E) :
    S.quad plus Z=∑' i, ‖Z.adjoint (S.ensemble i)‖^2 := by
  simp only [quad, S.plus_entry Z, S.image_ensemble_norm Z.adjoint]
  rw [(BKM.weighted_row_summable S.basis S.p (fun i => (S.pos i).le) S.sum.summable Z).tsum_prod]
  simp only [tsum_mul_left, (BKM.hasSum_row S.basis Z _).tsum_eq]
end ThermalSpectral.Space

namespace EnsembleL2
open scoped ComplexConjugate
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem mean_eq_of_operator_eq (b : HilbertBasis K ℂ E) {v : I → E} {w : J → E}
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (he : TraceEnsemble.operator v=TraceEnsemble.operator w) (Z : E →L[ℂ] E) :
    mean v Z=mean w Z :=
  CrossEnsemble.pairing_eq_of_operator_eq b hv hv hw hw he Z

theorem secondMoment_eq_of_operator_eq (b : HilbertBasis K ℂ E) {v : I → E} {w : J → E}
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (he : TraceEnsemble.operator v=TraceEnsemble.operator w) (Z : E →L[ℂ] E) :
    secondMoment v Z=secondMoment w Z := by
  have hh := congrArg Complex.re (mean_eq_of_operator_eq b hv hw he (Z.adjoint ∘L Z))
  have ht (x : E) : (inner ℂ x ((Z.adjoint ∘L Z) x)).re=‖Z x‖^2 := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    change ((‖Z x‖ : ℂ)^2).re=‖Z x‖^2
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have h₁ := (mean_hasSum v hv (Z.adjoint ∘L Z)).mapL Complex.reCLM
  have h₂ := (mean_hasSum w hw (Z.adjoint ∘L Z)).mapL Complex.reCLM
  have hm₁ : secondMoment v Z=(mean v (Z.adjoint ∘L Z)).re := by
    simpa only [Complex.reCLM_apply, ht, secondMoment] using h₁.tsum_eq
  have hm₂ : secondMoment w Z=(mean w (Z.adjoint ∘L Z)).re := by
    simpa only [Complex.reCLM_apply, ht, secondMoment] using h₂.tsum_eq
  exact hm₁.trans (hh.trans hm₂.symm)

theorem center_eq_of_operator_eq (b : HilbertBasis K ℂ E) {v : I → E} {w : J → E}
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (he : TraceEnsemble.operator v=TraceEnsemble.operator w) (Z : E →L[ℂ] E) :
    center v Z=center w Z := by
  simp only [center, mean_eq_of_operator_eq b hv hw he Z]

theorem variance_eq_of_operator_eq (b : HilbertBasis K ℂ E) {v : I → E} {w : J → E}
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (he : TraceEnsemble.operator v=TraceEnsemble.operator w) (Z : E →L[ℂ] E) :
    secondMoment v (center v Z)=secondMoment w (center w Z) := by
  rw [center_eq_of_operator_eq b hv hw he Z]
  exact secondMoment_eq_of_operator_eq b hv hw he _
end EnsembleL2

namespace BKM
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
def mean (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) : ℂ :=
  ∑' j, (p j : ℂ)*entry b Z j j
def center (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) : E →L[ℂ] E :=
  Z-mean b p Z • ContinuousLinearMap.id ℂ E
end BKM

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

theorem ensemble_operator (T : E →L[ℂ] E) (hT : T.IsSymmetric)
    (he : ∀ j, T (S.basis j)=(S.p j : ℂ) • S.basis j) :
    TraceEnsemble.operator S.ensemble=T :=
  CrossEnsemble.eigenEnsemble_operator S.basis S.p (fun j => (S.pos j).le) S.sum.summable T hT he

theorem ensemble_mean (Z : E →L[ℂ] E) : EnsembleL2.mean S.ensemble Z=BKM.mean S.basis S.p Z := by
  unfold EnsembleL2.mean BKM.mean
  apply tsum_congr
  intro j
  simp only [ensemble, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (S.pos j).le]
  rfl

theorem ensemble_center (Z : E →L[ℂ] E) : EnsembleL2.center S.ensemble Z=BKM.center S.basis S.p Z := by
  simp only [EnsembleL2.center, S.ensemble_mean, BKM.center]

theorem minus_quad_of_ensemble {I : Type*} (v : I → E)
    (hv : Summable (fun i => ‖v i‖^2)) (he : TraceEnsemble.operator S.ensemble=TraceEnsemble.operator v)
    (Z : E →L[ℂ] E) : S.quad minus Z=EnsembleL2.secondMoment v Z := by
  rw [S.minus_quad_ensemble]
  exact EnsembleL2.secondMoment_eq_of_operator_eq S.basis S.ensemble_hasSum.summable hv he Z

theorem plus_quad_of_ensemble {I : Type*} (v : I → E)
    (hv : Summable (fun i => ‖v i‖^2)) (he : TraceEnsemble.operator S.ensemble=TraceEnsemble.operator v)
    (Z : E →L[ℂ] E) : S.quad plus Z=EnsembleL2.secondMoment v Z.adjoint := by
  rw [S.plus_quad_ensemble]
  exact EnsembleL2.secondMoment_eq_of_operator_eq S.basis S.ensemble_hasSum.summable hv he Z.adjoint
end ThermalSpectral.Space

namespace TensorLp
open KrausBounded
variable {A B I J : Type*}

theorem conditionalLeft_center (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) :
    conditionalLeft y hy (EnsembleL2.center (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z)=
      EnsembleL2.center x (conditionalLeft y hy Z) := by
  have hh : EnsembleL2.mean x (conditionalLeft y hy Z)=
      EnsembleL2.mean (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z :=
    (conditionalLeft_mean x y hx hy Z).tsum_eq
  simp only [EnsembleL2.center]
  rw [hh]
  simp only [conditionalLeft, sub_eq_add_neg, ← neg_smul, dual_add, dual_smul, dual_id]

theorem conditionalRight_center (x : I → H A) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (Z : H (A × B) →L[ℂ] H (A × B)) :
    conditionalRight x hx (EnsembleL2.center (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z)=
      EnsembleL2.center y (conditionalRight x hx Z) := by
  have hh : EnsembleL2.mean y (conditionalRight x hx Z)=
      EnsembleL2.mean (fun ij : I × J => tensor (x ij.1) (y ij.2)) Z :=
    (conditionalRight_mean x y hx hy Z).tsum_eq
  simp only [EnsembleL2.center]
  rw [hh]
  simp only [conditionalRight, sub_eq_add_neg, ← neg_smul, dual_add, dual_smul, dual_id]
end TensorLp

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate

abbrev RawIndex (n : ℕ) := (NumberIndex n × NumberIndex n) ×
  (NumberIndex n × (NumberIndex n × NumberIndex n))

def rawEnsemble {n : ℕ} (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (ik : RawIndex n) : Fock n :=
  rawJointKraus η θ hη hθ τ ik.2 (tensor (rootColumn ρ ik.1.1) (rootColumn σ ik.1.2))

theorem rawEnsemble_norm {n : ℕ} (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τ : State n) : HasSum (fun i => ‖rawEnsemble η θ hη hθ ρ σ τ i‖^2) 1 := by
  let v : NumberIndex n × NumberIndex n → H (NumberIndex n × NumberIndex n) :=
    fun ij => tensor (rootColumn ρ ij.1) (rootColumn σ ij.2)
  have hv : HasSum (fun ij => ‖v ij‖^2) 1 := by
    simpa only [one_mul] using tensorFamily_norm (rootColumn ρ) (rootColumn σ) 1 1
      (rootColumn_norm ρ) (rootColumn_norm σ)
  have hh := family_hasSum (rawJointKraus η θ hη hθ τ) (rawJointKraus_norm η θ hη hθ τ) v 1 hv
  exact hh

def rawEnsembleEquiv (n : ℕ) : RawIndex n ≃
    (NumberIndex n × NumberIndex n) × (NumberIndex n × (NumberIndex n × NumberIndex n)) where
  toFun i := (i.2.2, (i.2.1,i.1))
  invFun i := (i.2.2,(i.2.1,i.1))
  left_inv _ := rfl
  right_inv _ := rfl

theorem rawEnsemble_operator {n : ℕ} (η θ : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (ρ σ τ : State n) :
    TraceEnsemble.operator (rawEnsemble η θ hη hθ ρ σ τ)=
      (beamOutput θ hθ (beamOutput η hη ρ σ) τ).op := by
  let v : NumberIndex n × (NumberIndex n × NumberIndex n) → Fock n := fun i =>
    slice (beamUnitary η hη (tensor (rootColumn ρ i.2.1) (rootColumn σ i.2.2))) i.1
  have hv : HasSum (fun i => ‖v i‖^2) 1 := by
    change HasSum (fun bi : NumberIndex n × (NumberIndex n × NumberIndex n) =>
      ‖slice (mixedVector η hη ρ σ bi.2) bi.1‖^2) 1
    exact hasSum_slice_family (v := mixedVector η hη ρ σ) (mixedVector_norm η hη ρ σ)
  have he : TraceEnsemble.operator v=(beamOutput η hη ρ σ).op := rfl
  have hr := TraceEnsemble.operator_reindex (rawEnsembleEquiv n)
    (fun i => firstKraus θ hθ τ i.1 (v i.2))
  exact hr.trans (firstKraus_ensemble θ hθ (beamOutput η hη ρ σ) τ v hv he)

theorem raw_centered_arithmetic {n : ℕ} (η θ : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (ρ σ τ : State n)
    (Z : Fock n →L[ℂ] Fock n) :
    EnsembleL2.secondMoment (rootColumn ρ)
      (EnsembleL2.center (rootColumn ρ)
        (conditionalLeft (rootColumn σ) (rootColumn_norm σ) (rawDual η θ hη hθ τ Z)))+
    EnsembleL2.secondMoment (rootColumn σ)
      (EnsembleL2.center (rootColumn σ)
        (conditionalRight (rootColumn ρ) (rootColumn_norm ρ) (rawDual η θ hη hθ τ Z))) ≤
      EnsembleL2.secondMoment (rawEnsemble η θ hη hθ ρ σ τ)
        (EnsembleL2.center (rawEnsemble η θ hη hθ ρ σ τ) Z) := by
  have hh := physical_arithmetic_projection η θ hη hθ ρ σ τ Z
  dsimp only at hh
  rw [conditionalLeft_center _ _ (rootColumn_norm ρ) (rootColumn_norm σ),
    conditionalRight_center _ _ (rootColumn_norm ρ) (rootColumn_norm σ)] at hh
  exact hh
end EntropyPhotonNumber

namespace EnsembleL2
open scoped ComplexConjugate
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem mean_adjoint (v : I → E) (Z : E →L[ℂ] E) : mean v Z.adjoint=conj (mean v Z) := by
  simp only [mean, ContinuousLinearMap.adjoint_inner_right, inner_conj_symm, Complex.conj_tsum]

theorem center_adjoint (v : I → E) (Z : E →L[ℂ] E) : center v Z.adjoint=(center v Z).adjoint := by
  simp only [center, mean_adjoint, map_sub, map_smulₛₗ,
    ContinuousLinearMap.adjoint_id]
end EnsembleL2

namespace EntropyPhotonNumber
open TensorLp KrausBounded
open scoped BigOperators ComplexConjugate
variable {n : ℕ}

def rawFirstSlice (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τ : State n) (Z : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  conditionalLeft (rootColumn σ) (rootColumn_norm σ) (rawDual η θ hη hθ τ Z)

def rawSecondSlice (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ τ : State n) (Z : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  conditionalRight (rootColumn ρ) (rootColumn_norm ρ) (rawDual η θ hη hθ τ Z)

theorem rawFirstSlice_adjoint (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τ : State n) (Z : Fock n →L[ℂ] Fock n) :
    rawFirstSlice η θ hη hθ σ τ Z.adjoint=(rawFirstSlice η θ hη hθ σ τ Z).adjoint := by
  simp only [rawFirstSlice, conditionalLeft, rawDual, dual_adjoint]

theorem rawSecondSlice_adjoint (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ τ : State n) (Z : Fock n →L[ℂ] Fock n) :
    rawSecondSlice η θ hη hθ ρ τ Z.adjoint=(rawSecondSlice η θ hη hθ ρ τ Z).adjoint := by
  simp only [rawSecondSlice, conditionalRight, rawDual, dual_adjoint]

theorem replaced_arithmetic {J : Type*} (η θ κ : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (v : J → Fock n) (hv : HasSum (fun j => ‖v j‖^2) 1)
    (Z : Fock n →L[ℂ] Fock n) :
    let m := EnsembleL2.mixture (rawEnsemble η θ hη hθ ρ σ τ) v (1-κ)
    (1-κ)*(EnsembleL2.secondMoment (rootColumn ρ)
      (EnsembleL2.center (rootColumn ρ) (rawFirstSlice η θ hη hθ σ τ Z))+
      EnsembleL2.secondMoment (rootColumn σ)
      (EnsembleL2.center (rootColumn σ) (rawSecondSlice η θ hη hθ ρ τ Z))) ≤
      EnsembleL2.secondMoment m (EnsembleL2.center m Z) ∧
    (1-κ)*(EnsembleL2.secondMoment (rootColumn ρ)
      (EnsembleL2.center (rootColumn ρ) (rawFirstSlice η θ hη hθ σ τ Z)).adjoint+
      EnsembleL2.secondMoment (rootColumn σ)
      (EnsembleL2.center (rootColumn σ) (rawSecondSlice η θ hη hθ ρ τ Z)).adjoint) ≤
      EnsembleL2.secondMoment m (EnsembleL2.center m Z).adjoint := by
  dsimp only
  have hk : 1-κ ∈ Set.Icc (0:ℝ) 1 := ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
  have hh (T : Fock n →L[ℂ] Fock n) :=
    (mul_le_mul_of_nonneg_left (raw_centered_arithmetic η θ hη hθ ρ σ τ T) hk.1).trans
      (EnsembleL2.mixture_variance_left (rawEnsemble η θ hη hθ ρ σ τ) v hk
        (rawEnsemble_norm η θ hη hθ ρ σ τ) hv T)
  refine ⟨hh Z, ?_⟩
  have ha := hh Z.adjoint
  change (1-κ)*(EnsembleL2.secondMoment (rootColumn ρ)
      (EnsembleL2.center (rootColumn ρ) (rawFirstSlice η θ hη hθ σ τ Z.adjoint))+
    EnsembleL2.secondMoment (rootColumn σ)
      (EnsembleL2.center (rootColumn σ) (rawSecondSlice η θ hη hθ ρ τ Z.adjoint))) ≤ _ at ha
  simpa only [rawFirstSlice_adjoint, rawSecondSlice_adjoint, EnsembleL2.center_adjoint] using ha
end EntropyPhotonNumber

namespace EnsembleL2
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem mixture_operator (v : I → E) (w : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2)) :
    TraceEnsemble.operator (mixture v w t)=
      (t:ℂ) • TraceEnsemble.operator v+((1-t:ℝ):ℂ) • TraceEnsemble.operator w := by
  have he {a : ℝ} (ha : 0 ≤ a) (x : E) :
      InnerProductSpace.rankOne ℂ ((Real.sqrt a:ℂ) • x) ((Real.sqrt a:ℂ) • x)=
        (a:ℂ) • InnerProductSpace.rankOne ℂ x x := by
    ext y
    simp only [InnerProductSpace.rankOne_apply, inner_smul_left, Complex.conj_ofReal,
      smul_apply, smul_smul]
    congr 1
    rw [mul_right_comm, ← Complex.ofReal_mul, Real.mul_self_sqrt ha]
  have h₁ : HasSum ((fun k => InnerProductSpace.rankOne ℂ (mixture v w t k) (mixture v w t k)) ∘ Sum.inl)
      ((t:ℂ) • TraceEnsemble.operator v) := by
    simpa only [Function.comp_def, mixture, Sum.elim_inl, he ht.1] using
      (TraceEnsemble.hasSum_rankOne hv).const_smul (t:ℂ)
  have h₂ : HasSum ((fun k => InnerProductSpace.rankOne ℂ (mixture v w t k) (mixture v w t k)) ∘ Sum.inr)
      (((1-t:ℝ):ℂ) • TraceEnsemble.operator w) := by
    simpa only [Function.comp_def, mixture, Sum.elim_inr, he (sub_nonneg.mpr ht.2)] using
      (TraceEnsemble.hasSum_rankOne hw).const_smul ((1-t:ℝ):ℂ)
  exact (h₁.sum h₂).tsum_eq
end EnsembleL2

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

theorem minus_center_of_ensemble (v : I → E) (hv : Summable (fun i => ‖v i‖^2))
    (he : TraceEnsemble.operator S.ensemble=TraceEnsemble.operator v) (Z : E →L[ℂ] E) :
    S.quad minus (BKM.center S.basis S.p Z)=EnsembleL2.secondMoment v (EnsembleL2.center v Z) := by
  rw [S.minus_quad_of_ensemble v hv he, ← S.ensemble_center,
    EnsembleL2.center_eq_of_operator_eq S.basis S.ensemble_hasSum.summable hv he]

theorem plus_center_of_ensemble (v : I → E) (hv : Summable (fun i => ‖v i‖^2))
    (he : TraceEnsemble.operator S.ensemble=TraceEnsemble.operator v) (Z : E →L[ℂ] E) :
    S.quad plus (BKM.center S.basis S.p Z)=EnsembleL2.secondMoment v (EnsembleL2.center v Z).adjoint := by
  rw [S.plus_quad_of_ensemble v hv he, ← S.ensemble_center,
    EnsembleL2.center_eq_of_operator_eq S.basis S.ensemble_hasSum.summable hv he]
end ThermalSpectral.Space

namespace EntropyPhotonNumber
open ThermalSpectral ThermalSpectral.Space
variable {n : ℕ}

theorem replaced_spectral_arithmetic (η θ κ : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1)
    (ρ σ τ ω : State n) (S₀ S₁ S₂ : Space (Fock n))
    (he₁ : ∀ j, ρ.op (S₁.basis j)=(S₁.p j:ℂ) • S₁.basis j)
    (he₂ : ∀ j, σ.op (S₂.basis j)=(S₂.p j:ℂ) • S₂.basis j)
    (he₀ : TraceEnsemble.operator S₀.ensemble=
      ((1-κ:ℝ):ℂ) • (beamOutput θ hθ (beamOutput η hη ρ σ) τ).op+(κ:ℂ) • ω.op)
    (Z : Fock n →L[ℂ] Fock n) :
    (1-κ)*(S₁.quad minus (BKM.center S₁.basis S₁.p (rawFirstSlice η θ hη hθ σ τ Z))+
      S₂.quad minus (BKM.center S₂.basis S₂.p (rawSecondSlice η θ hη hθ ρ τ Z))) ≤
      S₀.quad minus (BKM.center S₀.basis S₀.p Z) ∧
    (1-κ)*(S₁.quad plus (BKM.center S₁.basis S₁.p (rawFirstSlice η θ hη hθ σ τ Z))+
      S₂.quad plus (BKM.center S₂.basis S₂.p (rawSecondSlice η θ hη hθ ρ τ Z))) ≤
      S₀.quad plus (BKM.center S₀.basis S₀.p Z) := by
  have hr : TraceEnsemble.operator S₁.ensemble=TraceEnsemble.operator (rootColumn ρ) :=
    (S₁.ensemble_operator ρ.op ρ.positive.isSymmetric he₁).trans (rootColumn_operator ρ).symm
  have hs : TraceEnsemble.operator S₂.ensemble=TraceEnsemble.operator (rootColumn σ) :=
    (S₂.ensemble_operator σ.op σ.positive.isSymmetric he₂).trans (rootColumn_operator σ).symm
  let v := EnsembleL2.mixture (rawEnsemble η θ hη hθ ρ σ τ) (rootColumn ω) (1-κ)
  have hk : 1-κ ∈ Set.Icc (0:ℝ) 1 := ⟨sub_nonneg.mpr hκ.2,sub_le_self _ hκ.1⟩
  have hv := EnsembleL2.mixture_hasSum (rawEnsemble η θ hη hθ ρ σ τ) (rootColumn ω) hk
    (rawEnsemble_norm η θ hη hθ ρ σ τ) (rootColumn_norm ω)
  have he : TraceEnsemble.operator S₀.ensemble=TraceEnsemble.operator v := by
    dsimp only [v]
    rw [he₀, EnsembleL2.mixture_operator _ _ hk (rawEnsemble_norm η θ hη hθ ρ σ τ).summable
      (rootColumn_norm ω).summable, rawEnsemble_operator, rootColumn_operator, sub_sub_cancel]
  rw [S₁.minus_center_of_ensemble _ (rootColumn_norm ρ).summable hr,
    S₂.minus_center_of_ensemble _ (rootColumn_norm σ).summable hs,
    S₀.minus_center_of_ensemble v hv.summable he,
    S₁.plus_center_of_ensemble _ (rootColumn_norm ρ).summable hr,
    S₂.plus_center_of_ensemble _ (rootColumn_norm σ).summable hs,
    S₀.plus_center_of_ensemble v hv.summable he]
  exact replaced_arithmetic η θ κ hη hθ hκ ρ σ τ (rootColumn ω) (rootColumn_norm ω) Z
end EntropyPhotonNumber

namespace BKM

section
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem entry_add (b : HilbertBasis J ℂ E) (Z T : E →L[ℂ] E) (i j : J) :
    entry b (Z+T) i j=entry b Z i j+entry b T i j := by simp [entry]
theorem entry_sub (b : HilbertBasis J ℂ E) (Z T : E →L[ℂ] E) (i j : J) :
    entry b (Z-T) i j=entry b Z i j-entry b T i j := by simp [entry]
theorem entry_smul (b : HilbertBasis J ℂ E) (c : ℂ) (Z : E →L[ℂ] E) (i j : J) :
    entry b (c • Z) i j=c*entry b Z i j := by simp [entry]
theorem entry_norm_le (b : HilbertBasis J ℂ E) (Z : E →L[ℂ] E) (i j : J) :
    ‖entry b Z i j‖ ≤ ‖Z‖ := by
  calc
    _ ≤ ‖b i‖*‖Z (b j)‖ := norm_inner_le_norm _ _
    _ ≤ ‖b i‖*(‖Z‖*‖b j‖) := mul_le_mul_of_nonneg_left (Z.le_opNorm _) (norm_nonneg _)
    _ = ‖Z‖ := by simp [b.orthonormal.norm_eq_one]

theorem mean_summable (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    (Z : E →L[ℂ] E) : Summable (fun j => (p j : ℂ)*entry b Z j j) := by
  apply (hs.mul_right ‖Z‖).of_norm_bounded
  intro j
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp j)]
  exact mul_le_mul_of_nonneg_left (entry_norm_le b Z j j) (hp j)

theorem mean_add (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    (Z T : E →L[ℂ] E) : mean b p (Z+T)=mean b p Z+mean b p T := by
  simp only [mean, entry_add, mul_add]
  exact (mean_summable b p hp hs Z).tsum_add (mean_summable b p hp hs T)

theorem mean_smul (b : HilbertBasis J ℂ E) (p : J → ℝ) (c : ℂ) (Z : E →L[ℂ] E) :
    mean b p (c • Z)=c*mean b p Z := by
  simp only [mean, entry_smul, mul_left_comm (p _ : ℂ) c, tsum_mul_left]

theorem entry_id [DecidableEq J] (b : HilbertBasis J ℂ E) (i j : J) :
    entry b (ContinuousLinearMap.id ℂ E) i j = if i=j then 1 else 0 := by
  exact orthonormal_iff_ite.mp b.orthonormal i j

theorem mean_id (b : HilbertBasis J ℂ E) (p : J → ℝ) (hs : HasSum p 1) :
    mean b p (ContinuousLinearMap.id ℂ E)=1 := by
  classical
  simp only [mean, entry_id, ite_true, mul_one]
  exact (hs.mapL Complex.ofRealCLM).tsum_eq

end

section
open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem mean_neg (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) :
    mean b p (-Z) = -mean b p Z := by
  simpa only [neg_one_smul, neg_one_mul] using mean_smul b p (-1) Z

theorem mean_sub (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    (Z T : E →L[ℂ] E) : mean b p (Z-T)=mean b p Z-mean b p T := by
  rw [sub_eq_add_neg, mean_add b p hp hs, mean_neg, sub_eq_add_neg]

def centerLM (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p) :
    (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E) where
  toFun := center b p
  map_add' Z T := by simp only [center, mean_add b p hp hs, add_smul]; abel
  map_smul' c Z := by simp [center, mean_smul, smul_sub, smul_smul]

@[simp] theorem centerLM_apply (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    (Z : E →L[ℂ] E) : centerLM b p hp hs Z = center b p Z := rfl

theorem mean_center (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : HasSum p 1)
    (Z : E →L[ℂ] E) : mean b p (center b p Z)=0 := by
  rw [center, mean_sub b p hp hs.summable, mean_smul, mean_id b p hs, mul_one, sub_self]

end

open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem mean_rankOne [DecidableEq J] (b : HilbertBasis J ℂ E) (p : J → ℝ) (i j : J) :
    mean b p (InnerProductSpace.rankOne ℂ (b i) (b j))=if i=j then (p i:ℂ) else 0 := by
  classical
  rw [mean, tsum_eq_single i]
  · simp only [entry, InnerProductSpace.rankOne_apply, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal, ite_true, mul_one]
    split_ifs <;> simp_all
  · intro k hk
    simp only [entry, InnerProductSpace.rankOne_apply, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal, ite_eq_right hk, mul_zero]

end BKM

namespace CenteredTests
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem generator_eq_center (b : HilbertBasis J ℂ E) (p : J → ℝ) (ij : J × J) :
    generator b p ij=BKM.center b p (InnerProductSpace.rankOne ℂ (b ij.1) (b ij.2)) := by
  classical
  rw [BKM.center, BKM.mean_rankOne]
  rfl

theorem mean_eq_zero (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : HasSum p 1)
    {Z : E →L[ℂ] E} (hZ : Z ∈ operatorSpace b p) : BKM.mean b p Z=0 := by
  obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hZ
  have hc : (c.sum fun ij a => a • generator b p ij)=
      BKM.centerLM b p hp hs.summable (c.sum fun ij a => a • InnerProductSpace.rankOne ℂ (b ij.1) (b ij.2)) := by
    simp only [Finsupp.sum, map_sum, map_smul, BKM.centerLM_apply, ← generator_eq_center]
  rw [hc, BKM.centerLM_apply]
  exact BKM.mean_center b p hp hs _

end CenteredTests

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

theorem quad_smul (X : ℝ × ℝ → ℝ) (c : ℂ) (Z : E →L[ℂ] E) :
    S.quad X (c • Z)=Complex.normSq c*S.quad X Z := by
  simp only [quad, map_smul, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    mul_left_comm (X _) (Complex.normSq c), tsum_mul_left]

theorem pquad_smul (X : ThermalSpectral.Param → ℝ) (c : ℂ) (Z : E →L[ℂ] E) :
    S.pquad X (c • Z)=Complex.normSq c*S.pquad X Z := by
  simp only [pquad, map_smul, Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    mul_left_comm (X _) (Complex.normSq c), tsum_mul_left]

theorem pquad_constant (c : ℝ) (Z : E →L[ℂ] E) :
    S.pquad (fun _ => c) Z=c*S.pquad (fun _ => 1) Z := by
  simp only [pquad, one_mul, tsum_mul_left]

theorem pquad_nonneg {X : ThermalSpectral.Param → ℝ} (hX : ∀ q, 0 ≤ X q)
    (Z : E →L[ℂ] E) : 0 ≤ S.pquad X Z :=
  tsum_nonneg (fun _ij => mul_nonneg (hX _) (Complex.normSq_nonneg _))

theorem center_of_mem {Z : E →L[ℂ] E} (hZ : Z ∈ CenteredTests.operatorSpace S.basis S.p) :
    BKM.center S.basis S.p Z=Z := by
  simp only [BKM.center, CenteredTests.mean_eq_zero S.basis S.p (fun j => (S.pos j).le) S.sum hZ,
    zero_smul, sub_zero]

def normalize (lam : ℝ) : (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E) :=
  (Real.sqrt lam : ℂ)⁻¹ • BKM.centerLM S.basis S.p (fun j => (S.pos j).le) S.sum.summable

theorem normalize_quad {lam : ℝ} (hlam : 0 < lam) (X : ℝ × ℝ → ℝ) (Z : E →L[ℂ] E) :
    lam*S.quad X (S.normalize lam Z)=S.quad X (BKM.center S.basis S.p Z) := by
  change lam*S.quad X ((Real.sqrt lam:ℂ)⁻¹ • BKM.center S.basis S.p Z)=_
  rw [S.quad_smul, Complex.normSq_inv, Complex.normSq_ofReal,
    Real.mul_self_sqrt hlam.le, ← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul]
theorem normalize_pquad {lam : ℝ} (hlam : 0 < lam) (X : ThermalSpectral.Param → ℝ) (Z : E →L[ℂ] E) :
    lam*S.pquad X (S.normalize lam Z)=S.pquad X (BKM.center S.basis S.p Z) := by
  change lam*S.pquad X ((Real.sqrt lam:ℂ)⁻¹ • BKM.center S.basis S.p Z)=_
  rw [S.pquad_smul, Complex.normSq_inv, Complex.normSq_ofReal,
    Real.mul_self_sqrt hlam.le, ← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul]
end ThermalSpectral.Space

namespace EntropyPhotonNumber
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space
variable {n : ℕ}

def rawFirstSliceLM (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (σ τ : State n) : (Fock n →L[ℂ] Fock n) →ₗ[ℂ] (Fock n →L[ℂ] Fock n) where
  toFun := rawFirstSlice η θ hη hθ σ τ
  map_add' Z T := by simp only [rawFirstSlice, conditionalLeft, rawDual, dual_add]
  map_smul' c Z := by simp only [rawFirstSlice, conditionalLeft, rawDual, dual_smul, RingHom.id_apply]

def rawSecondSliceLM (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ τ : State n) : (Fock n →L[ℂ] Fock n) →ₗ[ℂ] (Fock n →L[ℂ] Fock n) where
  toFun := rawSecondSlice η θ hη hθ ρ τ
  map_add' Z T := by simp only [rawSecondSlice, conditionalRight, rawDual, dual_add]
  map_smul' c Z := by simp only [rawSecondSlice, conditionalRight, rawDual, dual_smul, RingHom.id_apply]

def normalizedSlices (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τ : State n) (S : Fin 2 → Space (Fock n)) (lam : Fin 2 → ℝ) :
    (i : Fin 2) → (Fock n →L[ℂ] Fock n) →ₗ[ℂ] (Fock n →L[ℂ] Fock n) :=
  ![((S 0).normalize (lam 0)).comp (rawFirstSliceLM η θ hη hθ σ τ),
    ((S 1).normalize (lam 1)).comp (rawSecondSliceLM η θ hη hθ ρ τ)]

theorem physical_diagram_arithmetic (η θ κ : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1)
    (ρ σ τ ω : State n) (S₀ : Space (Fock n)) (S : Fin 2 → Space (Fock n))
    (lam : Fin 2 → ℝ) (hlam : ∀ i, 0 < lam i)
    (he₁ : ∀ j, ρ.op ((S 0).basis j)=((S 0).p j:ℂ) • (S 0).basis j)
    (he₂ : ∀ j, σ.op ((S 1).basis j)=((S 1).p j:ℂ) • (S 1).basis j)
    (he₀ : TraceEnsemble.operator S₀.ensemble=
      ((1-κ:ℝ):ℂ) • (beamOutput θ hθ (beamOutput η hη ρ σ) τ).op+(κ:ℂ) • ω.op) :
    let D := diagram S₀ S (fun i => (1-κ)*lam i) (normalizedSlices η θ hη hθ ρ σ τ S lam)
    D.Comparison minusWeight ∧ D.Comparison plusWeight := by
  dsimp only
  have hw (i : Fin 2) : 0 ≤ (1-κ)*lam i := mul_nonneg (sub_nonneg.mpr hκ.2) (hlam i).le
  have hmain (X : Param → ℝ) (X' : ℝ × ℝ → ℝ) (heX : X=X' ∘ raw)
      (hX : ∀ q, 0 ≤ X q)
      (hs : ∀ i Z, Summable (fun ij => X ((S i).pparam ij)*Complex.normSq ((S i).coords Z ij)))
      (hp : ∀ Z, (1-κ)*((S 0).quad X' (BKM.center (S 0).basis (S 0).p (rawFirstSlice η θ hη hθ σ τ Z))+
        (S 1).quad X' (BKM.center (S 1).basis (S 1).p (rawSecondSlice η θ hη hθ ρ τ Z))) ≤
          S₀.quad X' (BKM.center S₀.basis S₀.p Z)) :
      (diagram S₀ S (fun i => (1-κ)*lam i) (normalizedSlices η θ hη hθ ρ σ τ S lam)).Comparison X := by
    apply diagram_comparison S₀ S _ hw _ X hX hs
    intro Z hZ
    have hh := hp Z
    rw [S₀.center_of_mem hZ] at hh
    simp only [Fin.sum_univ_two, heX, Space.pquad, Function.comp_apply]
    change (1-κ)*lam 0*(S 0).quad X' ((S 0).normalize (lam 0) (rawFirstSlice η θ hη hθ σ τ Z))+
      (1-κ)*lam 1*(S 1).quad X' ((S 1).normalize (lam 1) (rawSecondSlice η θ hη hθ ρ τ Z)) ≤ S₀.quad X' Z
    rw [mul_assoc, mul_assoc, (S 0).normalize_quad (hlam 0), (S 1).normalize_quad (hlam 1), ← mul_add]
    exact hh
  have hh := replaced_spectral_arithmetic η θ κ hη hθ hκ ρ σ τ ω S₀ (S 0) (S 1) he₁ he₂ he₀
  exact ⟨hmain minusWeight minus rfl (fun q => (minusWeight_pos q).le)
      (fun i Z => (S i).minus_summable Z) (fun Z => (hh Z).1),
    hmain plusWeight plus rfl (fun q => (plusWeight_pos q).le)
      (fun i Z => (S i).plus_summable Z) (fun Z => (hh Z).2)⟩
end EntropyPhotonNumber

namespace BKM
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
def quadratic (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) : ℝ :=
  ∑' ij : J × J, logMean (p ij.1) (p ij.2)*Complex.normSq (entry b Z ij.1 ij.2)
end BKM

namespace ThermalSpectral.Space
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : ThermalSpectral.Space E)

theorem pquad_one (Z : E →L[ℂ] E) :
    S.pquad (fun _ => 1) Z=h S.r*BKM.quadratic S.basis S.p Z := by
  simp only [pquad, one_mul, S.coords_norm, base, BKM.quadratic, mul_assoc, tsum_mul_left]

theorem normalized_hessian (S₀ : ThermalSpectral.Space E) {lam κ ε : ℝ}
    (hlam : 0 < lam) (hκ : κ < 1) (T Z : E →L[ℂ] E)
    (hh : (1-κ)^2*BKM.quadratic S.basis S.p (BKM.center S.basis S.p T) ≤
      (1+ε)*(1-κ)*lam*(h S₀.r/h S.r)*BKM.quadratic S₀.basis S₀.p Z) :
    (1-κ)*S.pquad (fun _ => 1) (S.normalize lam T) ≤ (1+ε)*S₀.pquad (fun _ => 1) Z := by
  have hn : lam*S.pquad (fun _ => 1) (S.normalize lam T)=S.pquad (fun _ => 1) (BKM.center S.basis S.p T) :=
    S.normalize_pquad hlam (fun _ => 1) T
  apply (mul_le_mul_iff_right₀ (mul_pos (sub_pos.mpr hκ) hlam)).mp
  calc
    _ = (1-κ)^2*(lam*S.pquad (fun _ => 1) (S.normalize lam T)) := by ring
    _ = h S.r*((1-κ)^2*BKM.quadratic S.basis S.p (BKM.center S.basis S.p T)) := by
      rw [hn, S.pquad_one]; ring
    _ ≤ h S.r*((1+ε)*(1-κ)*lam*(h S₀.r/h S.r)*BKM.quadratic S₀.basis S₀.p Z) :=
      mul_le_mul_of_nonneg_left hh (h_pos S.rpos).le
    _ = _ := by rw [S₀.pquad_one]; field_simp [(h_pos S.rpos).ne']
end ThermalSpectral.Space

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem diagram_constant (S₀ : Space E) (S : Fin 2 → Space E) (lam : Fin 2 → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (κ ε : ℝ) (hκ : κ ≤ 1)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E))
    (hh : ∀ i Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      (1-κ)*(S i).pquad (fun _ => 1) (L i Z) ≤ (1+ε)*S₀.pquad (fun _ => 1) Z)
    (X : Param → ℝ) (hX : ∀ q, 0 ≤ X q) (c₀ : ℝ) (c : Fin 2 → ℝ) (hc : ∀ i, 0 ≤ c i)
    (he₀ : ∀ a, X (S₀.pparam a)=c₀) (he : ∀ i a, X ((S i).pparam a)=c i)
    (hslack : (1+ε)*(∑ i, lam i*c i) ≤ c₀) :
    (diagram S₀ S (fun i => (1-κ)*lam i) L).Comparison X := by
  have hw i : 0 ≤ (1-κ)*lam i := mul_nonneg (sub_nonneg.mpr hκ) (hlam i)
  have hq₀ Z : S₀.pquad X Z=c₀*S₀.pquad (fun _ => 1) Z := by
    simp only [Space.pquad, he₀, one_mul, tsum_mul_left]
  have hq i Z : (S i).pquad X Z=c i*(S i).pquad (fun _ => 1) Z := by
    simp only [Space.pquad, he, one_mul, tsum_mul_left]
  apply diagram_comparison S₀ S _ hw L X hX
  · intro i Z
    simpa only [he] using (S i).constant_summable (c i) Z
  intro Z hZ
  rw [hq₀]
  calc
    _ = ∑ i, (lam i*c i)*((1-κ)*(S i).pquad (fun _ => 1) (L i Z)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hq]; ring
    _ ≤ ∑ i, (lam i*c i)*((1+ε)*S₀.pquad (fun _ => 1) Z) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hh i Z hZ) (mul_nonneg (hlam i) (hc i))
    _ = ((1+ε)*∑ i, lam i*c i)*S₀.pquad (fun _ => 1) Z := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hslack (S₀.pquad_nonneg (fun _ => zero_le_one) Z)

theorem diagram_reference (S₀ : Space E) (S : Fin 2 → Space E) (lam : Fin 2 → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (κ ε : ℝ) (hκ : κ ≤ 1)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E))
    (hh : ∀ i Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      (1-κ)*(S i).pquad (fun _ => 1) (L i Z) ≤ (1+ε)*S₀.pquad (fun _ => 1) Z)
    (hr : (1+ε)*(∑ i, lam i*(S i).r) ≤ S₀.r)
    (hs : (1+ε)*(∑ i, lam i*((S i).r+1)) ≤ S₀.r+1) :
    (diagram S₀ S (fun i => (1-κ)*lam i) L).Comparison (fun q => q.1.val) ∧
    (diagram S₀ S (fun i => (1-κ)*lam i) L).Comparison (fun q => q.1.val+1) := by
  constructor
  · exact diagram_constant S₀ S lam hlam κ ε hκ L hh (fun q => q.1.val) (fun q => q.1.property.le)
      S₀.r (fun i => (S i).r) (fun i => (S i).rpos.le) (fun _ => rfl) (fun _ _ => rfl) hr
  · exact diagram_constant S₀ S lam hlam κ ε hκ L hh (fun q => q.1.val+1) (fun q => by linarith [q.1.property])
      (S₀.r+1) (fun i => (S i).r+1) (fun i => by linarith [(S i).rpos])
      (fun _ => rfl) (fun _ _ => rfl) hs

theorem diagram_observable (S₀ : Space E) (S : Fin 2 → Space E) (w : Fin 2 → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (L : (i : Fin 2) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E)) (X : Param → ℝ)
    (hX : ∀ q, 0 ≤ X q)
    (hs : ∀ i Z, Summable (fun a => X ((S i).pparam a)*Complex.normSq ((S i).coords Z a)))
    (hh : (diagram S₀ S w L).Comparison X) (Z : E →L[ℂ] E)
    (hZ : Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p) :
    ∑ i, w i*(S i).pquad X (L i Z) ≤ S₀.pquad X Z := by
  let z : CenteredTests.coordinates S₀.basis S₀.p S₀.base := ⟨S₀.coords Z, ⟨Z,hZ,rfl⟩⟩
  have hz : CenteredTests.realize S₀.basis S₀.p S₀.base S₀.base_pos z=Z := by
    apply CenteredTests.entryMap_injective S₀.basis S₀.base S₀.base_pos
    exact CenteredTests.realize_entries S₀.basis S₀.p S₀.base S₀.base_pos z
  have hn (a : Σ i, (S i).I × (S i).I) : 0 ≤ X ((S a.1).pparam a.2)*
      (w a.1*Complex.normSq ((S a.1).coords (L a.1 Z) a.2)) :=
    mul_nonneg (hX _) (mul_nonneg (hw _) (Complex.normSq_nonneg _))
  have ht : Summable (fun a : Σ i, (S i).I × (S i).I => X ((S a.1).pparam a.2)*
      (w a.1*Complex.normSq ((S a.1).coords (L a.1 Z) a.2))) := by
    apply (summable_sigma_of_nonneg hn).mpr
    refine ⟨fun i => ?_, (hasSum_fintype _).summable⟩
    simpa only [mul_left_comm] using (hs i (L i Z)).mul_left (w i)
  have hsum : (∑' a : Σ i, (S i).I × (S i).I, X ((S a.1).pparam a.2)*
      (w a.1*Complex.normSq ((S a.1).coords (L a.1 Z) a.2))) =
      ∑ i, w i*(S i).pquad X (L i Z) := by
    rw [ht.tsum_sigma]
    simp only [tsum_fintype, Space.pquad, mul_left_comm (X _) (w _), tsum_mul_left]
  rw [← hsum]
  apply ht.tsum_le_of_sum_le
  intro s
  have hh' := hh z s
  change (∑ a ∈ s, X ((S a.1).pparam a.2)*Complex.normSq
    (targetMap S w L (CenteredTests.realize S₀.basis S₀.p S₀.base S₀.base_pos z) a)) ≤
      S₀.pquad X Z at hh'
  simpa only [hz, targetMap_norm S w hw L] using hh'
end ThermalSpectral

namespace EntropyPhotonNumber
open TensorLp KrausBounded ThermalSpectral ThermalSpectral.Space ThermalMetric
variable {n : ℕ}

theorem physical_thermal_contraction (η θ κ ε : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1) (hκ1 : κ < 1)
    (ρ σ τ ω : State n) (S₀ : Space (Fock n)) (S : Fin 2 → Space (Fock n))
    (lam : Fin 2 → ℝ) (hlam : ∀ i, 0 < lam i)
    (he₁ : ∀ j, ρ.op ((S 0).basis j)=((S 0).p j:ℂ) • (S 0).basis j)
    (he₂ : ∀ j, σ.op ((S 1).basis j)=((S 1).p j:ℂ) • (S 1).basis j)
    (he₀ : TraceEnsemble.operator S₀.ensemble=
      ((1-κ:ℝ):ℂ) • (beamOutput θ hθ (beamOutput η hη ρ σ) τ).op+(κ:ℂ) • ω.op)
    (hh₁ : ∀ Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      (1-κ)^2*BKM.quadratic (S 0).basis (S 0).p
        (BKM.center (S 0).basis (S 0).p (rawFirstSlice η θ hη hθ σ τ Z)) ≤
      (1+ε)*(1-κ)*lam 0*(h S₀.r/h (S 0).r)*BKM.quadratic S₀.basis S₀.p Z)
    (hh₂ : ∀ Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      (1-κ)^2*BKM.quadratic (S 1).basis (S 1).p
        (BKM.center (S 1).basis (S 1).p (rawSecondSlice η θ hη hθ ρ τ Z)) ≤
      (1+ε)*(1-κ)*lam 1*(h S₀.r/h (S 1).r)*BKM.quadratic S₀.basis S₀.p Z)
    (hr : (1+ε)*(∑ i, lam i*(S i).r) ≤ S₀.r)
    (hs : (1+ε)*(∑ i, lam i*((S i).r+1)) ≤ S₀.r+1)
    (Z : Fock n →L[ℂ] Fock n) (hZ : Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p) :
    ∑ i, ((1-κ)*lam i)*(S i).pquad thermalWeight
      (normalizedSlices η θ hη hθ ρ σ τ S lam i Z) ≤ S₀.pquad thermalWeight Z := by
  have ha := physical_diagram_arithmetic η θ κ hη hθ hκ ρ σ τ ω S₀ S lam hlam he₁ he₂ he₀
  have hh : ∀ i Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      (1-κ)*(S i).pquad (fun _ => 1) (normalizedSlices η θ hη hθ ρ σ τ S lam i Z) ≤
        (1+ε)*S₀.pquad (fun _ => 1) Z := by
    intro i U hU
    fin_cases i
    · exact (S 0).normalized_hessian S₀ (hlam 0) hκ1 _ U (hh₁ U hU)
    · exact (S 1).normalized_hessian S₀ (hlam 1) hκ1 _ U (hh₂ U hU)
  have hc := diagram_reference S₀ S lam (fun i => (hlam i).le) κ ε hκ.2
    (normalizedSlices η θ hη hθ ρ σ τ S lam) hh hr hs
  have ht := diagram_thermal S₀ S (fun i => (1-κ)*lam i)
    (normalizedSlices η θ hη hθ ρ σ τ S lam) ha.2 ha.1 hc.1 hc.2
  exact diagram_observable S₀ S _ (fun i => mul_nonneg (sub_nonneg.mpr hκ.2) (hlam i).le)
    _ thermalWeight (fun q => (weight_pos q.1.property _).le)
    (fun i U => (S i).thermal_summable U) ht Z hZ
end EntropyPhotonNumber

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

def thermalSpace (t : ℝ) (ht : 0<t) : ThermalSpectral.Space (Fock n) where
  I := G.J
  basis := G.basis
  p := G.probability
  pos := G.probability_pos
  sum := G.probability_sum
  r := t
  rpos := ht

theorem inverse_spectralColumns_operator :
    CrossEnsemble.operator (fun r => inverseWeight 3 (G.spectralColumns r))
      (fun r => inverseWeight 3 (G.spectralColumns r))=ρ.op := by
  simp only [G.spectralColumns_inverse]
  exact CrossEnsemble.eigenEnsemble_operator G.basis G.probability
    (fun r => (G.probability_pos r).le) G.probability_sum.summable ρ.op ρ.positive.isSymmetric G.eigen

def weightedColumns : WeightedColumns ρ where
  Index := G.J
  vector := G.spectralColumns
  summable := G.spectralColumns_summable
  normalized := G.spectralColumns_normalized
  density := G.inverse_spectralColumns_operator

def ambientDefect (t : ℝ) (ht : 0<t) (j : Fin n) : lp (fun _ : G.J × G.J => ℂ) 2 →L[ℂ] ℂ :=
  defectFunctional t ht G.probability G.probability_pos (G.centeredMatrix j)
    (G.centeredMatrix_defect_summable t j)

theorem ambientDefect_observable (t : ℝ) (ht : 0<t) (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    G.ambientDefect t ht j ((G.thermalSpace t ht).observable Z)=
      weakDefect t G.spectralColumns j (G.annihilationMean j) Z :=
  (G.thermalSpace t ht).defectFunctional_observable G.spectralColumns G.spectralColumns_summable
    G.spectralColumns_inverse j (G.annihilationMean j) (G.centeredMatrix_defect_summable t j) Z

theorem ambientDefect_one (t : ℝ) (ht : 0<t) (j : Fin n) :
    G.ambientDefect t ht j ((G.thermalSpace t ht).observable 1)=0 :=
  (G.thermalSpace t ht).defectFunctional_one (G.centeredMatrix j)
    (G.centeredMatrix_defect_summable t j) (G.centeredMatrix_mean_zero j)

theorem ambientDefect_norm (t : ℝ) (ht : 0<t) (j : Fin n) :
    ‖G.ambientDefect t ht j‖=‖G.defect t ht j‖ := by
  exact (defectFunctional_restrict_norm t ht G.probability G.probability_pos (G.centeredMatrix j)
    (G.centeredMatrix_defect_summable t j) _
    (defectVector_mem_centeredSpace t ht G.probability G.probability_pos G.probability_sum.summable
      (G.centeredMatrix j) (G.centeredMatrix_defect_summable t j) (G.centeredMatrix_mean_zero j))).symm

theorem weakDefect_centered (t : ℝ) (ht : 0<t) (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    weakDefect t G.spectralColumns j (G.annihilationMean j) Z=G.weightedColumns.centeredWeak t j Z :=
  (G.thermalSpace t ht).weakDefect_centered G.weightedColumns rfl G.spectralColumns
    G.spectralColumns_summable G.spectralColumns_inverse HEq.rfl j (G.annihilationMean j)
    (G.centeredMatrix_defect_summable t j) (G.centeredMatrix_mean_zero j) Z

theorem ambientDefect_centered (t : ℝ) (ht : 0<t) (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    G.ambientDefect t ht j ((G.thermalSpace t ht).observable Z)=G.weightedColumns.centeredWeak t j Z := by
  rw [G.ambientDefect_observable, G.weakDefect_centered t ht]

theorem weakMean_eq_conj (t : ℝ) (ht : 0<t) (j : Fin n) :
    G.weightedColumns.weakMean t j=conj (G.annihilationMean j) := by
  have hz := G.ambientDefect_one t ht j
  rw [G.ambientDefect_observable, weakDefect_uncentered _ _ G.spectralColumns_summable] at hz
  change G.weightedColumns.weakMean t j-conj (G.annihilationMean j)*G.weightedColumns.expectation 1=0 at hz
  rw [G.weightedColumns.expectation_one, mul_one] at hz
  exact sub_eq_zero.mp hz

end EntropyPhotonNumber.SpectralLogData

end

end OAI
