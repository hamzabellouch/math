import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.End
import OAI.Geometry.TamingCompatibility.Elliptic.OperatorCalculus
import OAI.Geometry.TamingCompatibility.DifferentialForms.Dpos2

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open scoped ContDiff
variable {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [Fintype ι] in
lemma scalar_second (χ : V → ℝ) (u : V → W)
    (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u) (x v w : V) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => χ z • u z) y w) x v =
      (fderiv ℝ (fun y => fderiv ℝ χ y w) x v) • u x +
      (fderiv ℝ χ x w) • fderiv ℝ u x v + (fderiv ℝ χ x v) • fderiv ℝ u x w +
      χ x • fderiv ℝ (fun y => fderiv ℝ u y w) x v := by
  have hχ' : ∀ y, DifferentiableAt ℝ χ y := hχ.differentiable (by norm_num)
  have hu' : ∀ y, DifferentiableAt ℝ u y := hu.differentiable (by norm_num)
  have hdχ : DifferentiableAt ℝ (fun y => fderiv ℝ χ y w) x :=
    (((hχ.contDiffAt (x := x)).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hdu : DifferentiableAt ℝ (fun y => fderiv ℝ u y w) x :=
    (((hu.contDiffAt (x := x)).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by norm_num)
  simp_rw [fderiv_fun_smul (hχ' _) (hu' _)]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply]
  have h₁ : DifferentiableAt ℝ (fun y => χ y • fderiv ℝ u y w) x := (hχ' x).smul hdu
  have h₂ : DifferentiableAt ℝ (fun y => fderiv ℝ χ y w • u y) x := hdχ.smul (hu' x)
  rw [fderiv_fun_add h₁ h₂]
  rw [fderiv_fun_smul (hχ' x) hdu,fderiv_fun_smul hdχ (hu' x)]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply]
  abel

lemma secondOrder_scalar_product (e : ι → V) (a : ι → ι → V → ℝ)
    (b : ι → V → W →L[ℝ] W) (c : V → W →L[ℝ] W)
    (χ : V → ℝ) (u : V → W) (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u) (x : V) :
    secondOrder e a b c (fun z => χ z • u z) x =
      χ x • secondOrder e a b c u x -
        (∑ i, ∑ j, a i j x •
          ((fderiv ℝ (fun y => fderiv ℝ χ y (e j)) x (e i)) • u x +
          (fderiv ℝ χ x (e j)) • fderiv ℝ u x (e i) +
          (fderiv ℝ χ x (e i)) • fderiv ℝ u x (e j))) +
        ∑ i, (fderiv ℝ χ x (e i)) • b i x (u x) := by
  simp only [secondOrder, scalar_second χ u hχ hu,
    fderiv_fun_smul (hχ.differentiable (by norm_num) x) (hu.differentiable (by norm_num) x),
    add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,map_smul,map_add,
    smul_add,Finset.sum_add_distrib,smul_neg,Finset.smul_sum]
  simp only [smul_comm (χ x)]
  abel

end TamingCompatibility.GeometricHilbert.OperatorCalculus

namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open scoped ContDiff
variable {V W ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def cutoffFirst (e : ι → V) (a : ι → ι → V → ℝ)
    (b : ι → V → W →L[ℝ] W) (χ : V → ℝ) (j : ι) (z : V) : W →L[ℝ] W :=
  χ z • b j z - (∑ i, (a i j z+a j i z)*fderiv ℝ χ z (e i)) • ContinuousLinearMap.id ℝ W

def cutoffZero (e : ι → V) (a : ι → ι → V → ℝ)
    (b : ι → V → W →L[ℝ] W) (c : V → W →L[ℝ] W) (χ : V → ℝ) (z : V) : W →L[ℝ] W :=
  χ z • c z - (∑ i, ∑ j, a i j z * fderiv ℝ (fun y => fderiv ℝ χ y (e j)) z (e i)) •
    ContinuousLinearMap.id ℝ W + ∑ i, fderiv ℝ χ z (e i) • b i z

lemma secondOrder_cutoff (e : ι → V) (a : ι → ι → V → ℝ)
    (b : ι → V → W →L[ℝ] W) (c : V → W →L[ℝ] W)
    (χ : V → ℝ) (u : V → W) (hχ : ContDiff ℝ 2 χ) (hu : ContDiff ℝ 2 u) (x : V) :
    secondOrder e a b c (fun z => χ z • u z) x =
      secondOrder e (fun i j z => χ z * a i j z)
        (cutoffFirst e a b χ) (cutoffZero e a b c χ) u x := by
  rw [secondOrder_scalar_product e a b c χ u hχ hu]
  simp only [secondOrder,cutoffFirst,cutoffZero,sub_apply,add_apply,smul_apply,sum_apply,
    ContinuousLinearMap.id_apply,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    smul_add,smul_neg,Finset.smul_sum,Finset.sum_smul,mul_smul,add_smul]
  rw [Finset.sum_comm (f := fun i j => a j i x • (fderiv ℝ χ x (e j) • fderiv ℝ u x (e i)))]
  simp only [smul_comm (χ x)]
  abel

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open OperatorCalculus FlatHeat Filter Set
open scoped Topology ContDiff
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

def cutoffPrincipal (a : Fin 4 → Fin 4 → V → ℝ) (χ : V → ℝ)
    (i j : Fin 4) (z : V) : ℝ :=
  euclideanPrincipal i j + χ z * (a i j z - euclideanPrincipal i j)

lemma cutoff_gaussian_residual (a : Fin 4 → Fin 4 → V → ℝ)
    (b : Fin 4 → V → W →L[ℝ] W) (c : V → W →L[ℝ] W)
    (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) {t : ℝ} (ht : 0 < t) (z : V) (u : W) :
    deriv (fun s => χ z • modelSection s u z) t +
      secondOrder (EuclideanSpace.basisFun (Fin 4) ℝ) a b c
        (fun y => χ y • modelSection t u y) z =
      residual (fun y i j => cutoffPrincipal a χ i j y)
        (fun y j => cutoffFirst (EuclideanSpace.basisFun (Fin 4) ℝ) a b χ j y)
        (cutoffZero (EuclideanSpace.basisFun (Fin 4) ℝ) a b c χ) t z u := by
  let e := EuclideanSpace.basisFun (Fin 4) ℝ
  have hm : ContDiff ℝ ∞ (modelSection t u) := (heat_contDiff t).smul contDiff_const
  have htime : deriv (fun s => χ z • modelSection s u z) t =
      χ z • deriv (fun s => modelSection s u z) t := by
    have hd := ((heat_hasDerivAt_time ht z).smul_const u)
    exact (hd.const_smul (χ z)).deriv.trans (congrArg (fun v : W => χ z • v) hd.deriv.symm)
  rw [htime,secondOrder_cutoff e a b c χ (modelSection t u)
    (hχ.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
    (hm.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))]
  rw [modelSection_time ht]
  simp only [secondOrder]
  simp_rw [modelSection_hessian,modelSection_fderiv]
  simp only [modelSection,map_smul]
  have he (i j : Fin 4) : euclideanPrincipal i j - cutoffPrincipal a χ i j z =
      χ z * (euclideanPrincipal i j-a i j z) := by unfold cutoffPrincipal; ring
  simp only [residual,he]
  simp [euclideanPrincipal,FlatHeat.laplacian,e,
    sub_smul,mul_smul,Finset.sum_smul,Finset.smul_sum,
    smul_sub,apply_ite,Finset.sum_sub_distrib,smul_comm (χ z)]
  abel

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.UniformJets
open Set Metric
open scoped ContDiff
variable {P V W A B : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma linear_bound_on_tube (F : P × V → W) (K : Set P) (hK : IsCompact K)
    {r : ℝ} (hr : 0 ≤ r)
    (hF : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ContDiffAt ℝ ∞ F x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ z : V, ‖z‖ ≤ r →
      ‖F (p,z)-F (p,0)‖ ≤ C*‖z‖ := by
  have hpc : ContinuousOn (dpos F) (K ×ˢ closedBall (0 : V) r) :=
    fun x hx => ((dpos_contDiffAt F x (hF x hx)).continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := (hK.prod (isCompact_closedBall (0 : V) r)).exists_bound_of_continuousOn hpc
  refine ⟨max C 0,le_max_right _ _,fun p hp z hz => ?_⟩
  have hd (u : V) (hu : u ∈ closedBall (0 : V) r) : DifferentiableAt ℝ F (p,u) :=
    (hF (p,u) ⟨hp,hu⟩).differentiableAt (by simp)
  have hb (u : V) (hu : u ∈ closedBall (0 : V) r) :
      ‖fderiv ℝ (fun v => F (p,v)) u‖ ≤ max C 0 := by
    rw [←dpos_eq_at F p u (hd u hu)]
    exact (hC (p,u) ⟨hp,hu⟩).trans (le_max_left _ _)
  simpa using (convex_closedBall (0 : V) r).norm_image_sub_le_of_norm_fderiv_le
    (fun u hu => (hd u hu).comp u ((differentiableAt_const p).prodMk differentiableAt_id)) hb
    (show (0 : V) ∈ closedBall 0 r by simpa using hr)
    (show z ∈ closedBall 0 r by simpa using hz)

lemma quadratic_bound_on_tube (F : P × V → W) (K : Set P) (hK : IsCompact K)
    {r : ℝ} (hr : 0 ≤ r)
    (hF : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ContDiffAt ℝ ∞ F x)
    (hzero : ∀ p ∈ K, dpos F (p,0) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ z : V, ‖z‖ ≤ r →
      ‖F (p,z)-F (p,0)‖ ≤ C*‖z‖^2 := by
  obtain ⟨C,hC,hb⟩ := linear_bound_on_tube (dpos F) K hK hr
    (fun x hx => dpos_contDiffAt F x (hF x hx))
  have hlin (p : P) (hp : p ∈ K) (z : V) (hz : ‖z‖ ≤ r) :
      ‖dpos F (p,z)‖ ≤ C*‖z‖ := by simpa [hzero p hp] using hb p hp z hz
  refine ⟨C,hC,fun p hp z hz => ?_⟩
  have hd (u : V) (hu : ‖u‖ ≤ r) : DifferentiableAt ℝ F (p,u) :=
    (hF (p,u) ⟨hp,by simpa using hu⟩).differentiableAt (by simp)
  have hder (u : V) (hu : u ∈ closedBall (0 : V) ‖z‖) :
      ‖fderiv ℝ (fun v => F (p,v)) u‖ ≤ C*‖z‖ := by
    have hu' : ‖u‖ ≤ ‖z‖ := by simpa using hu
    rw [←dpos_eq_at F p u (hd u (hu'.trans hz))]
    exact (hlin p hp u (hu'.trans hz)).trans (mul_le_mul_of_nonneg_left hu' hC)
  have hh := (convex_closedBall (0 : V) ‖z‖).norm_image_sub_le_of_norm_fderiv_le
    (fun u hu => (hd u ((by simpa using hu : ‖u‖ ≤ ‖z‖).trans hz)).comp u
      ((differentiableAt_const p).prodMk differentiableAt_id)) hder
    (show (0 : V) ∈ closedBall 0 ‖z‖ by simp)
    (show z ∈ closedBall 0 ‖z‖ by simp)
  simpa [pow_two,mul_assoc] using hh

omit [NormedSpace ℝ W] in
lemma normal_bounds_on_tube (F : P × V → A) (G : P × V → B) (H : P × V → W)
    (K : Set P) (hK : IsCompact K) {r : ℝ} (hr : 0 ≤ r)
    (hF : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ContDiffAt ℝ ∞ F x)
    (hG : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ContDiffAt ℝ ∞ G x)
    (hH : ∀ x ∈ K ×ˢ closedBall (0 : V) r, ContinuousAt H x)
    (hF0 : ∀ p ∈ K, dpos F (p,0) = 0) (hG0 : ∀ p ∈ K, G (p,0) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ z : V, ‖z‖ ≤ r →
      ‖F (p,z)-F (p,0)‖ ≤ C*‖z‖^2 ∧ ‖G (p,z)‖ ≤ C*‖z‖ ∧ ‖H (p,z)‖ ≤ C := by
  obtain ⟨Ca,hCa,hba⟩ := quadratic_bound_on_tube F K hK hr hF hF0
  obtain ⟨Cb,hCb,hbb⟩ := linear_bound_on_tube G K hK hr hG
  obtain ⟨Cc,hbc⟩ := (hK.prod (isCompact_closedBall (0 : V) r)).exists_bound_of_continuousOn
    (fun x hx => (hH x hx).continuousWithinAt)
  refine ⟨Ca+Cb+max Cc 0,by positivity,fun p hp z hz => ⟨?_,?_,?_⟩⟩
  · exact (hba p hp z hz).trans
      (mul_le_mul_of_nonneg_right (by linarith [le_max_right Cc 0] : Ca ≤ Ca+Cb+max Cc 0) (sq_nonneg _))
  · have hh : ‖G (p,z)‖ ≤ Cb*‖z‖ := by simpa [hG0 p hp] using hbb p hp z hz
    exact hh.trans (mul_le_mul_of_nonneg_right
      (by linarith [le_max_right Cc 0] : Cb ≤ Ca+Cb+max Cc 0) (norm_nonneg _))
  · exact (hbc (p,z) ⟨hp,by simpa using hz⟩).trans (by linarith [le_max_left Cc 0])

end TamingCompatibility.GeometricHilbert.UniformJets

end
end

end

end OAI
