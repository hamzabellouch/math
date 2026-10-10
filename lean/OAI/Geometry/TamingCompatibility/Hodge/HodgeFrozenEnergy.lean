import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSymbol
import OAI.Geometry.TamingCompatibility.Hodge.HodgeMatrixEnergy

namespace OAI

section
section

section
noncomputable section
open MeasureTheory
open scoped SchwartzMap LineDeriv
namespace TamingCompatibility.HodgeFrozenEnergy
open EuclideanEnergy HodgeMatrixEnergy HodgeNormalSymbol
open DirectionalEnergy (directionDeriv)

def directionalGradient (b : Fin 4 → V) (f : Field) (x : V) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 6, (directionDeriv b i (f j) x)^2
lemma directionalGradient_integrable (b : Fin 4 → V) (f : Field) :
    Integrable (directionalGradient b f) :=
  integrable_finsetSum _ (fun _ _ => integrable_finsetSum _
    (fun _ _ => schwartz_sq_integrable _))
lemma directionalGradient_integral (b : Fin 4 → V) (f : Field) :
    (∫ x, directionalGradient b f x) = HodgeFlatEnergy.gradientEnergy b f := by
  unfold directionalGradient
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · simp only [HodgeFlatEnergy.pairing,pow_two]
    · intro j _; exact schwartz_sq_integrable _
  · intro i _
    exact integrable_finsetSum _ (fun j _ => schwartz_sq_integrable _)

lemma gradient_basis_control (b : Module.Basis (Fin 4) ℝ V) (f : Field) (x : V) :
    gradient f x ≤ DirectionalEnergy.coordinateConstant b * directionalGradient b f x := by
  have h (i : Fin 4) (j : Fin 6) := DirectionalEnergy.covector_basis_sq b (fderiv ℝ (f j) x) i
  have hdir (i : Fin 4) : (∑ j : Fin 6, (coordinateDeriv i (f j) x)^2) ≤
      (∑ t, (b.repr (e i) t)^2) * directionalGradient b f x := by
    calc
      _ ≤ ∑ j : Fin 6, (∑ t, (b.repr (e i) t)^2) *
          ∑ t : Fin 4, (directionDeriv b t (f j) x)^2 := by
        exact Finset.sum_le_sum (fun j _ => by
          simpa only [coordinateDeriv,directionDeriv,SchwartzMap.lineDerivOp_apply_eq_fderiv] using h i j)
      _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_comm

  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hdir i)
  have hg : gradient f x = ∑ i : Fin 4, ∑ j : Fin 6, (coordinateDeriv i (f j) x)^2 := by
    simp only [HodgeMatrixEnergy.gradient,HodgeMatrixEnergy.derivative,value_norm]
  rw [← hg,← Finset.sum_mul] at he
  refine he.trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · simp [DirectionalEnergy.coordinateConstant]
  · exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma directionDeriv_expansion (b : Fin 4 → V) (j : Fin 4) (f : S) (x : V) :
    directionDeriv b j f x = ∑ i : Fin 4, b j i * coordinateDeriv i f x := by
  simp only [directionDeriv,coordinateDeriv,SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have he : b j = ∑ i, b j i • e i := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,e]
      using ((EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr (b j)).symm
  conv_lhs => rw [he]
  simp only [map_sum,map_smul,smul_eq_mul]

def coefficient (b : Fin 4 → V) (i : Fin 4) : HodgeMatrixEnergy.W →L[ℝ] Q :=
  normalSymbol (WithLp.toLp 2 (fun j => b j i))
def flatSystem (b : Fin 4 → V) (f : Field) (x : V) : Q := WithLp.toLp 2
  ![HodgeFlatEnergy.delta b f 0 x,HodgeFlatEnergy.delta b f 1 x,
    HodgeFlatEnergy.delta b f 2 x,HodgeFlatEnergy.delta b f 3 x,
    HodgeFlatEnergy.delta b (HodgeFlatEnergy.star f) 0 x,
    HodgeFlatEnergy.delta b (HodgeFlatEnergy.star f) 1 x,
    HodgeFlatEnergy.delta b (HodgeFlatEnergy.star f) 2 x,
    HodgeFlatEnergy.delta b (HodgeFlatEnergy.star f) 3 x]

lemma frozen_system (b : Fin 4 → V) (f : Field) (x : V) :
    constantSystem (coefficient b) f x = flatSystem b f x := by
  ext k
  fin_cases k <;>
    simp [constantSystem,coefficient,normalSymbol_apply,symbol,UnitaryFrame.interior,
      UnitaryFrame.star,derivative,value,flatSystem,HodgeFlatEnergy.delta,HodgeFlatEnergy.star,
      HodgeFlatEnergy.directionDeriv_neg,directionDeriv_expansion,Fin.sum_univ_succ] <;> ring

lemma flatSystem_integral (b : Fin 4 → V) (f : Field) :
    (∫ x, ‖flatSystem b f x‖^2) = HodgeFlatEnergy.energy b f := by
  have he (x : V) : ‖flatSystem b f x‖^2 =
      (∑ i : Fin 4, (HodgeFlatEnergy.delta b f i x)^2) +
        ∑ i : Fin 4, (HodgeFlatEnergy.delta b (HodgeFlatEnergy.star f) i x)^2 := by
    simp [flatSystem,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
    ring
  simp_rw [he]
  rw [integral_add]
  · rw [integral_finsetSum,integral_finsetSum]
    · simp only [HodgeFlatEnergy.energy,HodgeFlatEnergy.pairing,pow_two]
    · intro i _; exact schwartz_sq_integrable _
    · intro i _; exact schwartz_sq_integrable _
  · exact integrable_finsetSum _ (fun i _ => schwartz_sq_integrable _)
  · exact integrable_finsetSum _ (fun i _ => schwartz_sq_integrable _)

theorem frozen_energy (b : Module.Basis (Fin 4) ℝ V) (f : Field) :
    (∫ x, gradient f x) ≤ DirectionalEnergy.coordinateConstant b *
      (∫ x, ‖constantSystem (coefficient b) f x‖^2) := by
  have h := integral_mono (gradient_integrable f)
    ((directionalGradient_integrable b f).const_mul (DirectionalEnergy.coordinateConstant b))
    (gradient_basis_control b f)
  rw [integral_const_mul,directionalGradient_integral] at h
  simp_rw [frozen_system]
  rw [flatSystem_integral,HodgeFlatEnergy.energy_eq_gradient]
  exact h
end TamingCompatibility.HodgeFrozenEnergy

end
end

section
noncomputable section
open scoped ContDiff RealInnerProductSpace
namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms MetricHodge ExteriorForms ContinuousAlternatingMap
open FormMetric (pairLeft pairRight)
open HodgeNormalSymbol (W)
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

def coordinates (b : Fin 4 → E) : MetricForms.Form E 2 →L[ℝ] W :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 6 => ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => ContinuousAlternatingMap.apply ℝ E ℝ ![b (pairLeft i),b (pairRight i)])
lemma coordinates_apply (b : Fin 4 → E) (a : MetricForms.Form E 2) (i : Fin 6) :
    coordinates b a i = a ![b (pairLeft i),b (pairRight i)] := rfl

def basisForm (g : Metric E) (b : Fin 4 → E) (j : Fin 6) : MetricForms.Form E 2 :=
  AntiInvariantFrame.covectorWedge (g.bilinear (b (pairLeft j))) (g.bilinear (b (pairRight j)))
lemma basisForm_apply (g : Metric E) (b : Fin 4 → E) (j : Fin 6) (u v : E) :
    basisForm g b j ![u,v] = g.bilinear (b (pairLeft j)) u * g.bilinear (b (pairRight j)) v -
      g.bilinear (b (pairLeft j)) v * g.bilinear (b (pairRight j)) u :=
  AntiInvariantFrame.covectorWedge_apply _ _ _ _

def reconstruct (g : Metric E) (b : Fin 4 → E) : W →L[ℝ] MetricForms.Form E 2 :=
  ∑ i, (EuclideanSpace.proj i).smulRight (basisForm g b i)
lemma reconstruct_apply (g : Metric E) (b : Fin 4 → E) (a : W) :
    reconstruct g b a = ∑ i, a i • basisForm g b i := by
  simp only [reconstruct,_root_.sum_apply,ContinuousLinearMap.smulRight_apply,PiLp.proj_apply]

lemma coordinates_basisForm (g : Metric E) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (i j : Fin 6) :
    coordinates b (basisForm g b j) i = if i=j then 1 else 0 := by
  rw [coordinates_apply,basisForm_apply]
  simp only [hb]
  fin_cases i <;> fin_cases j <;> norm_num [pairLeft,pairRight,Fin.ext_iff]

lemma coordinates_reconstruct (g : Metric E) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (a : W) :
    coordinates b (reconstruct g b a) = a := by
  ext i
  rw [reconstruct_apply]
  simp only [coordinates_apply,ContinuousAlternatingMap.sum_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul]
  simp_rw [← coordinates_apply,coordinates_basisForm g b hb]
  simp

variable [FiniteDimensional ℝ E]

lemma coordinates_injective (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) :
    Function.Injective (coordinates b) := by
  intro a c h
  have he (i : Fin 6) := congrArg (fun v : W => v i) h
  simp only [coordinates_apply] at he
  apply AntiInvariantFrame.frame_ext g hdim b hb
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact he 0 | exact he 1 | exact he 2 | exact he 3 | exact he 4 | exact he 5
    | solve | simp only [AntiInvariantFrame.eval_self]
    | (rw [two_swap a,two_swap c]; congr 1
       first | exact he 0 | exact he 1 | exact he 2 | exact he 3 | exact he 4 | exact he 5)

lemma reconstruct_coordinates (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (a : MetricForms.Form E 2) :
    reconstruct g b (coordinates b a) = a := by
  apply coordinates_injective g hdim b hb
  exact coordinates_reconstruct g b hb _

lemma coordinates_pairing (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (a c : MetricForms.Form E 2) :
    ⟪coordinates b a,coordinates b c⟫ = pairing g a c := by
  rw [pairing_two_eq_sum g hdim b hb]
  simp only [PiLp.inner_apply,coordinates_apply,RCLike.inner_apply,conj_trivial,mul_comm]

lemma basisForm_smooth {g : D → Metric E} {b : Fin 4 → D → E} {U : Set D}
    (hg : ContDiffOn ℝ ∞ (fun x => (g x).bilinear) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) (j : Fin 6) :
    ContDiffOn ℝ ∞ (fun x => basisForm (g x) (fun i => b i x) j) U := by
  apply FormSmooth.contDiffOn_of_basis (Module.finBasis ℝ E)
  intro a
  have hv : (fun i => Module.finBasis ℝ E (a i)) =
      ![Module.finBasis ℝ E (a 0),Module.finBasis ℝ E (a 1)] := by ext i; fin_cases i <;> rfl
  simp only [hv,basisForm_apply]
  exact (((hg.clm_apply (hb (pairLeft j))).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb (pairRight j))).clm_apply contDiffOn_const)).sub
    (((hg.clm_apply (hb (pairLeft j))).clm_apply contDiffOn_const).mul
    ((hg.clm_apply (hb (pairRight j))).clm_apply contDiffOn_const))

lemma coordinates_model (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0) (a : MetricForms.Form E 2) :
    coordinates b a = GeometricSymbol.coords (basisOfFrame g hdim b hb) (formEquiv g 2 a) := by
  ext i
  fin_cases i <;> simp [coordinates_apply,GeometricSymbol.coords,pairLeft,pairRight,
    formEquiv_apply] <;> rfl

end TamingCompatibility.HodgeFrame

end
end

end
end

end OAI
