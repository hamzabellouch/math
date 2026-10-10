import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Form
import OAI.Geometry.TamingCompatibility.Elliptic.LocalGarding

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.JetOperator
open EuclideanEnergy ContinuousAlternatingMap
open scoped SchwartzMap ContDiff LineDeriv
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

abbrev Jet (F : Type*) := F × (Fin 4 → F) × (Fin 4 → Fin 4 → F)

def value (u : 𝓢(V,F)) (x : V) : Jet F :=
  (u x, (fun i => (∂_{e i} u) x), (fun i j => (∂_{e j} (∂_{e i} u)) x))

def projZero : Jet F →L[ℝ] F := ContinuousLinearMap.fst ℝ F _
def projOne (i : Fin 4) : Jet F →L[ℝ] F :=
  (ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ F _))
def projTwo (i j : Fin 4) : Jet F →L[ℝ] F :=
  ((ContinuousLinearMap.proj j) : (Fin 4 → F) →L[ℝ] F).comp
    (((ContinuousLinearMap.proj i) : (Fin 4 → Fin 4 → F) →L[ℝ] (Fin 4 → F)).comp
    ((ContinuousLinearMap.snd ℝ (Fin 4 → F) (Fin 4 → Fin 4 → F)).comp
      (ContinuousLinearMap.snd ℝ F _)))

def firstOrder (a : Fin 4 → V → F →L[ℝ] G) (b : V → F →L[ℝ] G)
    (u : 𝓢(V,F)) (x : V) : G := ∑ i, a i x ((∂_{e i} u) x) + b x (u x)

def derivativeComponent (a : Fin 4 → V → F →L[ℝ] G) (b : V → F →L[ℝ] G)
    (x : V) (j : Fin 4) : Jet F →L[ℝ] G :=
  (∑ i, ((a i x).comp (projTwo i j) + (fderiv ℝ (a i) x (e j)).comp (projOne i))) +
    (b x).comp (projOne j) + (fderiv ℝ b x (e j)).comp projZero

def derivativeJet (a : Fin 4 → V → F →L[ℝ] G) (b : V → F →L[ℝ] G)
    (x : V) : Jet F →L[ℝ] (V →L[ℝ] G) :=
  ∑ j, (ContinuousLinearMap.smulRightL ℝ V G (EuclideanSpace.proj j)).comp
    (derivativeComponent a b x j)

lemma derivative_component (a : Fin 4 → V → F →L[ℝ] G) (b : V → F →L[ℝ] G)
    (u : 𝓢(V,F)) (x : V) (ha : ∀ i, DifferentiableAt ℝ (a i) x)
    (hb : DifferentiableAt ℝ b x) (j : Fin 4) :
    fderiv ℝ (firstOrder a b u) x (e j) = derivativeComponent a b x j (value u x) := by
  have hu : DifferentiableAt ℝ (u : V → F) x := u.differentiableAt
  have hd (i : Fin 4) : DifferentiableAt ℝ (fun y => (a i y) ((∂_{e i} u) y)) x :=
    (ha i).clm_apply (∂_{e i} u).differentiableAt
  unfold firstOrder
  rw [fderiv_fun_add (DifferentiableAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hd i)) (hb.clm_apply hu),
    fderiv_fun_sum (fun i _ => hd i)]
  simp only [_root_.add_apply,_root_.sum_apply]
  simp_rw [fderiv_clm_apply (ha _) (SchwartzMap.differentiableAt _),fderiv_clm_apply hb hu]
  simp only [derivativeComponent,value,projZero,projOne,projTwo,_root_.add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.flip_apply,_root_.sum_apply,SchwartzMap.lineDerivOp_apply_eq_fderiv,add_assoc]

lemma directional_reconstruct (L : V →L[ℝ] G) :
    (∑ j : Fin 4, (EuclideanSpace.proj j).smulRight (L (e j))) = L := by
  ext x
  have hx : x = ∑ j : Fin 4, x j • e j := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,e] using
      ((EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr x).symm
  calc
    _ = L (∑ j : Fin 4, x j • e j) := by simp only [_root_.sum_apply,
      ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,_root_.map_sum,map_smul]
    _ = L x := congrArg L hx.symm

lemma derivativeJet_spec (a : Fin 4 → V → F →L[ℝ] G) (b : V → F →L[ℝ] G)
    (u : 𝓢(V,F)) (x : V) (ha : ∀ i, DifferentiableAt ℝ (a i) x)
    (hb : DifferentiableAt ℝ b x) :
    derivativeJet a b x (value u x) = fderiv ℝ (firstOrder a b u) x := by
  change (∑ j : Fin 4, (EuclideanSpace.proj j).smulRight
    (derivativeComponent a b x j (value u x))) = _
  simp_rw [← derivative_component a b u x ha hb]
  exact directional_reconstruct _

def exteriorJet (a : Fin 4 → V → F →L[ℝ] MetricForms.Form V 1)
    (b : V → F →L[ℝ] MetricForms.Form V 1) (x : V) :
    Jet F →L[ℝ] MetricForms.Form V 2 :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := 1) ℝ V ℝ).comp (derivativeJet a b x)

lemma exteriorJet_spec (a : Fin 4 → V → F →L[ℝ] MetricForms.Form V 1)
    (b : V → F →L[ℝ] MetricForms.Form V 1) (u : 𝓢(V,F)) (x : V)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hb : DifferentiableAt ℝ b x) :
    exteriorJet a b x (value u x) = extDeriv (firstOrder a b u) x := by
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := 1) ℝ V ℝ)
    (derivativeJet a b x (value u x)) = _
  rw [derivativeJet_spec a b u x ha hb]
  rfl

lemma value_norm (u : 𝓢(V,F)) (x : V) :
    ‖value u x‖ ≤ ‖u x‖ + ∑ i : Fin 4, ‖(∂_{e i} u) x‖ +
      ∑ i : Fin 4, ∑ j : Fin 4, ‖(∂_{e j} (∂_{e i} u)) x‖ := by
  have h1 : ‖(fun i : Fin 4 => (∂_{e i} u) x)‖ ≤ ∑ i : Fin 4, ‖(∂_{e i} u) x‖ := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
    intro i
    exact Finset.single_le_sum (f := fun i : Fin 4 => ‖(∂_{e i} u) x‖)
      (fun i _ => norm_nonneg ((∂_{e i} u) x)) (Finset.mem_univ i)
  have h2 : ‖(fun i : Fin 4 => fun j : Fin 4 => (∂_{e j} (∂_{e i} u)) x)‖ ≤
      ∑ i : Fin 4, ∑ j : Fin 4, ‖(∂_{e j} (∂_{e i} u)) x‖ := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)))).mpr
    intro i
    have hi : ‖(fun j : Fin 4 => (∂_{e j} (∂_{e i} u)) x)‖ ≤
        ∑ j : Fin 4, ‖(∂_{e j} (∂_{e i} u)) x‖ := by
      apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => norm_nonneg ((∂_{e j} (∂_{e i} u)) x)))).mpr
      intro j
      exact Finset.single_le_sum (f := fun j : Fin 4 => ‖(∂_{e j} (∂_{e i} u)) x‖)
        (fun j _ => norm_nonneg ((∂_{e j} (∂_{e i} u)) x)) (Finset.mem_univ j)
    exact hi.trans (Finset.single_le_sum
      (f := fun i : Fin 4 => ∑ j : Fin 4, ‖(∂_{e j} (∂_{e i} u)) x‖)
      (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg ((∂_{e j} (∂_{e i} u)) x))) (Finset.mem_univ i))
  simp only [value,Prod.norm_def]
  have hz0 := norm_nonneg (u x)
  have hz1 := norm_nonneg (fun i : Fin 4 => (∂_{e i} u) x)
  have hz2 := norm_nonneg (fun i j : Fin 4 => (∂_{e j} (∂_{e i} u)) x)
  apply max_le
  · linarith
  · apply max_le <;> linarith

lemma exteriorJet_bound (a : Fin 4 → V → F →L[ℝ] MetricForms.Form V 1)
    (b : V → F →L[ℝ] MetricForms.Form V 1) (u : 𝓢(V,F)) (x : V) :
    ‖exteriorJet a b x (value u x)‖ ≤ ‖exteriorJet a b x‖ *
      (‖u x‖ + ∑ i : Fin 4, ‖(∂_{e i} u) x‖ +
        ∑ i : Fin 4, ∑ j : Fin 4, ‖(∂_{e j} (∂_{e i} u)) x‖) :=
  ((exteriorJet a b x).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (value_norm u x) (norm_nonneg _))

end TamingCompatibility.JetOperator

end
end

section
noncomputable section
namespace TamingCompatibility.JetOperator
open EuclideanEnergy ContinuousAlternatingMap Set
open scoped SchwartzMap ContDiff LineDeriv
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma derivativeComponent_smooth {U : Set V} (hU : IsOpen U)
    (a : Fin 4 → V → F →L[ℝ] G) (b : V → F →L[ℝ] G)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U) (j : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => derivativeComponent a b x j) U := by
  have hda (i : Fin 4) : ContDiffOn ℝ ∞ (fderiv ℝ (a i)) U :=
    (ha i).fderiv_of_isOpen hU (by simp)
  have hdb : ContDiffOn ℝ ∞ (fderiv ℝ b) U := hb.fderiv_of_isOpen hU (by simp)
  unfold derivativeComponent
  exact ((ContDiffOn.sum (fun i _ => ((ha i).clm_comp contDiffOn_const).add
    (((hda i).clm_apply contDiffOn_const).clm_comp contDiffOn_const))).add
    (hb.clm_comp contDiffOn_const)).add
      ((hdb.clm_apply contDiffOn_const).clm_comp contDiffOn_const)

lemma derivativeJet_smooth {U : Set V} (hU : IsOpen U)
    (a : Fin 4 → V → F →L[ℝ] G) (b : V → F →L[ℝ] G)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U) :
    ContDiffOn ℝ ∞ (derivativeJet a b) U := by
  unfold derivativeJet
  exact ContDiffOn.sum (fun j _ => contDiffOn_const.clm_comp
    (derivativeComponent_smooth hU a b ha hb j))

lemma exteriorJet_smooth {U : Set V} (hU : IsOpen U)
    (a : Fin 4 → V → F →L[ℝ] MetricForms.Form V 1)
    (b : V → F →L[ℝ] MetricForms.Form V 1)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U) :
    ContDiffOn ℝ ∞ (exteriorJet a b) U :=
  contDiffOn_const.clm_comp (derivativeJet_smooth hU a b ha hb)

lemma exteriorJet_bounded {U K : Set V} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (a : Fin 4 → V → F →L[ℝ] MetricForms.Form V 1)
    (b : V → F →L[ℝ] MetricForms.Form V 1)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖exteriorJet a b x‖ ≤ C := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (f := exteriorJet a b)
    ((exteriorJet_smooth hU a b ha hb).continuousOn.mono hKU)
  exact ⟨max 0 C,le_max_left _ _,fun x hx => (hC x hx).trans (le_max_right _ _)⟩

end TamingCompatibility.JetOperator

end
end

end
end
end

end OAI
