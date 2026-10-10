import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Module
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def graphConormal (L : E →ₗ[ℝ] F) : (F →L[ℝ] ℝ) →ₗ[ℝ] L.graph.dualAnnihilator where
  toFun b := ⟨(-b.toLinearMap.comp L).coprod b.toLinearMap,by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro x hx
    have hx' : x.2 = L x.1 := hx
    change -b (L x.1) + b x.2 = 0
    rw [hx']
    ring⟩
  map_add' b c := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change -(b (L x.1) + c (L x.1)) + (b x.2 + c x.2) =
      (-b (L x.1) + b x.2) + (-c (L x.1) + c x.2)
    ring
  map_smul' r b := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change -(r * b (L x.1)) + r * b x.2 = r * (-b (L x.1) + b x.2)
    ring

theorem graphConormal_surjective [FiniteDimensional ℝ F]
    (L : E →ₗ[ℝ] F) : Function.Surjective (graphConormal L) := by
  intro g
  let b : F →L[ℝ] ℝ := (g.val.comp (LinearMap.inr ℝ E F)).toContinuousLinearMap
  refine ⟨b,?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  have hg : g.val (x.1,L x.1) = 0 :=
    (Submodule.mem_dualAnnihilator _).mp g.property _ rfl
  have hs : (x.1,L x.1) = (x.1,0)+(0,L x.1) := by simp
  rw [hs,map_add] at hg
  have hx : x = (x.1,0)+(0,x.2) := by simp
  change -g.val (0,L x.1)+g.val (0,x.2) = g.val x
  conv_rhs => rw [hx,map_add]
  linarith

theorem graphConormal_injective (L : E →ₗ[ℝ] F) :
    Function.Injective (graphConormal L) := by
  intro b c h
  apply ContinuousLinearMap.ext
  intro y
  have hh := congrArg (fun g : L.graph.dualAnnihilator => g.val (0,y)) h
  simpa [graphConormal] using hh

end

open Complex Set Filter Metric
open scoped Topology

def normalCayley (u : ℂ) : ℂ := (u-I)/(u+I)
def normalUncayley (v : ℂ) : ℂ := I*(1+v)/(1-v)

lemma add_I_ne_zero_of_im_pos {u : ℂ} (hu : 0 < u.im) : u+I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [add_im,I_im,zero_im] at this
  linarith

lemma one_sub_ne_zero_of_norm_lt_one {v : ℂ} (hv : ‖v‖ < 1) : 1-v ≠ 0 := by
  intro h
  have he : v = 1 := (sub_eq_zero.mp h).symm
  simp [he] at hv

lemma normalCayley_sub_one {u : ℂ} (hu : u+I ≠ 0) :
    1-normalCayley u = 2*I/(u+I) := by
  simp only [normalCayley]
  field_simp
  ring

lemma normalCayley_ne_one {u : ℂ} (hu : u+I ≠ 0) : normalCayley u ≠ 1 := by
  have hh : 1-normalCayley u ≠ 0 := by
    rw [normalCayley_sub_one hu]
    exact div_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hu
  exact fun h => hh (by rw [h,sub_self])

lemma normalUncayley_add_I {v : ℂ} (hv : 1-v ≠ 0) :
    normalUncayley v+I = 2*I/(1-v) := by
  simp only [normalUncayley]
  field_simp
  ring

lemma normalUncayley_add_I_ne_zero {v : ℂ} (hv : 1-v ≠ 0) :
    normalUncayley v+I ≠ 0 := by
  rw [normalUncayley_add_I hv]
  exact div_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hv

lemma normalUncayley_cayley {u : ℂ} (hu : u+I ≠ 0) :
    normalUncayley (normalCayley u) = u := by
  rw [normalUncayley,normalCayley_sub_one hu,normalCayley]
  field_simp
  ring

lemma normalCayley_uncayley {v : ℂ} (hv : 1-v ≠ 0) :
    normalCayley (normalUncayley v) = v := by
  rw [normalCayley,normalUncayley_add_I hv,normalUncayley]
  field_simp
  ring

lemma norm_normalCayley_lt_one {u : ℂ} (hu : 0 < u.im) :
    ‖normalCayley u‖ < 1 := by
  rw [normalCayley,norm_div,div_lt_one (norm_pos_iff.mpr (add_I_ne_zero_of_im_pos hu))]
  apply (sq_lt_sq₀ (norm_nonneg (u-I)) (norm_nonneg (u+I))).mp
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im,sub_zero,add_zero]
  nlinarith

lemma one_add_im_le_norm_add_I {u : ℂ} (hu : 0 ≤ u.im) :
    1+u.im ≤ ‖u+I‖ := by
  have hh := Complex.abs_im_le_norm (u+I)
  simpa only [add_im,I_im,abs_of_nonneg (by linarith : 0 ≤ u.im+1),add_comm] using hh

lemma cayley_tangent_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c : ℝ} (hc : 0 < c) {z : E} {u : ℂ} (hu : c*‖z‖^2 ≤ u.im) :
    ‖(u+I)⁻¹ • z‖ ≤ (2*Real.sqrt c)⁻¹ := by
  have hy : 0 ≤ u.im := (mul_nonneg hc.le (sq_nonneg _)).trans hu
  have hd : 0 < 1+u.im := by linarith
  have hd' : 0 < ‖u+I‖ := hd.trans_le (one_add_im_le_norm_add_I hy)
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsq := Real.sq_sqrt hc.le
  have hest : 2*Real.sqrt c*‖z‖ ≤ 1+u.im := by
    have hh := sq_nonneg (Real.sqrt c*‖z‖-1)
    nlinarith
  rw [norm_smul,norm_inv]
  rw [← one_div (2*Real.sqrt c)]
  apply (le_div_iff₀ (by positivity : 0 < 2*Real.sqrt c)).mpr
  calc
    ‖u+I‖⁻¹*‖z‖*(2*Real.sqrt c) = (2*Real.sqrt c*‖z‖)/‖u+I‖ := by ring
    _ ≤ 1 := (div_le_one hd').mpr (hest.trans (one_add_im_le_norm_add_I hy))

end Release061

end

end OAI
