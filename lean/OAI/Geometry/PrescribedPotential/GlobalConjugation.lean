import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalCompletion
import OAI.Geometry.PrescribedPotential.GlobalParametrix
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.SchwartzConjugation

namespace OAI

/-! Global Conjugation. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
namespace ChartCutoff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {U : Set E}
def conjugate (κ : ChartCutoff U) : ChartCutoff U where
  val := schwartzConj κ.val
  compact := by
    apply HasCompactSupport.of_support_subset_isCompact κ.compact
    intro x hx
    exact subset_tsupport _ (fun h => hx (by simp only [schwartzConj_apply,h,star_zero]))
  support_sub := by
    apply Subset.trans _ κ.support_sub
    apply closure_mono
    intro x hx h
    exact hx (by simp only [schwartzConj_apply,h,star_zero])
@[simp] lemma conjugate_apply (κ : ChartCutoff U) (x : E) : κ.conjugate x = star (κ x) := rfl
end ChartCutoff
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace Smooth

def conjugate : Smooth A →ₗ[ℝ] Smooth A where
  toFun f := ⟨fun x => star (f x),fun i => Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn (f.smooth i)⟩
  map_add' f h := by ext x; exact star_add _ _
  map_smul' c f := by ext x; exact map_smul Complex.conjCLE.toContinuousLinearMap c (f x)
@[simp] lemma conjugate_apply (f : Smooth A) (x : X) : conjugate f x = star (f x) := rfl

def realify : Smooth A →ₗ[ℝ] Smooth A := (1/2 : ℝ) • (LinearMap.id + conjugate)
lemma realify_apply (f : Smooth A) (x : X) : realify f x = ((f x).re : ℂ) := by
  change (1/2 : ℝ) • (f x + star (f x)) = _
  apply Complex.ext <;> simp
  ring
lemma realify_real (f : Smooth A) : realify f ∈ realSmoothSpace A := by
  intro x
  rw [realify_apply]
  rfl
lemma realify_eq_of_real (f : RealSmooth A) : realify f.val = f.val := by
  ext x
  rw [realify_apply]
  exact Complex.ext rfl (f.property x).symm
end Smooth
variable [T2Space X] {ι : Type*} [Fintype ι]
lemma conjugate_globalize (i : Fin A.count) (κ : ChartCutoff (A.euclideanChart i).target)
    (f : 𝓢(EC d,ℂ)) :
    Smooth.conjugate (globalize i κ f) = globalize i κ.conjugate (schwartzConj f) := by
  ext x
  rw [Smooth.conjugate_apply,globalize_apply,globalize_apply]
  split_ifs <;> simp only [ChartCutoff.conjugate_apply,schwartzConj_apply,star_mul',star_zero]
namespace GluingData
variable [CompactSpace X] {g : KaehlerMetric A} (D : GluingData g ι)

lemma conjugate_integer_bound (k : ℕ) : D.localizers.BoundedCore (k : ℝ) (k : ℝ) Smooth.conjugate := by
  have hb (p : ι) := globalize_integer_bound D.localizers (D.patch p).index (D.cutoff p).conjugate k
  choose B hB hb using hb
  obtain ⟨C,hC,hc⟩ := schwartzConj_integer_bound (E := EC d) k
  refine ⟨∑ p, B p*C,Finset.sum_nonneg (fun p _ => mul_nonneg (hB p) hC),fun f => ?_⟩
  have he : Smooth.conjugate f = ∑ p, globalize (D.patch p).index (D.cutoff p).conjugate
      (schwartzConj (D.forcing p f)) := by
    conv_lhs => rw [← D.forcing_reconstruction f]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro p _
    exact conjugate_globalize _ _ _
  rw [he,map_sum,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p _
  exact (hb p _).trans ((mul_le_mul_of_nonneg_left (hc _) (hB p)).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (D.forcing_bound p (k : ℝ) f)
      (mul_nonneg (hB p) hC)))

lemma embed_realify (k : ℕ) (f : Smooth A) :
    D.localizers.embed (k : ℝ) (Smooth.realify f) =
      (1/2 : ℝ) • (D.localizers.embed (k : ℝ) f + D.localizers.embed (k : ℝ) (Smooth.conjugate f)) := by
  change D.localizers.embed (k : ℝ) ((1/2 : ℝ) • (f + Smooth.conjugate f)) = _
  rw [map_smul,map_add]

lemma half_add_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : E) (C : ℝ) (hC : ‖v‖ ≤ C*‖u‖) :
    ‖(1/2 : ℝ) • (u+v)‖ ≤ ((1/2 : ℝ)*(1+C))*‖u‖ := by
  rw [norm_smul]
  norm_num only [norm_div,norm_one,Real.norm_ofNat]
  calc
    _ ≤ (1/2 : ℝ)*(‖u‖+‖v‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (1/2 : ℝ)*(‖u‖+C*‖u‖) := mul_le_mul_of_nonneg_left (add_le_add le_rfl hC) (by norm_num)
    _ = _ := by ring

lemma realify_integer_bound (k : ℕ) : D.localizers.BoundedCore (k : ℝ) (k : ℝ) Smooth.realify := by
  obtain ⟨C,hC,hb⟩ := D.conjugate_integer_bound k
  refine ⟨(1/2 : ℝ)*(1+C),mul_nonneg (by norm_num) (by linarith),fun f => ?_⟩
  rw [D.embed_realify]
  exact half_add_norm_le _ _ C (hb f)
end GluingData
end GlobalElliptic

end
end

end OAI
