import Mathlib
import OAI.Geometry.PrescribedPotential.CoreBounds
import OAI.Geometry.PrescribedPotential.GlobalPartition

namespace OAI

/-! Global Completion. -/

section

 

noncomputable section
open Set Filter Topology MeasureTheory
open scoped SchwartzMap ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace Localizers
variable (D : Localizers A ι)

def BoundedCore (s t : ℝ) (T : Smooth A →ₗ[ℝ] Smooth A) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ f, ‖D.embed t (T f)‖ ≤ C * ‖D.embed s f‖

def extendCore (s t : ℝ) (T : Smooth A →ₗ[ℝ] Smooth A) :
    D.Sobolev s →L[ℝ] D.Sobolev t :=
  ((D.embed t).comp T).extendOfNorm (D.embed s)

lemma extendCore_embed {s t : ℝ} {T : Smooth A →ₗ[ℝ] Smooth A}
    (hT : D.BoundedCore s t T) (f : Smooth A) :
    D.extendCore s t T (D.embed s f) = D.embed t (T f) :=
  LinearMap.extendOfNorm_eq (D.embed_dense s) (by
    obtain ⟨C, _, h⟩ := hT
    exact ⟨C, h⟩) f

lemma extendCore_norm {s t : ℝ} {T : Smooth A →ₗ[ℝ] Smooth A}
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ f, ‖D.embed t (T f)‖ ≤ C * ‖D.embed s f‖) :
    ‖D.extendCore s t T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  exact LinearMap.norm_extendOfNorm_apply_le (D.embed_dense s) C hT

lemma boundedCore_lower {s t : ℝ} (hst : t ≤ s) :
    D.BoundedCore s t (LinearMap.id : Smooth A →ₗ[ℝ] Smooth A) := by
  obtain ⟨C, hC, hc⟩ := CoreBound.id (E := EC d) hst
  refine ⟨C, hC, fun f => ?_⟩
  change ‖D.coordinates t f‖ ≤ C * ‖D.coordinates s f‖
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg _))).mpr
  intro p
  exact (hc (localize A (D.index p) (D.weight p) (D.support_sub p) f)).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm (D.coordinates s f) p) hC)

def lower (s t : ℝ) : D.Sobolev s →L[ℝ] D.Sobolev t :=
  D.extendCore s t LinearMap.id

lemma lower_embed {s t : ℝ} (hst : t ≤ s) (f : Smooth A) :
    D.lower s t (D.embed s f) = D.embed t f :=
  D.extendCore_embed (D.boundedCore_lower hst) f

lemma lower_self (s : ℝ) : D.lower s s = ContinuousLinearMap.id ℝ _ := by
  apply DFunLike.coe_injective
  apply (D.embed_dense s).equalizer (D.lower s s).continuous continuous_id
  funext f
  exact D.lower_embed le_rfl f

lemma lower_comp {s t r : ℝ} (hst : t ≤ s) (htr : r ≤ t) :
    (D.lower t r).comp (D.lower s t) = D.lower s r := by
  apply DFunLike.coe_injective
  apply (D.embed_dense s).equalizer (by fun_prop) (by fun_prop)
  funext f
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    D.lower_embed hst, D.lower_embed htr, D.lower_embed (htr.trans hst)]

 
def distribution (s : ℝ) (p : ι) : D.Sobolev s →L[ℝ] 𝓢'(EC d, ℂ) :=
  (realize s).restrictScalars ℝ ∘L (ContinuousLinearMap.proj p) ∘L (D.closedSpace s).subtypeL

lemma distribution_apply (s : ℝ) (p : ι) (u : D.Sobolev s) :
    D.distribution s p u = realize s (u.val p) := rfl

lemma distribution_embed (s : ℝ) (p : ι) (f : Smooth A) :
    D.distribution s p (D.embed s f) =
      SchwartzMap.toTemperedDistributionCLM (EC d) ℂ volume
        (localize A (D.index p) (D.weight p) (D.support_sub p) f) :=
  realize_schwartzCoord s _

lemma distribution_lower {s t : ℝ} (hst : t ≤ s) (p : ι) (u : D.Sobolev s) :
    D.distribution t p (D.lower s t u) = D.distribution s p u := by
  have he : (D.distribution t p) ∘ D.lower s t = D.distribution s p := by
    apply (D.embed_dense s).equalizer (by fun_prop) (by fun_prop)
    funext f
    simp only [Function.comp_apply, D.lower_embed hst, distribution_embed]
  exact congr_fun he u

lemma lower_injective {s t : ℝ} (hst : t ≤ s) : Function.Injective (D.lower s t) := by
  intro u v huv
  apply Subtype.ext
  funext p
  apply realize_injective s
  change D.distribution s p u = D.distribution s p v
  rw [← D.distribution_lower hst p u, ← D.distribution_lower hst p v, huv]

lemma lower_extendCore {s t r : ℝ} (htr : r ≤ t) (T : Smooth A →ₗ[ℝ] Smooth A)
    (hT : D.BoundedCore s t T) (hR : D.BoundedCore s r T) (u : D.Sobolev s) :
    D.lower t r (D.extendCore s t T u) = D.extendCore s r T u := by
  have he : (D.lower t r) ∘ D.extendCore s t T = D.extendCore s r T := by
    apply (D.embed_dense s).equalizer (by fun_prop) (by fun_prop)
    funext f
    simp only [Function.comp_apply, D.extendCore_embed hT, D.extendCore_embed hR, D.lower_embed htr]
  exact congr_fun he u

lemma extendCore_lower {s t r : ℝ} (hst : t ≤ s) (T : Smooth A →ₗ[ℝ] Smooth A)
    (hT : D.BoundedCore t r T) (hS : D.BoundedCore s r T) (u : D.Sobolev s) :
    D.extendCore t r T (D.lower s t u) = D.extendCore s r T u := by
  have he : (D.extendCore t r T) ∘ D.lower s t = D.extendCore s r T := by
    apply (D.embed_dense s).equalizer (by fun_prop) (by fun_prop)
    funext f
    simp only [Function.comp_apply, D.lower_embed hst, D.extendCore_embed hT, D.extendCore_embed hS]
  exact congr_fun he u
end Localizers
end GlobalElliptic

end
end

end OAI
