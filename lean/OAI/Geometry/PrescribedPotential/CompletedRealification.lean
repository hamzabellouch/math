import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalConjugation

namespace OAI

/-! Completed Realification. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance realifyNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance realifyNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance realifyTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance realifyCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

def completedRealify (k : ℕ) : D.localizers.Sobolev (k : ℝ) →L[ℝ] D.localizers.Sobolev (k : ℝ) :=
  D.localizers.extendCore (k : ℝ) (k : ℝ) Smooth.realify

lemma completedRealify_embed (k : ℕ) (f : Smooth A) :
    D.completedRealify k (D.localizers.embed (k : ℝ) f) = D.localizers.embed (k : ℝ) (Smooth.realify f) :=
  D.localizers.extendCore_embed (D.realify_integer_bound k) f

lemma completedRealify_mem (k : ℕ) (u : D.localizers.Sobolev (k : ℝ)) :
    D.completedRealify k u ∈ D.localizers.realCompletion (k : ℝ) := by
  have hf (f : Smooth A) : D.completedRealify k (D.localizers.embed (k : ℝ) f) ∈
      D.localizers.realCompletion (k : ℝ) := by
    rw [D.completedRealify_embed]
    exact (D.localizers.realEmbed (k : ℝ) ⟨Smooth.realify f,Smooth.realify_real f⟩).property
  exact (D.localizers.embed_dense (k : ℝ)).induction_on u
    ((Submodule.isClosed_topologicalClosure _).preimage (D.completedRealify k).continuous) hf

def realProjection (k : ℕ) : D.localizers.Sobolev (k : ℝ) →L[ℝ] D.localizers.RealSobolev (k : ℝ) :=
  (D.completedRealify k).codRestrict _ (D.completedRealify_mem k)

lemma completedRealify_of_real (k : ℕ) (u : D.localizers.RealSobolev (k : ℝ)) :
    D.completedRealify k u.val = u.val := by
  have he : (fun u : D.localizers.RealSobolev (k : ℝ) => D.completedRealify k u.val) =
      (fun u => u.val) := by
    apply (D.localizers.realEmbed_dense (k : ℝ)).equalizer (by fun_prop) continuous_subtype_val
    funext f
    dsimp only [Function.comp_apply]
    rw [Localizers.realEmbed_val,D.completedRealify_embed,Smooth.realify_eq_of_real]
  exact congr_fun he u

lemma realProjection_of_real (k : ℕ) (u : D.localizers.RealSobolev (k : ℝ)) :
    D.realProjection k u.val = u := Subtype.ext (D.completedRealify_of_real k u)

lemma completedRealify_lower (k l : ℕ) (hlk : l ≤ k) (u : D.localizers.Sobolev (k : ℝ)) :
    D.localizers.lower (k : ℝ) (l : ℝ) (D.completedRealify k u) =
      D.completedRealify l (D.localizers.lower (k : ℝ) (l : ℝ) u) := by
  have hkl : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlk
  have he : D.localizers.lower (k : ℝ) (l : ℝ) ∘ D.completedRealify k =
      D.completedRealify l ∘ D.localizers.lower (k : ℝ) (l : ℝ) := by
    apply (D.localizers.embed_dense (k : ℝ)).equalizer (by fun_prop) (by fun_prop)
    funext f
    dsimp only [Function.comp_apply]
    rw [D.completedRealify_embed,D.localizers.lower_embed hkl,
      D.localizers.lower_embed hkl,D.completedRealify_embed]
  exact congr_fun he u

 

lemma mem_real_of_lower (k l : ℕ) (hlk : l ≤ k) (u : D.localizers.Sobolev (k : ℝ))
    (hu : D.localizers.lower (k : ℝ) (l : ℝ) u ∈ D.localizers.realCompletion (l : ℝ)) :
    u ∈ D.localizers.realCompletion (k : ℝ) := by
  have he : D.completedRealify k u = u := by
    apply D.localizers.lower_injective (by exact_mod_cast hlk : (l : ℝ) ≤ (k : ℝ))
    rw [D.completedRealify_lower k l hlk]
    exact D.completedRealify_of_real l ⟨_,hu⟩
  rw [← he]
  exact D.completedRealify_mem k u

lemma mem_real_of_lower_eq (k l : ℕ) (s : ℝ) (hs : s = (l : ℝ))
    (hlk : l ≤ k) (u : D.localizers.Sobolev (k : ℝ))
    (hu : D.localizers.lower (k : ℝ) s u ∈ D.localizers.realCompletion s) :
    u ∈ D.localizers.realCompletion (k : ℝ) := by
  subst s
  exact D.mem_real_of_lower k l hlk u hu

end GluingData
end GlobalElliptic

end
end

end OAI
