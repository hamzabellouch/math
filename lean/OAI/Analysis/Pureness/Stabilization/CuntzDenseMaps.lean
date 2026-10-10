import OAI.Analysis.Pureness.Stabilization.CuntzFunctor
import OAI.Analysis.Pureness.Stabilization.Perturbation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

namespace OAI
noncomputable section
open scoped NNReal Topology
namespace CuntzTrace
variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma starHom_continuous (f : A →⋆ₙₐ[ℂ] B) : Continuous f := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simpa only [dist_eq_norm,← map_sub,NNReal.coe_one,one_mul] using
    NonUnitalStarAlgHom.norm_apply_le f (a-b)

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

@[simp] theorem Positive.map_cut (f : A →⋆ₙₐ[ℂ] B) (ε : ℝ≥0) (a : Positive A) :
    Positive.map f (Positive.cut ε a) = Positive.cut ε (Positive.map f a) := by
  apply Subtype.ext
  exact f.map_cfcₙ (fun t : ℝ => max (t-ε) 0) a.1
    (by fun_prop) (by simp) (starHom_continuous f) (IsSelfAdjoint.of_nonneg a.2)
    (IsSelfAdjoint.of_nonneg (Positive.map f a).2)

theorem cuntzClass_maps_eq_of_dense (f g : A →⋆ₙₐ[ℂ] B) (S : Set (Positive A))
    (hdense : ∀ (a : Positive A) (ε : ℝ), 0 < ε → ∃ b ∈ S, ‖a.1-b.1‖ < ε)
    (hcut : ∀ b ∈ S, ∀ ε : ℝ≥0, Positive.cut ε b ∈ S)
    (hfg : ∀ b ∈ S, CuntzClass.mk (Positive.map f b) = CuntzClass.mk (Positive.map g b))
    (a : Positive A) : CuntzClass.mk (Positive.map f a) = CuntzClass.mk (Positive.map g a) := by
  have oneWay (f g : A →⋆ₙₐ[ℂ] B)
      (hfg : ∀ b ∈ S, CuntzClass.mk (Positive.map f b) = CuntzClass.mk (Positive.map g b)) :
      CuntzBelow (Positive.map f a) (Positive.map g a) := by
    intro ε hε
    obtain ⟨b,hb,hab⟩ := hdense a (ε/4) (by linarith)
    let δ : ℝ≥0 := ⟨ε/4,by linarith⟩
    have hδ : 0 < δ := by change (0 : ℝ) < ε/4; linarith
    have hba : CuntzBelow (Positive.cut δ b) a :=
      cut_cuntzBelow_of_norm_sub_lt b a δ hδ (by change ‖b.1-a.1‖ < ε/4; rwa [norm_sub_rev])
    have hcb := ((CuntzClass.mk_eq_mk_iff _ _).mp (hfg _ (hcut b hb δ))).1.trans (hba.map g)
    obtain ⟨v,hv⟩ := hcb (ε/2) (by linarith)
    refine ⟨v,?_⟩
    have hd : ‖f (Positive.cut δ b).1-f a.1‖ < ε/2 := by
      rw [← map_sub]
      apply (NonUnitalStarAlgHom.norm_apply_le f _).trans_lt
      have hc := Positive.norm_sub_cut_le δ b
      have ht := norm_sub_le_norm_sub_add_norm_sub (Positive.cut δ b).1 b.1 a.1
      rw [norm_sub_rev (Positive.cut δ b).1 b.1,norm_sub_rev b.1 a.1] at ht
      change ‖b.1-(Positive.cut δ b).1‖ ≤ ε/4 at hc
      linarith
    have ht := norm_sub_le_norm_sub_add_norm_sub (star v * g a.1 * v) (f (Positive.cut δ b).1) (f a.1)
    change ‖star v*g a.1*v-f (Positive.cut δ b).1‖ < ε/2 at hv
    exact ht.trans_lt (by linarith)
  exact (CuntzClass.mk_eq_mk_iff _ _).mpr ⟨oneWay f g hfg,
    oneWay g f (fun b hb => (hfg b hb).symm)⟩
end CuntzTrace

end

end OAI
