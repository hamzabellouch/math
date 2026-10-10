import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.CornerCompression
import OAI.Analysis.JiangSu.Traceless.TracelessPureInfiniteness
import OAI.Analysis.JiangSu.Traceless.TracelessSpatialCorner

namespace OAI


noncomputable section
open Pureness

namespace CurrentMain.Traceless

section Reflection
variable {A B : Type*} [CStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma compress_norm_le {q : B} (hq : IsStarProjection q) (x : B) :
    ‖q*x*q‖ ≤ ‖x‖ := by
  have hn : ‖q‖ ≤ 1 := IsStarProjection.norm_le q hq
  calc
    ‖q*x*q‖ ≤ ‖q*x‖*‖q‖ := norm_mul_le _ _
    _ ≤ ‖q*x‖ := mul_le_of_le_one_right (norm_nonneg _) hn
    _ ≤ ‖q‖*‖x‖ := norm_mul_le _ _
    _ ≤ ‖x‖ := mul_le_of_le_one_left (norm_nonneg _) hn

theorem cuntz_reflect_corner (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ)
    (hcorner : ∀ x : B, φ 1*x*φ 1 = x → ∃ a : A, φ a = x)
    {a b : A} (hcomp : CuntzSubequiv (φ a) (φ b)) : CuntzSubequiv a b := by
  have hq : IsStarProjection (φ 1) := by
    constructor
    · change φ 1*φ 1 = φ 1
      rw [←map_mul,one_mul]
    · change star (φ 1) = φ 1
      rw [←map_star,star_one]
  have hl (c : A) : φ 1*φ c = φ c := by rw [←map_mul,one_mul]
  have hr (c : A) : φ c*φ 1 = φ c := by rw [←map_mul,mul_one]
  apply (cuntzSubequiv_iff_norm a b).mpr
  intro ε hε
  obtain ⟨x,hx⟩ := (cuntzSubequiv_iff_norm (φ a) (φ b)).mp hcomp ε hε
  have hfix : φ 1*(φ 1*x*φ 1)*φ 1 = φ 1*x*φ 1 := by
    simp only [←mul_assoc,hq.isIdempotentElem.eq]
    simp only [mul_assoc,hq.isIdempotentElem.eq]
  obtain ⟨y,hy⟩ := hcorner _ hfix
  refine ⟨y,?_⟩
  have he : φ (a-star y*b*y) = φ 1*(φ a-star x*φ b*x)*φ 1 := by
    rw [map_sub,map_mul,map_mul,map_star,hy,star_mul,star_mul,hq.isSelfAdjoint.star_eq]
    have hbp (z : B) : φ b*(φ 1*z) = φ b*z := by rw [←mul_assoc,hr]
    simp only [mul_sub,sub_mul,mul_assoc,hl,hr,hbp]
  rw [←NonUnitalStarAlgHom.norm_map φ hφ,he]
  exact (compress_norm_le hq _).trans_lt hx

end Reflection

section Spatial

open CurrentMain.Spatial

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

theorem cuntz_reflect_spatial (hπ : Function.Injective π) {a b : A}
    (hcomp : CuntzSubequiv (spatialCornerInto π a) (spatialCornerInto π b)) :
    CuntzSubequiv a b :=
  cuntz_reflect_corner (spatialCornerInto π) (spatialCornerInto_injective π hπ)
    (spatialCornerInto_full π hπ) hcomp

instance spatialStabilizationOrder : PartialOrder (SpatialStabilization π) :=
  CStarAlgebra.spectralOrder _

instance spatialStabilizationStarOrdered : StarOrderedRing (SpatialStabilization π) :=
  CStarAlgebra.spectralOrderedRing _

theorem infinite_projection_of_stabilized_comparison
    [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    (hπ : Function.Injective π)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcomparison : ∀ a b : SpatialStabilization π,
      0 ≤ a → 0 ≤ b → b ≠ 0 → CuntzSubequiv a b)
    (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0) :
    ∃ p : A, p ∈ hereditaryCorner h hh ∧ IsInfiniteProjection p := by
  have hmap (a : A) (ha : 0 ≤ a) : 0 ≤ spatialCornerInto π a := by
    have hs : star (CFC.sqrt a) * CFC.sqrt a = a := by
      rw [(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self a ha]
    rw [← hs, map_mul, map_star]
    exact star_mul_self_nonneg (spatialCornerInto π (CFC.sqrt a))
  apply infinite_projection_in_every_hereditary hsimple hinf ?_ h hh hh0
  intro b hb hb0
  apply cuntz_reflect_spatial π hπ
  apply hcomparison
  · exact hmap 1 (by positivity)
  · exact hmap b hb
  · intro he
    apply hb0
    exact spatialCornerInto_injective π hπ (he.trans (map_zero _).symm)

end Spatial


variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def IsHereditary (E : NonUnitalStarSubalgebra ℂ A) : Prop :=
  IsClosed (E : Set A) ∧ ∀ a b : A, 0 ≤ a → a ≤ b → b ∈ E → a ∈ E

lemma IsHereditary.sandwich {E : NonUnitalStarSubalgebra ℂ A} (hE : IsHereditary E)
    {h : A} (hh : 0 ≤ h) (hhE : h ∈ E) (a : A) : h*a*h ∈ E := by
  have ha : a ∈ Submodule.span ℂ {x : A | 0 ≤ x} := by
    rw [CStarAlgebra.span_nonneg]
    exact Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem a ha =>
    have hpos : 0 ≤ h*a*h := by
      simpa only [hh.isSelfAdjoint.star_eq] using star_left_conjugate_nonneg ha h
    have hle : h*a*h ≤ ‖a‖ • (h*h) := by
      simpa only [hh.isSelfAdjoint.star_eq] using
        (CStarAlgebra.star_left_conjugate_le_norm_smul h a ha.isSelfAdjoint)
    exact hE.2 _ _ hpos hle
      ((E.toSubmodule.restrictScalars ℝ).smul_mem ‖a‖ (E.mul_mem hhE hhE))
  | zero => rw [mul_zero,zero_mul]; exact E.zero_mem
  | add a b _ _ ha hb => rw [mul_add,add_mul]; exact E.add_mem ha hb
  | smul c a _ ha => rw [mul_smul_comm,smul_mul_assoc]; exact E.smul_mem c ha

lemma IsHereditary.principal_le {E : NonUnitalStarSubalgebra ℂ A}
    (hE : IsHereditary E) {h : A} (hh : 0 ≤ h) (hhE : h ∈ E) :
    hereditaryCorner h hh ≤ E := by
  intro x hx
  change x ∈ closure (Set.range fun a : A => h*a*h) at hx
  exact hE.1.closure_subset (closure_mono
    (Set.range_subset_iff.mpr (hE.sandwich hh hhE)) hx)

def IsInfiniteProjectionIn (E : NonUnitalStarSubalgebra ℂ A) (p : A) : Prop :=
  p ∈ E ∧ IsStarProjection p ∧ ∃ v : A, v ∈ E ∧ p*v = v ∧ v*p = v ∧
    star v*v = p ∧ v*star v ≤ p ∧ v*star v ≠ p

lemma IsHereditary.infiniteProjectionIn {E : NonUnitalStarSubalgebra ℂ A}
    (hE : IsHereditary E) {p : A} (hp : IsInfiniteProjection p) (hpE : p ∈ E) :
    IsInfiniteProjectionIn E p := by
  obtain ⟨hpp,v,hpv,hvp,hv,hvv,hproper⟩ := hp
  refine ⟨hpE,hpp,v,?_,hpv,hvp,hv,hvv,hproper⟩
  simpa only [hpv,hvp] using hE.sandwich hpp.nonneg hpE v

theorem infinite_projection_in_nonzero_hereditary [Nontrivial A]
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcomparison : ∀ b : A, 0 ≤ b → b ≠ 0 → CuntzSubequiv 1 b)
    (E : NonUnitalStarSubalgebra ℂ A) (hE : IsHereditary E) (hE0 : E ≠ ⊥) :
    ∃ p : A, IsInfiniteProjectionIn E p := by
  classical
  have hx : ∃ x : A, x ∈ E ∧ x ≠ 0 := by
    by_contra! hz
    apply hE0
    apply le_antisymm
    · intro x hx
      rw [hz x hx]
      exact (⊥ : NonUnitalStarSubalgebra ℂ A).zero_mem
    · exact bot_le
  obtain ⟨x,hxE,hx0⟩ := hx
  let h := star x*x
  have hh : 0 ≤ h := star_mul_self_nonneg x
  have hh0 : h ≠ 0 := (CStarRing.star_mul_self_ne_zero_iff x).mpr hx0
  have hhE : h ∈ E := E.mul_mem (E.star_mem' hxE) hxE
  obtain ⟨p,hpE,hp⟩ := infinite_projection_in_every_hereditary hsimple hinf hcomparison h hh hh0
  exact ⟨p,hE.infiniteProjectionIn hp (hE.principal_le hh hhE hpE)⟩

end CurrentMain.Traceless

end

end OAI
