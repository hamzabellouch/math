import Mathlib
import OAI.Analysis.WeakInfiniteness.Hereditary
import OAI.Analysis.WeakInfiniteness.LocalSplitting

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology ComplexStarModule

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {B : Type v} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_mul_of_hereditary_square (π : A →⋆ₙₐ[ℂ] B) {h : A} (hh : IsSelfAdjoint h)
    {l : ℝ} (he : π h*π h=l • π h) {b : A} (hb : b ∈ hereditarySubalgebra h hh) :
    π h*π b=l • π b := by
  have hc : IsClosed {x : A | π h*π x=l • π x} := isClosed_eq (by fun_prop) (by fun_prop)
  apply closure_minimal _ hc hb
  rintro _ ⟨x,rfl⟩
  change π h*π (h*x*h)=l • π (h*x*h)
  simp only [map_mul]
  rw [← mul_assoc,← mul_assoc,he,smul_mul_assoc,smul_mul_assoc]

lemma exists_real_scalar_of_no_orthogonal (π : A →⋆ₙₐ[ℂ] B)
    {h : A} (hh : 0 ≤ h) (hhn : π h ≠ 0)
    (hno : ∀ a ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      ∀ b ∈ hereditarySubalgebra h hh.isSelfAdjoint,
      0 ≤ a → 0 ≤ b → a*b=0 → π a=0 ∨ π b=0)
    {b : A} (hb : b ∈ hereditarySubalgebra h hh.isSelfAdjoint) (hb0 : 0 ≤ b) :
    ∃ r : ℝ,π b=r • π h := by
  let l := ‖π h‖
  let μ := ‖π b‖
  let r := ‖π (h+b)‖
  have hl : 0 < l := norm_pos_iff.mpr hhn
  have hsqh : π h*π h=l • π h := square_eq_norm_smul_of_no_orthogonal _ π hno
    (self_mem_hereditary h hh) hh
  have hsqb : π b*π b=μ • π b := square_eq_norm_smul_of_no_orthogonal _ π hno hb hb0
  have hsql : π h*π b=l • π b := map_mul_of_hereditary_square π hh.isSelfAdjoint hsqh hb
  have hsqr : π b*π h=l • π b := by
    have he := congrArg star hsql
    simpa only [star_mul,(map_nonneg π hh).star_eq,(map_nonneg π hb0).star_eq,
      star_smul,star_trivial] using he
  have hsum := square_eq_norm_smul_of_no_orthogonal _ π hno
    ((hereditarySubalgebra h hh.isSelfAdjoint).add_mem (self_mem_hereditary h hh) hb) (add_nonneg hh hb0)
  have hprod : π (h+b)*π (h+b)=l • π h+(2*l+μ) • π b := by
    simp only [map_add,mul_add,add_mul,hsqh,hsqb,hsql,hsqr]
    module
  rw [hprod] at hsum
  change l • π h+(2*l+μ) • π b=r • π (h+b) at hsum
  rw [map_add,smul_add] at hsum
  have hr : r ≤ l+μ := by dsimp [r,l,μ]; rw [map_add]; exact norm_add_le _ _
  have hd : 0 < 2*l+μ-r := by linarith
  have he : (2*l+μ-r) • π b=(r-l) • π h := by
    convert congrArg (fun z : B => z-l • π h-r • π b) hsum using 1 <;> module
  refine ⟨(2*l+μ-r)⁻¹*(r-l),?_⟩
  calc
    π b=(2*l+μ-r)⁻¹ • ((2*l+μ-r) • π b) := by
      rw [smul_smul,inv_mul_cancel₀ (ne_of_gt hd),one_smul]
    _ = (2*l+μ-r)⁻¹ • ((r-l) • π h) := by rw [he]
    _ = _ := by rw [smul_smul]

end

end WeakPureInfiniteness
end

end OAI
