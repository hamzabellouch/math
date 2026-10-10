import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TraceCone.Weights
import OAI.Analysis.JiangSu.Excision.JordanDomination

namespace OAI

section

noncomputable section
namespace NuclearNorm
open scoped ComplexOrder ComplexStarModule

section FiniteDomination

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma finite_state_domination [Nontrivial A] {I : Type*} [Fintype I]
    (l : I → selfAdjoint A →L[ℝ] ℝ) :
    ∃ (f : A →ₚ[ℂ] ℂ) (C : ℝ), f 1 = 1 ∧ 0 ≤ C ∧
      ∀ i, ∀ a : selfAdjoint A, 0 ≤ (a : A) → |l i a| ≤ C * (f a).re := by
  classical
  choose g hg1 hg using fun i => real_jordan_domination (l i)
  obtain ⟨f₀,hf₀⟩ := Pureness.exists_normalizedPositiveState (A := A)
  let C : ℝ := 1 + ∑ i, (‖l i‖ + 1)
  have hC : 0 < C := by
    dsimp [C]
    have h : 0 ≤ ∑ i, (‖l i‖ + 1) := Finset.sum_nonneg fun _ _ => by positivity
    linarith
  let G : A →ₗ[ℂ] ℂ := f₀.toLinearMap + ∑ i, (g i).toLinearMap
  have hG (a : A) : G a = f₀ a + ∑ i, g i a := by simp [G,LinearMap.sum_apply]
  have hGP (a : A) (ha : 0 ≤ a) : 0 ≤ G a := by
    rw [hG]; exact add_nonneg (f₀.map_nonneg ha)
      (Finset.sum_nonneg fun i _ => (g i).map_nonneg ha)
  have hG1 : G 1 = (C : ℂ) := by simp [hG,hf₀,hg1,C,Complex.ofReal_sum]
  let f : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ (((C⁻¹ : ℝ) : ℂ) • G) (by
    intro a ha
    change 0 ≤ ((C⁻¹ : ℝ) : ℂ) * G a
    exact mul_nonneg (by exact_mod_cast (inv_pos.mpr hC).le) (hGP a ha))
  have hf (a : A) : f a = ((C⁻¹ : ℝ) : ℂ) * G a := rfl
  have hreal (a : A) : C * (f a).re = (G a).re := by
    rw [hf,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [← mul_assoc,mul_inv_cancel₀ hC.ne',one_mul]
  refine ⟨f,C,?_,hC.le,?_⟩
  · rw [hf,hG1]
    exact_mod_cast inv_mul_cancel₀ hC.ne'
  · intro i a ha
    apply (hg i a ha).trans
    rw [hreal,hG,Complex.add_re,Complex.re_sum]
    have hgpos (j : I) : 0 ≤ (g j a).re := (Complex.nonneg_iff.mp ((g j).map_nonneg ha)).1
    have hsum := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) => hgpos j)
      (Finset.mem_univ i)
    have h0 : 0 ≤ (f₀ a).re := (Complex.nonneg_iff.mp (f₀.map_nonneg ha)).1
    linarith

end FiniteDomination

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {K I : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable [Fintype I]

theorem nuclear_norm_coefficient_approximation [Nontrivial A]
    (hA : Pureness.IsNuclear.{0,0} A)
    (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (hα : Function.Injective α)
    (x : I → selfAdjoint A) {ε : ℝ} (hε : 0 < ε) :
    ∃ L ∈ NuclearTrace.coefficientCone α, ‖x - fun i => L (x i)‖ < ε := by
  classical
  let C := (NuclearTrace.coefficientCone α).map (NuclearTrace.evalTuple x)
  have h0 : (0 : I → selfAdjoint A) ∈ C :=
    ⟨0,NuclearTrace.coefficientCone_zero α,by ext i; rfl⟩
  have hs : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ C, t • s ∈ C := by
    intro t ht s hs
    obtain rfl | ht := ht.eq_or_lt
    · simpa using h0
    · exact C.smul_mem ht hs
  have hdual (f : (I → selfAdjoint A) →L[ℝ] ℝ)
      (_ : ∃ c : ℝ, 0 ≤ c ∧ ∀ y, |f y| ≤ c * normSeminorm ℝ (I → selfAdjoint A) y)
      (hfc : ∀ s ∈ C, f s ≤ 0) : f x ≤ 0 := by
    let l (i : I) : selfAdjoint A →L[ℝ] ℝ := f.comp (ContinuousLinearMap.single ℝ (fun _ : I => selfAdjoint A) i)
    obtain ⟨g,c,hg,hc,hl⟩ := finite_state_domination l
    have he (y : I → selfAdjoint A) : (∑ i, l i (y i)) = f y := by
      change (∑ i, f (Pi.single i (y i))) = f y
      rw [← map_sum]
      congr 1
      exact Finset.univ_sum_single y
    rw [← he x]
    apply NuclearTrace.nuclear_coefficient_dual_bound hA α hα g hg x
      (fun i => (l i).toLinearMap) hc hl
    intro n k a
    change (∑ i, l i _) ≤ 0
    rw [he]
    apply hfc
    exact ⟨NuclearTrace.coefficientSelfAdjMap α k a,
      ConvexCone.subset_hull ⟨n,k,a,rfl⟩,rfl⟩
  obtain ⟨s,hs,hclose⟩ := NuclearTrace.seminorm_cone_approximation_of_dual
    (normSeminorm ℝ (I → selfAdjoint A)) continuous_norm C C.convex h0 hs x hdual hε
  obtain ⟨L,hL,rfl⟩ := hs
  exact ⟨L,hL,hclose⟩

end NuclearNorm

end
end

end OAI
