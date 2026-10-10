import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI

section

noncomputable section
namespace NuclearNorm
open scoped ComplexOrder ComplexStarModule

variable {A : Type*} [CStarAlgebra A]

lemma shifted_norm_bound [Nontrivial A] (x : selfAdjoint A) (t : ℝ) :
    ‖x‖ + |t| ≤ max ‖(x : A) + algebraMap ℝ A t‖ ‖-(x : A) + algebraMap ℝ A t‖ := by
  have hab (r : ℝ) (hr : r ∈ spectrum ℝ (x : A)) :
      |r + t| ≤ ‖(x : A) + algebraMap ℝ A t‖ := by
    rw [← Real.norm_eq_abs]
    apply spectrum.norm_le_norm_of_mem
    rw [← spectrum.add_singleton_eq]
    exact Set.add_mem_add hr (Set.mem_singleton t)
  have hnb (r : ℝ) (hr : r ∈ spectrum ℝ (x : A)) :
      |-r + t| ≤ ‖-(x : A) + algebraMap ℝ A t‖ := by
    rw [← Real.norm_eq_abs]
    apply spectrum.norm_le_norm_of_mem
    rw [← spectrum.add_singleton_eq]
    apply Set.add_mem_add _ (Set.mem_singleton t)
    rw [← spectrum.neg_eq]
    exact Set.neg_mem_neg.mpr hr
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum (x : A) x.property with h | h
  · have h1 := (hab _ h).trans (le_max_left _ ‖-(x : A) + algebraMap ℝ A t‖)
    have h2 := (hnb _ h).trans (le_max_right ‖(x : A) + algebraMap ℝ A t‖ _)
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
      exact (le_abs_self _).trans h1
    · rw [abs_of_nonpos ht]
      have := (neg_le_abs (-‖(x : A)‖ + t)).trans h2
      change ‖(x : A)‖ + -t ≤ _
      linarith only [this]
  · have h1 := (hab _ h).trans (le_max_left _ ‖-(x : A) + algebraMap ℝ A t‖)
    have h2 := (hnb _ h).trans (le_max_right ‖(x : A) + algebraMap ℝ A t‖ _)
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
      simpa using (le_abs_self _).trans h2
    · rw [abs_of_nonpos ht]
      have := (neg_le_abs (-‖(x : A)‖ + t)).trans h1
      change ‖(x : A)‖ + -t ≤ _
      linarith only [this]

def jordanEmbedding : (selfAdjoint A × ℝ) →ₗ[ℝ] selfAdjoint (A × A) where
  toFun p := ⟨((p.1 : A) + algebraMap ℝ A p.2,
      -(p.1 : A) + algebraMap ℝ A p.2), by
    change star _ = _
    apply Prod.ext <;> simp [Prod.star_def, Algebra.algebraMap_eq_smul_one, p.1.property.star_eq]⟩
  map_add' p q := by
    apply Subtype.ext
    ext <;> simp only [Prod.fst_add, Prod.snd_add, (selfAdjoint A).coe_add, (selfAdjoint (A × A)).coe_add,
      map_add, neg_add_rev] <;> abel
  map_smul' t p := by
    apply Subtype.ext
    ext <;> simp [selfAdjoint.val_smul,
      smul_add, smul_neg, Algebra.algebraMap_eq_smul_one, smul_smul]

lemma jordanEmbedding_bound [Nontrivial A] (p : selfAdjoint A × ℝ) :
    ‖p.1‖ + |p.2| ≤ ‖jordanEmbedding p‖ := shifted_norm_bound p.1 p.2

lemma jordanEmbedding_injective [Nontrivial A] :
    Function.Injective (jordanEmbedding (A := A)) := by
  apply (LinearMap.ker_eq_bot).mp
  apply (LinearMap.ker_eq_bot').mpr
  intro p hp
  have h := jordanEmbedding_bound p
  rw [hp, norm_zero] at h
  have hx : ‖p.1‖ = 0 := by linarith [abs_nonneg p.2, norm_nonneg p.1]
  have ht : |p.2| = 0 := by linarith [abs_nonneg p.2, norm_nonneg p.1]
  exact Prod.ext (norm_eq_zero.mp hx) (abs_eq_zero.mp ht)

variable [PartialOrder A] [StarOrderedRing A]

lemma real_jordan_domination [Nontrivial A] (l : selfAdjoint A →L[ℝ] ℝ) :
    ∃ g : A →ₚ[ℂ] ℂ, g 1 = (‖l‖ + 1 : ℝ) ∧
      ∀ a : selfAdjoint A, 0 ≤ (a : A) → |l a| ≤ (g a).re := by
  let C : ℝ := ‖l‖ + 1
  have hC : 0 < C := add_pos_of_nonneg_of_pos (norm_nonneg l) zero_lt_one
  have hl : ‖l‖ ≤ C := le_add_of_nonneg_right zero_le_one
  let e := LinearEquiv.ofInjective (jordanEmbedding (A := A)) jordanEmbedding_injective
  let F : (selfAdjoint A × ℝ) →ₗ[ℝ] ℝ :=
    l.toLinearMap.comp (LinearMap.fst ℝ (selfAdjoint A) ℝ) +
      C • LinearMap.snd ℝ (selfAdjoint A) ℝ
  let R := F.comp e.symm.toLinearMap
  have hR (y : LinearMap.range (jordanEmbedding (A := A))) : ‖R y‖ ≤ C * ‖y‖ := by
    obtain ⟨p,rfl⟩ := e.surjective y
    dsimp only [R, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [e.symm_apply_apply]
    change ‖l p.1 + C * p.2‖ ≤ C * ‖jordanEmbedding p‖
    calc
      _ ≤ ‖l p.1‖ + ‖C * p.2‖ := norm_add_le _ _
      _ ≤ C * ‖p.1‖ + C * |p.2| := by
        rw [norm_mul, Real.norm_eq_abs C, Real.norm_eq_abs p.2, abs_of_pos hC]
        exact add_le_add ((l.le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hl (norm_nonneg _))) le_rfl
      _ = C * (‖p.1‖ + |p.2|) := (mul_add _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (jordanEmbedding_bound p) hC.le
  let Rc := R.mkContinuous C hR
  obtain ⟨G,hG,hGn⟩ := exists_extension_norm_eq (jordanEmbedding (A := A)).range Rc
  have hGC : ‖G‖ ≤ C := by
    rw [hGn]
    exact LinearMap.mkContinuous_norm_le _ hC.le _
  have heval (p : selfAdjoint A × ℝ) : G (jordanEmbedding p) = l p.1 + C * p.2 := by
    have hh := hG (e p)
    change G (jordanEmbedding p) = F (e.symm (e p)) at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  have hE1 : jordanEmbedding (A := A) (0,1) = 1 := by
    apply Subtype.ext
    simp [jordanEmbedding]
  have hG1 : G 1 = C := by simpa [hE1] using heval (0,1)
  have hGP (a : selfAdjoint (A × A)) (ha : 0 ≤ (a : A × A)) : 0 ≤ G a := by
    let Gn : selfAdjoint (A × A) →L[ℝ] ℝ := C⁻¹ • G
    have hnn : ‖Gn‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro a
      change ‖C⁻¹ * G a‖ ≤ 1 * ‖a‖
      rw [norm_mul, Real.norm_eq_abs C⁻¹, abs_of_pos (inv_pos.mpr hC)]
      calc
        _ ≤ C⁻¹ * (‖G‖ * ‖a‖) := mul_le_mul_of_nonneg_left (G.le_opNorm a)
          (inv_pos.mpr hC).le
        _ ≤ C⁻¹ * (C * ‖a‖) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hGC (norm_nonneg _)) (inv_pos.mpr hC).le
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hC.ne']
    have hn1 : Gn 1 = 1 := by simp [Gn, hG1, hC.ne']
    have hh := Pureness.selfAdjointFunctional_nonneg Gn hnn hn1 a ha
    change 0 ≤ C⁻¹ * G a at hh
    exact nonneg_of_mul_nonneg_right hh (inv_pos.mpr hC)
  let d : A →ₗ[ℂ] A × A := LinearMap.id.prod LinearMap.id
  let H := Pureness.selfAdjointFunctionalComplex G.toLinearMap
  have hH (a : A × A) (ha : 0 ≤ a) : 0 ≤ H a := by
    change 0 ≤ Pureness.selfAdjointFunctionalComplex G.toLinearMap
      ((⟨a, IsSelfAdjoint.of_nonneg ha⟩ : selfAdjoint (A × A)) : A × A)
    rw [Pureness.selfAdjointFunctionalComplex_apply]
    exact_mod_cast hGP ⟨a, IsSelfAdjoint.of_nonneg ha⟩ ha
  let g : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ (H.comp d) (fun a ha => hH _ ⟨ha,ha⟩)
  refine ⟨g,?_,?_⟩
  · change H (1 : selfAdjoint (A × A)) = _
    rw [Pureness.selfAdjointFunctionalComplex_apply]
    change (G 1 : ℂ) = _
    exact congrArg Complex.ofReal hG1
  · intro a ha
    let x : selfAdjoint (A × A) := ⟨((a : A),0), by change star ((a : A),0) = _; simp [Prod.star_def, a.property.star_eq]⟩
    let y : selfAdjoint (A × A) := ⟨(0,(a : A)), by change star (0,(a : A)) = _; simp [Prod.star_def,a.property.star_eq]⟩
    have hx : 0 ≤ G x := hGP _ ⟨ha,le_rfl⟩
    have hy : 0 ≤ G y := hGP _ ⟨le_rfl,ha⟩
    have hsub : x - y = jordanEmbedding (a,0) := by
      apply Subtype.ext; simp [x,y,jordanEmbedding]
    have hv : l a = G x - G y := by
      rw [← map_sub, hsub, heval]; simp
    have hadd : (g (a : A)).re = G x + G y := by
      have hs : ((x+y : selfAdjoint (A × A)) : A × A) = ((a : A),(a : A)) := by
        ext <;> simp [x,y]
      change (H ((a : A),(a : A))).re = _
      rw [← hs, Pureness.selfAdjointFunctionalComplex_apply, Complex.ofReal_re]
      exact map_add G x y
    rw [hv,hadd]
    exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

end NuclearNorm

end
end

end OAI
