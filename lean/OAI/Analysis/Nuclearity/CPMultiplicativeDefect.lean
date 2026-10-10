import OAI.Analysis.Nuclearity.UnitalCPContraction

namespace OAI

/-! # A Cauchy--Schwarz bound for the multiplicative defect of a unital CP map -/

noncomputable section
open scoped CStarAlgebra ComplexOrder InnerProductSpace WithCStarModule
open Filter Topology

namespace WeakPureInfiniteness

section Matrix

variable {B n : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B] [Fintype n]

local instance multiplicativeDefectMatrixRealModule : Module ℝ (CStarMatrix n n B) := Module.complexToReal _

lemma positiveMatrix_entry_norm_le (M : CStarMatrix n n B) (hM : 0 ≤ M) (i j : n) :
    ‖M i j‖ ≤ Real.sqrt ‖M i i‖ * Real.sqrt ‖M j j‖ := by
  let S := CFC.sqrt M
  have hS : S * star S = M := by
    rw [show star S = S from (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self M hM
  let v (k : n) : C⋆ᵐᵒᵈ(B, n → B) :=
    (WithCStarModule.equiv B (n → B)).symm (fun l => S k l)
  have hi (a b : n) : inner B (v b) (v a) = M a b := by
    rw [← hS, CStarMatrix.mul_apply]
    simp only [v, WithCStarModule.pi_inner, WithCStarModule.equiv_symm_pi_apply,
      WithCStarModule.inner_def, CStarMatrix.star_apply]
  have hn (a : n) : ‖v a‖ = Real.sqrt ‖M a a‖ := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := B), hi]
  have h := CStarModule.norm_inner_le (A := B) (C⋆ᵐᵒᵈ(B, n → B)) (x := v j) (y := v i)
  rw [hi, hn, hn, mul_comm] at h
  exact h

end Matrix

section Defect

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

lemma completelyPositive_multiplicative_defect {φ : A →L[ℂ] B}
    (hφ : CompletelyPositive φ) (h1 : φ 1 = 1) (a b : A) :
    ‖φ (star a * b) - star (φ a) * φ b‖ ≤
      Real.sqrt ‖φ (star a * a) - star (φ a) * φ a‖ *
        Real.sqrt ‖φ (star b * b) - star (φ b) * φ b‖ := by
  let R : CStarMatrix (Fin 3) (Fin 3) A :=
    CStarMatrix.ofMatrix !![a,b,1;0,0,0;0,0,0]
  let M := matrixLinearMap φ (star R * R)
  have hM : 0 ≤ M := matrixLinearMap_nonneg hφ (star_mul_self_nonneg R)
  let V : CStarMatrix (Fin 3) (Fin 3) B :=
    CStarMatrix.ofMatrix !![1,0,0;0,1,0;-φ a,-φ b,0]
  let D := star V * M * V
  have hD : 0 ≤ D := star_left_conjugate_nonneg hM V
  have h00 : D 0 0 = φ (star a * a) - star (φ a) * φ a := by
    simp [D,V,M,R,CStarMatrix.mul_apply,CStarMatrix.star_apply,Fin.sum_univ_three,
      completelyPositive_map_star hφ,h1]
    noncomm_ring
  have h11 : D 1 1 = φ (star b * b) - star (φ b) * φ b := by
    simp [D,V,M,R,CStarMatrix.mul_apply,CStarMatrix.star_apply,Fin.sum_univ_three,
      completelyPositive_map_star hφ,h1]
    noncomm_ring
  have h01 : D 0 1 = φ (star a * b) - star (φ a) * φ b := by
    simp [D,V,M,R,CStarMatrix.mul_apply,CStarMatrix.star_apply,Fin.sum_univ_three,
      completelyPositive_map_star hφ,h1]
    noncomm_ring
  simpa only [h00,h11,h01] using positiveMatrix_entry_norm_le D hD 0 1

lemma completelyPositive_defect_sqrt_le {φ : A →L[ℂ] B}
    (hφ : CompletelyPositive φ) (h1 : φ 1 = 1) (a : A) :
    Real.sqrt ‖φ (star a * a) - star (φ a) * φ a‖ ≤ ‖a‖ := by
  have hp : 0 ≤ φ (star a * a) - star (φ a) * φ a :=
    sub_nonneg.mpr (completelyPositive_schwarz_of_unital hφ h1 a)
  have hn : ‖φ (star a * a) - star (φ a) * φ a‖ ≤ ‖a‖ ^ 2 := by
    calc
      _ ≤ ‖φ (star a * a)‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg
        (sub_le_self _ (star_mul_self_nonneg _)) hp
      _ ≤ ‖star a * a‖ := completelyPositive_norm_apply_le_of_unital hφ h1 _
      _ = _ := by rw [CStarRing.norm_star_mul_self]; ring
  exact (Real.sqrt_le_iff).mpr ⟨norm_nonneg _, hn⟩

lemma completelyPositive_mul_error_le {φ : A →L[ℂ] B}
    (hφ : CompletelyPositive φ) (h1 : φ 1 = 1) (a b : A) :
    ‖φ (a * b) - φ a * φ b‖ ≤
      Real.sqrt ‖φ (a * star a) - φ a * star (φ a)‖ * ‖b‖ := by
  have h := completelyPositive_multiplicative_defect hφ h1 (star a) b
  simp only [star_star, completelyPositive_map_star hφ] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (completelyPositive_defect_sqrt_le hφ h1 b) (Real.sqrt_nonneg _))

end Defect

section Convergence

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {l : Filter ι} {φ : ι → A →L[ℂ] A}

lemma completelyPositive_mul_tendsto (hφ : ∀ i, CompletelyPositive (φ i))
    (h1 : ∀ i, φ i 1 = 1) {a b : A}
    (ha : Tendsto (fun i => φ i a) l (𝓝 a))
    (haa : Tendsto (fun i => φ i (a * star a)) l (𝓝 (a * star a)))
    (hb : Tendsto (fun i => φ i b) l (𝓝 b)) :
    Tendsto (fun i => φ i (a * b)) l (𝓝 (a * b)) := by
  have hd : Tendsto (fun i => φ i (a * star a) - φ i a * star (φ i a)) l (𝓝 0) := by
    simpa only [sub_self] using haa.sub (ha.mul ha.star)
  have hn := tendsto_zero_iff_norm_tendsto_zero.mp hd
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simp only [Real.sqrt_zero] at hs
  have he : Tendsto (fun i => φ i (a * b) - φ i a * φ i b) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun i =>
      completelyPositive_mul_error_le (hφ i) (h1 i) a b)
    simpa only [Function.comp_def, zero_mul] using hs.mul_const ‖b‖
  simpa only [sub_add_cancel, zero_add] using he.add (ha.mul hb)

end Convergence

end WeakPureInfiniteness

end

end OAI
