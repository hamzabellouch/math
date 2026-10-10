import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.DegreeIdeals
import OAI.Combinatorics.Chromatic.Shuffle.TensorFiltration

namespace OAI

section
namespace ElementaryPositivity.CenterCalculus
open MvPolynomial
open scoped TensorProduct
variable {α β A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]

noncomputable def box (p : MvPolynomial α A) (q : MvPolynomial β B) :
    MvPolynomial (α ⊕ β) (A ⊗[ℚ] B) :=
  rename Sum.inl (map (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A ⊗[ℚ] B).toRingHom p) *
  rename Sum.inr (map (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] A ⊗[ℚ] B).toRingHom q)

lemma coeff_box (p : MvPolynomial α A) (q : MvPolynomial β B)
    (z : α →₀ ℕ) (w : β →₀ ℕ) :
    (box p q).coeff (z.sumElim w) = p.coeff z ⊗ₜ[ℚ] q.coeff w := by
  rw [box,IndependentCoefficientTensor.coeff_independent_product,coeff_map,coeff_map]
  change (_ ⊗ₜ[ℚ] 1) * (1 ⊗ₜ[ℚ] _) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

lemma box_mul (p p' : MvPolynomial α A) (q q' : MvPolynomial β B) :
    box (p*p') (q*q') = box p q * box p' q' := by
  simp only [box,map_mul]
  ring

lemma box_scalar (p : MvPolynomial α ℚ) (q : MvPolynomial β ℚ) :
    box (map (algebraMap ℚ A) p) (map (algebraMap ℚ B) q) =
      map (algebraMap ℚ (A ⊗[ℚ] B)) (rename Sum.inl p * rename Sum.inr q) := by
  have hL : (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A ⊗[ℚ] B).toRingHom.comp
      (algebraMap ℚ A)=algebraMap ℚ (A ⊗[ℚ] B) := by
    ext r
    exact (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A ⊗[ℚ] B).commutes r
  have hR : (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] A ⊗[ℚ] B).toRingHom.comp
      (algebraMap ℚ B)=algebraMap ℚ (A ⊗[ℚ] B) := by
    ext r
    exact (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] A ⊗[ℚ] B).commutes r
  simp only [box,map_mul,map_rename,map_map,hL,hR]

lemma box_scalar_left (p : MvPolynomial α ℚ) (q : MvPolynomial β ℚ)
    (f : MvPolynomial α A) (g : MvPolynomial β B) :
    box (map (algebraMap ℚ A) p*f) (map (algebraMap ℚ B) q*g)=
      map (algebraMap ℚ (A ⊗[ℚ] B)) (rename Sum.inl p*rename Sum.inr q)*box f g := by
  rw [box_mul,box_scalar]
end ElementaryPositivity.CenterCalculus

end
section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open ElementaryPositivity.CenterCalculus
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma weightComponent_node_tmul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (L R : SplitTree I) (U V : ℤ)
    (x : tensor (quotientFamily a μ) L) (y : tensor (quotientFamily a μ) R)
    (hx : x∈degreeCutSubmodule a μ L U) (hy : y∈degreeCutSubmodule a μ R V) :
    weightComponent a μ (.node L R) (U+V) (x⊗ₜ[ℚ]y)=
      weightComponent a μ L U x ⊗ₜ[ℚ] weightComponent a μ R V y := by
  classical
  apply sub_eq_zero.mp
  apply componentTensor_detect a μ (.node L R)
  rintro ⟨k,l⟩
  rw [map_sub,componentTensor_weightComponent]
  change (if 2*(L.totalDegree k+R.totalDegree l)+(L.doubleShift a+R.doubleShift a)=U+V
    then componentTensor a μ L k x⊗ₜ[ℚ]componentTensor a μ R l y else 0)-
    (componentTensor a μ L k (weightComponent a μ L U x)⊗ₜ[ℚ]
      componentTensor a μ R l (weightComponent a μ R V y))=0
  rw [componentTensor_weightComponent,componentTensor_weightComponent]
  by_cases hk : 2*L.totalDegree k+L.doubleShift a<U
  · rw [hx k hk]
    simp
  by_cases hl : 2*R.totalDegree l+R.doubleShift a<V
  · rw [hy l hl]
    simp
  split_ifs <;> (try simp only [TensorProduct.zero_tmul,TensorProduct.tmul_zero,sub_self]) <;> omega

lemma centeredRestrictionB_coeff_degreeCut (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (T : SplitTree I) (hT : T.OnSlope c η θ) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) T.dim)
    (hf : f∈sourceFiltration a c η hc θ T.dim W) (z : T.Centers →₀ ℕ) :
    (centeredRestrictionB a c η hc θ T hT f).coeff z∈
      degreeCutSubmodule a (SlopeArithmetic.slope c η) T W := by
  intro k hk
  exact sourceFiltration_allTrees a c η hc θ W f hf T hT rfl k z hk

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
