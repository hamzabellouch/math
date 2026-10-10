import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.PolynomialCharts

namespace OAI

section
noncomputable section
                                             
section

namespace MaximalSeshadri.Projective
noncomputable section
open MvPolynomial
variable {R A σ : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

lemma aeval_mem_grade (x : σ → A) (hx : ∀ i, x i ∈ 𝒜 1)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) :
    aeval x p ∈ 𝒜 d := by
  classical
  rw [p.as_sum]
  simp only [map_sum, aeval_monomial]
  apply sum_mem
  intro m hm
  have h := SetLike.prod_pow_mem_graded 𝒜 (fun _ : σ => (1 : ℕ)) x
    (F := m.support) m (fun i _ => hx i)
  simp only [smul_eq_mul, mul_one] at h
  rw [← hp.degree_eq_sum_deg_support hm] at h
  simpa only [Algebra.smul_def, Finsupp.prod] using (𝒜 d).smul_mem (p.coeff m) h

attribute [local instance] MvPolynomial.gradedAlgebra

def gradedPolynomialEval (x : σ → A) (hx : ∀ i, x i ∈ 𝒜 1) :
    homogeneousSubmodule σ R →+*ᵍ 𝒜 where
  toRingHom := (aeval x).toRingHom
  map_mem := fun hp => aeval_mem_grade 𝒜 x hx hp

end

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousIdeal MvPolynomial
universe u
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

def shiftedVariable (c : σ → K) : Option σ → MvPolynomial (Option σ) K
  | none => X none
  | some i => X (some i) + C (c i) * X none

lemma shiftedVariable_homogeneous (c : σ → K) (i : Option σ) :
    shiftedVariable c i ∈ PolyGrade K (Option σ) 1 := by
  cases i with
  | none => exact isHomogeneous_X _ _
  | some i =>
    exact (isHomogeneous_X _ _).add (by
      simpa using (isHomogeneous_C (Option σ) (c i)).mul (isHomogeneous_X K none))

def projectiveShiftHom (c : σ → K) :
    PolyGrade K (Option σ) →+*ᵍ PolyGrade K (Option σ) :=
  gradedPolynomialEval _ (shiftedVariable c) (shiftedVariable_homogeneous c)

@[simp] lemma projectiveShiftHom_X (c : σ → K) (i : Option σ) :
    projectiveShiftHom c (X i) = shiftedVariable c i := aeval_X _ _

@[simp] lemma projectiveShiftHom_C (c : σ → K) (a : K) :
    projectiveShiftHom c (C a) = C a := aeval_C _ _

lemma projectiveShiftHom_inverse (c : σ → K) :
    (projectiveShiftHom (fun i => -c i)).comp (projectiveShiftHom c) =
      GradedRingHom.id (PolyGrade K (Option σ)) := by
  have h : ((projectiveShiftHom (fun i => -c i)).comp
      (projectiveShiftHom c)).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      cases i <;> simp [shiftedVariable]
  exact GradedRingHom.ext (RingHom.congr_fun h)

lemma projectiveShiftHom_surjective (c : σ → K) :
    Function.Surjective (projectiveShiftHom c) := by
  intro p
  refine ⟨projectiveShiftHom (fun i => -c i) p, ?_⟩
  have h := projectiveShiftHom_inverse (fun i => -c i)
  simp only [neg_neg] at h
  exact DFunLike.congr_fun h p

lemma shift_irrelevant (c : σ → K) :
    (PolyGrade K (Option σ))₊ ≤
      (PolyGrade K (Option σ))₊.map (projectiveShiftHom c) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro d hd b hb
  have eqb : projectiveShiftHom c (projectiveShiftHom (fun i => -c i) b) = b := by
    have hh := projectiveShiftHom_inverse (fun i => -c i)
    simp only [neg_neg] at hh
    exact DFunLike.congr_fun hh b
  rw [← eqb]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hd ((projectiveShiftHom _).map_mem hb))

def projectiveShift (c : σ → K) :
    Proj (PolyGrade K (Option σ)) ≅ Proj (PolyGrade K (Option σ)) where
  hom := Proj.map (projectiveShiftHom c) (shift_irrelevant c)
  inv := Proj.map (projectiveShiftHom (fun i => -c i)) (shift_irrelevant _)
  hom_inv_id := by
    rw [← Proj.map_comp]
    have hh := projectiveShiftHom_inverse (fun i => -c i)
    simp only [neg_neg] at hh
    simpa only [hh] using (Proj.map_id (𝒜 := PolyGrade K (Option σ)))
  inv_hom_id := by
    rw [← Proj.map_comp]
    simpa only [projectiveShiftHom_inverse] using
      (Proj.map_id (𝒜 := PolyGrade K (Option σ)))

end
end MaximalSeshadri.Projective

end


end
end

end OAI
