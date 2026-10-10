import Mathlib
import OAI.Analysis.Commutator.CyclicMatrix

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra

namespace Kadison.Stinespring

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem gram_nonneg (φ : A →CP (H →L[ℂ] H)) {ι : Type*} [Fintype ι]
    (a : ι → A) (ξ : ι → H) :
    0 ≤ ∑ i, ∑ j, ⟪ξ i, φ (star (a i)*a j) (ξ j)⟫_ℂ := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => simp
  | inr h =>
    let i₀ : ι := Classical.choice h
    let R : CStarMatrix ι ι A := CStarMatrix.ofMatrix (fun i j => if i=i₀ then a j else 0)
    have he (i j : ι) : (star R*R) i j=star (a i)*a j := by
      rw [CStarMatrix.mul_apply]
      change (∑ k, star (if k=i₀ then a i else 0)*(if k=i₀ then a j else 0))=_
      simp
    have hp := φ.map_cstarMatrix_nonneg (star R*R) (star_mul_self_nonneg R)
    have hq := map_nonneg
      (CyclicColumns.matrixRepresentation (StarAlgHom.id ℂ (H →L[ℂ] H))) hp
    have hr := ContinuousLinearMap.nonneg_iff_isPositive.mp hq
    let v : PiLp 2 (fun _ : ι => H) := WithLp.toLp 2 ξ
    have hs := hr.inner_nonneg_right v
    change 0 ≤ ⟪v, CyclicColumns.matrixAction
      (fun i j => φ ((star R*R) i j)) v⟫_ℂ at hs
    simpa [PiLp.inner_apply,CyclicColumns.matrixAction_apply,inner_sum,he,v] using hs

def PreSpace (_φ : A →CP (H →L[ℂ] H)) := A →₀ H

instance (φ : A →CP (H →L[ℂ] H)) : AddCommGroup (PreSpace φ) :=
  inferInstanceAs (AddCommGroup (A →₀ H))

instance (φ : A →CP (H →L[ℂ] H)) : Module ℂ (PreSpace φ) :=
  inferInstanceAs (Module ℂ (A →₀ H))

def toPre (φ : A →CP (H →L[ℂ] H)) : (A →₀ H) ≃ₗ[ℂ] PreSpace φ := LinearEquiv.refl ℂ _

def ofPre (φ : A →CP (H →L[ℂ] H)) : PreSpace φ ≃ₗ[ℂ] (A →₀ H) := (toPre φ).symm

@[simp] lemma ofPre_toPre (φ : A →CP (H →L[ℂ] H)) (x : A →₀ H) :
    ofPre φ (toPre φ x)=x := rfl

@[simp] lemma toPre_ofPre (φ : A →CP (H →L[ℂ] H)) (x : PreSpace φ) :
    toPre φ (ofPre φ x)=x := rfl

def form (φ : A →CP (H →L[ℂ] H)) (x y : PreSpace φ) : ℂ :=
  (ofPre φ x).sum (fun a ξ => (ofPre φ y).sum (fun b η => ⟪ξ,φ (star a*b) η⟫_ℂ))

lemma form_conj (φ : A →CP (H →L[ℂ] H)) (x y : PreSpace φ) :
    star (form φ x y)=form φ y x := by
  classical
  change (starRingEnd ℂ) (form φ x y)=_
  simp only [form,Finsupp.sum,map_sum,inner_conj_symm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [←ContinuousLinearMap.adjoint_inner_left]
  simp [←ContinuousLinearMap.star_eq_adjoint,←map_star,star_mul]

lemma form_add_left (φ : A →CP (H →L[ℂ] H)) (x y z : PreSpace φ) :
    form φ (x+y) z=form φ x z+form φ y z := by
  classical
  unfold form
  rw [map_add]
  exact Finsupp.sum_add_index' (by simp [Finsupp.sum])
    (by intros; simp [Finsupp.sum,Finset.sum_add_distrib])

lemma form_smul_left (φ : A →CP (H →L[ℂ] H)) (c : ℂ) (x y : PreSpace φ) :
    form φ (c • x) y=star c*form φ x y := by
  classical
  unfold form
  rw [map_smul,Finsupp.sum_smul_index']
  · simp [Finsupp.sum,Finset.mul_sum,mul_comm]
  · simp [Finsupp.sum]

lemma form_nonneg (φ : A →CP (H →L[ℂ] H)) (x : PreSpace φ) :
    0 ≤ form φ x x := by
  classical
  have h := gram_nonneg φ (fun i : (ofPre φ x).support => (i : A))
    (fun i : (ofPre φ x).support => (ofPre φ x) i)
  have hi (a : A) : (∑ j : (ofPre φ x).support,
      ⟪ofPre φ x a,φ (star a*(j : A)) (ofPre φ x j)⟫_ℂ)=
      ∑ b ∈ (ofPre φ x).support,⟪ofPre φ x a,φ (star a*b) (ofPre φ x b)⟫_ℂ :=
    Finset.sum_coe_sort _ (fun b : A => ⟪ofPre φ x a,φ (star a*b) (ofPre φ x b)⟫_ℂ)
  simp_rw [hi] at h
  rw [Finset.sum_coe_sort _ (fun a : A => ∑ b ∈ (ofPre φ x).support,
    ⟪ofPre φ x a,φ (star a*b) (ofPre φ x b)⟫_ℂ)] at h
  exact h

abbrev preInner (φ : A →CP (H →L[ℂ] H)) : PreInnerProductSpace.Core ℂ (PreSpace φ) where
  inner := form φ
  conj_inner_symm x y := form_conj φ y x
  re_inner_nonneg x := (form_nonneg φ x).1
  add_left := form_add_left φ
  smul_left x y r := form_smul_left φ r x y

instance (φ : A →CP (H →L[ℂ] H)) : SeminormedAddCommGroup (PreSpace φ) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c:=preInner φ)

instance (φ : A →CP (H →L[ℂ] H)) : InnerProductSpace ℂ (PreSpace φ) :=
  InnerProductSpace.ofCore (preInner φ)

@[simp] lemma inner_def (φ : A →CP (H →L[ℂ] H)) (x y : PreSpace φ) :
    ⟪x,y⟫_ℂ=form φ x y := rfl

abbrev Space (φ : A →CP (H →L[ℂ] H)) := UniformSpace.Completion (PreSpace φ)

end Kadison.Stinespring

end

end
end

end OAI
