import OAI.Geometry.NodalSets.Charts.PiolaFour
import OAI.Geometry.NodalSets.Elliptic.JacobianCalculus

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

def complexDivergence (V : Fin 4 → Coord → ℂ) (x : Coord) : ℂ :=
  ∑ i, coordPartial i (V i) x

def signedPiola (F : Coord → Coord) (V : Fin 4 → Coord → ℂ)
    (i : Fin 4) (x : Coord) : ℂ :=
  ∑ a, ((jacobian F x).adjugate i a : ℂ) * V a (F x)

lemma adjugate_divergence_complex (F : Coord → Coord) (hF : ContDiff ℝ ∞ F)
    (x : Coord) (a : Fin 4) :
    ∑ i, coordPartial i (fun z ↦ ((jacobian F z).adjugate i a : ℂ)) x = 0 := by
  simp_rw [coordPartial_ofReal_at _ x
    ((adjugate_entry_smooth F hF _ _).differentiable (by simp) x)]
  rw [← Complex.ofReal_sum, adjugate_divergence_four (jacobian F) x
    (fun i j ↦ (jacobian_smooth F hF i j).differentiable (by simp) x)
    (jacobian_closed F hF x)]
  rfl

lemma jacobian_mul_adjugate_complex (F : Coord → Coord) (x : Coord) (a b : Fin 4) :
    ∑ i, ((jacobian F x).adjugate i a : ℂ) * (jacobian F x b i : ℂ) =
      if b=a then ((jacobian F x).det : ℂ) else 0 := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ ↦ M b a)
    (Matrix.mul_adjugate (jacobian F x))
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
  have hh := congrArg Complex.ofReal h
  push_cast at hh
  split_ifs with hba <;> simp [hba,mul_comm] at hh ⊢ <;> exact hh

theorem signedPiola_divergence (F : Coord → Coord) (hF : ContDiff ℝ ∞ F)
    (V : Fin 4 → Coord → ℂ) (x : Coord)
    (hV : ∀ a, DifferentiableAt ℝ (V a) (F x)) :
    complexDivergence (signedPiola F V) x =
      ((jacobian F x).det : ℂ) * complexDivergence V (F x) := by
  have hFc (i a : Fin 4) : DifferentiableAt ℝ
      (fun z ↦ ((jacobian F z).adjugate i a : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((adjugate_entry_smooth F hF i a).differentiable (by simp) x)
  have hVc (a : Fin 4) : DifferentiableAt ℝ (V a ∘ F) x :=
    (hV a).comp x (hF.differentiable (by simp) x)
  have hsum (i : Fin 4) : coordPartial i (signedPiola F V i) x =
      ∑ a, coordPartial i (fun z ↦ ((jacobian F z).adjugate i a : ℂ) * V a (F z)) x :=
    coordPartial_sum_at _ x (fun a ↦ (hFc i a).mul (hVc a)) i
  have hprod (i a : Fin 4) := coordPartial_mul_at
    (fun z ↦ ((jacobian F z).adjugate i a : ℂ)) (fun z ↦ V a (F z)) x (hFc i a) (hVc a) i
  unfold complexDivergence
  simp_rw [hsum,hprod]
  simp only [Finset.sum_add_distrib]
  have hz : (∑ i, ∑ a, coordPartial i (fun z ↦ ((jacobian F z).adjugate i a : ℂ)) x *
      V a (F x)) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, adjugate_divergence_complex F hF x]
    simp
  rw [hz, zero_add]
  have hc (a i : Fin 4) := coordPartial_comp F x
    (hF.differentiable (by simp) x) (V a) (hV a) i
  simp only [Function.comp_def] at hc
  simp_rw [hc]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans _ (by rfl)
  calc
    _ = ∑ a, ∑ b, (∑ i, ((jacobian F x).adjugate i a : ℂ) *
        (jacobian F x b i : ℂ)) * coordPartial b (V a) (F x) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul, mul_assoc]
    _ = _ := by
      simp_rw [jacobian_mul_adjugate_complex]
      simp

end
end Yau.Geometry

end OAI
