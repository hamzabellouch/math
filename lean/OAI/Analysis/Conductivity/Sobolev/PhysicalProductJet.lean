import Mathlib
import OAI.Analysis.Conductivity.Branching.ChildTransportFormula

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def piSmoothJet (q : (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) : JetFiber :=
  WithLp.toLp 2 (Fin.cases (q y) (fun j => fderiv ℝ q y (Pi.single j 1)))

lemma localJoinedJet_eq_piSmoothJet {τ χ q p : (Fin 3 → ℝ) → ℝ} {y : Fin 3 → ℝ}
    (hτ : τ y ≤ 0) (hχ : DifferentiableAt ℝ χ y) (hq : DifferentiableAt ℝ q y) :
    WithLp.toLp 2 (Fin.cases (localJoinedValue τ χ q p y)
      (fun i => localJoinedGradient τ χ q p i y))=piSmoothJet (χ*q) y := by
  have hn : ¬0<τ y := not_lt_of_ge hτ
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [localJoinedValue,piSmoothJet,hn]
  · simp only [localJoinedGradient,hn,ite_false,PiLp.toLp_apply,Fin.cases_succ,
      piSmoothJet,fderiv_mul hχ hq,add_apply,smul_apply,
      smul_eq_mul,Pi.mul_apply]
    ring

lemma sourceChild_piSmoothJet_cancel (q : (Fin 3 → ℝ) → ℝ)
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (σ : ℝ) (y : Fin 3 → ℝ) :
    WithLp.toLp 2 (Fin.cases
      (piSmoothJet (q ∘ sourceChildCoordinates σ) ((sourceChildHomeomorph σ).symm y) 0)
      (fun j => sourceScale⁻¹*piSmoothJet (q ∘ sourceChildCoordinates σ)
        ((sourceChildHomeomorph σ).symm y) (childAxis j).succ))=piSmoothJet q y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change q ((sourceChildHomeomorph σ) ((sourceChildHomeomorph σ).symm y))=q y
    rw [Homeomorph.apply_symm_apply]
  · exact physical_child_partial_cancel hq σ y j

lemma piSmoothJet_partition {ρ : Fin 4 → (Fin 3 → ℝ) → ℝ}
    (hρ : ∀ i,ContDiff ℝ (↑(⊤:ℕ∞)) (ρ i)) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (y : Fin 3 → ℝ)
    (hv : ∑ i : Fin 4,ρ i y=1)
    (hg : ∀ j : Fin 3,∑ i : Fin 4,fderiv ℝ (ρ i) y (Pi.single j 1)=0) :
    ∑ i : Fin 4,piSmoothJet (ρ i*q) y=piSmoothJet q y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (∑ i : Fin 4,piSmoothJet (ρ i*q) y) 0=q y
    simp only [WithLp.ofLp_sum,Finset.sum_apply,piSmoothJet,Fin.cases_zero,Pi.mul_apply]
    rw [←Finset.sum_mul,hv,one_mul]
  · change (∑ i : Fin 4,piSmoothJet (ρ i*q) y) j.succ=fderiv ℝ q y (Pi.single j 1)
    simp only [WithLp.ofLp_sum,Finset.sum_apply,piSmoothJet,Fin.cases_succ,
      fderiv_mul ((hρ _).differentiable (by simp) y) (hq.differentiable (by simp) y),
      add_apply,smul_apply,smul_eq_mul,
      Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,hv,hg,one_mul,mul_zero,add_zero]

end ScalarConductivity

end

end OAI
