import OAI.MeasureTheory.Falconer.Estimates.OrderedLeibniz
import OAI.MeasureTheory.Falconer.Angular.InheritedCircleRegularity
import OAI.MeasureTheory.Falconer.Shells.HighShellNormalization

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem normalizedMaskFactor_extract {w : ℝ → ℝ} {d : ℝ} (hd : d ≠ 0)
    (k : ℕ) (θ : ℝ) :
    (d⁻¹)^k * normalizedMaskFactor w d k θ = iteratedDeriv k w θ := by
  unfold normalizedMaskFactor
  rw [← mul_assoc,← mul_pow,inv_mul_cancel₀ hd,one_pow,one_mul]

theorem assignedDerivProduct_normalized {ι : Type*} (S : Finset ι)
    (w : ι → ℝ → ℝ) (d : ι → ℝ) (k : ι → ℕ)
    (hw : ∀ i ∈ S, ContDiff ℝ ∞ (w i)) (hd : ∀ i ∈ S, d i ≠ 0) (θ : ℝ) :
    assignedDerivProduct S (fun i t => (w i t : ℂ)) k θ =
      ((∏ i ∈ S, (d i)⁻¹^(k i) : ℝ):ℂ) *
        ((∏ i ∈ S, normalizedMaskFactor (w i) (d i) (k i) θ : ℝ):ℂ) := by
  simp only [assignedDerivProduct,← Complex.ofReal_mul,← Finset.prod_mul_distrib,Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [normalizedMaskFactor_extract (hd i hi),iteratedDeriv_ofReal (hw i hi)]

 theorem actual_assignment_normalized {ι : Type*} (S : Finset ι)
    (b : ι → PolicyDescriptor) (k : ι → ℕ) (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (x : ι → Plane) (θ : ℝ) :
    assignedDerivProduct S
      (fun a t => (descriptorAngleMask Q ρ m N lam sig J i (b a) (x a) t : ℂ)) k θ =
      ((∏ a ∈ S, (sourceAngularRadius N sig (descriptorLength (b a)))⁻¹^(k a) : ℝ):ℂ) *
        (inheritedMaskProduct S b k Q ρ m N lam sig J i x θ : ℂ) := by
  exact assignedDerivProduct_normalized S _ _ k
    (fun a _ => descriptorAngleMask_contDiff Q hQ ρ m N lam sig J i (b a) (x a))
    (fun a _ => (sourceAngularRadius_pos _ _ _).ne') θ

end PlanarFalconer

end OAI
