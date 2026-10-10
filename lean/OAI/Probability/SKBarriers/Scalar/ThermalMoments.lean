import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.FinitePartition

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
section ThermalMoments
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

def affineGibbs (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) (s : S) : ℝ :=
  Real.exp (c s+L s x)/(∑ t, Real.exp (c t+L t x))

def affineMoment (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (g : S → ℝ) (x : E) : ℝ :=
  ∑ s, affineGibbs c L x s*g s

theorem affinePartition_pos (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) :
    0 < ∑ s, Real.exp (c s+L s x) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem affineGibbs_pos (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) (s : S) :
    0 < affineGibbs c L x s := div_pos (Real.exp_pos _) (affinePartition_pos c L x)

theorem affineGibbs_sum (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) :
    ∑ s, affineGibbs c L x s = 1 := by
  simp only [affineGibbs,← Finset.sum_div]
  exact div_self (affinePartition_pos c L x).ne'

theorem affineMoment_continuous (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (g : S → ℝ) :
    Continuous (affineMoment c L g) := by
  apply continuous_finsetSum
  intro s _
  apply Continuous.mul _ continuous_const
  exact (Real.continuous_exp.comp (continuous_const.add (L s).continuous)).div
    (continuous_finsetSum _ (fun i _ => Real.continuous_exp.comp (continuous_const.add (L i).continuous)))
    (fun x => (affinePartition_pos c L x).ne')

theorem affineMoment_norm_le (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (g : S → ℝ)
    {C : ℝ} (hC : ∀ s, ‖g s‖ ≤ C) (x : E) : ‖affineMoment c L g x‖ ≤ C := by
  calc
    ‖affineMoment c L g x‖ ≤ ∑ s, ‖affineGibbs c L x s*g s‖ := norm_sum_le _ _
    _ = ∑ s, affineGibbs c L x s*‖g s‖ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [norm_mul,Real.norm_eq_abs,abs_of_pos (affineGibbs_pos c L x s)]
    _ ≤ ∑ s, affineGibbs c L x s*C :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hC s) (affineGibbs_pos c L x s).le)
    _ = C := by rw [← Finset.sum_mul,affineGibbs_sum,one_mul]

theorem affineMoment_variance_nonneg (c : S → ℝ) (L : S → E →L[ℝ] ℝ)
    (g : S → ℝ) (x : E) : 0 ≤ affineMoment c L (fun s => (g s)^2) x-(affineMoment c L g x)^2 := by
  let a := affineMoment c L g x
  have H : 0 ≤ ∑ s, affineGibbs c L x s*(g s-a)^2 :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (affineGibbs_pos c L x s).le (sq_nonneg _))
  have he : (∑ s, affineGibbs c L x s*(g s-a)^2) =
      affineMoment c L (fun s => (g s)^2) x-a^2 := by
    simp only [sub_sq]
    simp_rw [mul_add,mul_sub]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    have h₁ : (∑ s, affineGibbs c L x s*(2*g s*a)) = 2*a*a := by
      calc
        _ = (∑ s, affineGibbs c L x s*g s)*(2*a) := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro s _; ring
        _ = _ := by change a*(2*a) = _; ring
    have h₂ : (∑ s, affineGibbs c L x s*a^2) = a^2 := by
      rw [← Finset.sum_mul,affineGibbs_sum,one_mul]
    rw [h₁,h₂]
    dsimp only [affineMoment]
    ring
  rwa [he] at H

theorem fderiv_affineLogPartition_apply (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x u : E) :
    fderiv ℝ (affineLogPartition c L) x u = affineMoment c L (fun s => L s u) x := by
  classical
  let Z : E → ℝ := fun x => ∑ s, Real.exp (c s+L s x)
  have hz (x : E) : HasFDerivAt Z (∑ s, Real.exp (c s+L s x) • L s) x := by
    apply HasFDerivAt.fun_sum
    intro s _
    simpa only [zero_add] using ((hasFDerivAt_const (c s) x).fun_add (L s).hasFDerivAt).exp
  have hp : Z x ≠ 0 := (affinePartition_pos c L x).ne'
  change fderiv ℝ (fun y => Real.log (Z y)) x u = _
  rw [(hz x |>.log hp).fderiv]
  simp only [smul_apply,smul_eq_mul,sum_apply,affineMoment,affineGibbs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  change (Z x)⁻¹*(Real.exp (c s+L s x)*L s u) = Real.exp (c s+L s x)/(Z x)*L s u
  ring

theorem fderiv_fderiv_affineLogPartition_apply (c : S → ℝ) (L : S → E →L[ℝ] ℝ)
    (x u v : E) : fderiv ℝ (fderiv ℝ (affineLogPartition c L)) x u v =
      affineMoment c L (fun s => L s u*L s v) x -
      affineMoment c L (fun s => L s u) x*affineMoment c L (fun s => L s v) x := by
  classical
  let Z : E → ℝ := fun x => ∑ s, Real.exp (c s+L s x)
  let Z₁ : E → E →L[ℝ] ℝ := fun x => ∑ s, Real.exp (c s+L s x) • L s
  let Z₂ : E → E →L[ℝ] E →L[ℝ] ℝ := fun x =>
    ∑ s, (Real.exp (c s+L s x) • L s).smulRight (L s)
  have hd (s : S) (x : E) : HasFDerivAt (fun x => c s+L s x) (L s) x := by
    simpa only [zero_add] using (hasFDerivAt_const (c s) x).fun_add (L s).hasFDerivAt
  have hz₁ (x : E) : HasFDerivAt Z (Z₁ x) x :=
    HasFDerivAt.fun_sum (fun s _ => (hd s x).exp)
  have hz₂ (x : E) : HasFDerivAt Z₁ (Z₂ x) x :=
    HasFDerivAt.fun_sum (fun s _ => (hd s x).exp.smul_const (L s))
  have he : fderiv ℝ Z = Z₁ := funext (fun x => (hz₁ x).fderiv)
  have he₂ : fderiv ℝ (fderiv ℝ Z) = Z₂ := by
    rw [he]
    exact funext (fun x => (hz₂ x).fderiv)
  have hc : ContDiff ℝ 2 Z := by
    apply ContDiff.sum
    intro s _
    exact (contDiff_const.add (L s).contDiff).exp
  have hp (x : E) : Z x ≠ 0 := (affinePartition_pos c L x).ne'
  change fderiv ℝ (fderiv ℝ (fun x => Real.log (Z x))) x u v = _
  rw [fderiv_fderiv_log Z hc hp,he₂,he]
  simp only [Z₁,Z₂,smul_apply,smul_eq_mul,sum_apply,add_apply,ContinuousLinearMap.smulRight_apply,
    affineMoment,affineGibbs]
  have ha (g : S → ℝ) : (∑ s, Real.exp (c s+L s x)/(Z x)*g s) =
      (Z x)⁻¹*∑ s, Real.exp (c s+L s x)*g s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp_rw [show (∑ t, Real.exp (c t+L t x)) = Z x from rfl,ha]
  rw [Finset.mul_sum]
  have hs : (∑ s, (Z x)⁻¹*(Real.exp (c s+L s x)*L s u*L s v)) =
      (Z x)⁻¹*∑ s, Real.exp (c s+L s x)*(L s u*L s v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hs]
  field_simp [hp x]
  ring

end ThermalMoments
end SK.Analytic

end
end
end
end
end
end
end

end OAI
