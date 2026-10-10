import Mathlib
import OAI.Geometry.PrescribedPotential.JetDissipation
import OAI.Geometry.PrescribedPotential.JetEnergyCoercivity
import OAI.Geometry.PrescribedPotential.RealFrameScalar

namespace OAI

/-! Jet Energy Uniform. -/

section

 

noncomputable section
open Set Filter Topology Finset Module
open scoped ContDiff
namespace HigherJet
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι]

lemma jetEnergy_le_norm {U : Set E} (hU : IsOpen U) {u : E → F}
    (hu : ContDiffOn ℝ ∞ u U) (e : OrthonormalBasis ι ℝ E) (m : ℕ) {x : E} (hx : x ∈ U) :
    jetEnergy e m u x ≤ (Fintype.card (Fin m → ι) : ℝ)*‖iteratedFDeriv ℝ m u x‖^2 := by
  calc
    _ ≤ ∑ _σ : Fin m → ι, ‖iteratedFDeriv ℝ m u x‖^2 := by
      apply Finset.sum_le_sum
      intro σ _
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [jetFamily,e.norm_eq_one,Finset.prod_const_one,mul_one] using norm_word_ofFn_le hU hu m (fun i => e (σ i)) hx
    _ = _ := by simp

lemma jetEnergy_gradient_bound {U : Set E} (hU : IsOpen U) {u : E → F}
    (hu : ContDiffOn ℝ ∞ u U) (e : ι → E) (m : ℕ) {x : E} (hx : x ∈ U) (v : ι → E) :
    ‖frameGradient v (jetEnergy e m u) x‖^2 ≤
      4*jetEnergy e m u x*familyDissipation v (jetFamily e m u) x := by
  rw [norm_frameGradient_sq]
  exact familyEnergy_gradient_bound hU (jetFamily_smoothOn hU hu e m) hx v

lemma familyDissipation_nonneg (v : ι → E) {κ : Type*} [Fintype κ] (f : κ → E → F) (x : E) :
    0 ≤ familyDissipation v f x := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
lemma jetEnergy_frame_upper (e : OrthonormalBasis ι ℝ E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (u : E → F) (x : E) (τ : E ≃L[ℝ] E) (B : ℝ),
      0 ≤ B → ‖τ.toContinuousLinearMap‖ ≤ B →
      familyDissipation (fun i => τ (e i)) (jetFamily e m u) x ≤ C*B^2*jetEnergy e (m+1) u x := by
  obtain ⟨A,hA,hb⟩ := linearArray_norm_control (F := F) e.toBasis
  refine ⟨(Fintype.card ι+1)*A^2,by positivity,fun m u x τ B hB hτ => ?_⟩
  rw [jetEnergy_succ]
  unfold familyDissipation frameGradientSq dir
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro σ _
  let T := fderiv ℝ (jetFamily e m u σ) x
  have ht : ‖T‖^2 ≤ A^2*(∑ i, ‖T (e i)‖^2) := by
    have hh := pow_le_pow_left₀ (norm_nonneg T) (hb T) 2
    rw [mul_pow,PiLp.norm_sq_eq_of_L2] at hh
    exact hh
  calc
    _ ≤ ∑ _i : ι, (‖T‖*B)^2 := by
      apply sum_le_sum
      intro i _
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((τ.toContinuousLinearMap.le_opNorm (e i)).trans (by simpa only [e.norm_eq_one,mul_one] using hτ)) (norm_nonneg _))
    _ = (Fintype.card ι : ℝ)*(‖T‖*B)^2 := by simp
    _ ≤ ((Fintype.card ι : ℝ)+1)*A^2*B^2*(∑ i, ‖T (e i)‖^2) := by
      have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (sq_nonneg B)) (show 0 ≤ (Fintype.card ι : ℝ) by positivity)
      have h2 : 0 ≤ A^2*B^2*(∑ i, ‖T (e i)‖^2) := by positivity
      nlinarith only [h1,h2]

end HigherJet
namespace BernsteinEstimate
lemma first_energy_scaled {S D A R W L : ℝ} (_hS : 0 ≤ S) (hD : 0 ≤ D)
    (hA : 1 ≤ A) (hR : 0 ≤ R) (hSbound : Real.sqrt S ≤ A)
    (hW : W ≤ R*(1+A*Real.sqrt D)) (hL : 2*D-2*Real.sqrt S*W ≤ L) :
    D-(2*(A+R*A)^2+(A+R*A)^4) ≤ L := by
  have hc : 0 ≤ A+R*A := by positivity
  have hr : R*(1+A*Real.sqrt D) ≤ (A+R*A)*(1+Real.sqrt D) := by
    nlinarith only [hA,mul_nonneg hR (by linarith : 0 ≤ A-1),mul_nonneg (show 0 ≤ A by linarith) (Real.sqrt_nonneg D)]
  have hh := energy_first_numeric (Real.sqrt_nonneg S) (Real.sqrt_nonneg D) hc
    (hSbound.trans (le_add_of_nonneg_right (mul_nonneg hR (by linarith)))) (hW.trans hr)
    (by simpa only [Real.sq_sqrt hD] using hL)
  simpa only [Real.sq_sqrt hD] using hh

lemma cubic_energy_scaled {S D A R W L : ℝ} (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hA : 1 ≤ A) (hR : 0 ≤ R)
    (hW : W ≤ R*(1+A^2*S+A*Real.sqrt D)) (hL : 2*D-2*Real.sqrt S*W ≤ L) :
    D-(4*(R*A^2)+2*(R*A^2)^2)*(1+S*Real.sqrt S) ≤ L := by
  have hA0 : 0 ≤ A := by linarith
  have hAA : A ≤ A^2 := by nlinarith
  have hW' : W ≤ R*A^2*(1+(Real.sqrt S)^2+Real.sqrt D) := by
    rw [Real.sq_sqrt hS]
    have hh : 1+A^2*S+A*Real.sqrt D ≤ A^2*(1+S+Real.sqrt D) := by
      nlinarith only [hAA,hA,mul_nonneg (by linarith : 0 ≤ A^2-A) (Real.sqrt_nonneg D)]
    exact hW.trans ((mul_le_mul_of_nonneg_left hh hR).trans_eq (by ring))
  have hh := energy_cubic_numeric (Real.sqrt_nonneg S) (Real.sqrt_nonneg D)
    (show 0 ≤ R*A^2 by positivity) hW' (by simpa only [Real.sq_sqrt hD] using hL)
  have he : (Real.sqrt S)^3 = S*Real.sqrt S := by rw [pow_succ,Real.sq_sqrt hS]
  simpa only [Real.sq_sqrt hD,he] using hh

lemma linear_energy_scaled {S D A R W L : ℝ} (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hA : 1 ≤ A) (hR : 0 ≤ R)
    (hW : W ≤ R*(1+A*Real.sqrt S+A*Real.sqrt D)) (hL : 2*D-2*Real.sqrt S*W ≤ L) :
    D-(4*(R*A)+(R*A)^2)*(1+S) ≤ L := by
  have hW' : W ≤ R*A*(1+Real.sqrt S+Real.sqrt D) := by
    apply hW.trans
    nlinarith only [mul_nonneg hR (by linarith : 0 ≤ A-1)]
  have hh := energy_linear_numeric (Real.sqrt_nonneg S) (Real.sqrt_nonneg D)
    (show 0 ≤ R*A by positivity) hW' (by simpa only [Real.sq_sqrt hD] using hL)
  simpa only [Real.sq_sqrt hD,Real.sq_sqrt hS] using hh
end BernsteinEstimate

end
end

end OAI
