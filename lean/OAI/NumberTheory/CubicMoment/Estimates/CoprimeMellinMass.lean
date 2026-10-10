import OAI.NumberTheory.CubicMoment.Estimates.GramMellinTwist

namespace OAI

/-! The divisor expansion of the actual radial kernel is bounded by its
literal character-row masses. This keeps the oscillation that is lost in
the coarse operator norm bound. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finite_bilinear_mass_bound {α : Type*} (H : Finset α)
    (v w phase : α → ℂ) (hp : ∀ h ∈ H, ‖phase h‖ ≤ 1) :
    ‖∑ h ∈ H, phase h*v h*star (w h)‖ ≤
      ((∑ h ∈ H, ‖v h‖^2)+(∑ h ∈ H, ‖w h‖^2))/2 := by
  apply (norm_sum_le _ _).trans
  rw [← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_le_sum
  intro h hh
  rw [norm_mul,norm_mul,norm_star]
  calc
    _ ≤ ‖v h‖*‖w h‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (_root_.norm_nonneg _) (hp h hh)) (_root_.norm_nonneg _)
    _ ≤ _ := by nlinarith [sq_nonneg (‖v h‖-‖w h‖)]

def coprimeMellinMass (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) (t : ℝ) : ℝ :=
  ∑ s ∈ U.powerset,
    ((∑ h ∈ H, ‖∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a),
      v a*star (gramMellinPhase t (y a))*star (cubicSymbol a h)‖^2)+
     (∑ h ∈ H, ‖∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a),
      w a*gramMellinPhase t (y a)*star (cubicSymbol a h)‖^2))/2

theorem norm_coprimeMellinKernel_le_mass (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1)
    (x y : Eisenstein → ℝ) (t : ℝ) :
    ‖coprimeMellinKernel S H v w phase x y t‖ ≤ coprimeMellinMass S H U v w y t := by
  let V (s : Finset Eisenstein) (h : Eisenstein) : ℂ :=
    ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a),
      v a*star (gramMellinPhase t (y a))*star (cubicSymbol a h)
  let W (s : Finset Eisenstein) (h : Eisenstein) : ℂ :=
    ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a),
      w a*gramMellinPhase t (y a)*star (cubicSymbol a h)
  have he (h : Eisenstein) := coprime_bilinear_moebius S S U hS hU hSU
    (fun a => v a*star (gramMellinPhase t (y a))*star (cubicSymbol a h))
    (fun a => w a*gramMellinPhase t (y a)*star (cubicSymbol a h))
  have he' (h : Eisenstein) :
      (∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
        (v a*star (gramMellinPhase t (y a))*star (cubicSymbol a h))*
          star (w b*gramMellinPhase t (y b)*star (cubicSymbol b h)) else 0) =
      ∑ s ∈ U.powerset, (idealMoebius (∏ p ∈ s, p):ℂ)*V s h*star (W s h) := by
    simpa only [V,W,Finset.sum_filter] using he h
  unfold coprimeMellinKernel
  simp_rw [he',Finset.mul_sum]
  rw [Finset.sum_comm]
  have hf (s : Finset Eisenstein) :
      (∑ h ∈ H, (phase h*gramMellinPhase t (x h))*
        ((idealMoebius (∏ p ∈ s, p):ℂ)*V s h*star (W s h))) =
      (idealMoebius (∏ p ∈ s, p):ℂ)*
        ∑ h ∈ H, (phase h*gramMellinPhase t (x h))*V s h*star (W s h) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  simp_rw [hf]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  rw [norm_mul]
  apply (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _)).trans
  exact finite_bilinear_mass_bound H (V s) (W s)
    (fun h => phase h*gramMellinPhase t (x h)) (fun h hh => by
      simpa only [norm_mul,norm_gramMellinPhase,mul_one] using hphase h hh)

end CubicFirstMoment

end

end OAI
