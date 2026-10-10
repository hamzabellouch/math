import OAI.Analysis.AncientFlat.Regularity.InterpolationAlgebra

namespace OAI
noncomputable section
open Set Filter Metric
open scoped ContDiff
namespace ParabolicInterpolation
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
lemma next_jet_bound (j : ℕ) (hj : j≤3) (f : V → E) (hf : ContDiff ℝ 4 f)
    (x : V) (R q U M : ℝ) (hq : 0<q) (hU : 0≤U) (hM : 0≤M)
    (hx : ‖x‖+6*q<R) (hu : ∀ y, ‖y‖<R → ‖f y‖≤U)
    (hD : ∀ y, ‖y‖<R → ‖iteratedFDeriv ℝ 4 f y‖≤M) :
    ‖iteratedFDeriv ℝ (j+1) f x‖≤22*(U/q^j+q^(4-j)*M)/q := by
  by_cases hj2 : j≤2
  · have hb := lower_jet_bound (j+1) (by omega) f hf x R q U M hq hU hM hx hu hD
    convert hb using 1
    rw [show 4-j=(3-j)+1 by omega,show 4-(j+1)=3-j by omega,pow_succ,pow_succ]
    field_simp
  · have hj3 : j=3 := by omega
    subst j
    norm_num only [Nat.reduceAdd,Nat.reduceSub,pow_one]
    have hb := hD x (by linarith)
    have hq' : 0≤U/q^3 := by positivity
    calc
      _≤M := hb
      _≤22*(U/q^3+q*M)/q := by
        apply (le_div_iff₀ hq).mpr
        nlinarith [mul_nonneg hq.le hM]
lemma space_lower_holder (j : ℕ) (hj : j≤3) (f : V → E) (hf : ContDiff ℝ 4 f)
    (x y : V) (R q U M α : ℝ) (hq : 0<q) (hU : 0≤U) (hM : 0≤M)
    (hα : 0≤α) (hα1 : α≤1) (hx : ‖x‖+12*q<R) (hy : ‖y‖+12*q<R)
    (hu : ∀ z, ‖z‖<R → ‖f z‖≤U)
    (hD : ∀ z, ‖z‖<R → ‖iteratedFDeriv ℝ 4 f z‖≤M) :
    ‖iteratedFDeriv ℝ j f x-iteratedFDeriv ℝ j f y‖≤
      44*(U/q^j+q^(4-j)*M)/q^α*‖x-y‖^α := by
  let B := 22*(U/q^j+q^(4-j)*M)
  have hB : 0≤B := by dsimp [B]; positivity
  have hbx := lower_jet_bound j hj f hf x R q U M hq hU hM (by linarith) hu hD
  have hby := lower_jet_bound j hj f hf y R q U M hq hU hM (by linarith) hu hD
  have hb : ‖iteratedFDeriv ℝ j f x-iteratedFDeriv ℝ j f y‖≤2*B :=
    (norm_sub_le _ _).trans (by dsimp [B]; linarith)
  have hl : ‖iteratedFDeriv ℝ j f x-iteratedFDeriv ℝ j f y‖≤B/q*‖x-y‖ := by
    apply jet_lipschitz_ball j f (hf.of_le (by exact_mod_cast (show j+1≤4 by omega))) (R-6*q) (B/q)
    · intro z hz
      exact next_jet_bound j hj f hf z R q U M hq hU hM (by linarith) hu hD
    · linarith
    · linarith
  have hh := le_scaled_holder_of_two_bounds _ B ‖x-y‖ q α hB (norm_nonneg _) hq hα hα1 hb hl
  convert hh using 1
  dsimp [B]
  ring
end ParabolicInterpolation

end

end OAI
