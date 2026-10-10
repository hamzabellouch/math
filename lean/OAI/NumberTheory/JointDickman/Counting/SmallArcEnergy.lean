import OAI.NumberTheory.JointDickman.Amplification.RealMajorIntegrals
import OAI.NumberTheory.JointDickman.Counting.IntervalEnergyError

namespace OAI

/-! # Summing local approximation errors without a factor for the arc count -/

namespace JointDickman
open Filter MeasureTheory Function Finset
open scoped Topology

noncomputable def smallArcSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B j : ℕ) [NeZero j] (X : ℝ) (Q : ℕ) (K : (q : ℕ+) → ZMod (j*(q : ℕ)) → ℝ → E) : E :=
  ∑ q ∈ positiveDenominators (B^12), if (q : ℕ) ≤ Q then
    ∑ h : ZMod (j*(q : ℕ)), if h.val.Coprime (q : ℕ) then
      ∫ x in (h.val : ℝ)/(j*(q : ℕ) : ℕ)-(B : ℝ)^13/(j*X)..
        (h.val : ℝ)/(j*(q : ℕ) : ℕ)+(B : ℝ)^13/(j*X), K q h x
    else 0 else 0

theorem smallArcSum_error_bound :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      ∀ j : ℕ, ∀ (_ : NeZero j), ∀ Q : ℕ,
      ∀ F G H : ℝ → ℂ, Continuous F → Continuous G → Continuous H →
      Periodic F 1 → Periodic G 1 → Periodic (fun x => F x*G x*H x) 1 →
      ∀ K : (q : ℕ+) → ZMod (j*(q : ℕ)) → ℝ → ℂ,
      (∀ q h, Continuous (K q h)) → ∀ E : ℝ, 0 ≤ E →
      (∀ q ∈ positiveDenominators (B^12), (q : ℕ) ≤ Q →
        ∀ h : ZMod (j*(q : ℕ)), h.val.Coprime (q : ℕ) →
        ∀ x ∈ Set.Icc ((h.val : ℝ)/(j*(q : ℕ) : ℕ)-(B : ℝ)^13/(j*X))
          ((h.val : ℝ)/(j*(q : ℕ) : ℕ)+(B : ℝ)^13/(j*X)), ‖H x-K q h x‖ ≤ E) →
      ‖(∫ x in smallMajorArcRegion B j X Q, F x*G x*H x)-
        smallArcSum B j X Q (fun q h x => F x*G x*K q h x)‖ ≤
        E/2*((∫ x in (0 : ℝ)..1, ‖F x‖^2)+(∫ x in (0 : ℝ)..1, ‖G x‖^2)) := by
  filter_upwards [smallMajorArc_finite_sum,smallMajorArc_finite_sum_real] with B hsum hreal
  intro X hX hlog j hj Q F G H hF hG hH hpF hpG hp K hK E hE he
  let : NeZero j := hj
  let U : ℝ → ℝ := fun x => E/2*(‖F x‖^2+‖G x‖^2)
  have hU : Continuous U := continuous_const.mul ((hF.norm.pow 2).add (hG.norm.pow 2))
  have hpU : Periodic U 1 := fun x => by dsimp [U]; rw [hpF x,hpG x]
  have hU0 : ∀ x, 0 ≤ U x := fun x => by dsimp [U]; positivity
  have hw : 0 ≤ (B : ℝ)^13/(j*X) := by positivity
  have hlocal (q : ℕ+) (hq : q ∈ positiveDenominators (B^12)) (hqQ : (q : ℕ) ≤ Q)
      (h : ZMod (j*(q : ℕ))) (hh : h.val.Coprime (q : ℕ)) :
      ‖(∫ x in (h.val : ℝ)/(j*(q : ℕ) : ℕ)-(B : ℝ)^13/(j*X)..
          (h.val : ℝ)/(j*(q : ℕ) : ℕ)+(B : ℝ)^13/(j*X), F x*G x*H x)-
        (∫ x in (h.val : ℝ)/(j*(q : ℕ) : ℕ)-(B : ℝ)^13/(j*X)..
          (h.val : ℝ)/(j*(q : ℕ) : ℕ)+(B : ℝ)^13/(j*X), F x*G x*K q h x)‖ ≤
        ∫ x in (h.val : ℝ)/(j*(q : ℕ) : ℕ)-(B : ℝ)^13/(j*X)..
          (h.val : ℝ)/(j*(q : ℕ) : ℕ)+(B : ℝ)^13/(j*X), U x := by
    have hab : (h.val : ℝ)/(j*(q : ℕ) : ℕ)-(B : ℝ)^13/(j*X) ≤
        (h.val : ℝ)/(j*(q : ℕ) : ℕ)+(B : ℝ)^13/(j*X) := by linarith
    have hh' := weighted_interval_energy_error hab hE hF hG hH (hK q h) (he q hq hqQ h hh)
    simpa only [U,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (f := fun x => ‖F x‖^2) (g := fun x => ‖G x‖^2) ((hF.norm.pow 2).intervalIntegrable _ _)
        ((hG.norm.pow 2).intervalIntegrable _ _)] using hh'
  have hs : ‖smallArcSum B j X Q (fun _ _ x => F x*G x*H x)-
      smallArcSum B j X Q (fun q h x => F x*G x*K q h x)‖ ≤
      smallArcSum B j X Q (fun _ _ x => U x) := by
    unfold smallArcSum
    rw [← sum_sub_distrib]
    refine (norm_sum_le _ _).trans (sum_le_sum (fun q hq => ?_))
    by_cases hqQ : (q : ℕ) ≤ Q
    · simp only [ite_eq_left hqQ,← sum_sub_distrib]
      refine (norm_sum_le _ _).trans (sum_le_sum (fun h _ => ?_))
      by_cases hh : h.val.Coprime (q : ℕ)
      · simpa only [ite_eq_left hh] using hlocal q hq hqQ h hh
      · simp [hh]
    · simp [hqQ]
  have hset : smallMajorArcRegion B j X Q ⊆ Set.Ioc 0 1 :=
    (smallMajorArcRegion_subset B j X Q).trans (by intro x hx; exact hx.1)
  have hi : IntegrableOn U (Set.Ioc 0 1) := (hU.intervalIntegrable 0 1).1
  calc
    _ ≤ smallArcSum B j X Q (fun _ _ x => U x) := by
      rw [hsum X hX hlog j hj Q (fun x => F x*G x*H x) ((hF.mul hG).mul hH) hp]
      exact hs
    _ = ∫ x in smallMajorArcRegion B j X Q, U x :=
      (hreal X hX hlog j hj Q U hU hpU).symm
    _ ≤ ∫ x in Set.Ioc 0 1, U x := setIntegral_mono_set hi
      (Filter.Eventually.of_forall hU0) (Filter.Eventually.of_forall hset)
    _ = _ := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      dsimp [U]
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (f := fun x => ‖F x‖^2) (g := fun x => ‖G x‖^2)
        ((hF.norm.pow 2).intervalIntegrable 0 1) ((hG.norm.pow 2).intervalIntegrable 0 1)]

end JointDickman

end OAI
