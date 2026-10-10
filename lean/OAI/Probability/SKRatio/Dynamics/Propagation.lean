import Mathlib
import OAI.Probability.SKRatio.Calculus.Energy
import OAI.Probability.SKRatio.Dynamics.Concentration

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap MeasureTheory Filter
namespace SKRatio.Calculus
attribute [local instance] Classical.propDecidable

lemma backward_observable_hasDerivAt {n : ℕ} (J : Interaction n)
    (F F' : ℝ → Observables n) (hF : ∀ r, HasDerivAt F (F' r) r)
    (d a u : ℝ) (x : Spin n) :
    HasDerivAt (fun v : ℝ => Real.exp (a*v)*semigroup J v (F (d-v)) x)
      (Real.exp (a*u)*semigroup J u
        (fun y => a*F (d-u) y + generator J (F (d-u)) y - F' (d-u) y) x) u := by
  have hb : HasDerivAt (fun v : ℝ => F (d-v)) (-F' (d-u)) u := by
    simpa only [Function.comp_def, sub_zero, zero_sub, neg_smul, one_smul] using
      (hF (d-u)).scomp u ((hasDerivAt_const u d).sub (hasDerivAt_id u))
  have h := (((hasDerivAt_id u).const_mul a).exp).mul
    (hasDerivAt_pi.mp ((semigroup_hasDerivAt J u).clm_apply hb) x)
  apply h.congr_deriv
  simp only [mul_apply_eq_comp, Pi.add_apply, map_neg, Pi.neg_apply, id_eq, mul_one]
  have hv : (fun y => a*F (d-u) y + generator J (F (d-u)) y - F' (d-u) y) =
      a • F (d-u) + generator J (F (d-u)) - F' (d-u) := rfl
  rw [hv, map_sub, map_add, map_smul]
  change (Real.exp (a*u)*a)*semigroup J u (F (d-u)) x +
    Real.exp (a*u)*(semigroup J u (generator J (F (d-u))) x -
      semigroup J u (F' (d-u)) x) =
    Real.exp (a*u)*(a*semigroup J u (F (d-u)) x +
      semigroup J u (generator J (F (d-u))) x - semigroup J u (F' (d-u)) x)
  ring

lemma semigroup_subsolution_comparison {n : ℕ} (J : Interaction n)
    (F F' : ℝ → Observables n) (hF : ∀ r, HasDerivAt F (F' r) r)
    {d s a : ℝ} (hs : 0 ≤ s)
    (hineq : ∀ r ∈ Set.Icc (d-s) d, ∀ y,
      F' r y - generator J (F r) y ≤ a*F r y) (x : Spin n) :
    F d x ≤ Real.exp (a*s)*semigroup J s (F (d-s)) x := by
  let H (u : ℝ) := Real.exp (a*u)*semigroup J u (F (d-u)) x
  have hD (u : ℝ) := backward_observable_hasDerivAt J F F' hF d a u x
  have hmono : MonotoneOn H (Set.Icc 0 s) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun u _ => (hD u).continuousAt.continuousWithinAt)
      (fun u _ => (hD u).differentiableAt.differentiableWithinAt)
    intro u hu
    have hui : u ∈ Set.Icc (0:ℝ) s := interior_subset hu
    rw [(hD u).deriv]
    exact mul_nonneg (Real.exp_nonneg _) (semigroup_nonneg J u hui.1 _ (fun y => by
      have h := hineq (d-u) ⟨by linarith only [hui.2], by linarith only [hui.1]⟩ y
      linarith only [h]) x)
  have h := hmono ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs
  simpa [H] using h

lemma gradient_flow_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n)
    (r : ℝ) :
    HasDerivAt (fun t => unweightedGradient (semigroup J t f))
      (fun x => deriv (fun t => unweightedGradient (semigroup J t f) x) r) r := by
  apply hasDerivAt_pi.mpr
  intro x
  exact (unweightedGradient_hasDerivAt J f x r).differentiableAt.hasDerivAt

lemma gradient_comparison_of_drift {n : ℕ} (J : Interaction n) (f : Observables n)
    {d s a : ℝ} (hs : 0 ≤ s)
    (hineq : ∀ r ∈ Set.Icc (d-s) d, ∀ y,
      deriv (fun t => unweightedGradient (semigroup J t f) y) r -
        generator J (unweightedGradient (semigroup J r f)) y ≤
          a*unweightedGradient (semigroup J r f) y) (x : Spin n) :
    unweightedGradient (semigroup J d f) x ≤
      Real.exp (a*s)*semigroup J s (unweightedGradient (semigroup J (d-s) f)) x :=
  semigroup_subsolution_comparison J _ _ (gradient_flow_hasDerivAt J f) hs hineq x

lemma gradient_envelope_of_drift {n : ℕ} (J : Interaction n) (f : Observables n)
    {d a B : ℝ} (hd : 0 ≤ d)
    (hineq : ∀ r ∈ Set.Icc (0:ℝ) d, ∀ y,
      deriv (fun t => unweightedGradient (semigroup J t f) y) r -
        generator J (unweightedGradient (semigroup J r f)) y ≤
          a*unweightedGradient (semigroup J r f) y)
    (hB : ∀y, unweightedGradient f y ≤ B) (x : Spin n) :
    unweightedGradient (semigroup J d f) x ≤ Real.exp (a*d)*B := by
  have h := gradient_comparison_of_drift J f (d := d) (s := d) hd
    (by simpa only [sub_self] using hineq) x
  simp only [sub_self, semigroup_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left (semigroup_le_const J d hd hB x) (Real.exp_nonneg _))

lemma semigroup_subsolution_small_set {n : ℕ} (J : Interaction n)
    (F F' : ℝ → Observables n) (hF : ∀ r, HasDerivAt F (F' r) r)
    (bad : Set (Spin n)) {κ A d₀ T d s q B : ℝ}
    (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hs : 0 ≤ s)
    (hsd : s ≤ d) (hdT : d ≤ T) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hpos : ∀ r ∈ Set.Icc (0:ℝ) d, ∀ y, 0 ≤ F r y)
    (hineq : ∀ r ∈ Set.Icc (0:ℝ) d, ∀ y,
      F' r y - generator J (F r) y ≤ (-κ + if y ∈ bad then A else 0)*F r y)
    (havoid : ∀ u ∈ Set.Icc d₀ T, ∀ x,
      semigroup J u (fun y => if y ∈ bad then 1 else 0) x ≤ q)
    (hend : ∀y, F (d-s) y ≤ B) (x : Spin n) :
    F d x ≤ Real.exp (A*d₀)*Real.exp (-κ*s)*semigroup J s (F (d-s)) x +
      A*Real.exp (A*d₀)*T*Real.exp (A*T)*q*B := by
  classical
  have hT : 0 ≤ T := hs.trans (hsd.trans hdT)
  have hor (r : ℝ) (hr : r ∈ Set.Icc (0:ℝ) d) (y : Spin n) :
      F' r y - generator J (F r) y ≤ (A-κ)*F r y := by
    refine (hineq r hr y).trans ?_
    apply mul_le_mul_of_nonneg_right _ (hpos r hr y)
    split_ifs <;> linarith only [hA]
  have hbase (v : ℝ) (hv : 0 ≤ v) (hvd : v ≤ d) :
      F d x ≤ Real.exp ((A-κ)*v)*semigroup J v (F (d-v)) x := by
    apply semigroup_subsolution_comparison J F F' hF hv
    intro r hr y
    exact hor r ⟨by linarith only [hr.1, hvd], hr.2⟩ y
  have hspos : 0 ≤ semigroup J s (F (d-s)) x :=
    semigroup_nonneg J s hs _ (hpos (d-s) ⟨sub_nonneg.mpr hsd, by linarith only [hs]⟩) x
  have herr : 0 ≤ A*Real.exp (A*d₀)*T*Real.exp (A*T)*q*B := by positivity
  by_cases hlong : d₀ ≤ s
  · let H (u : ℝ) := Real.exp (-κ*u)*semigroup J u (F (d-u)) x
    let M : ℝ := A*Real.exp (A*T)*q*B
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have henv (u : ℝ) (hu : u ∈ Set.Icc d₀ s) (y : Spin n) :
        F (d-u) y ≤ Real.exp (A*T)*B := by
      have hu0 : 0 ≤ u := hd₀.trans hu.1
      have hus : 0 ≤ s-u := sub_nonneg.mpr hu.2
      have hcmp := semigroup_subsolution_comparison J F F' hF
        (d := d-u) (s := s-u) (a := A-κ) hus (by
          intro r hr z
          apply hor r ⟨by linarith only [hr.1, hsd], by linarith only [hr.2, hu0]⟩ z) y
      rw [show d-u-(s-u) = d-s by ring] at hcmp
      have hconst := semigroup_le_const J (s-u) hus hend y
      have hexp : Real.exp ((A-κ)*(s-u)) ≤ Real.exp (A*T) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [hus, hκ, hA, hs, hsd, hdT, hu0]
      exact hcmp.trans ((mul_le_mul_of_nonneg_left hconst (Real.exp_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hexp hB))
    have hD (u : ℝ) := backward_observable_hasDerivAt J F F' hF d (-κ) u x
    have hderivLower (u : ℝ) (hu : u ∈ Set.Icc d₀ s) :
        -M ≤ deriv H u := by
      have hu0 : 0 ≤ u := hd₀.trans hu.1
      have hru : d-u ∈ Set.Icc (0:ℝ) d :=
        ⟨by linarith only [hu.2, hsd], by linarith only [hu0]⟩
      let bF : Observables n := fun y => if y ∈ bad then F (d-u) y else 0
      have hdual (y : Spin n) :
          -A*bF y ≤ -κ*F (d-u) y + generator J (F (d-u)) y - F' (d-u) y := by
        have h := hineq (d-u) hru y
        dsimp [bF]
        split_ifs at * <;> linarith only [h]
      have hmon := semigroup_mono J hu0 _ _ hdual x
      have heq : (fun y => -A*bF y) = (-A) • bF := rfl
      rw [heq, map_smul] at hmon
      change -A*semigroup J u bF x ≤ _ at hmon
      have hbF : 0 ≤ semigroup J u bF x :=
        semigroup_nonneg J u hu0 _ (fun y => by
          dsimp [bF]; split_ifs <;> first | exact hpos (d-u) hru y | rfl) x
      have hcF (y : Spin n) : bF y ≤
          (Real.exp (A*T)*B)*(if y ∈ bad then 1 else 0) := by
        dsimp [bF]
        split_ifs <;> simp only [mul_one, mul_zero]
        · exact henv u hu y
        · rfl
      have hcbound := semigroup_mono J hu0 _ _ hcF x
      have hceq : (fun y => Real.exp (A*T)*B*(if y ∈ bad then 1 else 0)) =
          (Real.exp (A*T)*B) • (fun y => if y ∈ bad then 1 else 0) := rfl
      rw [hceq, map_smul] at hcbound
      have hcbound' : semigroup J u bF x ≤ Real.exp (A*T)*B*q := by
        apply hcbound.trans
        exact mul_le_mul_of_nonneg_left
          (havoid u ⟨hu.1, hu.2.trans (hsd.trans hdT)⟩ x) (by positivity)
      have he : Real.exp (-κ*u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hκ, hu0])
      have hprod : Real.exp (-κ*u)*A*semigroup J u bF x ≤ M := by
        dsimp [M]
        calc
          _ ≤ 1*A*(Real.exp (A*T)*B*q) :=
            mul_le_mul (mul_le_mul_of_nonneg_right he hA) hcbound' hbF (by positivity)
          _ = _ := by ring
      have hbound := mul_le_mul_of_nonneg_left hmon (Real.exp_nonneg (-κ*u))
      rw [(hD u).deriv]
      dsimp [H] at *
      linarith only [hprod, hbound]
    have hmono : MonotoneOn (fun u => H u+M*u) (Set.Icc d₀ s) := by
      have hf (u : ℝ) : HasDerivAt (fun u => H u+M*u) (deriv H u+M) u := by
        have hdH : HasDerivAt H (deriv H u) u := (hD u).differentiableAt.hasDerivAt
        simpa only [Pi.add_apply, id_eq, mul_one] using hdH.fun_add ((hasDerivAt_id u).const_mul M)
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (fun u _ => (hf u).continuousAt.continuousWithinAt)
        (fun u _ => (hf u).differentiableAt.differentiableWithinAt)
      intro u hu
      rw [(hf u).deriv]
      linarith only [hderivLower u (interior_subset hu)]
    have hhs := hmono ⟨le_rfl, hlong⟩ ⟨hlong, le_rfl⟩ hlong
    have hH : H d₀ ≤ H s+M*T := by
      have h := mul_le_mul_of_nonneg_left (show s-d₀ ≤ T by linarith only [hsd, hdT, hd₀]) hM
      nlinarith only [hhs, h]
    have hstart := hbase d₀ hd₀ (hlong.trans hsd)
    have heq : Real.exp ((A-κ)*d₀)*semigroup J d₀ (F (d-d₀)) x =
        Real.exp (A*d₀)*H d₀ := by
      dsimp [H]
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [heq] at hstart
    calc
      _ ≤ Real.exp (A*d₀)*(H s+M*T) :=
        hstart.trans (mul_le_mul_of_nonneg_left hH (Real.exp_nonneg _))
      _ = _ := by dsimp [H, M]; ring
  · have hshort : s ≤ d₀ := (lt_of_not_ge hlong).le
    have he : Real.exp ((A-κ)*s) ≤ Real.exp (A*d₀)*Real.exp (-κ*s) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith only [hA, hshort]
    exact (hbase s hs hsd).trans ((mul_le_mul_of_nonneg_right he hspos).trans
      (le_add_of_nonneg_right herr))

lemma unweightedGradient_nonneg {n : ℕ} (f : Observables n) (x : Spin n) :
    0 ≤ unweightedGradient f x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem gradient_propagation_small_set {n : ℕ} (J : Interaction n)
    (f : Observables n) (bad : Set (Spin n)) {κ A d₀ T d s q B : ℝ}
    (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (hs : 0 ≤ s)
    (hsd : s ≤ d) (hdT : d ≤ T) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hineq : ∀ r ∈ Set.Icc (0:ℝ) d, ∀ y,
      deriv (fun t => unweightedGradient (semigroup J t f) y) r -
        generator J (unweightedGradient (semigroup J r f)) y ≤
          (-κ + if y ∈ bad then A else 0)*unweightedGradient (semigroup J r f) y)
    (havoid : ∀ u ∈ Set.Icc d₀ T, ∀ x,
      semigroup J u (fun y => if y ∈ bad then 1 else 0) x ≤ q)
    (hend : ∀y, unweightedGradient (semigroup J (d-s) f) y ≤ B) (x : Spin n) :
    unweightedGradient (semigroup J d f) x ≤
      Real.exp (A*d₀)*Real.exp (-κ*s)*
        semigroup J s (unweightedGradient (semigroup J (d-s) f)) x +
      A*Real.exp (A*d₀)*T*Real.exp (A*T)*q*B := by
  exact semigroup_subsolution_small_set J _ _ (gradient_flow_hasDerivAt J f) bad
    hκ hA hd₀ hs hsd hdT hq hB
    (fun r _ y => unweightedGradient_nonneg _ y) hineq havoid hend x

lemma tanh_mono : Monotone Real.tanh :=
  monotone_of_deriv_nonneg (fun r => (hasDerivAt_tanh r).differentiableAt)
    (fun r => by rw [(hasDerivAt_tanh r).deriv]; exact (scalarVariance_pos r).le)

lemma gradientWeight_exp_lower {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    Real.exp (-2*|field J x i|) ≤ gradientWeight J x i := by
  let a := |field J x i|
  have hat : 0 ≤ Real.tanh a := by
    simpa only [Real.tanh_zero] using tanh_mono (abs_nonneg (field J x i))
  have hl : Real.exp (-2*a) ≤ 1-Real.tanh a := by
    have h := exp_two_mul_one_sub_tanh a
    have hm := mul_le_mul_of_nonneg_left (show 1 ≤ 1+Real.tanh a by linarith only [hat])
      (Real.exp_nonneg (-2*a))
    calc
      Real.exp (-2*a) = Real.exp (-2*a)*1 := (mul_one _).symm
      _ ≤ Real.exp (-2*a)*(Real.exp (2*a)*(1-Real.tanh a)) := by rwa [h]
      _ = 1-Real.tanh a := by
        rw [← mul_assoc, ← Real.exp_add, show -2*a+2*a=0 by ring, Real.exp_zero, one_mul]
  have hspin : spin x i*Real.tanh (field J x i) ≤ Real.tanh a := by
    unfold spin
    cases x i <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
    · rw [← Real.tanh_neg]
      exact tanh_mono (neg_le_abs (field J x i))
    · exact tanh_mono (le_abs_self (field J x i))
  exact hl.trans (sub_le_sub_left hspin 1)

lemma unweightedGradient_le_exp_weighted {n : ℕ} (J : Interaction n)
    (f : Observables n) (x : Spin n) {H : ℝ}
    (hfields : ∀ i, |field J x i| ≤ H) :
    unweightedGradient f x ≤ Real.exp (2*H)*weightedGradient J f x := by
  have hw (i : Fin n) : 1 ≤ Real.exp (2*H)*gradientWeight J x i := by
    have h := mul_le_mul_of_nonneg_left (gradientWeight_exp_lower J x i)
      (Real.exp_nonneg (2*H))
    have he : 1 ≤ Real.exp (2*H)*Real.exp (-2*|field J x i|) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      linarith only [hfields i]
    exact he.trans h
  unfold unweightedGradient weightedGradient
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [one_mul, mul_assoc] using
    mul_le_mul_of_nonneg_right (hw i) (sq_nonneg (halfDiff i f x))

lemma field_gradient_expectation {n : ℕ} (J : Interaction n) (f : Observables n)
    (hf : ∀ y, |f y| ≤ 1) {z H τ : ℝ} (hz : 0 ≤ z)
    (htail : ∀ x, semigroup J z
      (fun y => if ∃ i, H < |field J y i| then 1 else 0) x ≤ τ) (x : Spin n) :
    semigroup J z (unweightedGradient f) x ≤
      Real.exp (2*H)*semigroup J z (weightedGradient J f) x + (n:ℝ)*τ := by
  classical
  have hp (y : Spin n) : unweightedGradient f y ≤
      Real.exp (2*H)*weightedGradient J f y +
        (n:ℝ)*(if ∃ i, H < |field J y i| then 1 else 0) := by
    split_ifs with h
    · have hb := unweightedGradient_le_dim f hf y
      have hw := mul_nonneg (Real.exp_nonneg (2*H)) (weightedGradient_nonneg J f y)
      linarith only [hb, hw]
    · have hb := unweightedGradient_le_exp_weighted J f y
        (fun i => le_of_not_gt (fun hi => h ⟨i,hi⟩))
      simpa only [mul_zero, add_zero] using hb
  have h := semigroup_mono J hz _ _ hp x
  have heq :
      (fun y => Real.exp (2*H)*weightedGradient J f y +
        (n:ℝ)*(if ∃ i, H < |field J y i| then 1 else 0)) =
      Real.exp (2*H) • weightedGradient J f +
        (n:ℝ) • (fun y => if ∃ i, H < |field J y i| then 1 else 0) := rfl
  rw [heq, map_add, map_smul, map_smul] at h
  change semigroup J z (unweightedGradient f) x ≤
      Real.exp (2*H)*semigroup J z (weightedGradient J f) x +
        (n:ℝ)*semigroup J z (fun y => if ∃ i, H < |field J y i| then 1 else 0) x at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (htail x) (Nat.cast_nonneg n)))

lemma backward_gradient_propagation {n : ℕ} (J : Interaction n) (f : Observables n)
    {D u z C κ r : ℝ} (hu : 0 ≤ u)
    (hprop : ∀ y, unweightedGradient (semigroup J (D-u) f) y ≤
      C*Real.exp (-κ*(z-u))*
        semigroup J (z-u) (unweightedGradient (semigroup J (D-z) f)) y + (n:ℝ)*r)
    (x : Spin n) :
    semigroup J u (unweightedGradient (semigroup J (D-u) f)) x ≤
      C*Real.exp (-κ*(z-u))*
        semigroup J z (unweightedGradient (semigroup J (D-z) f)) x + (n:ℝ)*r := by
  have h := semigroup_mono J hu _ _ hprop x
  have heq :
      (fun y => C*Real.exp (-κ*(z-u))*
        semigroup J (z-u) (unweightedGradient (semigroup J (D-z) f)) y + (n:ℝ)*r) =
      (C*Real.exp (-κ*(z-u))) •
        semigroup J (z-u) (unweightedGradient (semigroup J (D-z) f)) +
      (fun _ => (n:ℝ)*r) := rfl
  rw [heq, map_add, map_smul, semigroup_const] at h
  have hsem : semigroup J u (semigroup J (z-u)
      (unweightedGradient (semigroup J (D-z) f))) =
      semigroup J z (unweightedGradient (semigroup J (D-z) f)) := by
    rw [← mul_apply_eq_comp,
      ← semigroup_add, add_sub_cancel]
  change semigroup J u (unweightedGradient (semigroup J (D-u) f)) x ≤
      C*Real.exp (-κ*(z-u))*
        semigroup J u (semigroup J (z-u) (unweightedGradient (semigroup J (D-z) f))) x +
        (n:ℝ)*r at h
  rwa [hsem] at h

lemma energy_comparison_from_gradient {n : ℕ} (J : Interaction n) (f : Observables n)
    (hf : ∀ y, |f y| ≤ 1) {D u z v C κ r H τ : ℝ}
    (hu : 0 ≤ u) (hz : 0 ≤ z) (hzD : z ≤ D) (hv : 0 ≤ v) (hvzu : v ≤ z-u)
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hτ : 0 ≤ τ)
    (hprop : ∀ y, unweightedGradient (semigroup J (D-u) f) y ≤
      C*Real.exp (-κ*(z-u))*
        semigroup J (z-u) (unweightedGradient (semigroup J (D-z) f)) y + (n:ℝ)*r)
    (htail : ∀ x, semigroup J z
      (fun y => if ∃ i, H < |field J y i| then 1 else 0) x ≤ τ) (x : Spin n) :
    backwardEnergy J f x D u ≤
      (2*C*Real.exp (-κ*v)*Real.exp (2*H))*backwardEnergy J f x D z +
        (2*(n:ℝ)*r + 2*C*(n:ℝ)*τ) := by
  have hU := backward_gradient_propagation J f hu hprop x
  have hlate := field_gradient_expectation J (semigroup J (D-z) f)
    (semigroup_abs_le J (sub_nonneg.mpr hzD) f hf) hz htail x
  have hΓ : backwardEnergy J f x D u ≤
      2*semigroup J u (unweightedGradient (semigroup J (D-u) f)) x := by
    have h := semigroup_mono J hu _ _
      (weightedGradient_le J (semigroup J (D-u) f)) x
    have heq : (fun y => 2*unweightedGradient (semigroup J (D-u) f) y) =
      (2:ℝ) • unweightedGradient (semigroup J (D-u) f) := rfl
    rw [heq, map_smul] at h
    exact h
  have hpoint := (mul_le_mul_of_nonneg_left hlate
    (show 0 ≤ C*Real.exp (-κ*(z-u)) by positivity))
  have hexp : Real.exp (-κ*(z-u)) ≤ Real.exp (-κ*v) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hκ, hvzu]
  have heone : Real.exp (-κ*(z-u)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith only [hκ, hvzu, hv]
  have hcoeff := mul_le_mul_of_nonneg_right hexp
    (show 0 ≤ 2*C*Real.exp (2*H)*backwardEnergy J f x D z by
      exact mul_nonneg (by positivity) (backwardEnergy_nonneg J f x D z hz))
  have herror := mul_le_mul_of_nonneg_right heone
    (show 0 ≤ 2*C*(n:ℝ)*τ by positivity)
  change semigroup J z (unweightedGradient (semigroup J (D-z) f)) x ≤
      Real.exp (2*H)*backwardEnergy J f x D z + (n:ℝ)*τ at hlate
  change C*Real.exp (-κ*(z-u))*
      semigroup J z (unweightedGradient (semigroup J (D-z) f)) x ≤
      C*Real.exp (-κ*(z-u))*(Real.exp (2*H)*backwardEnergy J f x D z+(n:ℝ)*τ) at hpoint
  nlinarith only [hU, hΓ, hpoint, hcoeff, herror]

theorem smoothing_of_small_set_gradient {n : ℕ} (g : Disorder n)
    (bad : Set (Spin n)) {κ A d₀ T t s q H τ γ ε : ℝ}
    (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hd₀ : 0 ≤ d₀) (ht : 0 ≤ t) (hs : 0 < s)
    (hT : t+s ≤ T) (hq : 0 ≤ q) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (hoverlap : continuousDistance g t ≤ 1-ε)
    (hgap : ∀ f : Observables n,
      γ*FiniteLaw.variance (mass g 0) f ≤ stationaryEnergy g f)
    (hdrift : ∀ (f : Observables n), ∀ r ∈ Set.Icc (0:ℝ) T, ∀ y,
      deriv (fun v => unweightedGradient (semigroup (coupling g) v f) y) r -
        generator (coupling g) (unweightedGradient (semigroup (coupling g) r f)) y ≤
          (-κ + if y ∈ bad then A else 0)*
            unweightedGradient (semigroup (coupling g) r f) y)
    (havoid : ∀ u ∈ Set.Icc d₀ T, ∀ x,
      semigroup (coupling g) u (fun y => if y ∈ bad then 1 else 0) x ≤ q)
    (hfields : ∀ z ∈ Set.Icc t (t+s), ∀ x, semigroup (coupling g) z
      (fun y => if ∃ i, H < |field (coupling g) y i| then 1 else 0) x ≤ τ) :
    let C := Real.exp (A*d₀)
    let r := A*C*T*Real.exp (A*T)*q
    let a := 2*C*Real.exp (-κ*(s/2))*Real.exp (2*H)
    let R := 2*(n:ℝ)*r+2*C*(n:ℝ)*τ
    continuousDistance g (t+s) ≤
      (Real.sqrt (2*t*(a/s+R))+Real.exp (-γ*s))/(2*Real.sqrt ε) := by
  dsimp only
  apply smoothing_of_energy_comparison g ht hs (by positivity) hε hoverlap hgap
  intro f hf x u hu z hz
  apply energy_comparison_from_gradient (coupling g) f hf hu.1
    (by linarith only [hz.1, ht, hs]) hz.2 (by linarith only [hs])
    (by linarith only [hz.1, hu.2]) (Real.exp_nonneg _) hκ hτ _
    (hfields z ⟨by linarith only [hz.1, hs], hz.2⟩) x
  intro y
  have hd : t+s-u ≤ T := by linarith only [hT, hu.1]
  have h := gradient_propagation_small_set (coupling g) f bad
    (d := t+s-u) (s := z-u) (B := n) hκ hA hd₀
    (by linarith only [hz.1, hu.2, hs])
    (by linarith only [hz.2]) hd hq (Nat.cast_nonneg n)
    (fun r hr y => hdrift f r ⟨hr.1, hr.2.trans hd⟩ y) havoid
    (fun y => unweightedGradient_le_dim _
      (semigroup_abs_le (coupling g) (by linarith only [hz.2]) f hf) y) y
  rw [show t+s-u-(z-u) = t+s-z by ring] at h
  convert h using 1
  ring

end SKRatio.Calculus

end
end

end OAI
