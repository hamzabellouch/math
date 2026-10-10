import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

namespace OAI

/-!
# Polar unitaries close to the identity

We construct the polar factor of an invertible element using the positive
square root supplied by continuous functional calculus.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A : Type*} [CStarAlgebra A]

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

/-- The absolute value of an invertible element is invertible. -/
theorem isUnit_abs (t : Aˣ) : IsUnit (CFC.abs (t : A)) := by
  apply (CFC.isUnit_sqrt_iff _).mpr
  exact t.isUnit.star.mul t.isUnit

/-- Polar decomposition of an invertible element, with unitary polar factor. -/
theorem exists_unitary_mul_abs (t : Aˣ) :
    ∃ u : unitary A, (u : A) * CFC.abs (t : A) = (t : A) := by
  let s : Aˣ := (isUnit_abs t).unit
  have hs : (s : A) = CFC.abs (t : A) := (isUnit_abs t).unit_spec
  have hsstar : star s = s := Units.ext (by
    change star (s : A) = (s : A)
    rw [hs]
    exact (CFC.abs_nonneg _).star_eq)
  have hsinvstar : star ((s⁻¹ : Aˣ) : A) = ((s⁻¹ : Aˣ) : A) := by
    rw [← Units.coe_star, star_inv, hsstar]
  have hss : (s : A) * (s : A) = star (t : A) * (t : A) := by
    rw [hs, CFC.abs_mul_abs]
  let v : Aˣ := t * s⁻¹
  have hunit : (v : A) ∈ unitary A := by
    apply v.isUnit.mem_unitary_of_star_mul_self
    change star ((t : A) * (s⁻¹ : Aˣ)) * ((t : A) * (s⁻¹ : Aˣ)) = 1
    rw [star_mul, hsinvstar]
    calc
      ((s⁻¹ : Aˣ) : A) * star (t : A) * ((t : A) * (s⁻¹ : Aˣ)) =
          ((s⁻¹ : Aˣ) : A) * (star (t : A) * (t : A)) * (s⁻¹ : Aˣ) := by simp only [mul_assoc]
      _ = ((s⁻¹ : Aˣ) : A) * ((s : A) * (s : A)) * (s⁻¹ : Aˣ) := by rw [hss]
      _ = 1 := by simp only [← mul_assoc, Units.inv_mul, one_mul, Units.mul_inv]
  refine ⟨⟨v, hunit⟩, ?_⟩
  change (t : A) * (s⁻¹ : Aˣ) * CFC.abs (t : A) = (t : A)
  rw [← hs, mul_assoc, Units.inv_mul, mul_one]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Inverting a unit close to one gives the usual geometric-series bound. -/
theorem norm_unit_inv_le_of_near_one [Nontrivial A] (t : Aˣ)
    (ht : ‖(t : A) - 1‖ < 1) :
    ‖((t⁻¹ : Aˣ) : A)‖ ≤ (1 - ‖(t : A) - 1‖)⁻¹ := by
  have hpos : 0 < 1 - ‖(t : A) - 1‖ := sub_pos.mpr ht
  have hidentity : ((t⁻¹ : Aˣ) : A) - 1 =
      ((t⁻¹ : Aˣ) : A) * (1 - (t : A)) := by
    rw [mul_sub, mul_one, Units.inv_mul]
  have htriangle := norm_le_norm_sub_add (((t⁻¹ : Aˣ) : A)) (1 : A)
  have hproduct := norm_mul_le (((t⁻¹ : Aˣ) : A)) (1 - (t : A))
  rw [← hidentity, norm_sub_rev (1 : A) (t : A)] at hproduct
  rw [norm_one] at htriangle
  have hbound : (1 - ‖(t : A) - 1‖) * ‖((t⁻¹ : Aˣ) : A)‖ ≤ 1 := by nlinarith
  simpa only [mul_one] using (le_inv_mul_iff₀ hpos).mpr hbound

/-- A positive unit with upper bounds on its norm and inverse lies within
the same radius of the identity. -/
theorem norm_positive_unit_sub_one_le [Nontrivial A] (s : Aˣ) (hs : 0 ≤ (s : A)) {r : ℝ}
    (hr : 0 ≤ r) (hr₁ : r < 1) (hnorm : ‖(s : A)‖ ≤ 1 + r)
    (hinv : ‖((s⁻¹ : Aˣ) : A)‖ ≤ (1 - r)⁻¹) :
    ‖(s : A) - 1‖ ≤ r := by
  have hrepr : cfc (fun x : ℝ => x - 1) (s : A) = (s : A) - 1 := by
    rw [cfc_sub (fun x : ℝ => x) (fun _ : ℝ => 1) (s : A),
      cfc_id' ℝ (s : A), cfc_const_one ℝ (s : A)]
  rw [← hrepr]
  apply norm_cfc_le hr
  intro x hx
  have hx₀ : 0 ≤ x := spectrum_nonneg_of_nonneg hs hx
  have hxne : x ≠ 0 := by
    intro hzero
    exact spectrum.zero_notMem ℝ s.isUnit (hzero ▸ hx)
  have hxpos : 0 < x := lt_of_le_of_ne hx₀ (Ne.symm hxne)
  have hxupper : x ≤ 1 + r :=
    (Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans hnorm)
  have hxinv : x⁻¹ ≤ (1 - r)⁻¹ :=
    (Real.le_norm_self (x⁻¹)).trans
      ((spectrum.norm_le_norm_of_mem (spectrum.inv₀_mem_inv hx)).trans hinv)
  have hxlower : 1 - r ≤ x :=
    (inv_le_inv₀ hxpos (sub_pos.mpr hr₁)).mp hxinv
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Taking the absolute value of a unit does not increase its distance from
one, provided that distance is less than one. -/
theorem norm_abs_sub_one_le [Nontrivial A] (t : Aˣ)
    (ht : ‖(t : A) - 1‖ < 1) :
    ‖CFC.abs (t : A) - 1‖ ≤ ‖(t : A) - 1‖ := by
  obtain ⟨u, hu⟩ := exists_unitary_mul_abs t
  let s : Aˣ := (isUnit_abs t).unit
  have hs : (s : A) = CFC.abs (t : A) := (isUnit_abs t).unit_spec
  have hdecomp : (u : A) * (s : A) = (t : A) := by rwa [hs]
  have hinveq : ((s⁻¹ : Aˣ) : A) = ((t⁻¹ : Aˣ) : A) * (u : A) := by
    calc
      ((s⁻¹ : Aˣ) : A) =
          (((t⁻¹ : Aˣ) : A) * (t : A)) * ((s⁻¹ : Aˣ) : A) := by simp
      _ = (((t⁻¹ : Aˣ) : A) * ((u : A) * (s : A))) * ((s⁻¹ : Aˣ) : A) := by
        rw [hdecomp]
      _ = ((t⁻¹ : Aˣ) : A) * (u : A) := by
        simp only [mul_assoc, Units.mul_inv, mul_one]
  have hsinv : ‖((s⁻¹ : Aˣ) : A)‖ = ‖((t⁻¹ : Aˣ) : A)‖ := by
    rw [hinveq, CStarRing.norm_mul_coe_unitary]
  have hsnorm : ‖(s : A)‖ ≤ 1 + ‖(t : A) - 1‖ := by
    rw [hs, CFC.norm_abs]
    have h := norm_le_norm_sub_add (t : A) (1 : A)
    simpa only [norm_one, add_comm] using h
  rw [← hs]
  apply norm_positive_unit_sub_one_le s (by rw [hs]; exact CFC.abs_nonneg _)
    (norm_nonneg _) ht hsnorm
  rw [hsinv]
  exact norm_unit_inv_le_of_near_one t ht

/-- The polar unitary of a unit close to one is within twice that distance
of one. -/
theorem exists_polar_unitary_near_one_of_unit [Nontrivial A] (t : Aˣ)
    (ht : ‖(t : A) - 1‖ < 1) :
    ∃ u : unitary A, (u : A) * CFC.abs (t : A) = (t : A) ∧
      ‖(u : A) - 1‖ ≤ 2 * ‖(t : A) - 1‖ := by
  obtain ⟨u, hu⟩ := exists_unitary_mul_abs t
  refine ⟨u, hu, ?_⟩
  have hdiff : (u : A) - (t : A) = (u : A) * (1 - CFC.abs (t : A)) := by
    rw [mul_sub, mul_one, hu]
  calc
    ‖(u : A) - 1‖ ≤ ‖(u : A) - (t : A)‖ + ‖(t : A) - 1‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖1 - CFC.abs (t : A)‖ + ‖(t : A) - 1‖ := by
      rw [hdiff, CStarRing.norm_coe_unitary_mul]
    _ ≤ ‖(t : A) - 1‖ + ‖(t : A) - 1‖ := by
      apply add_le_add _ le_rfl
      simpa only [norm_sub_rev] using norm_abs_sub_one_le t ht
    _ = 2 * ‖(t : A) - 1‖ := by ring

/-- Every element within distance one of the identity has a unitary polar
factor within twice its original distance of the identity. -/
theorem exists_polar_unitary_near_one (T : A) (hT : ‖T - 1‖ < 1) :
    ∃ u : unitary A, (u : A) * CFC.abs T = T ∧ ‖(u : A) - 1‖ ≤ 2 * ‖T - 1‖ := by
  nontriviality A
  let t : Aˣ := Units.ofNearby 1 T (by simpa using hT)
  have ht : (t : A) = T := rfl
  simpa only [ht] using exists_polar_unitary_near_one_of_unit t (by rwa [ht])

end Ordered

/-- Polar decomposition near one without an order instance in the statement.
Positivity of the second factor is expressed as being a star square. -/
theorem exists_positive_polar_decomposition_near_one (T : A) (hT : ‖T - 1‖ < 1) :
    ∃ (u : unitary A) (p : A), (∃ q : A, p = star q * q) ∧
      p * p = star T * T ∧ (u : A) * p = T ∧ ‖(u : A) - 1‖ ≤ 2 * ‖T - 1‖ := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  obtain ⟨u, hup, hu⟩ := exists_polar_unitary_near_one T hT
  refine ⟨u, CFC.abs T, ⟨CFC.sqrt (CFC.abs T), ?_⟩, CFC.abs_mul_abs T, hup, hu⟩
  rw [(CFC.sqrt_nonneg (CFC.abs T)).star_eq,
    CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)]

end

end KadisonKastler

end OAI
