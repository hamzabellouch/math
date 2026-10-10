import OAI.NumberTheory.PiExponent.Cohomology.CurveEuler

namespace OAI

namespace PiExponent.NumericalAmpleness

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Filter
open PiExponentSeshadri.Geometry
open scoped BigOperators

variable {X : Scheme.{0}}

theorem exists_nonzero_globalSection_of_cohomologyDimension_pos
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules)
    (hpos : 0 < cohomologyDimension p M 0) :
    ∃ s : GlobalSections X M, s ≠ 0 := by
  let := Module.compHom (cohomology M 0) (baseScalars p)
  have : Nontrivial (cohomology M 0) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨z,hz⟩ := exists_ne (0 : cohomology M 0)
  refine ⟨Ext.homEquiv₀ z, ?_⟩
  intro hs
  apply hz
  have hzero := congrArg (fun s : GlobalSections X M => Ext.mk₀ s) hs
  simpa only [Ext.mk₀_homEquiv₀_apply, Ext.mk₀_zero] using hzero

theorem eulerCharacteristic_eq_zero_sub_one_add_tail
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d : ℕ) (hd : 1 ≤ d) :
    eulerCharacteristic p d M =
      (cohomologyDimension p M 0 : ℤ) - (cohomologyDimension p M 1 : ℤ) +
        ∑ i ∈ Finset.range (d - 1),
          (-1 : ℤ) ^ (i + 2) * (cohomologyDimension p M (i + 2) : ℤ) := by
  unfold eulerCharacteristic
  rw [show d + 1 = 2 + (d - 1) by omega, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    pow_zero, one_mul, zero_add, pow_one, neg_one_mul]
  simp only [Nat.add_comm 2, sub_eq_add_neg]

theorem eventually_nonzero_globalSection_of_euler_growth
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F : ℕ → X.Modules)
    (d : ℕ) (hd : 1 ≤ d)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p d (F n)) atTop atTop)
    (hconstant : ∀ i, 2 ≤ i → i ≤ d →
      ∃ c : ℕ, ∀ᶠ n in atTop, cohomologyDimension p (F n) i = c) :
    ∀ᶠ n in atTop, ∃ s : GlobalSections X (F n), s ≠ 0 := by
  classical
  have hh (i : Fin (d - 1)) :
      ∃ c : ℕ, ∀ᶠ n in atTop, cohomologyDimension p (F n) (i.val + 2) = c := by
    apply hconstant (i.val + 2) (by omega) (by have := i.isLt; omega)
  choose c hc using hh
  let C : ℤ := ∑ i : Fin (d - 1), (-1 : ℤ) ^ (i.val + 2) * (c i : ℤ)
  have hall : ∀ᶠ n in atTop,
      ∀ i : Fin (d - 1), cohomologyDimension p (F n) (i.val + 2) = c i :=
    Filter.eventually_all.mpr hc
  have hlarge : ∀ᶠ n in atTop, C < eulerCharacteristic p d (F n) :=
    hgrowth.eventually (eventually_gt_atTop C)
  filter_upwards [hall, hlarge] with n hn hχ
  apply exists_nonzero_globalSection_of_cohomologyDimension_pos p (F n)
  have htail : (∑ i ∈ Finset.range (d - 1),
      (-1 : ℤ) ^ (i + 2) * (cohomologyDimension p (F n) (i + 2) : ℤ)) = C := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [hn i]
  rw [eulerCharacteristic_eq_zero_sub_one_add_tail p (F n) d hd, htail] at hχ
  have hnonneg : (0 : ℤ) ≤ (cohomologyDimension p (F n) 1 : ℤ) := Int.natCast_nonneg _
  omega

theorem eventually_nonzero_globalSection_of_eventually_stationary
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F : ℕ → X.Modules)
    (d : ℕ) (hd : 1 ≤ d)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p d (F n)) atTop atTop)
    (hstationary : ∀ i, 2 ≤ i → i ≤ d →
      ∃ N, ∀ n, N ≤ n → cohomologyDimension p (F n) i =
        cohomologyDimension p (F N) i) :
    ∀ᶠ n in atTop, ∃ s : GlobalSections X (F n), s ≠ 0 := by
  apply eventually_nonzero_globalSection_of_euler_growth p F d hd hgrowth
  intro i hi hid
  obtain ⟨N,hN⟩ := hstationary i hi hid
  refine ⟨cohomologyDimension p (F N) i, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN n hn

end
end PiExponent.NumericalAmpleness

end OAI
