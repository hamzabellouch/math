import OAI.NumberTheory.Jacobsthal.Primes.PrimeChoiceCoordinateMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.WrongOwnerBinMass
open PrimeBinAlignmentMass ActualBinOwners OwnerUniquenessFinite OwnerSearchBounds
open ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

noncomputable def wrongOwnerPrimes (Y w Cs eta R xi : ℝ) (a : ℕ → ℤ) (q : ℚ) : Finset ℕ :=
  (primeBin R xi).filter (fun p => aligns a q p ∧ ∃ r,
    owner Y w Cs eta R xi a=some r ∧ r ≠ q ∧ aligns a r p)

theorem wrongOwnerPrimes_none (Y w Cs eta R xi : ℝ) (a : ℕ → ℤ) (q : ℚ)
    (ho : owner Y w Cs eta R xi a=none) : wrongOwnerPrimes Y w Cs eta R xi a q=∅ := by
  ext p
  simp [wrongOwnerPrimes,ho]

theorem wrongOwnerPrimes_self (Y w Cs eta R xi : ℝ) (a : ℕ → ℤ) (q : ℚ)
    (ho : owner Y w Cs eta R xi a=some q) : wrongOwnerPrimes Y w Cs eta R xi a q=∅ := by
  ext p
  simp [wrongOwnerPrimes,ho]

theorem wrongOwnerPrimes_eq_common (Y w Cs eta R xi : ℝ) (a : ℕ → ℤ) (q r : ℚ)
    (ho : owner Y w Cs eta R xi a=some r) (hne : r ≠ q) :
    wrongOwnerPrimes Y w Cs eta R xi a q=commonAligners (primeBin R xi) a q r := by
  ext p
  simp [wrongOwnerPrimes,ho,hne,commonAligners]

theorem wrong_owner_mass_bound {Y w Cs eta R xi : ℝ} (hY : 0 ≤ Y) (hw : 1 < w)
    (hCs : 0 ≤ Cs) (hwlarge : 2*Cs+3 ≤ w) (hYup : Y ≤ Real.exp (w^2))
    (hR : 1 < R) (hxi : 0 ≤ xi) (a : ℕ → ℤ) (q : ℚ) (hq : eligible Y w Cs q) :
    mass (wrongOwnerPrimes Y w Cs eta R xi a q) ≤ 2*w^2/(R*Real.log R) := by
  have hRp0 : 0 < R := zero_lt_one.trans hR
  have hlog0 : 0 < Real.log R := Real.log_pos hR
  have hnon : 0 ≤ 2*w^2/(R*Real.log R) := by positivity
  cases ho : owner Y w Cs eta R xi a with
  | none => simpa only [wrongOwnerPrimes_none Y w Cs eta R xi a q ho,mass,Finset.sum_empty] using hnon
  | some r =>
    by_cases he : r=q
    · subst r
      simpa only [wrongOwnerPrimes_self Y w Cs eta R xi a q ho,mass,Finset.sum_empty] using hnon
    · rw [wrongOwnerPrimes_eq_common Y w Cs eta R xi a q r ho he]
      have hr := (actual_owner_witness hY hw a ho).1
      have hd := (eligible_determinant_height hY hw q r hq hr).trans
        (height_exp_square hY hw.le hCs hwlarge hYup)
      have hRp : 0 < R := zero_lt_one.trans hR
      have hlog : 0 < Real.log R := Real.log_pos hR
      have hheight : ((determinant q r).natAbs:ℝ) ≤ R^(2*w^2/Real.log R) := by
        have hh : R^(2*w^2/Real.log R)=Real.exp (2*w^2) := by
          rw [Real.rpow_def_of_pos hRp]
          congr 1
          field_simp [hlog.ne']
        rwa [hh]
      have hp : ∀ p ∈ primeBin R xi,p.Prime := fun p hp => ((mem_primeBin hRp.le hxi p).mp hp).1
      have hlarge : ∀ p ∈ primeBin R xi,R^(1:ℝ) ≤ (p:ℝ) := by
        intro p hp
        rw [Real.rpow_one]
        exact ((mem_primeBin hRp.le hxi p).mp hp).2.1.le
      have hc := common_primes_power_height_bound (primeBin R xi) a (Ne.symm he) hp hR
        (by norm_num : (0:ℝ)<1) hlarge hheight
      rw [div_one] at hc
      calc
        _ ≤ ((commonAligners (primeBin R xi) a q r).card:ℝ)/R :=
          (subset_mass_bounds hRp hxi _ (Finset.filter_subset _ _)).2
        _ ≤ (2*w^2/Real.log R)/R := div_le_div_of_nonneg_right hc hRp.le
        _ = _ := by rw [div_div,mul_comm (Real.log R) R]
end NumberTheoryLean.WrongOwnerBinMass



namespace NumberTheoryLean.WrongOwnerFraction
open _root_.Filter PrimeBinAlignmentMass WrongOwnerBinMass ActualBinOwners
open ErdosInversePrimeBin ErdosInverseAlignment


theorem uniform_bin_mass_lower {theta : ℝ} (htheta : 0 < theta) :
    ∀ᶠ R : ℝ in atTop,2 ≤ R ∧ ∀ xi : ℝ,theta ≤ xi → xi ≤ 1 →
      theta/(8*Real.log R) ≤ mass (primeBin R xi) := by
  filter_upwards [uniform_prime_bin_count htheta] with R hR
  refine ⟨hR.1,?_⟩
  intro xi hxi hxi1
  have hRp : 0 < R := by linarith [hR.1]
  have hlog : 0 < Real.log R := Real.log_pos (by linarith [hR.1])
  have hxi0 : 0 ≤ xi := htheta.le.trans hxi
  have hden : 0 < (1+xi)*R := by positivity
  have hc : theta/8 ≤ xi/(4*(1+xi)) := by
    apply (le_div_iff₀ (by positivity : 0 < 4*(1+xi))).mpr
    have hh := mul_le_mul_of_nonneg_left hxi1 htheta.le
    nlinarith
  have hm := (div_le_div_of_nonneg_right (hR.2 xi hxi hxi1).1 hden.le).trans
    (subset_mass_bounds hRp hxi0 (primeBin R xi) (fun _ h => h)).1
  calc
    _ = (theta/8)/Real.log R := by rw [div_div]
    _ ≤ (xi/(4*(1+xi)))/Real.log R := div_le_div_of_nonneg_right hc hlog.le
    _ = (xi*R/(4*Real.log R))/((1+xi)*R) := by
      field_simp [hRp.ne',hlog.ne',(by positivity : (1+xi:ℝ) ≠ 0)]
    _ ≤ _ := hm

theorem uniform_wrong_owner_fraction {theta : ℝ} (htheta : 0 < theta) :
    ∀ᶠ R : ℝ in atTop,2 ≤ R ∧ ∀ Y w Cs eta xi : ℝ,
      0 ≤ Y → 1 < w → 0 ≤ Cs → 2*Cs+3 ≤ w → Y ≤ Real.exp (w^2) →
      theta ≤ xi → xi ≤ 1 → ∀ (a : ℕ → ℤ) (q : ℚ),eligible Y w Cs q →
      mass (wrongOwnerPrimes Y w Cs eta R xi a q) ≤
        (16*w^2/(theta*R))*mass (primeBin R xi) := by
  filter_upwards [uniform_bin_mass_lower htheta] with R hR
  refine ⟨hR.1,?_⟩
  intro Y w Cs eta xi hY hw hCs hwlarge hYup hxi hxi1 a q hq
  have hRp : 0 < R := by linarith [hR.1]
  have hR1 : 1 < R := by linarith [hR.1]
  have hlog : 0 < Real.log R := Real.log_pos hR1
  have habs := wrong_owner_mass_bound (eta := eta) hY hw hCs hwlarge hYup hR1 (htheta.le.trans hxi) a q hq
  have hm := mul_le_mul_of_nonneg_left (hR.2 xi hxi hxi1)
    (show 0 ≤ 16*w^2/(theta*R) by positivity)
  have he : (16*w^2/(theta*R))*(theta/(8*Real.log R))=2*w^2/(R*Real.log R) := by
    field_simp [hRp.ne',hlog.ne',htheta.ne']
    norm_num
  rw [he] at hm
  exact habs.trans hm
end NumberTheoryLean.WrongOwnerFraction



namespace NumberTheoryLean.WrongOwnerSearchTail
open _root_.Filter PrimeBinAlignmentMass WrongOwnerBinMass WrongOwnerFraction ActualBinOwners OwnerSearchBounds
open ErdosInversePrimeBin


theorem search_fraction_factor {theta A : ℝ} (_htheta : 0 < theta) (_hA : 0 < A) :
    ∀ᶠ w : ℝ in atTop,∀ R : ℝ,w^(w^((1/4:ℝ))) ≤ R →
      16*w^2/(theta*R) ≤ w^(-A) := by
  have hquarter : ∀ᶠ w : ℝ in atTop,A+3 ≤ w^((1/4:ℝ)) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).eventually_ge_atTop (A+3)
  filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop (16/theta),hquarter] with w hw2 hwC hwPow
  intro R hR
  have hw1 : 1 ≤ w := by linarith
  have hw0 : 0 < w := by linarith
  have hRa : w^(A+3) ≤ R := (Real.rpow_le_rpow_of_exponent_le hw1 hwPow).trans hR
  have hden : 0 < w^(A+3) := Real.rpow_pos_of_pos hw0 _
  have hRp : 0 < R := hden.trans_le hRa
  have hnum : (16/theta)*w^2 ≤ w^3 := by
    have hh := mul_le_mul_of_nonneg_right hwC (sq_nonneg w)
    nlinarith
  calc
    _ = ((16/theta)*w^2)/R := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
    _ ≤ w^3/R := div_le_div_of_nonneg_right hnum hRp.le
    _ ≤ w^3/w^(A+3) := div_le_div_of_nonneg_left (pow_nonneg hw0.le 3) hden hRa
    _ = w^(-A) := by
      rw [show w^3=w^(3:ℝ) by norm_num,← Real.rpow_sub hw0]
      congr 1
      ring

theorem actual_wrong_search_mass {Cs theta A : ℝ} (hCs : 0 ≤ Cs)
    (htheta : 0 < theta) (hA : 0 < A) :
    ∀ᶠ w : ℝ in atTop,∀ Y R xi eta : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) →
      w^(w^((1/4:ℝ))) ≤ R → theta ≤ xi → xi ≤ 1 →
      ∀ (a : ℕ → ℤ) (q : ℚ),eligible Y w Cs q →
      mass (wrongOwnerPrimes Y w Cs eta R xi a q) ≤ w^(-A)*mass (primeBin R xi) := by
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp (uniform_wrong_owner_fraction htheta)
  have hquarter : ∀ᶠ w : ℝ in atTop,4 ≤ w^((1/4:ℝ)) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).eventually_ge_atTop 4
  filter_upwards [search_fraction_factor htheta hA,eventually_ge_atTop (2:ℝ),eventually_ge_atTop R₀,
    eventually_ge_atTop (2*Cs+3),hquarter] with w hfactor hw2 hwR hwCs hwPow
  intro Y R xi eta hY hYup hsearch hxi hxi1 a q hq
  have hw1 : 1 ≤ w := by linarith
  have hRlarge : R₀ ≤ R := hwR.trans ((le_fourth hw1).trans (search_ge_fourth hw1 hwPow hsearch))
  have hh := (hR₀ R hRlarge).2 Y w Cs eta xi hY (by linarith) hCs hwCs hYup hxi hxi1 a q hq
  exact hh.trans (mul_le_mul_of_nonneg_right (hfactor R hsearch) (mass_nonnegative _))
end NumberTheoryLean.WrongOwnerSearchTail



namespace NumberTheoryLean.WrongOwnerBoxMass
open _root_.Filter PrimeChoiceBoxMass PrimeChoiceCoordinateMass PrimeChoiceAlignmentDecay
open PrimeBinAlignmentMass WrongOwnerBinMass WrongOwnerSearchTail ActualBinOwners
open ErdosInversePrimeBin

attribute [local instance] Classical.propDecidable

theorem wrong_owner_box_mass {Cs theta A : ℝ} (hCs : 0 ≤ Cs) (htheta : 0 < theta) (hA : 0 < A) :
    ∀ᶠ w : ℝ in atTop,∀ Y xi eta : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) → theta ≤ xi → xi ≤ 1 →
      ∀ (m : ℕ) (R : Fin m → ℝ) (S : Finset (Fin m)),
      (∀ i ∈ S,w^(w^((1/4:ℝ))) ≤ R i) → ∀ (a : ℕ → ℤ) (q : ℚ),eligible Y w Cs q →
      (∑ f ∈ someCoordinateEvent (fun i => primeBin (R i) xi) S
        (fun i => wrongOwnerPrimes Y w Cs eta (R i) xi a q),weight f) ≤
      (S.card:ℝ)*w^(-A)*boxMass (fun i => primeBin (R i) xi) := by
  filter_upwards [actual_wrong_search_mass hCs htheta hA] with w hw
  intro Y xi eta hY hYup hxi hxi1 m R S hsearch a q hq
  apply some_coordinate_mass_bound
  · intro i _hi
    exact Finset.filter_subset _ _
  · intro i hi
    exact hw Y (R i) xi eta hY hYup (hsearch i hi) hxi hxi1 a q hq

theorem logarithmic_positions_le_w (Clen : ℝ) (hC : 0 ≤ Clen) :
    ∀ᶠ w : ℝ in atTop,2*Clen*Real.log w ≤ w := by
  have hD : 0 < 2*Clen+1 := by linarith
  have hh := (isLittleO_log_rpow_atTop (r := 1) (by norm_num)).bound
    (show 0 < 1/(2*Clen+1) by positivity)
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with w hsmall hw
  have hw0 : 0 < w := zero_lt_one.trans hw
  have hlog0 : 0 < Real.log w := Real.log_pos hw
  have hs : Real.log w ≤ w/(2*Clen+1) := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos hlog0,abs_of_pos hw0,
      one_div,mul_comm,div_eq_mul_inv,one_mul] using hsmall
  have hm := (le_div_iff₀ hD).mp hs
  nlinarith

theorem length_bounded_wrong_box_mass {Cs theta A Clen : ℝ} (hCs : 0 ≤ Cs)
    (htheta : 0 < theta) (hA : 0 < A) (hC : 0 ≤ Clen) :
    ∀ᶠ w : ℝ in atTop,∀ Y xi eta B : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) → theta ≤ xi → xi ≤ 1 →
      Real.log B ≤ 2*Real.log w → ∀ (m : ℕ),(m:ℝ) ≤ Clen*Real.log B →
      ∀ (R : Fin m → ℝ) (S : Finset (Fin m)),
      (∀ i ∈ S,w^(w^((1/4:ℝ))) ≤ R i) → ∀ (a : ℕ → ℤ) (q : ℚ),eligible Y w Cs q →
      (∑ f ∈ someCoordinateEvent (fun i => primeBin (R i) xi) S
        (fun i => wrongOwnerPrimes Y w Cs eta (R i) xi a q),weight f) ≤
      w^(-A)*boxMass (fun i => primeBin (R i) xi) := by
  filter_upwards [wrong_owner_box_mass hCs htheta (show 0 < A+1 by linarith),
    logarithmic_positions_le_w Clen hC,eventually_gt_atTop (1:ℝ)] with w hw hlength hw1
  intro Y xi eta B hY hYup hxi hxi1 hB m hm R S hsearch a q hq
  have hraw := hw Y xi eta hY hYup hxi hxi1 m R S hsearch a q hq
  have hcard : (S.card:ℝ) ≤ w := by
    have hsm : S.card ≤ m := by simpa using Finset.card_le_univ S
    have hsmr : (S.card:ℝ) ≤ (m:ℝ) := by exact_mod_cast hsm
    have hmul := mul_le_mul_of_nonneg_left hB hC
    nlinarith
  have hw0 : 0 < w := zero_lt_one.trans hw1
  have hmul := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hw0.le (-(A+1)))
  have he : w*w^(-(A+1))=w^(-A) := by
    calc
      _ = w^(1:ℝ)*w^(-(A+1)) := by rw [Real.rpow_one]
      _ = w^((1:ℝ)+(-(A+1))) := (Real.rpow_add hw0 _ _).symm
      _ = _ := by congr 1; ring
  rw [he] at hmul
  exact hraw.trans (mul_le_mul_of_nonneg_right hmul (boxMass_nonnegative _))
end NumberTheoryLean.WrongOwnerBoxMass


end Erdos970

end OAI
