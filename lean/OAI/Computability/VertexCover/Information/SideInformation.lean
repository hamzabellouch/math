import Mathlib
import OAI.Computability.VertexCover.Information.Kernels
import OAI.Computability.VertexCover.Information.Tensorization
import OAI.Computability.VertexCover.Information.LogSum

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                                
section

namespace UniqueGames.Foundations.Information
open scoped BigOperators

noncomputable def posteriorOrOriginal
    {A : Type*} [Fintype A] (p e : A → ℝ) (z : ℝ) : A → ℝ := by
  classical
  exact if 0 < z then posterior p e z else p

theorem posteriorOrOriginal_isProbability
    {A : Type*} [Fintype A] (p e : A → ℝ)
    (hp : IsProbability p) (he : ∀ a, 0 ≤ e a)
    {z : ℝ} (hmass : ∑ a, p a * e a = z) :
    IsProbability (posteriorOrOriginal p e z) := by
  classical
  by_cases hz : 0 < z
  · simpa only [posteriorOrOriginal, ite_eq_left hz] using
      posterior_isProbability p e hp he hz hmass
  · simpa only [posteriorOrOriginal, ite_eq_right hz] using hp

theorem mass_mul_posteriorOrOriginal
    {A : Type*} [Fintype A] (p e : A → ℝ)
    (hp : IsProbability p) (he : ∀ a, 0 ≤ e a)
    {«c» : ℝ} (hmass : ∑ a, p a * e a = «c») (x : A) :
    «c» * posteriorOrOriginal p e «c» x = p x * e x := by
  classical
  by_cases hc : 0 < «c»
  · simp only [posteriorOrOriginal, ite_eq_left hc, posterior]
    field_simp [hc.ne']
  · have hcnonneg : 0 ≤ «c» := by
      rw [← hmass]
      exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp.1 a) (he a))
    have hc0 : «c» = 0 := le_antisymm (le_of_not_gt hc) hcnonneg
    have hpoint := Finset.single_le_sum
      (fun a (_ : a ∈ (Finset.univ : Finset A)) => mul_nonneg (hp.1 a) (he a))
      (Finset.mem_univ x)
    rw [hmass, hc0] at hpoint
    have hzero : p x * e x = 0 := le_antisymm hpoint (mul_nonneg (hp.1 x) (he x))
    simp [posteriorOrOriginal, hc0, hzero]

theorem weighted_coordinate_posterior_recombine
    {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
    (p e : (I → A) → ℝ) (hp : IsProbability p) (he : ∀ x, 0 ≤ e x)
    {«c» : ℝ} (hmass : ∑ x, p x * e x = «c») (b z : ℝ) (i : I) (a : A) :
    (b * «c» / z) * coordinateMarginal (posteriorOrOriginal p e «c») i a =
      (b / z) * ∑ x, if x i = a then p x * e x else 0 := by
  classical
  simp only [coordinateMarginal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hxa : x i = a
  · simp only [ite_eq_left hxa]
    calc
      (b * «c» / z) * posteriorOrOriginal p e «c» x =
          (b / z) * («c» * posteriorOrOriginal p e «c» x) := by ring
      _ = (b / z) * (p x * e x) := by
        rw [mass_mul_posteriorOrOriginal p e hp he hmass x]
  · simp [hxa]

variable {J I A : Type*}
variable [Fintype J] [Fintype I] [Fintype A] [DecidableEq I]

theorem side_information_bound
    (w b «c» : J → ℝ)
    (q : J → I → A → ℝ)
    (e : J → (I → A) → ℝ)
    (hw : IsProbability w)
    (hb : ∀ j, 0 ≤ b j)
    (hq : ∀ j i, IsProbability (q j i))
    (he : ∀ j x, 0 ≤ e j x)
    (he_one : ∀ j x, e j x ≤ 1)
    (hmass : ∀ j, ∑ x, independentProduct (q j) x * e j x = «c» j)
    {z B : ℝ} (hz : 0 < z) (hB : 0 < B)
    (hbase : ∑ j, b j = B)
    (hweight : ∀ j, w j = b j * «c» j / z) :
    (∑ i, totalVariation
      (fun ja : J × A => w ja.1 * coordinateMarginal
        (posteriorOrOriginal (independentProduct (q ja.1))
          (e ja.1) («c» ja.1)) i ja.2)
      (fun ja : J × A => w ja.1 * q ja.1 i ja.2)) ≤
      Real.sqrt ((Fintype.card I : ℝ) * Real.log (B / z)) := by
  classical
  let d : J → I → ℝ := fun j i => totalVariation
    (coordinateMarginal
      (posteriorOrOriginal (independentProduct (q j)) (e j) («c» j)) i)
    (q j i)
  have hbudget : ∀ j,
      w j * (∑ i, d j i ^ 2) ≤ w j * Real.log (1 / «c» j) := by
    intro j
    by_cases hwzero : w j = 0
    · simp [hwzero]
    have hcne : «c» j ≠ 0 := by
      intro hczero
      apply hwzero
      rw [hweight j, hczero, mul_zero, zero_div]
    have hcnonneg : 0 ≤ «c» j := by
      rw [← hmass j]
      exact Finset.sum_nonneg (fun x _ => mul_nonneg
        ((independentProduct_isProbability (q j) (hq j)).1 x) (he j x))
    have hcpos : 0 < «c» j := lt_of_le_of_ne hcnonneg (Ne.symm hcne)
    have hlocal := posterior_coordinate_totalVariation_sq_sum_le_log
      (q j) (hq j) (e j) (he j) (he_one j) hcpos (hmass j)
    have hweighted := mul_le_mul_of_nonneg_left hlocal (hw.1 j)
    simpa only [d, posteriorOrOriginal, ite_eq_left hcpos] using hweighted
  have hcs := weighted_coordinate_sum_sq_le
    w d (fun j => Real.log (1 / «c» j)) hw hbudget
  have hlog := posterior_weighted_log_inverse_le w b «c» hw hb hz hB hbase hweight
  have hsq : (∑ i, ∑ j, w j * d j i)^2 ≤
      (Fintype.card I : ℝ) * Real.log (B / z) :=
    hcs.trans (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _))
  have htv : ∀ i, totalVariation
      (fun ja : J × A => w ja.1 * coordinateMarginal
        (posteriorOrOriginal (independentProduct (q ja.1))
          (e ja.1) («c» ja.1)) i ja.2)
      (fun ja : J × A => w ja.1 * q ja.1 i ja.2) =
      ∑ j, w j * d j i := by
    intro i
    exact totalVariation_joint_common_weights w
      (fun j => coordinateMarginal
        (posteriorOrOriginal (independentProduct (q j)) (e j) («c» j)) i)
      (fun j => q j i) hw.1
  simp_rw [htv]
  have hradicand : 0 ≤ (Fintype.card I : ℝ) * Real.log (B / z) :=
    (sq_nonneg _).trans hsq
  have hsqrt := Real.sq_sqrt hradicand
  have hsqrt_nonneg := Real.sqrt_nonneg ((Fintype.card I : ℝ) * Real.log (B / z))
  nlinarith

variable {T V : Type*} [Fintype T] [Fintype V] [Nonempty V]

theorem finite_side_information_bound
    (pT : T → ℝ) (q : T → I → A → ℝ)
    (e : T × V → (I → A) → ℝ) («c» w : T × V → ℝ)
    (hpT : IsProbability pT)
    (hq : ∀ t i, IsProbability (q t i))
    (he : ∀ tv x, 0 ≤ e tv x)
    (he_sum : ∀ t x, (∑ v, e (t, v) x) ≤ 1)
    (hc : ∀ tv, ∑ x, independentProduct (q tv.1) x * e tv x = «c» tv)
    {z : ℝ} (hz : 0 < z)
    (hZ : ∑ tv, pT tv.1 * «c» tv = z)
    (hweight : ∀ tv, w tv = pT tv.1 * «c» tv / z) :
    (∑ i, totalVariation
      (fun tva : (T × V) × A => w tva.1 * coordinateMarginal
        (posteriorOrOriginal (independentProduct (q tva.1.1))
          (e tva.1) («c» tva.1)) i tva.2)
      (fun tva : (T × V) × A => w tva.1 * q tva.1.1 i tva.2)) ≤
      Real.sqrt ((Fintype.card I : ℝ) *
        (Real.log (Fintype.card V : ℝ) + Real.log (1 / z))) := by
  classical
  have hcnonneg : ∀ tv, 0 ≤ «c» tv := by
    intro tv
    rw [← hc tv]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg
      ((independentProduct_isProbability (q tv.1) (hq tv.1)).1 x) (he tv x))
  have hw : IsProbability w := by
    constructor
    · intro tv
      rw [hweight tv]
      exact div_nonneg (mul_nonneg (hpT.1 tv.1) (hcnonneg tv)) hz.le
    · simp_rw [hweight, div_eq_mul_inv]
      rw [← Finset.sum_mul, hZ, mul_inv_cancel₀ hz.ne']
  have he_one : ∀ tv x, e tv x ≤ 1 := by
    intro tv x
    have hsingle : e tv x ≤ ∑ v, e (tv.1, v) x :=
      Finset.single_le_sum (fun v _ => he (tv.1, v) x) (Finset.mem_univ tv.2)
    exact hsingle.trans (he_sum tv.1 x)
  have hB : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hbase : (∑ tv : T × V, pT tv.1) = (Fintype.card V : ℝ) := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum, hpT.2, mul_one]
  have h := side_information_bound w (fun tv : T × V => pT tv.1) «c»
    (fun tv => q tv.1) e hw (fun tv => hpT.1 tv.1) (fun tv => hq tv.1)
    he he_one hc hz hB hbase hweight
  have hlog : Real.log ((Fintype.card V : ℝ) / z) =
      Real.log (Fintype.card V : ℝ) + Real.log (1 / z) := by
    rw [Real.log_div hB.ne' hz.ne', Real.log_div one_ne_zero hz.ne', Real.log_one]
    ring
  simpa only [hlog] using h

end UniqueGames.Foundations.Information
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
