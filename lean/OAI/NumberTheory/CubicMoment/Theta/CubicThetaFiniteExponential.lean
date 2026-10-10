import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGeometricNumerics

namespace OAI

/-! Finite rational certificates for the exponential factors in the two
coordinate boxes. Every bound is checked from the positive Taylor series. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubic_exp_neg_le_taylor {x b : ℝ} (hx : 0≤x) (hb : 0<b) (n : ℕ)
    (h : b⁻¹≤∑ i∈Finset.range n,x^i/(i.factorial:ℝ)) :
    Real.exp (-x)≤b := by
  rw [Real.exp_neg]
  exact (inv_le_comm₀ (Real.exp_pos _) hb).mpr
    (h.trans (Real.sum_le_exp_of_nonneg hx n))

lemma cubic_primary_exp_4 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 4)≤(20167/2500000:ℝ) := by
  have hr : 2≤Real.sqrt 4 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(241/50:ℝ))≤(20167/2500000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_7 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 7)≤(8523/5000000:ℝ) := by
  have hr : (529/200:ℝ)≤Real.sqrt 7 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(127489/20000:ℝ))≤(8523/5000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_13 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 13)≤(843/5000000:ℝ) := by
  have hr : (721/200:ℝ)≤Real.sqrt 13 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(173761/20000:ℝ))≤(843/5000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_16 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 16)≤(651/10000000:ℝ) := by
  have hr : 4≤Real.sqrt 16 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(241/25:ℝ))≤(651/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_19 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 19)≤(11/400000:ℝ) := by
  have hr : (2179/500:ℝ)≤Real.sqrt 19 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(525139/50000:ℝ))≤(11/400000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_25 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 25)≤(59/10000000:ℝ) := by
  have hr : 5≤Real.sqrt 25 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(241/20:ℝ))≤(59/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_28 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 28)≤(29/10000000:ℝ) := by
  have hr : (5291/1000:ℝ)≤Real.sqrt 28 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(1275131/100000:ℝ))≤(29/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_31 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 31)≤(3/2000000:ℝ) := by
  have hr : (5567/1000:ℝ)≤Real.sqrt 31 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(1341647/100000:ℝ))≤(3/2000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_37 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 37)≤(1/2000000:ℝ) := by
  have hr : (3041/500:ℝ)≤Real.sqrt 37 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(732881/50000:ℝ))≤(1/2000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_43 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 43)≤(1/5000000:ℝ) := by
  have hr : (6557/1000:ℝ)≤Real.sqrt 43 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(1580237/100000:ℝ))≤(1/5000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_49 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 49)≤(1/10000000:ℝ) := by
  have hr : 7≤Real.sqrt 49 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(1687/100:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_52 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 52)≤(1/10000000:ℝ) := by
  have hr : (7211/1000:ℝ)≤Real.sqrt 52 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(1737851/100000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_61 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 61)≤(1/10000000:ℝ) := by
  have hr : (781/100:ℝ)≤Real.sqrt 61 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(188221/10000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_64 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 64)≤(1/10000000:ℝ) := by
  have hr : 8≤Real.sqrt 64 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(482/25:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_67 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 67)≤(1/10000000:ℝ) := by
  have hr : (1637/200:ℝ)≤Real.sqrt 67 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(394517/20000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_73 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 73)≤(1/10000000:ℝ) := by
  have hr : (1068/125:ℝ)≤Real.sqrt 73 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(64347/3125:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_76 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 76)≤(1/10000000:ℝ) := by
  have hr : (8717/1000:ℝ)≤Real.sqrt 76 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(2100797/100000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_79 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 79)≤(1/10000000:ℝ) := by
  have hr : (1111/125:ℝ)≤Real.sqrt 79 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(267751/12500:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_91 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 91)≤(1/10000000:ℝ) := by
  have hr : (9539/1000:ℝ)≤Real.sqrt 91 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(2298899/100000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_97 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 97)≤(1/10000000:ℝ) := by
  have hr : (1231/125:ℝ)≤Real.sqrt 97 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(296671/12500:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_100 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 100)≤(1/10000000:ℝ) := by
  have hr : 10≤Real.sqrt 100 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(241/10:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_103 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 103)≤(1/10000000:ℝ) := by
  have hr : (2537/250:ℝ)≤Real.sqrt 103 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(611417/25000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_127 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 127)≤(1/10000000:ℝ) := by
  have hr : (11269/1000:ℝ)≤Real.sqrt 127 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(2715829/100000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_133 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 133)≤(1/10000000:ℝ) := by
  have hr : (2883/250:ℝ)≤Real.sqrt 133 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(694803/25000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_139 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 139)≤(1/10000000:ℝ) := by
  have hr : (11789/1000:ℝ)≤Real.sqrt 139 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(2841149/100000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_148 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 148)≤(1/10000000:ℝ) := by
  have hr : (2433/200:ℝ)≤Real.sqrt 148 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(586353/20000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_151 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 151)≤(1/10000000:ℝ) := by
  have hr : (1536/125:ℝ)≤Real.sqrt 151 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(92544/3125:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_193 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 193)≤(1/10000000:ℝ) := by
  have hr : (3473/250:ℝ)≤Real.sqrt 193 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(836993/25000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_196 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 196)≤(1/10000000:ℝ) := by
  have hr : 14≤Real.sqrt 196 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(1687/50:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_217 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 217)≤(1/10000000:ℝ) := by
  have hr : (1473/100:ℝ)≤Real.sqrt 217 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(354993/10000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_primary_exp_271 :
    Real.exp (-(241/100:ℝ)*Real.sqrt 271)≤(1/10000000:ℝ) := by
  have hr : (8231/500:ℝ)≤Real.sqrt 271 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(1983671/50000:ℝ))≤(1/10000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_ramified_exp_1 :
    Real.exp (-(29/4:ℝ)*Real.sqrt 1)≤(28407/40000000:ℝ) := by
  have hr : 1≤Real.sqrt 1 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(29/4:ℝ))≤(28407/40000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_ramified_exp_3 :
    Real.exp (-(29/4:ℝ)*Real.sqrt 3)≤(3521/1000000000:ℝ) := by
  have hr : (433/250:ℝ)≤Real.sqrt 3 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(12557/1000:ℝ))≤(3521/1000000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_ramified_exp_4 :
    Real.exp (-(29/4:ℝ)*Real.sqrt 4)≤(101/200000000:ℝ) := by
  have hr : 2≤Real.sqrt 4 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(29/2:ℝ))≤(101/200000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_ramified_exp_7 :
    Real.exp (-(29/4:ℝ)*Real.sqrt 7)≤(1/200000000:ℝ) := by
  have hr : (529/200:ℝ)≤Real.sqrt 7 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(15341/800:ℝ))≤(1/200000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

lemma cubic_ramified_exp_12 :
    Real.exp (-(29/4:ℝ)*Real.sqrt 12)≤(1/1000000000:ℝ) := by
  have hr : (433/125:ℝ)≤Real.sqrt 12 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : Real.exp (-(12557/500:ℝ))≤(1/1000000000:ℝ) :=
    cubic_exp_neg_le_taylor (by norm_num) (by norm_num) 32
      (by norm_num [Finset.sum_range_succ])
  exact (Real.exp_le_exp.mpr (by nlinarith)).trans he

end CubicFirstMoment

end

end OAI
