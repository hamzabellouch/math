import OAI.Analysis.AncientFlat.Evolution.MovingScalar

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace FlatSimilarity
def unitClamp (t : ℝ) : ℝ := max 0 (min t 1)
lemma unitClamp_mem (t : ℝ) : unitClamp t ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le zero_le_one (min_le_right _ _)
lemma unitClamp_eq {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : unitClamp t=t := by
  simp only [unitClamp,min_eq_left ht.2,max_eq_right ht.1]
lemma unitClamp_lipschitz : LipschitzWith 1 unitClamp := by
  convert (LipschitzWith.const (0:ℝ)).max (LipschitzWith.id.min (LipschitzWith.const (1:ℝ))) using 1 <;> first | rfl | norm_num
lemma exp_neg_le_one {t : ℝ} (ht : 0≤t) : Real.exp (-t)≤1 := by
  simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr ht)
lemma exp_neg_lip (s t : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖Real.exp (-t)-Real.exp (-s)‖≤|t-s| := by
  have hd (r : ℝ) : HasDerivAt (fun q : ℝ => Real.exp (-q)) (-Real.exp (-r)) r := by
    simpa using (hasDerivAt_id r).neg.exp
  have hb (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) : ‖-Real.exp (-r)‖≤(1:ℝ) := by
    rw [norm_neg, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact exp_neg_le_one hr.1
  simpa only [one_mul,Real.norm_eq_abs] using
    (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r _ => (hd r).hasDerivWithinAt) hb hs ht
lemma timeweight_bounds {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    0<Real.exp (-t)/16 ∧ ‖Real.exp (-t)/16‖≤1 := by
  constructor
  · positivity
  · rw [Real.norm_of_nonneg (by positivity)]
    have := exp_neg_le_one ht.1
    linarith
lemma timeweight_lip (s t : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖Real.exp (-t)/16-Real.exp (-s)/16‖≤|t-s| := by
  rw [←sub_div,norm_div,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤16)]
  have := exp_neg_lip s t hs ht
  have := abs_nonneg (t-s)
  linarith
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma moving_scalar_joint_lip (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (L : ℝ)
    (hL0 : 0≤L) (hL : ∀ x, ‖fderiv ℝ f x‖≤L) (hE : ∀ x, ‖x‖*‖fderiv ℝ f x‖≤L)
    (t r : ℝ) (ht : t≤1) (x z : V) :
    ‖f (Real.exp (t/4) • x)-f (Real.exp (r/4) • z)‖≤
      (Real.exp (1/4)*L+L)*(‖x-z‖+|t-r|) := by
  have ha := moving_scalar_space_lipschitz f hf L hL0 hL t ht z x
  have hb := moving_scalar_time_lipschitz f hf L hE z r t
  have he : 0≤Real.exp (1/4)*L := mul_nonneg (Real.exp_pos _).le hL0
  calc
    _≤‖f (Real.exp (t/4) • x)-f (Real.exp (t/4) • z)‖+
       ‖f (Real.exp (t/4) • z)-f (Real.exp (r/4) • z)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _≤(Real.exp (1/4)*L)*‖x-z‖+(L/4)*|t-r| := add_le_add ha hb
    _≤_ := by nlinarith [norm_nonneg (x-z),abs_nonneg (t-r),mul_nonneg he (abs_nonneg (t-r)),mul_nonneg hL0 (norm_nonneg (x-z))]
lemma moving_product_joint_lip (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (M L : ℝ)
    (hM0 : 0≤M) (hL0 : 0≤L) (hM : ∀ x, ‖f x‖≤M)
    (hL : ∀ x, ‖fderiv ℝ f x‖≤L) (hE : ∀ x, ‖x‖*‖fderiv ℝ f x‖≤L)
    (t r : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (hr : r ∈ Icc (0:ℝ) 1) (x z : V) :
    ‖Real.exp (-t)/16*f (Real.exp (t/4) • x)-Real.exp (-r)/16*f (Real.exp (r/4) • z)‖≤
      (M+Real.exp (1/4)*L+L)*(‖x-z‖+|t-r|) := by
  have ha := moving_scalar_joint_lip f hf L hL0 hL hE t r ht.2 x z
  have hb := timeweight_lip r t hr ht
  have he := (timeweight_bounds ht).2
  calc
    _=‖Real.exp (-t)/16*(f (Real.exp (t/4) • x)-f (Real.exp (r/4) • z))+
      (Real.exp (-t)/16-Real.exp (-r)/16)*f (Real.exp (r/4) • z)‖ := by congr 1; ring
    _≤‖Real.exp (-t)/16‖*‖f (Real.exp (t/4) • x)-f (Real.exp (r/4) • z)‖+
      ‖Real.exp (-t)/16-Real.exp (-r)/16‖*‖f (Real.exp (r/4) • z)‖ := by
        calc
          _≤‖Real.exp (-t)/16*(f (Real.exp (t/4) • x)-f (Real.exp (r/4) • z))‖+
            ‖(Real.exp (-t)/16-Real.exp (-r)/16)*f (Real.exp (r/4) • z)‖ := norm_add_le _ _
          _=_ := by simp only [norm_mul]
    _≤1*((Real.exp (1/4)*L+L)*(‖x-z‖+|t-r|))+|t-r| * M :=
      add_le_add (mul_le_mul he ha (norm_nonneg _) zero_le_one)
        (mul_le_mul hb (hM _) (norm_nonneg _) (abs_nonneg _))
    _≤_ := by nlinarith [mul_nonneg hM0 (norm_nonneg (x-z))]
end FlatSimilarity

end

end OAI
