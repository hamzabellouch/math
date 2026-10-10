import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterEuler
import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeMass

namespace OAI

/-! Moving the finite character Euler product from Re(s)=1 to
Re(s)=1+delta costs a bounded amount when delta=1/log X. All constants
are independent of the character modulus and of the imaginary part. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical ComplexConjugate

lemma mrt_log_lipschitz_half {a b : ℝ} (ha : 1/2≤a) (hb : 1/2≤b) :
    |Real.log a-Real.log b|≤2*|a-b| := by
  have ha0 : 0<a := by linarith
  have hb0 : 0<b := by linarith
  have upper {x y : ℝ} (hx : 0<x) (hy : 1/2≤y) :
      Real.log x-Real.log y≤2*|x-y| := by
    have hy0 : 0<y := by linarith
    calc
      _ = Real.log (x/y) := (Real.log_div (ne_of_gt hx) (ne_of_gt hy0)).symm
      _ ≤ x/y-1 := Real.log_le_sub_one_of_pos (div_pos hx hy0)
      _ = (x-y)/y := by field_simp
      _ ≤ |x-y|/y := div_le_div_of_nonneg_right (le_abs_self _) (le_of_lt hy0)
      _ ≤ 2*|x-y| := (div_le_iff₀ hy0).mpr (by nlinarith [abs_nonneg (x-y)])
  apply abs_le.mpr
  constructor
  · have hh := upper hb0 ha
    rw [abs_sub_comm b a] at hh
    linarith
  · exact upper ha0 hb

lemma mrt_local_euler_log_lipschitz {z w : ℂ}
    (hz : ‖z‖≤1/2) (hw : ‖w‖≤1/2) :
    |Real.log ‖(1-z)⁻¹‖-Real.log ‖(1-w)⁻¹‖|≤2*‖z-w‖ := by
  have hza : 1/2≤‖(1:ℂ)-z‖ := by
    have hh := norm_sub_norm_le (1:ℂ) z
    rw [norm_one] at hh
    linarith
  have hwa : 1/2≤‖(1:ℂ)-w‖ := by
    have hh := norm_sub_norm_le (1:ℂ) w
    rw [norm_one] at hh
    linarith
  have hn : |‖(1:ℂ)-z‖-‖(1:ℂ)-w‖|≤‖z-w‖ := by
    have hh := abs_norm_sub_norm_le ((1:ℂ)-z) ((1:ℂ)-w)
    rw [show (1-z)-(1-w)=w-z by ring, norm_sub_rev w z] at hh
    exact hh
  calc
    _ = |Real.log ‖(1:ℂ)-z‖-Real.log ‖(1:ℂ)-w‖| := by
      rw [norm_inv,norm_inv,Real.log_inv,Real.log_inv,neg_sub_neg,abs_sub_comm]
    _ ≤ 2*|‖(1:ℂ)-z‖-‖(1:ℂ)-w‖| := mrt_log_lipschitz_half hza hwa
    _ ≤ 2*‖z-w‖ := mul_le_mul_of_nonneg_left hn (by norm_num)

noncomputable def mrtCharacterShiftedEuler {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t δ : ℝ) (S : Finset ℕ) : ℂ :=
  ∏ p ∈ S, (1-(characterTwist χ t p/(p:ℂ))*
    (Real.exp (-δ*Real.log (p:ℝ)):ℂ))⁻¹

lemma mrt_character_euler_shift_local {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {δ : ℝ} (hδ : 0≤δ) {p : ℕ} (hp : p.Prime) :
    |Real.log ‖(1-characterTwist χ t p/(p:ℂ))⁻¹‖-
      Real.log ‖(1-(characterTwist χ t p/(p:ℂ))*
        (Real.exp (-δ*Real.log (p:ℝ)):ℂ))⁻¹‖| ≤
          2*δ*(Real.log (p:ℝ)/(p:ℝ)) := by
  let z : ℂ := characterTwist χ t p/(p:ℂ)
  let r : ℝ := Real.exp (-δ*Real.log (p:ℝ))
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hl : 0≤Real.log (p:ℝ) := Real.log_nonneg (by linarith)
  have hr0 : 0≤r := (Real.exp_pos _).le
  have hr1 : r≤1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hr : 1-r≤δ*Real.log (p:ℝ) := by
    have hh := Real.add_one_le_exp (-δ*Real.log (p:ℝ))
    dsimp only [r]
    linarith
  have hz : ‖z‖≤1/(p:ℝ) := by
    dsimp only [z]
    rw [norm_div,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (characterTwist_norm_le_one χ t p) hp0.le
  have hz2 : ‖z‖≤1/2 := hz.trans (one_div_le_one_div_of_le (by norm_num) hp2)
  have hzr : ‖z*(r:ℂ)‖≤1/2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0]
    exact (mul_le_of_le_one_right (norm_nonneg z) hr1).trans hz2
  have hd : ‖z-z*(r:ℂ)‖≤δ*(Real.log (p:ℝ)/(p:ℝ)) := by
    calc
      _ = ‖z‖*(1-r) := by
        rw [show z-z*(r:ℂ)=z*(1-(r:ℂ)) by ring, norm_mul,
          ← Complex.ofReal_one, ← Complex.ofReal_sub,
          Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hr1)]
      _ ≤ (1/(p:ℝ))*(δ*Real.log (p:ℝ)) :=
        mul_le_mul hz hr (sub_nonneg.mpr hr1) (by positivity)
      _ = _ := by ring
  exact (mrt_local_euler_log_lipschitz hz2 hzr).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ)≤2))

theorem mrt_character_euler_shift_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) {δ : ℝ} (hδ : 0≤δ) (X : ℕ) (S : Finset ℕ)
    (hS : S⊆primesUpTo X) :
    |Real.log ‖mrtCharacterPrimeEuler χ t S‖-
      Real.log ‖mrtCharacterShiftedEuler χ t δ S‖| ≤
        2*δ*(∑ p ∈ S, Real.log (p:ℝ)/(p:ℝ)) := by
  have hp (p : ℕ) (hh : p∈S) : p.Prime := (mem_filter.mp (hS hh)).2
  have hz (p : ℕ) (hh : p∈S) : ‖characterTwist χ t p/(p:ℂ)‖≤1/2 := by
    rw [norm_div,Complex.norm_natCast]
    have h2 : (2:ℝ)≤p := by exact_mod_cast (hp p hh).two_le
    exact (div_le_div_of_nonneg_right (characterTwist_norm_le_one χ t p)
      (Nat.cast_nonneg p)).trans (one_div_le_one_div_of_le (by norm_num) h2)
  have hr (p : ℕ) (hh : p∈S) :
      0≤Real.exp (-δ*Real.log (p:ℝ)) ∧ Real.exp (-δ*Real.log (p:ℝ))≤1 := by
    refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr ?_⟩
    have h1 : (1:ℝ)≤p := by exact_mod_cast (hp p hh).one_le
    nlinarith [Real.log_nonneg h1]
  have hne {z : ℂ} (hh : ‖z‖≤1/2) : 1-z≠0 := by
    intro he
    have he' : z=1 := (sub_eq_zero.mp he).symm
    rw [he',norm_one] at hh
    norm_num at hh
  have hns (p : ℕ) (hh : p∈S) :
      1-(characterTwist χ t p/(p:ℂ))*(Real.exp (-δ*Real.log (p:ℝ)):ℂ)≠0 := by
    apply hne
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hr p hh).1]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hr p hh).2).trans (hz p hh)
  have hlog1 : Real.log ‖mrtCharacterPrimeEuler χ t S‖ =
      ∑ p ∈ S, Real.log ‖(1-characterTwist χ t p/(p:ℂ))⁻¹‖ := by
    rw [mrtCharacterPrimeEuler,norm_prod]
    exact Real.log_prod (fun p hh => norm_ne_zero_iff.mpr (inv_ne_zero (hne (hz p hh))))
  have hlog2 : Real.log ‖mrtCharacterShiftedEuler χ t δ S‖ =
      ∑ p ∈ S, Real.log ‖(1-(characterTwist χ t p/(p:ℂ))*
        (Real.exp (-δ*Real.log (p:ℝ)):ℂ))⁻¹‖ := by
    rw [mrtCharacterShiftedEuler,norm_prod]
    exact Real.log_prod (fun p hh => norm_ne_zero_iff.mpr (inv_ne_zero (hns p hh)))
  rw [hlog1,hlog2,← sum_sub_distrib,Finset.mul_sum]
  exact (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum (fun p hh => mrt_character_euler_shift_local χ t hδ (hp p hh)))

theorem mrt_character_euler_logarithmic_shift {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {X : ℕ}
    (hX : 1≤Real.log (X:ℝ)) (S : Finset ℕ) (hS : S⊆primesUpTo X) :
    |Real.log ‖mrtCharacterPrimeEuler χ t S‖-
      Real.log ‖mrtCharacterShiftedEuler χ t (1/Real.log (X:ℝ)) S‖| ≤
        2+2*halaszMertensConstant := by
  have hl0 : 0<Real.log (X:ℝ) := by linarith
  have hX1 : (1:ℝ)≤X := by
    by_contra hh
    have hh' : (X:ℝ)<1 := lt_of_not_ge hh
    have hnatlt : X<1 := by exact_mod_cast hh'
    have hnat : X=0 := by omega
    norm_num [hnat] at hX
  have hs : (∑ p ∈ S, Real.log (p:ℝ)/(p:ℝ))≤
      Real.log (X:ℝ)+halaszMertensConstant := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg hS ?_)
    · simpa only [mrt_sievePrimesUpTo_nat] using halasz_prime_prefix_mass_le hX1
    · intro p hp _
      have hp1 : (1:ℝ)≤p := by exact_mod_cast (mem_filter.mp hp).2.one_le
      exact div_nonneg (Real.log_nonneg hp1) (Nat.cast_nonneg p)
  calc
    _ ≤ 2*(1/Real.log (X:ℝ))*(∑ p ∈ S, Real.log (p:ℝ)/(p:ℝ)) :=
      mrt_character_euler_shift_bound χ t (by positivity) X S hS
    _ ≤ 2*(1/Real.log (X:ℝ))*(Real.log (X:ℝ)+halaszMertensConstant) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 2+2*halaszMertensConstant/Real.log (X:ℝ) := by
      field_simp [ne_of_gt hl0]
    _ ≤ 2+2*halaszMertensConstant := by
      have hh := div_le_self
        (mul_nonneg (by norm_num : (0:ℝ)≤2) halaszMertensConstant_nonneg) hX
      linarith

end TwoPointCorrelations

end OAI
