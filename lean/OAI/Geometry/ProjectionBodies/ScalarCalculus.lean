import OAI.Geometry.ProjectionBodies.ScalarBounds

namespace OAI

noncomputable section
open Set Filter Topology
namespace PettyProjection.Scalar

lemma hasDerivAt_inverse_pow (n : ℕ) {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (fun x : ℝ => (x⁻¹) ^ n) (-(n : ℝ) * (z⁻¹) ^ (n + 1)) z := by
  have h := hasDerivAt_zpow (-(n : ℤ)) z (Or.inl hz)
  have he : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by omega
  simpa only [he, zpow_neg, zpow_natCast, inv_pow, Int.cast_neg, Int.cast_natCast] using h

lemma hasDerivAt_e {n : ℕ} (hn : n ≠ 0) {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (e n) (-(z⁻¹) ^ (n + 1)) z := by
  have h := ((hasDerivAt_inverse_pow n hz).sub_const 1).div_const (n : ℝ)
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  convert! h using 1
  field_simp

lemma hasDerivAt_M {n : ℕ} (hn : n ≠ 0) {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (M n) ((exponent n : ℝ) * (z ^ (exponent n - 1) - (z⁻¹) ^ (n + 1))) z := by
  have h := ((hasDerivAt_pow (exponent n) z).sub_const 1).add
    ((hasDerivAt_e hn hz).const_mul (exponent n : ℝ))
  convert! h using 1
  ring

lemma M_one (n : ℕ) : M n 1 = 0 := by simp [M, e]

lemma paste_hasDerivAt {f f' : ℝ → ℝ}
    (hf : ∀ x, 1 ≤ x → HasDerivAt f (f' x) x) (hf1 : f 1 = 0) (hf'1 : f' 1 = 0)
    (x : ℝ) :
    HasDerivAt (fun z => if 1 < z then f z else 0) (if 1 < x then f' x else 0) x := by
  rcases lt_trichotomy x 1 with hx | rfl | hx
  · have he : (fun z => if 1 < z then f z else 0) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds hx] with z hz
      simp only [ite_eq_right (not_lt.mpr hz.le)]
    simpa only [ite_eq_right (not_lt.mpr hx.le)] using (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he
  · have hl : HasDerivWithinAt (fun z => if 1 < z then f z else 0) 0 (Iic 1) 1 := by
      apply (hasDerivAt_const 1 (0 : ℝ)).hasDerivWithinAt.congr
      · intro z hz
        simp only [ite_eq_right (not_lt.mpr (show z ≤ 1 from hz))]
      · simp
    have hr : HasDerivWithinAt (fun z => if 1 < z then f z else 0) 0 (Ici 1) 1 := by
      have h := (hf 1 le_rfl).hasDerivWithinAt (s := Ici 1)
      rw [hf'1] at h
      apply h.congr
      · intro z hz
        rcases lt_or_eq_of_le (show 1 ≤ z from hz) with hz | rfl
        · simp only [ite_eq_left hz]
        · simp [hf1]
      · simp [hf1]
    have h := hl.union hr
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at h
    simpa using h
  · have he : (fun z => if 1 < z then f z else 0) =ᶠ[𝓝 x] f := by
      filter_upwards [eventually_gt_nhds hx] with z hz
      simp only [ite_eq_left hz]
    simpa only [ite_eq_left hx] using (hf x hx.le).congr_of_eventuallyEq he

lemma paste_contDiff_one {f f' : ℝ → ℝ}
    (hf : ∀ x, 1 ≤ x → HasDerivAt f (f' x) x) (hf1 : f 1 = 0) (hf'1 : f' 1 = 0)
    (hcont : ContinuousOn f' (Ici 1)) :
    ContDiff ℝ 1 (fun z => if 1 < z then f z else 0) := by
  have hd := paste_hasDerivAt hf hf1 hf'1
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun x => (hd x).differentiableAt
  · have he : deriv (fun z => if 1 < z then f z else 0) =
        (fun z => if z ≤ 1 then 0 else f' z) := by
      funext z
      rw [(hd z).deriv]
      simp only [← not_le, ite_not]
    rw [he]
    exact continuous_if_le continuous_id continuous_const continuousOn_const hcont
      (fun x hx => by change x = 1 at hx; subst x; exact hf'1.symm)

end PettyProjection.Scalar
end

noncomputable section
open Set Filter Topology
namespace PettyProjection.Scalar

def Mprime (n : ℕ) (z : ℝ) : ℝ :=
  (exponent n : ℝ) * (z ^ (exponent n - 1) - (z⁻¹) ^ (n + 1))

def Iformula (n : ℕ) (z : ℝ) : ℝ :=
  (exponent n : ℝ)^2 *
    ((z ^ (2 * exponent n - 1) - 1) / (2 * exponent n - 1 : ℕ) -
      2 * (1 - (z⁻¹) ^ (n + 1 - exponent n)) / (n + 1 - exponent n : ℕ) +
      (1 - (z⁻¹) ^ (2 * n + 1)) / (2 * n + 1 : ℕ))

lemma hasDerivAt_Iformula_four {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (Iformula 4) (Mprime 4 z ^ 2) z := by
  have h := ((((hasDerivAt_pow 1 z).sub_const 1).div_const 1).sub
    (((hasDerivAt_inverse_pow 4 hz).const_sub 1).const_mul 2 |>.div_const 4)).add
    (((hasDerivAt_inverse_pow 9 hz).const_sub 1).div_const 9)
  convert! h using 1
  · funext x
    simp [Iformula, exponent]
  · simp only [Mprime, exponent]
    norm_num
    rw [show 10 = 5 * 2 by omega, pow_mul]
    ring

lemma hasDerivAt_Iformula_other {n : ℕ} (hn : 4 ≤ n) (hne : n ≠ 4)
    {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (Iformula n) (Mprime n z ^ 2) z := by
  have hn1 : (n - 1 : ℝ) ≠ 0 := by
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hn2 : (2 * n + 1 : ℝ) ≠ 0 := by positivity
  have h := (((((hasDerivAt_pow 3 z).sub_const 1).div_const 3).sub
    (((hasDerivAt_inverse_pow (n-1) hz).const_sub 1).const_mul 2 |>.div_const (n-1 : ℝ))).add
    (((hasDerivAt_inverse_pow (2*n+1) hz).const_sub 1).div_const (2*n+1 : ℝ))).const_mul 4
  have he : n + 1 - 2 = n - 1 := by omega
  have he' : n - 1 + 1 = n := by omega
  have hncast : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hi := z_mul_inverse_pow_succ hz n
  have hp : (z⁻¹) ^ (2*n+1+1) = ((z⁻¹) ^ (n+1)) ^ 2 := by
    rw [show 2*n+1+1 = (n+1)*2 by omega, pow_mul]
  convert! h using 1
  · funext x
    simp only [Iformula, exponent, ite_eq_right hne, Nat.reduceMul, Nat.reduceSub,
      Nat.cast_ofNat, he, hncast, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Pi.add_apply, Pi.sub_apply]
    norm_num
  · simp only [Mprime, exponent, ite_eq_right hne]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, Nat.reducePow, pow_one,
      Nat.cast_add, Nat.cast_mul, hncast, he', hp]
    field_simp
    simp only [one_div]
    nlinarith only [hi]

lemma hasDerivAt_Iformula {n : ℕ} (hn : 4 ≤ n) {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (Iformula n) (Mprime n z ^ 2) z := by
  by_cases hne : n = 4
  · subst n; exact hasDerivAt_Iformula_four hz
  · exact hasDerivAt_Iformula_other hn hne hz

lemma Mprime_one (n : ℕ) : Mprime n 1 = 0 := by simp [Mprime]
lemma Iformula_one (n : ℕ) : Iformula n 1 = 0 := by simp [Iformula]

lemma continuousOn_Mprime (n : ℕ) : ContinuousOn (Mprime n) (Ici 1) := by
  apply continuousOn_const.mul
  apply (continuousOn_id.pow _).sub
  exact (continuousOn_id.inv₀ (fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx))).pow _

lemma contDiff_G {n : ℕ} (hn : 4 ≤ n) : ContDiff ℝ 1 (G n) := by
  apply paste_contDiff_one (f' := fun z => beta n * Mprime n z)
  · intro x hx
    exact (hasDerivAt_M (by omega) (ne_of_gt (lt_of_lt_of_le zero_lt_one hx))).const_mul _
  · simp [M_one]
  · simp [Mprime_one]
  · exact continuousOn_const.mul (continuousOn_Mprime n)

lemma contDiff_I {n : ℕ} (hn : 4 ≤ n) : ContDiff ℝ 1 (I n) := by
  exact paste_contDiff_one (f' := fun z => Mprime n z ^ 2)
    (fun x hx => hasDerivAt_Iformula hn (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)))
    (Iformula_one n) (by simp [Mprime_one]) ((continuousOn_Mprime n).pow 2)

lemma deriv_G {n : ℕ} (hn : 4 ≤ n) (z : ℝ) :
    deriv (G n) z = if 1 < z then beta n * Mprime n z else 0 :=
  (paste_hasDerivAt (f' := fun z => beta n * Mprime n z)
    (fun x hx => (hasDerivAt_M (by omega) (ne_of_gt (lt_of_lt_of_le zero_lt_one hx))).const_mul _)
    (by simp [M_one]) (by simp [Mprime_one]) z).deriv

lemma deriv_I {n : ℕ} (hn : 4 ≤ n) (z : ℝ) :
    deriv (I n) z = if 1 < z then Mprime n z ^ 2 else 0 :=
  (paste_hasDerivAt (f' := fun z => Mprime n z ^ 2)
    (fun x hx => hasDerivAt_Iformula hn (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)))
    (Iformula_one n) (by simp [Mprime_one]) z).deriv

lemma derivative_relation {n : ℕ} (hn : 4 ≤ n) (z : ℝ) :
    deriv (G n) z ^ 2 = beta n ^ 2 * deriv (I n) z := by
  rw [deriv_G hn, deriv_I hn]
  split_ifs <;> ring

lemma I_nonneg {n : ℕ} (hn : 4 ≤ n) (z : ℝ) : 0 ≤ I n z := by
  by_cases hz : 1 < z
  · have hmono : Monotone (I n) := by
      apply monotone_of_deriv_nonneg ((contDiff_I hn).differentiable (by norm_num))
      intro x
      rw [deriv_I hn]
      split_ifs <;> positivity
    have h := hmono hz.le
    simpa [I] using h
  · simp [I, hz]

end PettyProjection.Scalar
end

noncomputable section
open Set
namespace PettyProjection.Scalar

lemma convex_tangent_bound {f : ℝ → ℝ} {S : Set ℝ} {x y f' : ℝ}
    (hc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f f' x) :
    f x + f' * (y - x) ≤ f y := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hh := hc.le_slope_of_hasDerivAt hx hy h hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hh
    linarith
  · simp
  · have hh := hc.slope_le_of_hasDerivAt hy hx h hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hh
    nlinarith

lemma inverse_pow_tangent (n : ℕ) {z : ℝ} (hz : 0 < z) :
    1 + (n : ℝ) * (1 - z) ≤ (z⁻¹) ^ n := by
  have hc : ConvexOn ℝ (Ioi 0) (fun x : ℝ => (x⁻¹) ^ n) := by
    simpa only [zpow_neg, zpow_natCast, inv_pow] using (convexOn_zpow (-(n : ℤ)) (𝕜 := ℝ))
  have hd : HasDerivAt (fun x : ℝ => (x⁻¹) ^ n) (-(n : ℝ)) 1 := by
    simpa only [inv_one, one_pow, mul_one] using hasDerivAt_inverse_pow n (one_ne_zero : (1 : ℝ) ≠ 0)
  have h := convex_tangent_bound hc (show (1 : ℝ) ∈ Ioi 0 by norm_num) hz hd
  simp only [inv_one, one_pow] at h
  nlinarith only [h]

lemma e_lower {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : 0 < z) : 1 - z ≤ e n z := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [e, le_div_iff₀ hn']
  nlinarith only [inverse_pow_tangent n hz]

lemma M_nonneg {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : 0 < z) : 0 ≤ M n z := by
  have h := e_lower hn hz
  unfold M exponent
  split_ifs <;> norm_num <;> nlinarith [sq_nonneg (z-1)]

lemma G_bounds {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : 0 < z) :
    0 ≤ G n z ∧ G n z ≤ beta n * M n z := by
  have hm := M_nonneg hn hz
  have hb := (beta_pos n).le
  unfold G
  split_ifs <;> constructor <;> nlinarith

lemma W_mean_expression (n : ℕ) (z : ℝ) :
    W n z = (z ^ exponent n - 1) - (z ^ (exponent n - 1) - 1) + e n z := by
  unfold W
  ring

end PettyProjection.Scalar
end

end OAI
