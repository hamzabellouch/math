import OAI.NumberTheory.CubicMoment.Estimates.HeightEndpointProfile

namespace OAI

/-! A fixed Schwartz function localized in a genuine dyadic height window.
The normalized profile and its scaled second derivative decay like 1/T. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff Topology
namespace CubicFirstMoment

lemma heightWindow_compact {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (heightWindow T) := by
  have hs : tsupport (heightWindow T) ⊆ dyadicHeightSupport T := by
    apply closure_minimal _ (isClosed_Icc.union isClosed_Icc)
    intro t ht
    by_contra hh
    exact ht (heightWindow_zero hT hh)
  exact (isCompact_Icc.union isCompact_Icc).of_isClosed_subset isClosed_closure hs

def heightWindowSchwartz : SchwartzMap ℝ ℂ :=
  (heightWindow_compact (by norm_num : (0:ℝ) < 1)).toSchwartzMap (heightWindow_smooth 1)

def schwartzHeightWindow (f : SchwartzMap ℝ ℂ) (T t : ℝ) : ℂ :=
  (T:ℂ)*f t*heightWindow T t

lemma schwartzHeightWindow_smooth (f : SchwartzMap ℝ ℂ) (T : ℝ) :
    ContDiff ℝ ∞ (schwartzHeightWindow f T) :=
  (contDiff_const.mul f.smooth').mul (heightWindow_smooth T)

lemma schwartzHeightWindow_zero (f : SchwartzMap ℝ ℂ) {T : ℝ} (hT : 0 < T)
    (t : ℝ) (ht : t ∉ dyadicHeightSupport T) : schwartzHeightWindow f T t = 0 := by
  simp only [schwartzHeightWindow,heightWindow_zero hT ht,mul_zero]

lemma schwartzHeightWindow_tsupport (f : SchwartzMap ℝ ℂ) {T : ℝ} (hT : 0 < T) :
    tsupport (schwartzHeightWindow f T) ⊆ dyadicHeightSupport T := by
  apply closure_minimal _ (isClosed_Icc.union isClosed_Icc)
  intro t ht
  by_contra hh
  exact ht (schwartzHeightWindow_zero f hT t hh)

lemma schwartzHeightWindow_compact (f : SchwartzMap ℝ ℂ) {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (schwartzHeightWindow f T) :=
  (isCompact_Icc.union isCompact_Icc).of_isClosed_subset isClosed_closure
    (schwartzHeightWindow_tsupport f hT)

lemma schwartzHeightWindow_derivatives (f : SchwartzMap ℝ ℂ) {T : ℝ} (hT : 0 < T) :
    Integrable (schwartzHeightWindow f T) ∧
    Differentiable ℝ (schwartzHeightWindow f T) ∧
    Integrable (deriv (schwartzHeightWindow f T)) ∧
    Differentiable ℝ (deriv (schwartzHeightWindow f T)) ∧
    Integrable (deriv (deriv (schwartzHeightWindow f T))) := by
  have hs := schwartzHeightWindow_smooth f T
  have hd := (contDiff_infty_iff_deriv.mp hs).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hc := schwartzHeightWindow_compact f hT
  exact ⟨hs.continuous.integrable_of_hasCompactSupport hc,
    hs.differentiable (by simp),hd.continuous.integrable_of_hasCompactSupport hc.deriv,
    hd.differentiable (by simp),hdd.continuous.integrable_of_hasCompactSupport hc.deriv.deriv⟩

lemma schwartzHeightWindow_second_zero (f : SchwartzMap ℝ ℂ) {T : ℝ} (hT : 0 < T)
    (t : ℝ) (ht : t ∉ dyadicHeightSupport T) :
    deriv (deriv (schwartzHeightWindow f T)) t = 0 := by
  apply deriv_of_notMem_tsupport
  intro hh
  exact ht (schwartzHeightWindow_tsupport f hT (tsupport_deriv_subset hh))

lemma schwartzHeightWindow_norm_bound (f : SchwartzMap ℝ ℂ) {T : ℝ} (hT : 0 < T)
    (t : ℝ) :
    ‖schwartzHeightWindow f T t‖ ≤ SchwartzMap.seminorm ℝ 2 0 f/T := by
  by_cases ht : t ∈ dyadicHeightSupport T
  · have htl : T ≤ |t| := by
      rcases ht with ht | ht
      · exact ht.1.trans (le_abs_self t)
      · exact (by linarith [ht.2] : T ≤ -t).trans (neg_le_abs t)
    have hf := SchwartzMap.le_seminorm' ℝ 2 0 f t
    simp only [iteratedDeriv_zero] at hf
    have hb : T^2*‖f t‖ ≤ SchwartzMap.seminorm ℝ 2 0 f :=
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT.le htl 2) (_root_.norm_nonneg _)).trans hf
    rw [schwartzHeightWindow,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hT.le]
    apply (mul_le_mul_of_nonneg_left (heightWindow_norm_le T t) (by positivity : 0 ≤ T*‖f t‖)).trans
    rw [mul_one]
    apply (le_div_iff₀ hT).mpr
    nlinarith only [hb]
  · rw [schwartzHeightWindow_zero f hT t ht,norm_zero]
    exact div_nonneg (apply_nonneg _ _) hT.le

lemma heightWindow_iteratedDeriv_bound {T : ℝ} (hT : 0 < T) (i : ℕ) (t : ℝ) :
    ‖iteratedDeriv i (heightWindow T) t‖ ≤
      SchwartzMap.seminorm ℝ 0 i heightWindowSchwartz/T^i := by
  have he : heightWindow T = fun x => heightWindowSchwartz (T⁻¹*x) := by
    change heightWindow T = fun x => heightWindow 1 (T⁻¹*x)
    funext x
    simpa only [div_eq_mul_inv,mul_comm T⁻¹] using heightWindow_dilation hT x
  rw [he,iteratedDeriv_comp_const_smul (heightWindowSchwartz.smooth i),norm_smul,
    Real.norm_eq_abs,abs_pow,abs_inv,abs_of_pos hT]
  have hb := SchwartzMap.le_seminorm' ℝ 0 i heightWindowSchwartz (T⁻¹*t)
  simp only [pow_zero,one_mul] at hb
  apply (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (T⁻¹)^i)).trans_eq
  rw [inv_pow,div_eq_mul_inv,mul_comm]

lemma schwartz_derivative_on_height (f : SchwartzMap ℝ ℂ) {T t : ℝ}
    (hT : 0 < T) (ht : T ≤ |t|) (i : ℕ) :
    ‖iteratedDeriv i f t‖ ≤ SchwartzMap.seminorm ℝ (i+2) i f/T^(i+2) := by
  apply (le_div_iff₀ (pow_pos hT _)).mpr
  have hb := SchwartzMap.le_seminorm' ℝ (i+2) i f t
  calc
    _ = T^(i+2)*‖iteratedDeriv i f t‖ := by ring
    _ ≤ |t|^(i+2)*‖iteratedDeriv i f t‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT.le ht _) (_root_.norm_nonneg _)
    _ ≤ _ := hb

lemma schwartzHeightWindow_second_bound (f : SchwartzMap ℝ ℂ) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℝ, 0 < T → ∀ t : ℝ,
      ‖(T:ℂ)^2*deriv (deriv (schwartzHeightWindow f T)) t‖ ≤ K/T := by
  let Q := fun i : ℕ => ((2:ℕ).choose i:ℝ)*
    SchwartzMap.seminorm ℝ (i+2) i f*SchwartzMap.seminorm ℝ 0 (2-i) heightWindowSchwartz
  let K := 1+∑ i ∈ Finset.range 3, Q i
  have hQ : ∀ i, 0 ≤ Q i := fun i => by dsimp [Q]; positivity
  have hK : 0 < K := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range 3) => hQ i)
    dsimp only [K]
    linarith
  refine ⟨K,hK,?_⟩
  intro T hT t
  by_cases ht : t ∈ dyadicHeightSupport T
  · have htl : T ≤ |t| := by
      rcases ht with ht | ht
      · exact ht.1.trans (le_abs_self t)
      · exact (by linarith [ht.2] : T ≤ -t).trans (neg_le_abs t)
    let z := fun i : ℕ => ((2:ℕ).choose i:ℂ)*iteratedDeriv i f t*
      iteratedDeriv (2-i) (heightWindow T) t
    have hz (i : ℕ) (hi : i ∈ Finset.range 3) : T^3*‖z i‖ ≤ Q i/T := by
      have hi2 : i ≤ 2 := by have := Finset.mem_range.mp hi; omega
      have hf := schwartz_derivative_on_height f hT htl i
      have hw := heightWindow_iteratedDeriv_bound hT (2-i) t
      dsimp only [z]
      rw [norm_mul,norm_mul,Complex.norm_natCast]
      calc
        _ ≤ T^3*(((2:ℕ).choose i:ℝ)*
            (SchwartzMap.seminorm ℝ (i+2) i f/T^(i+2))*
            (SchwartzMap.seminorm ℝ 0 (2-i) heightWindowSchwartz/T^(2-i))) := by
          gcongr
        _ = Q i/T := by
          dsimp only [Q]
          interval_cases i <;> norm_num <;> field_simp
    have he : schwartzHeightWindow f T = fun x => (T:ℂ)*(f x*heightWindow T x) := by
      funext x
      simp only [schwartzHeightWindow,mul_assoc]
    have hp := iteratedDeriv_mul (n := 2) (x := t) (f.smooth 2).contDiffAt
      ((heightWindow_smooth T).of_le (by simp)).contDiffAt
    have hd : iteratedDeriv 2 (schwartzHeightWindow f T) t =
        (T:ℂ)*∑ i ∈ Finset.range 3, z i := by
      rw [he,iteratedDeriv_const_mul_field]
      change iteratedDeriv 2 (fun x => f x*heightWindow T x) t = _ at hp
      rw [hp]
    have hd' : deriv (deriv (schwartzHeightWindow f T)) t =
        (T:ℂ)*∑ i ∈ Finset.range 3, z i := by
      simpa only [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] using hd
    rw [hd',norm_mul,norm_pow,norm_mul,Complex.norm_real,Real.norm_of_nonneg hT.le]
    calc
      _ = T^3*‖∑ i ∈ Finset.range 3, z i‖ := by ring
      _ ≤ T^3*∑ i ∈ Finset.range 3, ‖z i‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = ∑ i ∈ Finset.range 3, T^3*‖z i‖ := by rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range 3, Q i/T := Finset.sum_le_sum hz
      _ = (∑ i ∈ Finset.range 3, Q i)/T := by rw [Finset.sum_div]
      _ ≤ K/T := div_le_div_of_nonneg_right (by dsimp [K]; linarith) hT.le
  · rw [schwartzHeightWindow_second_zero f hT t ht,mul_zero,norm_zero]
    positivity

end CubicFirstMoment

end

end OAI
