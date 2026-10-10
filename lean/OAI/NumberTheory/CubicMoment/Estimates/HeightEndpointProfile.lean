import OAI.NumberTheory.CubicMoment.Estimates.HeightEndpointRegularity

namespace OAI

/-! A fixed compact profile removes the reciprocal singularity. Dilating
this profile gives the normalized endpoint weights used in localization. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def endpointProfile : SchwartzMap ℝ ℂ :=
  (localizedEndpointWeight_compact (2/Real.pi) (by norm_num : (0:ℝ) < 1)).toSchwartzMap
    (localizedEndpointWeight_smooth (2/Real.pi) (by norm_num : (0:ℝ) < 1))

lemma endpointProfile_eq (x : ℝ) :
    endpointProfile x = heightWindow 1 x/((x:ℂ)*Complex.I) := by
  change localizedEndpointWeight (2/Real.pi) 1 x = _
  by_cases hx : x ∈ dyadicHeightSupport 1
  · have hnorm : |x| ≤ 2 := by
      rcases hx with hx | hx
      · exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have he : (x/(2*Real.pi))/(2/Real.pi) = x/4 := by field_simp; ring
    have hf : frequencyCutoff ((x/(2*Real.pi))/(2/Real.pi)) = 1 := by
      rw [he]
      apply frequencyCutoff_one
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 4)]
      linarith
    simp only [localizedEndpointWeight, hf, Complex.ofReal_one, one_mul]
    ring
  · rw [localizedEndpointWeight_zero _ (by norm_num) _ hx,
      heightWindow_zero (by norm_num) hx, zero_div]

lemma heightWindow_dilation {T : ℝ} (hT : 0 < T) (t : ℝ) :
    heightWindow T t = heightWindow 1 (t/T) := by
  have he : t/((3/2)*T) = (t/T)/((3/2)*1)  := by field_simp [hT.ne']
  simp only [heightWindow, he, mul_one, div_one]

lemma localizedEndpointWeight_dilation {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (t : ℝ) :
    localizedEndpointWeight S T t =
      frequencyCutoff ((T/(2*Real.pi*S))*(t/T))*endpointProfile (t/T) := by
  have hf : (T/(2*Real.pi*S))*(t/T) = (t/(2*Real.pi))/S := by field_simp
  rw [hf, endpointProfile_eq, ← heightWindow_dilation hT]
  unfold localizedEndpointWeight
  by_cases ht : t = 0
  · subst t
    simp
  · have hc : (T:ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have htc : (t:ℂ) ≠ 0 := by exact_mod_cast ht
    push_cast
    field_simp

private def secondDerivativeBudget (f : SchwartzMap ℝ ℂ) : ℝ :=
  1+∑ i ∈ Finset.range 3, SchwartzMap.seminorm ℝ 0 i f

private lemma secondDerivativeBudget_pos (f : SchwartzMap ℝ ℂ) :
    0 < secondDerivativeBudget f := by
  have hs : 0 ≤ ∑ i ∈ Finset.range 3, SchwartzMap.seminorm ℝ 0 i f :=
    Finset.sum_nonneg (fun _ _ => apply_nonneg _ _)
  dsimp [secondDerivativeBudget]
  linarith

private lemma norm_iteratedDeriv_le_budget (f : SchwartzMap ℝ ℂ) {i : ℕ}
    (hi : i ≤ 2) (x : ℝ) : ‖iteratedDeriv i f x‖ ≤ secondDerivativeBudget f := by
  have hb := SchwartzMap.le_seminorm' ℝ 0 i f x
  simp only [pow_zero, one_mul] at hb
  have hs : SchwartzMap.seminorm ℝ 0 i f ≤
      ∑ j ∈ Finset.range 3, SchwartzMap.seminorm ℝ 0 j f :=
    Finset.single_le_sum (fun _ _ => apply_nonneg _ _) (Finset.mem_range.mpr (by omega))
  exact hb.trans (by dsimp [secondDerivativeBudget]; linarith)

/-- Only two derivatives are needed for the far-cell integration by parts. -/
lemma scaled_schwartz_product_second_bound (f g : SchwartzMap ℝ ℂ) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ x : ℝ,
      ‖deriv (deriv (fun y => f (a*y)*g y)) x‖ ≤ K := by
  let A := secondDerivativeBudget f
  let B := secondDerivativeBudget g
  have hA : 0 < A := secondDerivativeBudget_pos f
  have hB : 0 < B := secondDerivativeBudget_pos g
  refine ⟨4*A*B, by positivity, ?_⟩
  intro a ha ha1 x
  have hf : ContDiff ℝ (2:ℕ) (fun y => f (a*y)) :=
    (f.smooth 2).comp (contDiff_const.mul contDiff_id)
  have he := iteratedDeriv_mul (n := 2) (x := x) hf.contDiffAt (g.smooth 2).contDiffAt
  have hb (i : ℕ) (hi : i ∈ Finset.range 3) :
      ‖((2:ℕ).choose i : ℂ)*iteratedDeriv i (fun y => f (a*y)) x*
          iteratedDeriv (2-i) g x‖ ≤ ((2:ℕ).choose i : ℝ)*A*B := by
    have hi2 : i ≤ 2 := by have := Finset.mem_range.mp hi; omega
    have hfi : ‖iteratedDeriv i (fun y => f (a*y)) x‖ ≤ A := by
      rw [iteratedDeriv_comp_const_smul (f.smooth i), norm_smul, Real.norm_eq_abs,
        abs_pow, abs_of_nonneg ha]
      apply (mul_le_mul (pow_le_one₀ ha ha1) (norm_iteratedDeriv_le_budget f hi2 (a*x))
        (_root_.norm_nonneg _) (by norm_num)).trans_eq
      exact one_mul _
    have hgi : ‖iteratedDeriv (2-i) g x‖ ≤ B :=
      norm_iteratedDeriv_le_budget g (by omega) x
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    gcongr
  have hsum := (norm_sum_le (Finset.range 3) _).trans (Finset.sum_le_sum hb)
  rw [← he] at hsum
  simp only [show 2=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero] at hsum
  norm_num [Finset.sum_range_succ] at hsum
  convert hsum using 1
  ring

theorem localizedEndpointWeight_second_uniform :
    ∃ K : ℝ, 0 < K ∧ ∀ S T : ℝ, 0 < S → 0 < T → T ≤ 2*Real.pi*S →
      ∀ t : ℝ, ‖(T:ℂ)^2*deriv (deriv (localizedEndpointWeight S T)) t‖ ≤ K := by
  obtain ⟨K,hK,hbound⟩ := scaled_schwartz_product_second_bound frequencyCutoff endpointProfile
  refine ⟨K,hK,?_⟩
  intro S T hS hT hTS t
  let a := T/(2*Real.pi*S)
  let q := fun x => frequencyCutoff (a*x)*endpointProfile x
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := (div_le_one (by positivity)).mpr hTS
  have hq : ContDiff ℝ (2:ℕ) q :=
    ((frequencyCutoff.smooth 2).comp (contDiff_const.mul contDiff_id)).mul
      (endpointProfile.smooth 2)
  have he : localizedEndpointWeight S T = fun x => q (T⁻¹*x) := by
    funext x
    simpa only [q,a,div_eq_mul_inv,mul_comm T⁻¹] using
      localizedEndpointWeight_dilation hS hT x
  have hd := congrFun (iteratedDeriv_comp_const_smul (n := 2) hq T⁻¹) t
  simp only [show 2=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero] at hd
  rw [he,hd,norm_mul,norm_pow,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hT,Real.norm_eq_abs,abs_pow,abs_inv,abs_of_pos hT]
  calc
    T^2*(T⁻¹^2*‖deriv (deriv q) (T⁻¹*t)‖) = ‖deriv (deriv q) (T⁻¹*t)‖ := by field_simp
    _ ≤ K := hbound a ha ha1 (T⁻¹*t)

end CubicFirstMoment

end

end OAI
