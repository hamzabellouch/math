import OAI.Geometry.RCD.Harmonic.QuantitativeAffineMean
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace OAI

/-! # Quantitative quadratic laws from integrated second variation

The second derivative need only be represented by an integrable density.
No pointwise second differentiability is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem quadratic_chord_error_of_integrated_bound
    (F G : ℝ → ℝ) {a b x c D : ℝ} (hab : a<b) (hD : 0≤D) (hx : x∈Icc a b)
    (hF : ∀ t∈Icc a b, DifferentiableAt ℝ F t)
    (hG : ∀ t∈Icc a b, |G t-c|≤D)
    (hint : ∀ u v, a≤u → u≤v → v≤b →
      IntervalIntegrable G volume u v ∧ (∫ t in u..v, G t)=deriv F v-deriv F u) :
    |F x-F a-((F b-F a)/(b-a))*(x-a)-c*(x-a)*(x-b)/2|≤D*(b-a)^2 := by
  let P t := F t-c*t^2/2
  have hp (t : ℝ) : HasDerivAt (fun z : ℝ => c*z^2/2) (c*t) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul c).div_const 2 using 1 <;> simp
    ring
  have hP (t : ℝ) (ht : t∈Icc a b) : HasDerivAt P (deriv F t-c*t) t :=
    (hF t ht).hasDerivAt.sub (hp t)
  have hPint (u v : ℝ) (hu : a≤u) (huv : u≤v) (hv : v≤b) :
      (∫ t in u..v, G t-c)=deriv P v-deriv P u := by
    rw [intervalIntegral.integral_sub (hint u v hu huv hv).1 intervalIntegrable_const,
      intervalIntegral.integral_const,smul_eq_mul,(hint u v hu huv hv).2,
      (hP v ⟨hu.trans huv,hv⟩).deriv,(hP u ⟨hu,huv.trans hv⟩).deriv]
    ring
  have hh := chord_error_le_of_derivative_oscillation hab hD hx
    (fun t ht => (hP t ht).differentiableAt)
    (fun u hu v hv => integrated_derivative_oscillation hD hG hPint hu hv)
  convert hh using 1
  congr 1
  dsimp only [P]
  field_simp [(sub_pos.mpr hab).ne']
  ring

theorem quadratic_limit_chord_error
    (F G : ℕ → ℝ → ℝ) (f : ℝ → ℝ) {a b x c D : ℝ}
    (hab : a<b) (hD : 0≤D) (hx : x∈Icc a b)
    (hF : ∀ k t, t∈Icc a b → DifferentiableAt ℝ (F k) t)
    (hint : ∀ k u v, a≤u → u≤v → v≤b →
      IntervalIntegrable (G k) volume u v ∧ (∫ t in u..v, G k t)=deriv (F k) v-deriv (F k) u)
    (hG : ∀ ε : ℝ, 0<ε → ∀ᶠ k in atTop, ∀ t∈Icc a b, |G k t-c|≤D+ε)
    (hval : ∀ t∈Icc a b, Tendsto (fun k => F k t) atTop (𝓝 (f t))) :
    |f x-f a-((f b-f a)/(b-a))*(x-a)-c*(x-a)*(x-b)/2|≤D*(b-a)^2 := by
  have hlim := ((((hval x hx).sub (hval a (left_mem_Icc.mpr hab.le))).sub
    ((((hval b (right_mem_Icc.mpr hab.le)).sub (hval a (left_mem_Icc.mpr hab.le))).div_const
      (b-a)).mul_const (x-a))).sub_const (c*(x-a)*(x-b)/2)).abs
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/((b-a)^2+1)
  have hδ : 0<δ := div_pos hε (by positivity)
  have he : δ*((b-a)^2+1)=ε := div_mul_cancel₀ ε (by positivity)
  have hh : ∀ᶠ k in atTop,
      |F k x-F k a-((F k b-F k a)/(b-a))*(x-a)-c*(x-a)*(x-b)/2|≤(D+δ)*(b-a)^2 := by
    filter_upwards [hG δ hδ] with k hk
    exact quadratic_chord_error_of_integrated_bound (F k) (G k) hab (by positivity) hx
      (hF k) hk (hint k)
  have hle := le_of_tendsto hlim hh
  nlinarith only [hle,he,hδ]

end RegularPointCoordinates

end

end OAI
