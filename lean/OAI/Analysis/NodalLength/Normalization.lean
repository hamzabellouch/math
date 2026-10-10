import OAI.Analysis.NodalLength.Energy

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

open Filter in
lemma sqrt_div_tendsto_zero {S D : ℕ → ℝ}
    (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j) (hSinf : Tendsto S atTop atTop) :
    Tendsto (fun j => Real.sqrt (S j) / D j) atTop (𝓝 0) := by
  have hbound (j : ℕ) : Real.sqrt (S j) / D j ≤ (Real.sqrt (S j))⁻¹ := by
    have hs : 0 < S j := by linarith only [hS j]
    have hd : 0 < D j := hs.trans_le (hD j)
    have hr : 0 < Real.sqrt (S j) := Real.sqrt_pos.mpr hs
    rw [div_le_iff₀ hd, ← div_eq_inv_mul, le_div_iff₀ hr]
    nlinarith only [Real.sq_sqrt hs.le, hD j]
  apply squeeze_zero (fun j => div_nonneg (Real.sqrt_nonneg _) (by linarith only [hS j, hD j])) hbound
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hSinf)

open Filter in
lemma pairing_div_square_tendsto_zero {f v : ℕ → Plane → ℝ} {S D : ℕ → ℝ} {C : ℝ}
    (hf : ∀ j, Smooth (f j)) (hv : ∀ j, Smooth (v j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hcv : ∀ j, HasCompactSupport (v j))
    (hv1 : ∀ j, l2sq (v j) = 1)
    (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j) (hSinf : Tendsto S atTop atTop)
    (hbound : ∀ j, l2norm (f j) ≤ C * (Real.sqrt (S j) * D j)) :
    Tendsto (fun j => (∫ x, f j x * v j x) / (D j)^2) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hlim : Tendsto (fun j => C * (Real.sqrt (S j) / D j)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (sqrt_div_tendsto_zero hS hD hSinf).const_mul C
  apply squeeze_zero (fun j => abs_nonneg _) (fun j => ?_) hlim
  have hDpos : 0 < D j := by linarith only [hS j, hD j]
  have hp := pairing_abs_le_l2norm (hf j) (hv j) (hcf j) (hcv j)
  rw [l2norm_eq_one (hv1 j), mul_one] at hp
  rw [abs_div, abs_of_nonneg (sq_nonneg (D j))]
  calc
    _ ≤ (C*(Real.sqrt (S j)*D j))/(D j)^2 := div_le_div_of_nonneg_right (hp.trans (hbound j)) (sq_nonneg _)
    _ = _ := by field_simp [hDpos.ne']

open Filter in
lemma coefficient_pairing_tendsto_zero_of_bound {a f g : ℕ → Plane → ℝ}
    {e r : ℕ → ℝ} {L : ℝ}
    (ha : ∀ j, Smooth (a j)) (hf : ∀ j, Smooth (f j)) (hg : ∀ j, Smooth (g j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hcg : ∀ j, HasCompactSupport (g j))
    (he : ∀ j, 0 ≤ e j) (hb : ∀ j x, x ∈ tsupport (f j) → |a j x| ≤ e j)
    (he0 : Tendsto e atTop (𝓝 0))
    (hbound : ∀ j, l2sq (f j) + l2sq (g j) ≤ r j) (hr : Tendsto r atTop (𝓝 L)) :
    Tendsto (fun j => ∫ x, a j x * f j x * g j x) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero (fun j => abs_nonneg _) (fun j =>
    (integral_coefficient_mul_abs_le (ha j) (hf j) (hg j) (hcf j) (hcg j) (he j) (hb j)).trans
      (mul_le_mul_of_nonneg_left (hbound j) (div_nonneg (he j) (by norm_num))))
  simpa only [zero_div, zero_mul] using (he0.div_const 2).mul hr

open Filter in
lemma coefficient_square_tendsto_const {a v : ℕ → Plane → ℝ} {e : ℕ → ℝ} {A : ℝ}
    (ha : ∀ j, Smooth (a j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j) = 1)
    (he : ∀ j, 0 ≤ e j) (hb : ∀ j x, x ∈ tsupport (v j) → |a j x - A| ≤ e j)
    (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, a j x * (v j x * v j x)) atTop (𝓝 A) := by
  have h := coefficient_pairing_tendsto_zero_of_bound
    (fun j => (ha j).sub contDiff_const) hv hv hcv hcv he hb he0
    (r := fun _ => 2) (fun j => by rw [hv1 j]; norm_num) tendsto_const_nhds
  have hi (j : ℕ) : (∫ x, (a j x - A) * v j x * v j x) =
      (∫ x, a j x * (v j x * v j x)) - A := by
    calc
      _ = ∫ x, a j x * (v j x * v j x) - A * (v j x * v j x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := by
        rw [integral_sub (integrable_mul_compact_right (ha j) ((hv j).mul (hv j)) (hcv j).mul_right)
          ((integrable_mul_compact_left (hv j) (hv j) (hcv j)).const_mul A), integral_const_mul]
        change _ - A * l2sq (v j) = _
        rw [hv1 j, mul_one]
  have h' := h.add_const A
  simpa only [hi, sub_add_cancel, zero_add] using h'

lemma l2sq_div (f : Plane → ℝ) (D : ℝ) :
    l2sq (fun x => f x / D) = l2sq f / D^2 := by
  simp only [div_eq_mul_inv, mul_comm (f _) D⁻¹]
  rw [l2sq_const_mul]
  ring

def normalizedPartial (v : Plane → ℝ) (D : ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  coordPartial v i x / D

lemma smooth_normalizedPartial {v : Plane → ℝ} (hv : Smooth v) (D : ℝ) (i : Fin 2) :
    Smooth (normalizedPartial v D i) := (smooth_partial hv i).div_const D

lemma compact_normalizedPartial {v : Plane → ℝ} (hv : HasCompactSupport v) (D : ℝ) (i : Fin 2) :
    HasCompactSupport (normalizedPartial v D i) := by
  change HasCompactSupport (fun x => coordPartial v i x * D⁻¹)
  exact (compact_partial hv i).mul_right

lemma normalizedPartial_energy (v : Plane → ℝ) (D : ℝ) :
    l2sq (normalizedPartial v D 0) + l2sq (normalizedPartial v D 1) = gradientEnergy v / D^2 := by
  change l2sq (fun x => coordPartial v 0 x / D) + l2sq (fun x => coordPartial v 1 x / D) = _
  simp only [l2sq_div, gradientEnergy, Fin.sum_univ_two, add_div]

lemma normalized_coefficient_integral (a v : Plane → ℝ) (D : ℝ) :
    (∫ x, (a x / D^2) * (v x * v x)) = (∫ x, a x * (v x * v x)) / D^2 := by
  calc
    _ = ∫ x, (a x * (v x * v x)) / D^2 := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := integral_div _ _

open Filter in

lemma normalized_gradient_energy_limit {a v : ℕ → Plane → ℝ} {S D e : ℕ → ℝ} {C A : ℝ}
    (ha : ∀ j, Smooth (a j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j) = 1)
    (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j) (hSinf : Tendsto S atTop atTop)
    (hbound : ∀ j, l2norm (plusPart (a j) (v j)) ≤ C * (Real.sqrt (S j) * D j))
    (he : ∀ j, 0 ≤ e j) (hb : ∀ j x, x ∈ tsupport (v j) → |a j x / (D j)^2 - A| ≤ e j)
    (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun j => l2sq (normalizedPartial (v j) (D j) 0) +
      l2sq (normalizedPartial (v j) (D j) 1)) atTop (𝓝 A) := by
  have hpair := pairing_div_square_tendsto_zero (fun j => smooth_plus (ha j) (hv j)) hv
    (fun j => compact_plus (hcv j)) hcv hv1 hS hD hSinf hbound
  have hcoeff := coefficient_square_tendsto_const (fun j => (ha j).div_const ((D j)^2)) hv
    hcv hv1 he hb he0
  have hi (j : ℕ) : l2sq (normalizedPartial (v j) (D j) 0) +
      l2sq (normalizedPartial (v j) (D j) 1) =
      (∫ x, (a j x / (D j)^2) * (v j x * v j x)) -
        (∫ x, plusPart (a j) (v j) x * v j x) / (D j)^2 := by
    rw [normalizedPartial_energy, normalized_coefficient_integral, plus_energy_identity (ha j) (hv j) (hcv j)]
    ring
  simpa only [← hi, sub_zero] using hcoeff.sub hpair

lemma normalizedPartial_tsupport_subset (v : Plane → ℝ) (D : ℝ) (i : Fin 2) :
    tsupport (normalizedPartial v D i) ⊆ tsupport v := by
  change tsupport (fun x => coordPartial v i x * D⁻¹) ⊆ tsupport v
  exact tsupport_mul_subset_left.trans (partial_tsupport_subset v i)

lemma l2sq_add_le {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    l2sq (fun x => f x + g x) ≤ 2*(l2sq f + l2sq g) := by
  convert l2sq_linearCombination_le hf hg hcf hcg 1 1 using 1 <;> norm_num

lemma l2sq_coefficient_mul_le {a f : Plane → ℝ} {C : ℝ}
    (ha : Smooth a) (hf : Smooth f) (hc : HasCompactSupport f)
    (hC : 0 ≤ C) (hb : ∀ x ∈ tsupport f, |a x| ≤ C) :
    l2sq (fun x => a x * f x) ≤ C ^ 2 * l2sq f := by
  have hIf := integrable_mul_compact_left hf hf hc
  have hI : Integrable (fun x => (a x * f x) * (a x * f x)) :=
    integrable_mul_compact_left (ha.mul hf) (ha.mul hf) hc.mul_left
  calc
    _ ≤ ∫ x, C ^ 2 * (f x * f x) := by
      apply integral_mono hI (hIf.const_mul (C ^ 2))
      intro x
      by_cases hx : f x = 0
      · simp only [hx, mul_zero, le_refl]
      · have haC := (sq_le_sq₀ (abs_nonneg (a x)) hC).mpr (hb x (subset_closure hx))
        rw [sq_abs] at haC
        have h := mul_le_mul_of_nonneg_right haC (mul_self_nonneg (f x))
        nlinarith only [h]
    _ = _ := integral_const_mul _ _

open Filter in
lemma l2sq_add_tendsto_zero {f g : ℕ → Plane → ℝ}
    (hf : ∀ j, Smooth (f j)) (hg : ∀ j, Smooth (g j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hcg : ∀ j, HasCompactSupport (g j))
    (hf0 : Tendsto (fun j => l2sq (f j)) atTop (𝓝 0))
    (hg0 : Tendsto (fun j => l2sq (g j)) atTop (𝓝 0)) :
    Tendsto (fun j => l2sq (fun x => f j x + g j x)) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => l2sq_nonneg _) (fun j => l2sq_add_le (hf j) (hg j) (hcf j) (hcg j))
  simpa only [add_zero, mul_zero] using (hf0.add hg0).const_mul 2

open Filter in
lemma l2sq_coefficient_mul_tendsto_zero {a f : ℕ → Plane → ℝ} {e r : ℕ → ℝ} {L : ℝ}
    (ha : ∀ j, Smooth (a j)) (hf : ∀ j, Smooth (f j))
    (hcf : ∀ j, HasCompactSupport (f j))
    (he : ∀ j, 0 ≤ e j) (hb : ∀ j x, x ∈ tsupport (f j) → |a j x| ≤ e j)
    (he0 : Tendsto e atTop (𝓝 0))
    (hbound : ∀ j, l2sq (f j) ≤ r j) (hr : Tendsto r atTop (𝓝 L)) :
    Tendsto (fun j => l2sq (fun x => a j x * f j x)) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => l2sq_nonneg _) (fun j =>
    (l2sq_coefficient_mul_le (ha j) (hf j) (hcf j) (he j) (hb j)).trans
      (mul_le_mul_of_nonneg_left (hbound j) (sq_nonneg _)))
  simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_mul] using (he0.pow 2).mul hr

open Filter in
lemma scaled_operator_square_limit {f : ℕ → Plane → ℝ} {S D : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j)
    (hSinf : Tendsto S atTop atTop)
    (hbound : ∀ j, l2norm (f j) ≤ C * (Real.sqrt (S j) * D j)) :
    Tendsto (fun j => l2sq (fun x => f j x / (D j)^2)) atTop (𝓝 0) := by
  have he0 : Tendsto (fun j => (C * (Real.sqrt (S j) / D j))^2) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      ((sqrt_div_tendsto_zero hS hD hSinf).const_mul C).pow 2
  apply squeeze_zero (fun j => l2sq_nonneg _) (fun j => ?_) he0
  have hd : 0 < D j := by linarith only [hS j, hD j]
  have h : l2norm (f j) / (D j)^2 ≤ C * (Real.sqrt (S j) / D j) := by
    calc
      _ ≤ (C * (Real.sqrt (S j) * D j)) / (D j)^2 :=
        div_le_div_of_nonneg_right (hbound j) (sq_nonneg _)
      _ = _ := by field_simp [hd.ne']
  have hsq := (sq_le_sq₀ (div_nonneg (l2norm_nonneg _) (sq_nonneg _))
    (mul_nonneg hC (div_nonneg (Real.sqrt_nonneg _) hd.le))).mpr h
  rw [l2sq_div, ← l2norm_sq]
  simpa only [div_pow] using hsq

def normalizedTransport (T v : Plane → ℝ) (D : ℝ) (x : Plane) : ℝ :=
  (coordPartial T 0 x / D) * normalizedPartial v D 0 x +
  (coordPartial T 1 x / D) * normalizedPartial v D 1 x

lemma smooth_normalizedTransport {T v : Plane → ℝ} (hT : Smooth T) (hv : Smooth v) (D : ℝ) :
    Smooth (normalizedTransport T v D) :=
  (((smooth_partial hT 0).div_const D).mul (smooth_normalizedPartial hv D 0)).add
    (((smooth_partial hT 1).div_const D).mul (smooth_normalizedPartial hv D 1))

lemma compact_normalizedTransport {T v : Plane → ℝ} (hc : HasCompactSupport v) (D : ℝ) :
    HasCompactSupport (normalizedTransport T v D) :=
  (compact_normalizedPartial hc D 0).mul_left.add (compact_normalizedPartial hc D 1).mul_left

lemma normalized_transport_identity (T v : Plane → ℝ) (D : ℝ) (x : Plane) :
    normalizedTransport T v D x = (-1/2 : ℝ) *
      (skewPart T v x / D^2 + (euclideanLaplacian T x / D^2) * v x) := by
  simp only [normalizedTransport, normalizedPartial, skewPart, euclideanLaplacian,
    Fin.sum_univ_two, div_eq_mul_inv]
  ring

lemma normalized_laplacian_abs_le {T v : Plane → ℝ} {c S D : ℝ} (hS : 0 ≤ S)
    (hH : ∀ i j x, x ∈ tsupport v → |coordPartial (coordPartial T j) i x| ≤ c*S)
    (x : Plane) (hx : x ∈ tsupport v) :
    |euclideanLaplacian T x / D^2| ≤ 2*c*(Real.sqrt S / D)^2 := by
  have hsum : |euclideanLaplacian T x| ≤ 2*c*S := by
    calc
      _ ≤ |coordPartial (coordPartial T 0) 0 x| + |coordPartial (coordPartial T 1) 1 x| := by
        simpa only [euclideanLaplacian, Fin.sum_univ_two] using
          abs_add_le (coordPartial (coordPartial T 0) 0 x) (coordPartial (coordPartial T 1) 1 x)
      _ ≤ _ := by linarith only [hH 0 0 x hx, hH 1 1 x hx]
  rw [abs_div, abs_of_nonneg (sq_nonneg D)]
  calc
    _ ≤ (2*c*S)/D^2 := div_le_div_of_nonneg_right hsum (sq_nonneg D)
    _ = _ := by rw [div_pow, Real.sq_sqrt hS]; ring

open Filter in
lemma normalized_transport_square_limit {T v : ℕ → Plane → ℝ} {S D : ℕ → ℝ} {c C : ℝ}
    (hT : ∀ j, Smooth (T j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j) = 1)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j)
    (hSinf : Tendsto S atTop atTop)
    (hY : ∀ j, l2norm (skewPart (T j) (v j)) ≤ C*(Real.sqrt (S j)*D j))
    (hH : ∀ j i k x, x ∈ tsupport (v j) →
      |coordPartial (coordPartial (T j) k) i x| ≤ c*S j) :
    Tendsto (fun j => l2sq (normalizedTransport (T j) (v j) (D j))) atTop (𝓝 0) := by
  have hskew := scaled_operator_square_limit hC hS hD hSinf hY
  have hlap : Tendsto (fun j => l2sq (fun x =>
      (euclideanLaplacian (T j) x / (D j)^2) * v j x)) atTop (𝓝 0) := by
    apply l2sq_coefficient_mul_tendsto_zero
      (fun j => (smooth_laplacian (hT j)).div_const _) hv hcv
      (e := fun j => 2*c*(Real.sqrt (S j)/D j)^2) (r := fun _ => 1)
    · intro j
      positivity
    · intro j x hx
      exact normalized_laplacian_abs_le (by linarith only [hS j]) (hH j) x hx
    · simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
        ((sqrt_div_tendsto_zero hS hD hSinf).pow 2).const_mul (2*c)
    · intro j
      exact (hv1 j).le
    · exact tendsto_const_nhds
  have hadd := l2sq_add_tendsto_zero
    (fun j => (smooth_skew (hT j) (hv j)).div_const _)
    (fun j => ((smooth_laplacian (hT j)).div_const _).mul (hv j))
    (fun j => by
      change HasCompactSupport (fun x => skewPart (T j) (v j) x * ((D j)^2)⁻¹)
      exact (compact_skew (hcv j)).mul_right)
    (fun j => (hcv j).mul_left) hskew hlap
  have hconst := hadd.const_mul ((-1/2 : ℝ)^2)
  have hid (j : ℕ) : l2sq (normalizedTransport (T j) (v j) (D j)) =
      (-1/2 : ℝ)^2 * l2sq (fun x => skewPart (T j) (v j) x / (D j)^2 +
        (euclideanLaplacian (T j) x / (D j)^2) * v j x) := by
    rw [show normalizedTransport (T j) (v j) (D j) = (fun x => (-1/2 : ℝ) *
      (skewPart (T j) (v j) x / (D j)^2 + (euclideanLaplacian (T j) x / (D j)^2) * v j x)) from
        funext (normalized_transport_identity (T j) (v j) (D j)), l2sq_const_mul]
  simpa only [← hid, mul_zero] using hconst

open Filter in

lemma normalized_parallel_limit {T v : ℕ → Plane → ℝ} {S D e : ℕ → ℝ} {c C E : ℝ}
    (a : Fin 2 → ℝ)
    (hT : ∀ j, Smooth (T j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j)) (hv1 : ∀ j, l2sq (v j) = 1)
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hS : ∀ j, 1 ≤ S j) (hD : ∀ j, S j ≤ D j)
    (hSinf : Tendsto S atTop atTop)
    (hY : ∀ j, l2norm (skewPart (T j) (v j)) ≤ C*(Real.sqrt (S j)*D j))
    (hH : ∀ j i k x, x ∈ tsupport (v j) →
      |coordPartial (coordPartial (T j) k) i x| ≤ c*S j)
    (he : ∀ j, 0 ≤ e j) (he0 : Tendsto e atTop (𝓝 0))
    (ha : ∀ j i x, x ∈ tsupport (v j) → |coordPartial (T j) i x / D j - a i| ≤ e j)
    (henergy : Tendsto (fun j => l2sq (normalizedPartial (v j) (D j) 0) +
      l2sq (normalizedPartial (v j) (D j) 1)) atTop (𝓝 E)) :
    Tendsto (fun j => l2sq (fun x => a 0 * normalizedPartial (v j) (D j) 0 x +
      a 1 * normalizedPartial (v j) (D j) 1 x)) atTop (𝓝 0) := by
  let f (j : ℕ) (i : Fin 2) := normalizedPartial (v j) (D j) i
  let q (j : ℕ) (i : Fin 2) (x : Plane) := a i - coordPartial (T j) i x / D j
  have hf (j : ℕ) (i : Fin 2) : Smooth (f j i) := smooth_normalizedPartial (hv j) _ _
  have hcf (j : ℕ) (i : Fin 2) : HasCompactSupport (f j i) := compact_normalizedPartial (hcv j) _ _
  have hq (j : ℕ) (i : Fin 2) : Smooth (q j i) := contDiff_const.sub ((smooth_partial (hT j) i).div_const _)
  have htotal (j : ℕ) (i : Fin 2) : l2sq (f j i) ≤ l2sq (f j 0) + l2sq (f j 1) := by
    fin_cases i
    · change l2sq (f j 0) ≤ l2sq (f j 0) + l2sq (f j 1)
      linarith only [l2sq_nonneg (f j 1)]
    · change l2sq (f j 1) ≤ l2sq (f j 0) + l2sq (f j 1)
      linarith only [l2sq_nonneg (f j 0)]
  have hzero (i : Fin 2) : Tendsto (fun j => l2sq (fun x => q j i x * f j i x)) atTop (𝓝 0) := by
    apply l2sq_coefficient_mul_tendsto_zero (fun j => hq j i) (fun j => hf j i)
      (fun j => hcf j i) he _ he0 (fun j => htotal j i) henergy
    intro j x hx
    change |a i - coordPartial (T j) i x / D j| ≤ e j
    rw [abs_sub_comm]
    exact ha j i x (normalizedPartial_tsupport_subset (v j) (D j) i hx)
  have hcorr := l2sq_add_tendsto_zero
    (fun j => (hq j 0).mul (hf j 0)) (fun j => (hq j 1).mul (hf j 1))
    (fun j => (hcf j 0).mul_left) (fun j => (hcf j 1).mul_left) (hzero 0) (hzero 1)
  have htransport := normalized_transport_square_limit hT hv hcv hv1 hc hC hS hD hSinf hY hH
  have hsum := l2sq_add_tendsto_zero (fun j => smooth_normalizedTransport (hT j) (hv j) _)
    (fun j => ((hq j 0).mul (hf j 0)).add ((hq j 1).mul (hf j 1)))
    (fun j => compact_normalizedTransport (hcv j) _)
    (fun j => (hcf j 0).mul_left.add (hcf j 1).mul_left) htransport hcorr
  convert hsum using 1
  ext j
  congr 1
  ext x
  dsimp [normalizedTransport, f, q]
  ring

lemma integral_normalized_hessian (T v : Plane → ℝ) (S D : ℝ) (i j : Fin 2) :
    (∫ x, (coordPartial (coordPartial T j) i x / S) *
      normalizedPartial v D i x * normalizedPartial v D j x) =
    (∫ x, coordPartial (coordPartial T j) i x * coordPartial v i x * coordPartial v j x) /
      (S*D^2) := by
  calc
    _ = ∫ x, (coordPartial (coordPartial T j) i x * coordPartial v i x * coordPartial v j x) /
        (S*D^2) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [normalizedPartial, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := integral_div _ _

lemma normalized_hessian_expansion {T v : Plane → ℝ} (hT : Smooth T) (S D : ℝ) :
    hessianEnergy T v / (S*D^2) =
      (∫ x, (coordPartial (coordPartial T 0) 0 x / S) *
        normalizedPartial v D 0 x * normalizedPartial v D 0 x) +
      2*(∫ x, (coordPartial (coordPartial T 0) 1 x / S) *
        normalizedPartial v D 0 x * normalizedPartial v D 1 x) +
      (∫ x, (coordPartial (coordPartial T 1) 1 x / S) *
        normalizedPartial v D 1 x * normalizedPartial v D 1 x) := by
  have hcross : (∫ x, (coordPartial (coordPartial T 0) 1 x / S) *
      normalizedPartial v D 1 x * normalizedPartial v D 0 x) =
      (∫ x, (coordPartial (coordPartial T 0) 1 x / S) *
        normalizedPartial v D 0 x * normalizedPartial v D 1 x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  unfold hessianEnergy
  simp only [Fin.sum_univ_two, add_div, ← integral_normalized_hessian]
  simp_rw [partial_partial hT 1 0]
  rw [hcross]
  ring

lemma integral_coefficient_difference {a f g : Plane → ℝ} (A : ℝ)
    (ha : Smooth a) (hf : Smooth f) (hg : Smooth g) (hc : HasCompactSupport f) :
    (∫ x, (a x - A) * f x * g x) =
      (∫ x, a x * f x * g x) - A*(∫ x, f x * g x) := by
  calc
    _ = ∫ x, a x * f x * g x - A*(f x*g x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := by
      rw [integral_sub (integrable_mul_compact_left (ha.mul hf) hg hc.mul_left)
        ((integrable_mul_compact_left hf hg hc).const_mul A), integral_const_mul]

open Filter in
lemma variable_quadratic_difference_limit {h₀ h₁ h₂ f g : ℕ → Plane → ℝ}
    {e : ℕ → ℝ} {A B C E : ℝ}
    (hh₀ : ∀ j, Smooth (h₀ j)) (hh₁ : ∀ j, Smooth (h₁ j)) (hh₂ : ∀ j, Smooth (h₂ j))
    (hf : ∀ j, Smooth (f j)) (hg : ∀ j, Smooth (g j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hcg : ∀ j, HasCompactSupport (g j))
    (he : ∀ j, 0 ≤ e j) (he0 : Tendsto e atTop (𝓝 0))
    (hb₀ : ∀ j x, x ∈ tsupport (f j) → |h₀ j x - A| ≤ e j)
    (hb₁ : ∀ j x, x ∈ tsupport (f j) → |h₁ j x - B| ≤ e j)
    (hb₂ : ∀ j x, x ∈ tsupport (g j) → |h₂ j x - C| ≤ e j)
    (henergy : Tendsto (fun j => l2sq (f j) + l2sq (g j)) atTop (𝓝 E)) :
    Tendsto (fun j =>
      ((∫ x, h₀ j x * f j x * f j x) + 2*(∫ x, h₁ j x * f j x * g j x) +
        (∫ x, h₂ j x * g j x * g j x)) - quadraticEnergy A B C (f j) (g j))
      atTop (𝓝 0) := by
  have hfbound (j : ℕ) : l2sq (f j) + l2sq (f j) ≤ 2*(l2sq (f j)+l2sq (g j)) := by
    linarith only [l2sq_nonneg (g j)]
  have hgbound (j : ℕ) : l2sq (g j) + l2sq (g j) ≤ 2*(l2sq (f j)+l2sq (g j)) := by
    linarith only [l2sq_nonneg (f j)]
  have h₀zero := coefficient_pairing_tendsto_zero_of_bound
    (fun j => (hh₀ j).sub contDiff_const) hf hf hcf hcf he hb₀ he0 hfbound (henergy.const_mul 2)
  have h₁zero := coefficient_pairing_tendsto_zero (fun j => (hh₁ j).sub contDiff_const)
    hf hg hcf hcg he hb₁ he0 henergy
  have h₂zero := coefficient_pairing_tendsto_zero_of_bound
    (fun j => (hh₂ j).sub contDiff_const) hg hg hcg hcg he hb₂ he0 hgbound (henergy.const_mul 2)
  have hi (j : ℕ) :
      (∫ x, (h₀ j x-A)*f j x*f j x) + 2*(∫ x, (h₁ j x-B)*f j x*g j x) +
      (∫ x, (h₂ j x-C)*g j x*g j x) =
      ((∫ x, h₀ j x * f j x * f j x) + 2*(∫ x, h₁ j x * f j x * g j x) +
        (∫ x, h₂ j x * g j x * g j x)) - quadraticEnergy A B C (f j) (g j) := by
    rw [integral_coefficient_difference A (hh₀ j) (hf j) (hf j) (hcf j),
      integral_coefficient_difference B (hh₁ j) (hf j) (hg j) (hcf j),
      integral_coefficient_difference C (hh₂ j) (hg j) (hg j) (hcg j)]
    unfold quadraticEnergy l2sq
    ring
  simpa only [hi, mul_zero, add_zero] using (h₀zero.add (h₁zero.const_mul 2)).add h₂zero

open Filter in
lemma normalized_hessian_trace_limit {T v : ℕ → Plane → ℝ} {S D e : ℕ → ℝ}
    (a₀ a₁ A B C : ℝ) (ha : a₀^2+a₁^2 ≠ 0)
    (hT : ∀ j, Smooth (T j)) (hv : ∀ j, Smooth (v j))
    (hcv : ∀ j, HasCompactSupport (v j))
    (he : ∀ j, 0 ≤ e j) (he0 : Tendsto e atTop (𝓝 0))
    (hb₀ : ∀ j x, x ∈ tsupport (v j) →
      |coordPartial (coordPartial (T j) 0) 0 x / S j - A| ≤ e j)
    (hb₁ : ∀ j x, x ∈ tsupport (v j) →
      |coordPartial (coordPartial (T j) 0) 1 x / S j - B| ≤ e j)
    (hb₂ : ∀ j x, x ∈ tsupport (v j) →
      |coordPartial (coordPartial (T j) 1) 1 x / S j - C| ≤ e j)
    (henergy : Tendsto (fun j => l2sq (normalizedPartial (v j) (D j) 0) +
      l2sq (normalizedPartial (v j) (D j) 1)) atTop (𝓝 (a₀^2+a₁^2)))
    (hparallel : Tendsto (fun j => l2sq (fun x => a₀ * normalizedPartial (v j) (D j) 0 x +
      a₁ * normalizedPartial (v j) (D j) 1 x)) atTop (𝓝 0)) :
    Tendsto (fun j => hessianEnergy (T j) (v j) / (S j*(D j)^2) +
      (A*a₀^2+2*B*a₀*a₁+C*a₁^2)) atTop (𝓝 ((a₀^2+a₁^2)*(A+C))) := by
  have htrace := plane_trace_energy_limit a₀ a₁ A B C ha
    (fun j => smooth_normalizedPartial (hv j) _ _) (fun j => smooth_normalizedPartial (hv j) _ _)
    (fun j => compact_normalizedPartial (hcv j) _ _) (fun j => compact_normalizedPartial (hcv j) _ _)
    henergy hparallel
  have herr := variable_quadratic_difference_limit
    (fun j => (smooth_partial (smooth_partial (hT j) 0) 0).div_const _)
    (fun j => (smooth_partial (smooth_partial (hT j) 0) 1).div_const _)
    (fun j => (smooth_partial (smooth_partial (hT j) 1) 1).div_const _)
    (fun j => smooth_normalizedPartial (hv j) _ _) (fun j => smooth_normalizedPartial (hv j) _ _)
    (fun j => compact_normalizedPartial (hcv j) _ _) (fun j => compact_normalizedPartial (hcv j) _ _)
    he he0
    (fun j x hx => hb₀ j x (normalizedPartial_tsupport_subset _ _ _ hx))
    (fun j x hx => hb₁ j x (normalizedPartial_tsupport_subset _ _ _ hx))
    (fun j x hx => hb₂ j x (normalizedPartial_tsupport_subset _ _ _ hx)) henergy
  have hsum := herr.add htrace
  convert hsum using 1
  · ext j
    rw [normalized_hessian_expansion (hT j)]
    ring
  · simp only [zero_add]


end Carleman
end SharpNodal

end

end OAI
