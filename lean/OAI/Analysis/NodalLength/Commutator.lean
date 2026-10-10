import OAI.Analysis.NodalLength.Integration

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

lemma partial_finset_sum {ι : Type*} (s : Finset ι) {f : ι → Plane → ℝ}
    (hf : ∀ i ∈ s, Smooth (f i)) (k : Fin 2) (x : Plane) :
    coordPartial (fun y => ∑ i ∈ s, f i y) k x = ∑ i ∈ s, coordPartial (f i) k x := by
  unfold coordPartial
  rw [fderiv_fun_sum (fun i hi => ((hf i hi).differentiable (by simp)).differentiableAt)]
  simp only [sum_apply]

def gradientSquared (T : Plane → ℝ) (x : Plane) : ℝ :=
  ∑ i : Fin 2, coordPartial T i x * coordPartial T i x

lemma smooth_gradientSquared {T : Plane → ℝ} (hT : Smooth T) :
    Smooth (gradientSquared T) :=
  ContDiff.sum fun i _ => (smooth_partial hT i).mul (smooth_partial hT i)

lemma partial_gradientSquared {T : Plane → ℝ} (hT : Smooth T) (i : Fin 2) (x : Plane) :
    coordPartial (gradientSquared T) i x =
      ∑ j : Fin 2, 2 * coordPartial (coordPartial T j) i x * coordPartial T j x := by
  unfold gradientSquared
  rw [partial_finset_sum Finset.univ
    (fun j _ => (smooth_partial hT j).mul (smooth_partial hT j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [partial_mul (smooth_partial hT j) (smooth_partial hT j)]
  ring

lemma potential_transport_component {T p v : Plane → ℝ}
    (hT : Smooth T) (hp : Smooth p) (hv : Smooth v) (hc : HasCompactSupport v)
    (K : ℝ) (i : Fin 2) :
    2 * (∫ x, coordPartial (fun y => gradientSquared T y + K^2 * p y) i x *
      coordPartial T i x * (v x * v x)) =
      (∑ j : Fin 2, 4 * (∫ x, coordPartial (coordPartial T j) i x *
        coordPartial T j x * coordPartial T i x * (v x * v x))) +
      2 * K^2 * (∫ x, coordPartial p i x * coordPartial T i x * (v x * v x)) := by
  have hI₁ := integrable_mul_compact_right
    ((smooth_partial (smooth_gradientSquared hT) i).mul (smooth_partial hT i))
    (hv.mul hv) hc.mul_right
  have hI₂ := integrable_mul_compact_right
    ((smooth_partial hp i).mul (smooth_partial hT i)) (hv.mul hv) hc.mul_right
  have hsplit : (∫ x, coordPartial (fun y => gradientSquared T y + K^2 * p y) i x *
      coordPartial T i x * (v x * v x)) =
      (∫ x, coordPartial (gradientSquared T) i x * coordPartial T i x * (v x * v x)) +
      K^2 * (∫ x, coordPartial p i x * coordPartial T i x * (v x * v x)) := by
    calc
      _ = ∫ x, (coordPartial (gradientSquared T) i x * coordPartial T i x * (v x * v x)) +
          K^2 * (coordPartial p i x * coordPartial T i x * (v x * v x)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [partial_add (smooth_gradientSquared hT) (contDiff_const.mul hp),
          partial_const_mul hp]
        ring
      _ = _ := by rw [integral_add hI₁ (hI₂.const_mul (K^2)), integral_const_mul]
  rw [hsplit, mul_add]
  have hgrad : 2 * (∫ x, coordPartial (gradientSquared T) i x * coordPartial T i x *
      (v x * v x)) = ∑ j : Fin 2, 4 * (∫ x, coordPartial (coordPartial T j) i x *
        coordPartial T j x * coordPartial T i x * (v x * v x)) := by
    simp_rw [partial_gradientSquared hT, mul_assoc]
    rw [integral_sum_mul Finset.univ
      (fun j _ => contDiff_const.mul ((smooth_partial (smooth_partial hT j) i).mul
        (smooth_partial hT j)))
      ((smooth_partial hT i).mul (hv.mul hv)) hc.mul_right.mul_left,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    ring
  rw [hgrad]
  ring

theorem carleman_commutator {T p v : Plane → ℝ}
    (hT : Smooth T) (hp : Smooth p) (hv : Smooth v) (hc : HasCompactSupport v)
    (K : ℝ) :
    2 * (∫ x, (euclideanLaplacian v x + (gradientSquared T x + K^2 * p x) * v x) *
      skewPart T v x) =
      (∑ j : Fin 2, ∑ i : Fin 2,
        (4 * (∫ x, coordPartial (coordPartial T j) i x *
          coordPartial v i x * coordPartial v j x) -
        (∫ x, coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x *
          (v x * v x)))) +
      ∑ i : Fin 2,
        ((∑ j : Fin 2, 4 * (∫ x, coordPartial (coordPartial T j) i x *
          coordPartial T j x * coordPartial T i x * (v x * v x))) +
        2 * K^2 * (∫ x, coordPartial p i x * coordPartial T i x * (v x * v x))) := by
  rw [transport_commutator ((smooth_gradientSquared hT).add (contDiff_const.mul hp)) hT hv hc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact potential_transport_component hT hp hv hc K i

lemma partial_exp {T : Plane → ℝ} (hT : Smooth T) (i : Fin 2) (x : Plane) :
    coordPartial (fun y => Real.exp (T y)) i x = Real.exp (T x) * coordPartial T i x := by
  unfold coordPartial
  rw [fderiv_exp ((hT.differentiable (by simp)).differentiableAt)]
  rfl

lemma partial_exp_mul {T w : Plane → ℝ} (hT : Smooth T) (hw : Smooth w)
    (i : Fin 2) (x : Plane) :
    coordPartial (fun y => Real.exp (T y) * w y) i x =
      Real.exp (T x) * (coordPartial T i x * w x + coordPartial w i x) := by
  rw [partial_mul hT.exp hw, partial_exp hT]
  ring

lemma partial2_exp_mul {T w : Plane → ℝ} (hT : Smooth T) (hw : Smooth w)
    (i : Fin 2) (x : Plane) :
    coordPartial (coordPartial (fun y => Real.exp (T y) * w y) i) i x =
      Real.exp (T x) * (coordPartial (coordPartial w i) i x +
        2 * coordPartial T i x * coordPartial w i x +
        (coordPartial (coordPartial T i) i x + coordPartial T i x * coordPartial T i x) * w x) := by
  rw [show coordPartial (fun y => Real.exp (T y) * w y) i =
      (fun y => Real.exp (T y) * (coordPartial T i y * w y + coordPartial w i y)) from
    funext (partial_exp_mul hT hw i)]
  rw [partial_exp_mul hT (((smooth_partial hT i).mul hw).add (smooth_partial hw i)),
    partial_add ((smooth_partial hT i).mul hw) (smooth_partial hw i),
    partial_mul (smooth_partial hT i) hw]
  ring

lemma conjugation_component {T w : Plane → ℝ} (hT : Smooth T) (hw : Smooth w)
    (i : Fin 2) (x : Plane) :
    coordPartial (coordPartial (fun y => Real.exp (T y) * w y) i) i x +
      (coordPartial T i x * coordPartial T i x) * (Real.exp (T x) * w x) +
      (-2 * coordPartial T i x * coordPartial (fun y => Real.exp (T y) * w y) i x -
        coordPartial (coordPartial T i) i x * (Real.exp (T x) * w x)) =
      Real.exp (T x) * coordPartial (coordPartial w i) i x := by
  rw [partial2_exp_mul hT hw, partial_exp_mul hT hw]
  ring

lemma conjugation {T w : Plane → ℝ} (hT : Smooth T) (hw : Smooth w)
    (p : Plane → ℝ) (K : ℝ) (x : Plane) :
    euclideanLaplacian (fun y => Real.exp (T y) * w y) x +
      (gradientSquared T x + K^2 * p x) * (Real.exp (T x) * w x) +
      skewPart T (fun y => Real.exp (T y) * w y) x =
      Real.exp (T x) * (euclideanLaplacian w x + K^2 * p x * w x) := by
  have h := congrArg (fun f : Fin 2 → ℝ => ∑ i, f i)
    (funext (fun i => conjugation_component hT hw i x))
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum] at h
  unfold euclideanLaplacian gradientSquared skewPart
  linear_combination h

lemma integral_laplacian_mul {v : Plane → ℝ} (hv : Smooth v) (hc : HasCompactSupport v) :
    (∫ x, euclideanLaplacian v x * v x) =
      -(∑ i : Fin 2, ∫ x, coordPartial v i x * coordPartial v i x) := by
  unfold euclideanLaplacian
  rw [integral_sum_mul Finset.univ (fun i _ => smooth_partial (smooth_partial hv i) i) hv hc,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_partial_mul (smooth_partial hv i) hv (compact_partial hc i) i

def l2sq (f : Plane → ℝ) : ℝ := ∫ x, f x * f x

lemma l2sq_nonneg (f : Plane → ℝ) : 0 ≤ l2sq f :=
  integral_nonneg fun x => mul_self_nonneg (f x)

lemma l2sq_add {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    l2sq (fun x => f x + g x) = l2sq f + l2sq g + 2 * (∫ x, f x * g x) := by
  have hI₁ := integrable_mul_compact_left hf hf hcf
  have hI₂ := integrable_mul_compact_left hg hg hcg
  have hI₃ := integrable_mul_compact_left hf hg hcf
  unfold l2sq
  calc
    _ = ∫ x, (f x * f x + g x * g x) + 2 * (f x * g x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := by
      rw [integral_add (f := fun x => f x * f x + g x * g x)
        (hI₁.add hI₂) (hI₃.const_mul 2), integral_add hI₁ hI₂, integral_const_mul]

lemma pairing_le_l2sq_add {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    2 * (∫ x, f x * g x) ≤ l2sq (fun x => f x + g x) := by
  rw [l2sq_add hf hg hcf hcg]
  linarith only [l2sq_nonneg f, l2sq_nonneg g]

lemma l2sq_const_mul (f : Plane → ℝ) (c : ℝ) :
    l2sq (fun x => c * f x) = c^2 * l2sq f := by
  unfold l2sq
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

lemma pairing_sq_le {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    (∫ x, f x * g x)^2 ≤ l2sq f * l2sq g := by
  have hquad (t : ℝ) : 0 ≤ l2sq f * (t * t) + (2 * (∫ x, f x * g x)) * t + l2sq g := by
    have h := l2sq_nonneg (fun x => t * f x + g x)
    rw [l2sq_add (contDiff_const.mul hf) hg hcf.mul_left hcg, l2sq_const_mul] at h
    simp_rw [mul_assoc] at h
    rw [integral_const_mul] at h
    nlinarith only [h]
  have h := discrim_le_zero hquad
  unfold discrim at h
  nlinarith only [h]

lemma plane_trace_identity (a₀ a₁ A B C q₀ q₁ : ℝ) :
    (a₀^2 + a₁^2) * (A * q₀^2 + 2 * B * q₀ * q₁ + C * q₁^2) =
      (C * a₀^2 - 2 * B * a₀ * a₁ + A * a₁^2) * (q₀^2 + q₁^2) +
      2 * ((A * a₀ + B * a₁) * q₀ + (B * a₀ + C * a₁) * q₁) *
        (a₀ * q₀ + a₁ * q₁) -
      (A + C) * (a₀ * q₀ + a₁ * q₁)^2 := by
  ring

lemma plane_trace_sum (a₀ a₁ A B C : ℝ) :
    (C * a₀^2 - 2 * B * a₀ * a₁ + A * a₁^2) +
      (A * a₀^2 + 2 * B * a₀ * a₁ + C * a₁^2) =
      (a₀^2 + a₁^2) * (A + C) := by
  ring

lemma l2sq_linearCombination_le {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) (a b : ℝ) :
    l2sq (fun x => a * f x + b * g x) ≤ (a^2 + b^2) * (l2sq f + l2sq g) := by
  have hI₁ := integrable_mul_compact_left hf hf hcf
  have hI₂ := integrable_mul_compact_left hg hg hcg
  have hs : Smooth (fun x => a * f x + b * g x) :=
    (contDiff_const.mul hf).add (contDiff_const.mul hg)
  have hc : HasCompactSupport (fun x => a * f x + b * g x) := hcf.mul_left.add hcg.mul_left
  have hsum : (a^2 + b^2) * (l2sq f + l2sq g) =
      ∫ x, (a^2 + b^2) * (f x * f x + g x * g x) := by
    unfold l2sq
    rw [integral_const_mul, integral_add hI₁ hI₂]
  rw [hsum]
  apply integral_mono (integrable_mul_compact_left hs hs hc)
    ((hI₁.add hI₂).const_mul (a^2 + b^2))
  intro x
  change (a * f x + b * g x) * (a * f x + b * g x) ≤
    (a^2 + b^2) * (f x * f x + g x * g x)
  nlinarith only [sq_nonneg (a * g x - b * f x)]

lemma integral_quadratic {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) (a b c : ℝ) :
    (∫ x, a * (f x * f x) + b * (f x * g x) + c * (g x * g x)) =
      a * l2sq f + b * (∫ x, f x * g x) + c * l2sq g := by
  have hI₁ := (integrable_mul_compact_left hf hf hcf).const_mul a
  have hI₂ := (integrable_mul_compact_left hf hg hcf).const_mul b
  have hI₃ := (integrable_mul_compact_left hg hg hcg).const_mul c
  rw [integral_add (f := fun x => a * (f x * f x) + b * (f x * g x))
    (hI₁.add hI₂) hI₃, integral_add hI₁ hI₂]
  simp only [integral_const_mul, l2sq]

lemma l2sq_linearCombination {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) (a b : ℝ) :
    l2sq (fun x => a * f x + b * g x) =
      a^2 * l2sq f + (2 * a * b) * (∫ x, f x * g x) + b^2 * l2sq g := by
  calc
    _ = ∫ x, a^2 * (f x * f x) + (2 * a * b) * (f x * g x) + b^2 * (g x * g x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := integral_quadratic hf hg hcf hcg _ _ _

lemma pairing_linearCombination {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) (a b c d : ℝ) :
    (∫ x, (a * f x + b * g x) * (c * f x + d * g x)) =
      (a * c) * l2sq f + (a * d + b * c) * (∫ x, f x * g x) + (b * d) * l2sq g := by
  calc
    _ = ∫ x, (a * c) * (f x * f x) + (a * d + b * c) * (f x * g x) +
        (b * d) * (g x * g x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := integral_quadratic hf hg hcf hcg _ _ _

def quadraticEnergy (A B C : ℝ) (f g : Plane → ℝ) : ℝ :=
  A * l2sq f + (2 * B) * (∫ x, f x * g x) + C * l2sq g

lemma plane_trace_energy_identity {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) (a₀ a₁ A B C : ℝ) :
    (a₀^2 + a₁^2) * quadraticEnergy A B C f g =
      (C * a₀^2 - 2 * B * a₀ * a₁ + A * a₁^2) * (l2sq f + l2sq g) +
      2 * (∫ x, ((A * a₀ + B * a₁) * f x + (B * a₀ + C * a₁) * g x) *
        (a₀ * f x + a₁ * g x)) -
      (A + C) * l2sq (fun x => a₀ * f x + a₁ * g x) := by
  rw [pairing_linearCombination hf hg hcf hcg, l2sq_linearCombination hf hg hcf hcg]
  unfold quadraticEnergy
  ring

open Filter in
lemma pairing_tendsto_zero_of_bound {f g : ℕ → Plane → ℝ} {r : ℕ → ℝ} {r₀ : ℝ}
    (hf : ∀ j, Smooth (f j)) (hg : ∀ j, Smooth (g j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hcg : ∀ j, HasCompactSupport (g j))
    (hbound : ∀ j, l2sq (f j) ≤ r j)
    (hr : Tendsto r atTop (𝓝 r₀))
    (hz : Tendsto (fun j => l2sq (g j)) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, f j x * g j x) atTop (𝓝 0) := by
  have hsq : Tendsto (fun j => (∫ x, f j x * g j x)^2) atTop (𝓝 0) :=
    squeeze_zero (fun j => sq_nonneg _) (fun j =>
      (pairing_sq_le (hf j) (hg j) (hcf j) (hcg j)).trans
        (mul_le_mul_of_nonneg_right (hbound j) (l2sq_nonneg (g j))))
      (by simpa using hr.mul hz)
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hroot

open Filter in

lemma plane_trace_energy_limit {f g : ℕ → Plane → ℝ} (a₀ a₁ A B C : ℝ)
    (ha : a₀^2 + a₁^2 ≠ 0)
    (hf : ∀ j, Smooth (f j)) (hg : ∀ j, Smooth (g j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hcg : ∀ j, HasCompactSupport (g j))
    (he : Tendsto (fun j => l2sq (f j) + l2sq (g j)) atTop (𝓝 (a₀^2 + a₁^2)))
    (hp : Tendsto (fun j => l2sq (fun x => a₀ * f j x + a₁ * g j x)) atTop (𝓝 0)) :
    Tendsto (fun j => quadraticEnergy A B C (f j) (g j) +
      (A * a₀^2 + 2 * B * a₀ * a₁ + C * a₁^2)) atTop
      (𝓝 ((a₀^2 + a₁^2) * (A + C))) := by
  let c₀ := A * a₀ + B * a₁
  let c₁ := B * a₀ + C * a₁
  have hpair : Tendsto (fun j => ∫ x, (c₀ * f j x + c₁ * g j x) *
      (a₀ * f j x + a₁ * g j x)) atTop (𝓝 0) := by
    apply pairing_tendsto_zero_of_bound
      (fun j => (contDiff_const.mul (hf j)).add (contDiff_const.mul (hg j)))
      (fun j => (contDiff_const.mul (hf j)).add (contDiff_const.mul (hg j)))
      (fun j => (hcf j).mul_left.add (hcg j).mul_left)
      (fun j => (hcf j).mul_left.add (hcg j).mul_left)
      (fun j => l2sq_linearCombination_le (hf j) (hg j) (hcf j) (hcg j) c₀ c₁)
      (he.const_mul (c₀^2 + c₁^2)) hp
  let J := C * a₀^2 - 2 * B * a₀ * a₁ + A * a₁^2
  have hid (j : ℕ) : (a₀^2 + a₁^2) * quadraticEnergy A B C (f j) (g j) =
      J * (l2sq (f j) + l2sq (g j)) +
      2 * (∫ x, (c₀ * f j x + c₁ * g j x) * (a₀ * f j x + a₁ * g j x)) -
      (A + C) * l2sq (fun x => a₀ * f j x + a₁ * g j x) :=
    plane_trace_energy_identity (hf j) (hg j) (hcf j) (hcg j) a₀ a₁ A B C
  have hl := (((he.const_mul J).add (hpair.const_mul 2)).sub (hp.const_mul (A + C)))
  have hq : Tendsto (fun j => quadraticEnergy A B C (f j) (g j)) atTop (𝓝 J) := by
    have hd := hl.div_const (a₀^2 + a₁^2)
    convert hd using 1
    · ext j
      rw [← hid j, mul_div_cancel_left₀ _ ha]
    · simp only [mul_zero, add_zero, sub_zero, mul_div_cancel_right₀ _ ha]
  have ht := hq.add_const (A * a₀^2 + 2 * B * a₀ * a₁ + C * a₁^2)
  convert ht using 1
  congr 1
  exact (plane_trace_sum a₀ a₁ A B C).symm


end Carleman
end SharpNodal

end

end OAI
