import OAI.Analysis.NodalLength.Commutator

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

lemma l2sq_pos {f : Plane → ℝ} (hf : Smooth f) (hc : HasCompactSupport f) (hn : f ≠ 0) :
    0 < l2sq f := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hn
  apply integral_pos_of_integrable_nonneg_nonzero
    (hf.continuous.mul hf.continuous) (integrable_mul_compact_left hf hf hc)
    (fun x => mul_self_nonneg (f x))
  exact mul_ne_zero hx hx

def l2norm (f : Plane → ℝ) : ℝ := Real.sqrt (l2sq f)

lemma l2norm_nonneg (f : Plane → ℝ) : 0 ≤ l2norm f := Real.sqrt_nonneg _

lemma l2norm_sq (f : Plane → ℝ) : (l2norm f)^2 = l2sq f :=
  Real.sq_sqrt (l2sq_nonneg f)

lemma normalize_l2sq {f : Plane → ℝ} (hf : Smooth f) (hc : HasCompactSupport f) (hn : f ≠ 0) :
    l2sq (fun x => (l2norm f)⁻¹ * f x) = 1 := by
  have hs : l2norm f ≠ 0 := (Real.sqrt_pos.mpr (l2sq_pos hf hc hn)).ne'
  rw [l2sq_const_mul, ← l2norm_sq f]
  field_simp

lemma partial_tsupport_subset (f : Plane → ℝ) (i : Fin 2) :
    tsupport (coordPartial f i) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)

lemma abs_mul_mul_le {c C : ℝ} (hC : 0 ≤ C) (hc : |c| ≤ C) (x y : ℝ) :
    |c * x * y| ≤ C / 2 * (x * x + y * y) := by
  have hxy : 2 * |x| * |y| ≤ x * x + y * y := by
    have h := two_mul_le_add_sq |x| |y|
    rw [sq_abs, sq_abs, pow_two, pow_two] at h
    exact h
  calc
    |c * x * y| = |c| * (|x| * |y|) := by rw [abs_mul, abs_mul]; ring
    _ ≤ C * (|x| * |y|) := mul_le_mul_of_nonneg_right hc (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hxy hC]

lemma integral_coefficient_mul_abs_le {a f g : Plane → ℝ} {C : ℝ}
    (ha : Smooth a) (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g)
    (hC : 0 ≤ C) (hb : ∀ x ∈ tsupport f, |a x| ≤ C) :
    |∫ x, a x * f x * g x| ≤ C / 2 * (l2sq f + l2sq g) := by
  have hI : Integrable (fun x => a x * f x * g x) :=
    integrable_mul_compact_left (ha.mul hf) hg hcf.mul_left
  have hIf := integrable_mul_compact_left hf hf hcf
  have hIg := integrable_mul_compact_left hg hg hcg
  have hbound (x : Plane) : |a x * f x * g x| ≤ C / 2 * (f x * f x + g x * g x) := by
    by_cases hx : f x = 0
    · simp only [hx, mul_zero, zero_mul, abs_zero, zero_add]
      exact mul_nonneg (div_nonneg hC (by norm_num)) (mul_self_nonneg _)
    · exact abs_mul_mul_le hC (hb x (subset_closure hx)) _ _
  calc
    _ ≤ ∫ x, |a x * f x * g x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, C / 2 * (f x * f x + g x * g x) :=
      integral_mono hI.abs (by exact (hIf.add hIg).const_mul (C / 2)) hbound
    _ = _ := by rw [integral_const_mul, integral_add hIf hIg]; rfl

lemma integral_coefficient_square_abs_le {a f : Plane → ℝ} {C : ℝ}
    (ha : Smooth a) (hf : Smooth f) (hc : HasCompactSupport f)
    (hC : 0 ≤ C) (hb : ∀ x ∈ tsupport f, |a x| ≤ C) :
    |∫ x, a x * (f x * f x)| ≤ C * l2sq f := by
  have h := integral_coefficient_mul_abs_le ha hf hf hc hc hC hb
  simp only [mul_assoc] at h
  linarith only [h]

open Filter in
lemma coefficient_pairing_tendsto_zero {a f g : ℕ → Plane → ℝ} {e : ℕ → ℝ} {L : ℝ}
    (ha : ∀ j, Smooth (a j)) (hf : ∀ j, Smooth (f j)) (hg : ∀ j, Smooth (g j))
    (hcf : ∀ j, HasCompactSupport (f j)) (hcg : ∀ j, HasCompactSupport (g j))
    (he : ∀ j, 0 ≤ e j) (hb : ∀ j x, x ∈ tsupport (f j) → |a j x| ≤ e j)
    (he0 : Tendsto e atTop (𝓝 0))
    (hL : Tendsto (fun j => l2sq (f j) + l2sq (g j)) atTop (𝓝 L)) :
    Tendsto (fun j => ∫ x, a j x * f j x * g j x) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero (fun j => abs_nonneg _)
    (fun j => integral_coefficient_mul_abs_le (ha j) (hf j) (hg j) (hcf j) (hcg j) (he j) (hb j))
  simpa only [zero_div, zero_mul] using (he0.div_const 2).mul hL

def plusPart (a v : Plane → ℝ) (x : Plane) : ℝ := euclideanLaplacian v x + a x * v x

lemma smooth_plus {a v : Plane → ℝ} (ha : Smooth a) (hv : Smooth v) :
    Smooth (plusPart a v) := (smooth_laplacian hv).add (ha.mul hv)

lemma compact_plus {a v : Plane → ℝ} (hc : HasCompactSupport v) :
    HasCompactSupport (plusPart a v) := (compact_laplacian hc).add hc.mul_left

def gradientEnergy (v : Plane → ℝ) : ℝ := ∑ i : Fin 2, l2sq (coordPartial v i)

lemma gradientEnergy_nonneg (v : Plane → ℝ) : 0 ≤ gradientEnergy v :=
  Finset.sum_nonneg fun _ _ => l2sq_nonneg _

lemma plus_energy_identity {a v : Plane → ℝ} (ha : Smooth a)
    (hv : Smooth v) (hc : HasCompactSupport v) :
    (∫ x, plusPart a v x * v x) = -gradientEnergy v + (∫ x, a x * (v x * v x)) := by
  unfold plusPart
  simp_rw [add_mul]
  rw [integral_add (integrable_mul_compact_right (smooth_laplacian hv) hv hc)
    (integrable_mul_compact_right (ha.mul hv) hv hc), integral_laplacian_mul hv hc]
  simp only [gradientEnergy, l2sq, mul_assoc]

lemma pairing_abs_le_l2norm {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    |∫ x, f x * g x| ≤ l2norm f * l2norm g := by
  have h := pairing_sq_le hf hg hcf hcg
  have h₁ := l2norm_sq f
  have h₂ := l2norm_sq g
  have h₀ := mul_nonneg (l2norm_nonneg f) (l2norm_nonneg g)
  nlinarith only [h, h₁, h₂, sq_abs (∫ x, f x * g x), abs_nonneg (∫ x, f x * g x), h₀]

lemma l2norm_eq_one {f : Plane → ℝ} (h : l2sq f = 1) : l2norm f = 1 := by
  simp only [l2norm, h, Real.sqrt_one]

lemma plus_energy_bound {a v : Plane → ℝ} {C : ℝ} (ha : Smooth a)
    (hv : Smooth v) (hc : HasCompactSupport v) (hv1 : l2sq v = 1)
    (hC : 0 ≤ C) (haC : ∀ x ∈ tsupport v, |a x| ≤ C) :
    gradientEnergy v ≤ C + l2norm (plusPart a v) := by
  have hid := plus_energy_identity ha hv hc
  have hb := pairing_abs_le_l2norm (smooth_plus ha hv) hv (compact_plus hc) hc
  rw [l2norm_eq_one hv1, mul_one] at hb
  have haI := integral_coefficient_square_abs_le ha hv hc hC haC
  rw [hv1, mul_one] at haI
  linarith only [hid, (neg_le_abs (∫ x, plusPart a v x * v x)).trans hb,
    (le_abs_self (∫ x, a x * (v x * v x))).trans haI]

lemma commutator_le_sum_square {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    2 * (∫ x, f x * g x) ≤ l2sq (fun x => f x + g x) := by
  rw [l2sq_add hf hg hcf hcg]
  linarith only [l2sq_nonneg f, l2sq_nonneg g]

lemma carleman_scalar_bootstrap {X Y E S D t c : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (_hE : 0 ≤ E)
    (hS : 1 ≤ S) (hD : S ≤ D) (ht : 0 ≤ t) (htsq : t^2 = S * D^2)
    (hc : 1 ≤ c)
    (hpair : X^2 + Y^2 ≤ c * S * (E + D^2))
    (henergy : E ≤ c * D^2 + X) :
    X ≤ (2*c + 2) * t ∧ Y ≤ (2*c + 2) * t ∧ E ≤ (3*c + 2) * D^2 := by
  have hD0 : 0 ≤ D := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hSD : S ≤ D^2 := by nlinarith only [hS, hD]
  have hSt : S ≤ t := by
    nlinarith only [ht, hS, htsq, mul_le_mul_of_nonneg_left hSD hS0]
  have htD : t ≤ D^2 := by
    have h := mul_le_mul_of_nonneg_right hSD (sq_nonneg D)
    nlinarith only [ht, htsq, h, sq_nonneg D]
  have hbase : X^2 + Y^2 ≤ c * S * X + c * (c+1) * t^2 := by
    calc
      _ ≤ c * S * (E + D^2) := hpair
      _ ≤ c * S * (c * D^2 + X + D^2) :=
        mul_le_mul_of_nonneg_left (add_le_add henergy le_rfl) (mul_nonneg hc0 hS0)
      _ = _ := by rw [htsq]; ring
  have hSX : c * S * X ≤ c * t * X := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSt hc0) hX
  have hA0 : 0 ≤ (2*c+2)*t := mul_nonneg (by linarith) ht
  have hct2 := mul_nonneg (sq_nonneg c) (sq_nonneg t)
  have hct1 := mul_nonneg hc0 (sq_nonneg t)
  have ht2 := sq_nonneg t
  have hsum : X^2 + 2*Y^2 ≤ (3*c^2+2*c)*t^2 := by
    nlinarith only [hbase, hSX, sq_nonneg (X-c*t)]
  have hXb : X ≤ (2*c+2) * t := by
    apply (sq_le_sq₀ hX hA0).mp
    nlinarith only [hsum, sq_nonneg Y, hct2, hct1, ht2]
  have hYb : Y ≤ (2*c+2) * t := by
    apply (sq_le_sq₀ hY hA0).mp
    nlinarith only [hsum, sq_nonneg X, hct2, hct1, ht2]
  refine ⟨hXb, hYb, ?_⟩
  have hxD := hXb.trans (mul_le_mul_of_nonneg_left htD (by linarith))
  linarith only [henergy, hxD]

def hessianEnergy (T v : Plane → ℝ) : ℝ :=
  ∑ j : Fin 2, ∑ i : Fin 2,
    ∫ x, coordPartial (coordPartial T j) i x * coordPartial v i x * coordPartial v j x

def bilaplacianEnergy (T v : Plane → ℝ) : ℝ :=
  ∑ j : Fin 2, ∑ i : Fin 2,
    ∫ x, coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x * (v x * v x)

def potentialTransport (a T v : Plane → ℝ) : ℝ :=
  ∑ i : Fin 2, ∫ x, coordPartial a i x * coordPartial T i x * (v x * v x)

lemma transport_commutator_energy {a T v : Plane → ℝ}
    (ha : Smooth a) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) :
    2 * (∫ x, plusPart a v x * skewPart T v x) =
      4 * hessianEnergy T v - bilaplacianEnergy T v + 2 * potentialTransport a T v := by
  rw [show plusPart a v = (fun x => euclideanLaplacian v x + a x * v x) from rfl,
    transport_commutator ha hT hv hc]
  simp only [hessianEnergy, bilaplacianEnergy, potentialTransport,
    Finset.sum_sub_distrib, Finset.mul_sum]

lemma hessianEnergy_abs_le {T v : Plane → ℝ} {C : ℝ}
    (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) (hC : 0 ≤ C)
    (hb : ∀ i j x, x ∈ tsupport v → |coordPartial (coordPartial T j) i x| ≤ C) :
    |hessianEnergy T v| ≤ 2 * C * gradientEnergy v := by
  have hi (i j : Fin 2) :
      |∫ x, coordPartial (coordPartial T j) i x * coordPartial v i x * coordPartial v j x| ≤
        C / 2 * (l2sq (coordPartial v i) + l2sq (coordPartial v j)) :=
    integral_coefficient_mul_abs_le (smooth_partial (smooth_partial hT j) i)
      (smooth_partial hv i) (smooth_partial hv j) (compact_partial hc i) (compact_partial hc j)
      hC (fun x hx => hb i j x (partial_tsupport_subset v i hx))
  calc
    _ ≤ ∑ j : Fin 2, ∑ i : Fin 2,
        |∫ x, coordPartial (coordPartial T j) i x * coordPartial v i x * coordPartial v j x| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j : Fin 2, ∑ i : Fin 2,
        C / 2 * (l2sq (coordPartial v i) + l2sq (coordPartial v j)) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hi i j
    _ = _ := by simp only [gradientEnergy, Fin.sum_univ_two]; ring

lemma bilaplacianEnergy_abs_le {T v : Plane → ℝ} {C : ℝ}
    (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) (hC : 0 ≤ C)
    (hb : ∀ i j x, x ∈ tsupport v →
      |coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x| ≤ C) :
    |bilaplacianEnergy T v| ≤ 4 * C * l2sq v := by
  have hi (i j : Fin 2) := integral_coefficient_square_abs_le
    (smooth_partial (smooth_partial (smooth_partial (smooth_partial hT j) j) i) i)
    hv hc hC (hb i j)
  calc
    _ ≤ ∑ j : Fin 2, ∑ i : Fin 2,
        |∫ x, coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x * (v x * v x)| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j : Fin 2, ∑ i : Fin 2, C * l2sq v :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hi i j
    _ = _ := by simp only [Fin.sum_univ_two]; ring

lemma potentialTransport_abs_le {a T v : Plane → ℝ} {C : ℝ}
    (ha : Smooth a) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) (hC : 0 ≤ C)
    (hb : ∀ i x, x ∈ tsupport v → |coordPartial a i x * coordPartial T i x| ≤ C) :
    |potentialTransport a T v| ≤ 2 * C * l2sq v := by
  have hi (i : Fin 2) := integral_coefficient_square_abs_le
    ((smooth_partial ha i).mul (smooth_partial hT i)) hv hc hC (hb i)
  calc
    _ ≤ ∑ i : Fin 2, |∫ x, coordPartial a i x * coordPartial T i x * (v x * v x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 2, C * l2sq v := Finset.sum_le_sum fun i _ => hi i
    _ = _ := by simp only [Fin.sum_univ_two]; ring

lemma transport_commutator_abs_le {a T v : Plane → ℝ} {c S D : ℝ}
    (ha : Smooth a) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v)
    (hc0 : 0 ≤ c) (hS : 0 ≤ S) (hv1 : l2sq v = 1)
    (hH : ∀ i j x, x ∈ tsupport v → |coordPartial (coordPartial T j) i x| ≤ c*S)
    (hB : ∀ i j x, x ∈ tsupport v →
      |coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x| ≤ c*S*D^2)
    (hA : ∀ i x, x ∈ tsupport v → |coordPartial a i x * coordPartial T i x| ≤ c*S*D^2) :
    |2 * (∫ x, plusPart a v x * skewPart T v x)| ≤
      8*c*S*(gradientEnergy v + D^2) := by
  rw [transport_commutator_energy ha hT hv hc]
  have hH' := hessianEnergy_abs_le hT hv hc (mul_nonneg hc0 hS) hH
  have hB' := bilaplacianEnergy_abs_le hT hv hc
    (mul_nonneg (mul_nonneg hc0 hS) (sq_nonneg D)) hB
  have hA' := potentialTransport_abs_le ha hT hv hc
    (mul_nonneg (mul_nonneg hc0 hS) (sq_nonneg D)) hA
  rw [hv1, mul_one] at hB' hA'
  calc
    _ ≤ |4 * hessianEnergy T v - bilaplacianEnergy T v| + |2 * potentialTransport a T v| :=
      abs_add_le _ _
    _ ≤ |4 * hessianEnergy T v| + |bilaplacianEnergy T v| + |2 * potentialTransport a T v| :=
      add_le_add (abs_sub _ _) le_rfl
    _ = 4*|hessianEnergy T v| + |bilaplacianEnergy T v| + 2*|potentialTransport a T v| := by
      rw [abs_mul, abs_mul]; norm_num
    _ ≤ _ := by linarith only [hH', hB', hA']

lemma operator_bootstrap {a T v : Plane → ℝ} {c S D : ℝ}
    (ha : Smooth a) (hT : Smooth T) (hv : Smooth v) (hcv : HasCompactSupport v)
    (hc : 1 ≤ c) (hS : 1 ≤ S) (hD : S ≤ D) (hv1 : l2sq v = 1)
    (hP : ∀ x ∈ tsupport v, |a x| ≤ c*D^2)
    (hH : ∀ i j x, x ∈ tsupport v → |coordPartial (coordPartial T j) i x| ≤ c*S)
    (hB : ∀ i j x, x ∈ tsupport v →
      |coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x| ≤ c*S*D^2)
    (hA : ∀ i x, x ∈ tsupport v → |coordPartial a i x * coordPartial T i x| ≤ c*S*D^2)
    (hsmall : l2sq (fun x => plusPart a v x + skewPart T v x) ≤ S*D^2) :
    l2norm (plusPart a v) ≤ (16*c+4) * (Real.sqrt S * D) ∧
    l2norm (skewPart T v) ≤ (16*c+4) * (Real.sqrt S * D) ∧
    gradientEnergy v ≤ (24*c+5)*D^2 := by
  have hc0 : 0 ≤ c := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hcomm := transport_commutator_abs_le ha hT hv hcv hc0 hS0 hv1 hH hB hA
  have hdecomp := l2sq_add (smooth_plus ha hv) (smooth_skew hT hv) (compact_plus hcv)
    (compact_skew hcv)
  have hpair : (l2norm (plusPart a v))^2 + (l2norm (skewPart T v))^2 ≤
      (8*c+1)*S*(gradientEnergy v+D^2) := by
    rw [l2norm_sq, l2norm_sq]
    have hlow := (neg_le_abs (2*(∫ x, plusPart a v x * skewPart T v x))).trans hcomm
    have hpos := mul_nonneg hS0 (gradientEnergy_nonneg v)
    nlinarith only [hsmall, hdecomp, hlow, hpos]
  have henergy : gradientEnergy v ≤ (8*c+1)*D^2 + l2norm (plusPart a v) := by
    have h := plus_energy_bound ha hv hcv hv1 (mul_nonneg hc0 (sq_nonneg D)) hP
    have h' := mul_nonneg (show 0 ≤ 7*c+1 by linarith) (sq_nonneg D)
    linarith only [h, h']
  have hb := carleman_scalar_bootstrap (l2norm_nonneg _) (l2norm_nonneg _)
    (gradientEnergy_nonneg v) hS hD (mul_nonneg (Real.sqrt_nonneg S) hD0)
    (by rw [mul_pow, Real.sq_sqrt hS0]) (show 1 ≤ 8*c+1 by linarith) hpair henergy
  simpa only [show 2*(8*c+1)+2 = 16*c+4 by ring,
    show 3*(8*c+1)+2 = 24*c+5 by ring] using hb


end Carleman
end SharpNodal

end

end OAI
