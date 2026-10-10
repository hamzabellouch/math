import Mathlib
import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! Loewner Reflection for chordal SLE. -/

section
section

open Set Filter Complex Metric ComplexConjugate
open scoped Topology NNReal
namespace SLEExactGauge

 

noncomputable def loewnerMirror : ℂ ≃ₜ ℂ where
  toFun z := -conj z
  invFun z := -conj z
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := Complex.continuous_conj.neg
  continuous_invFun := Complex.continuous_conj.neg

@[simp] lemma loewnerMirror_apply (z : ℂ) : loewnerMirror z = -conj z := rfl
@[simp] lemma loewnerMirror_twice (z : ℂ) : loewnerMirror (loewnerMirror z) = z := by simp
@[simp] lemma loewnerMirror_im (z : ℂ) : (loewnerMirror z).im = z.im := by simp
@[simp] lemma loewnerMirror_re (z : ℂ) : (loewnerMirror z).re = -z.re := by simp
@[simp] lemma loewnerMirror_dist (z w : ℂ) : dist (loewnerMirror z) (loewnerMirror w) = dist z w := by
  simp only [loewnerMirror_apply,dist_neg_neg,Complex.dist_conj_conj]
@[simp] lemma loewnerMirror_norm (z : ℂ) : ‖loewnerMirror z‖ = ‖z‖ := by simp

lemma loewnerMirror_bounded (s : Set ℂ) :
    Bornology.IsBounded (loewnerMirror '' s) ↔ Bornology.IsBounded s := by
  rw [Metric.isBounded_image_iff,Metric.isBounded_iff]
  simp only [loewnerMirror_dist]

lemma loewnerMirror_free (γ : ℝ≥0 → ℂ) (t : ℝ≥0) (z : ℂ) :
    loewnerMirror z ∈ upperHalfPlane \ ((loewnerMirror ∘ γ) '' Icc 0 t) ↔
      z ∈ upperHalfPlane \ (γ '' Icc 0 t) := by
  constructor
  · rintro ⟨hup,hn⟩
    refine ⟨by simpa only [upperHalfPlane,mem_ofPred_eq,loewnerMirror_im] using hup,?_⟩
    rintro ⟨u,hu,rfl⟩
    exact hn ⟨u,hu,rfl⟩
  · rintro ⟨hup,hn⟩
    refine ⟨by simpa only [upperHalfPlane,mem_ofPred_eq,loewnerMirror_im] using hup,?_⟩
    rintro ⟨u,hu,he⟩
    exact hn ⟨u,hu,loewnerMirror.injective he⟩

lemma loewnerMirror_free_image (γ : ℝ≥0 → ℂ) (t : ℝ≥0) :
    loewnerMirror '' (upperHalfPlane \ (γ '' Icc 0 t)) =
      upperHalfPlane \ ((loewnerMirror ∘ γ) '' Icc 0 t) := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact (loewnerMirror_free γ t w).mpr hw
  · intro hz
    refine ⟨loewnerMirror z,?_,loewnerMirror_twice z⟩
    apply (loewnerMirror_free γ t (loewnerMirror z)).mp
    simpa only [loewnerMirror_twice] using hz

lemma loewnerMirror_surviving (γ : ℝ≥0 → ℂ) (t : ℝ≥0) (z : ℂ) :
    loewnerMirror z ∈ survivingDomain (loewnerMirror ∘ γ) t ↔
      z ∈ survivingDomain γ t := by
  have hcc (hz : z ∈ upperHalfPlane \ (γ '' Icc 0 t)) :
      loewnerMirror '' connectedComponentIn (upperHalfPlane \ (γ '' Icc 0 t)) z =
        connectedComponentIn (upperHalfPlane \ ((loewnerMirror ∘ γ) '' Icc 0 t)) (loewnerMirror z) := by
    rw [loewnerMirror.image_connectedComponentIn hz,loewnerMirror_free_image]
  constructor
  · rintro ⟨hz,hun⟩
    have hz' := (loewnerMirror_free γ t z).mp hz
    refine ⟨hz',?_⟩
    intro hb
    apply hun
    rw [← hcc hz']
    exact (loewnerMirror_bounded _).mpr hb
  · rintro ⟨hz,hun⟩
    refine ⟨(loewnerMirror_free γ t z).mpr hz,?_⟩
    intro hb
    apply hun
    apply (loewnerMirror_bounded _).mp
    rwa [hcc hz]

lemma mirror_conjugate_differentiable {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f (loewnerMirror z)) :
    DifferentiableAt ℂ (fun w => loewnerMirror (f (loewnerMirror w))) z := by
  have hg : DifferentiableAt ℂ (fun w => f (-w)) (conj z) :=
    hf.comp (conj z) (differentiableAt_id.neg)
  have hh := hg.conj_conj.neg
  convert! hh using 1
  simp only [Complex.conj_conj]

end SLEExactGauge

namespace SLEExactGauge

 

lemma IsCapacityTwoWitness.mirror
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) :
    IsCapacityTwoWitness (fun t => -U t) (loewnerMirror ∘ γ)
      (fun t z => loewnerMirror (G t (loewnerMirror z)))
      (fun t z => loewnerMirror (F t (loewnerMirror z))) := by
  have hm (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain (loewnerMirror ∘ γ) t) :
      loewnerMirror z ∈ survivingDomain γ t := by
    apply (loewnerMirror_surviving γ t (loewnerMirror z)).mp
    simpa only [loewnerMirror_twice] using hz
  have hup (z : ℂ) : loewnerMirror z ∈ upperHalfPlane ↔ z ∈ upperHalfPlane := by
    simp only [upperHalfPlane,mem_ofPred_eq,loewnerMirror_im]
  rcases h with ⟨hc,h0,him,hG,hF,hGm,hFm,hFG,hGF,hG0,hode,hnorm,htip⟩
  refine ⟨loewnerMirror.continuous.comp hc,by simp [h0],?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro t; simpa only [Function.comp_apply,loewnerMirror_im] using him t
  · intro t z hz
    exact (mirror_conjugate_differentiable ((hG t (loewnerMirror z) (hm t z hz)).differentiableAt
      ((isOpen_survivingDomain hc t).mem_nhds (hm t z hz)))).differentiableWithinAt
  · intro t z hz
    exact (mirror_conjugate_differentiable ((hF t (loewnerMirror z) ((hup z).mpr hz)).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds ((hup z).mpr hz)))).differentiableWithinAt
  · intro t z hz
    exact (hup _).mpr (hGm t (hm t z hz))
  · intro t z hz
    exact (loewnerMirror_surviving γ t _).mpr (hFm t ((hup z).mpr hz))
  · intro t z hz
    dsimp only
    rw [loewnerMirror_twice,hFG t _ (hm t z hz),loewnerMirror_twice]
  · intro t z hz
    dsimp only
    rw [loewnerMirror_twice,hGF t _ ((hup z).mpr hz),loewnerMirror_twice]
  · intro z hz
    dsimp only
    rw [hG0 _ ((hup z).mpr hz),loewnerMirror_twice]
  · intro t z hz
    have hd := (hode t (loewnerMirror z) (hm t z hz)).star.neg
    convert! hd using 1
    dsimp only
    simp only [loewnerMirror_apply,Complex.ofReal_neg,neg_sub_neg,Complex.star_def]
    rw [← neg_sub,div_neg]
    simp only [map_div₀,map_sub,map_ofNat,Complex.conj_ofReal]
  · intro t
    have hmir : Tendsto loewnerMirror
        (cocompact ℂ ⊓ 𝓟 (survivingDomain (loewnerMirror ∘ γ) t))
        (cocompact ℂ ⊓ 𝓟 (survivingDomain γ t)) := by
      apply tendsto_inf.mpr
      constructor
      · exact (show Tendsto loewnerMirror (cocompact ℂ) (cocompact ℂ) from
          le_of_eq loewnerMirror.map_cocompact).mono_left inf_le_left
      · apply tendsto_principal.mpr
        exact (eventually_inf_principal.mpr (Filter.Eventually.of_forall fun z hz => hm t z hz))
    have hh := Complex.continuous_conj.continuousAt.tendsto.comp ((hnorm t).comp hmir)
    convert! hh using 1
    · ext z
      simp only [Function.comp_def,loewnerMirror_apply,map_mul,map_sub,map_neg,
        Complex.conj_conj]
      ring
    · simp only [map_mul,map_ofNat,Complex.conj_ofReal]
  · intro t
    have hh := loewnerMirror.continuous.continuousAt.tendsto.comp (htip t)
    convert! hh using 1
    ext y
    apply Complex.ext <;> simp [add_comm]

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

noncomputable def rightCenter (a u : ℝ) (z : ℂ) : ℂ :=
  ((max a (z.re - u) : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * I

noncomputable def rightField (a u : ℝ) (z : ℂ) : ℂ := 2 * (rightCenter a u z)⁻¹

lemma rightCenter_re (a u : ℝ) (z : ℂ) : (rightCenter a u z).re = max a (z.re-u) := by
  simp [rightCenter]

lemma rightCenter_norm (a u : ℝ) (z : ℂ) : a ≤ ‖rightCenter a u z‖ :=
  (le_max_left a (z.re-u)).trans ((rightCenter_re a u z).symm.le.trans (Complex.re_le_norm _))

lemma rightCenter_ne_zero {a : ℝ} (ha : 0 < a) (u : ℝ) (z : ℂ) : rightCenter a u z ≠ 0 :=
  norm_pos_iff.mp (ha.trans_le (rightCenter_norm a u z))

lemma rightCenter_eq {a u : ℝ} {z : ℂ} (hz : a ≤ z.re-u) : rightCenter a u z = z - (u : ℂ) := by
  apply Complex.ext <;> simp [rightCenter, max_eq_right hz]

lemma rightCenter_dist (a u : ℝ) (z w : ℂ) :
    dist (rightCenter a u z) (rightCenter a u w) ≤ 2 * dist z w := by
  have hr : |max a (z.re-u) - max a (w.re-u)| ≤ ‖z-w‖ := by
    have h := ((LipschitzWith.id : LipschitzWith 1 (fun x : ℝ => x)).const_max a).dist_le_mul
      (z.re-u) (w.re-u)
    have hh : |max a (z.re-u) - max a (w.re-u)| ≤ |z.re-w.re| := by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul,id_eq,sub_sub_sub_cancel_right] using h
    exact hh.trans (Complex.abs_re_le_norm (z-w))
  have hi : |z.im-w.im| ≤ ‖z-w‖ := Complex.abs_im_le_norm (z-w)
  have he : rightCenter a u z - rightCenter a u w =
      ((max a (z.re-u) - max a (w.re-u) : ℝ) : ℂ) + ((z.im-w.im : ℝ) : ℂ)*I := by
    simp only [rightCenter,Complex.ofReal_sub]; ring
  rw [dist_eq_norm,he]
  have hb := norm_add_le ((max a (z.re-u)-max a (w.re-u) : ℝ) : ℂ) (((z.im-w.im : ℝ) : ℂ)*I)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one] at hb
  rw [dist_eq_norm]
  linarith

lemma rightField_bound {a : ℝ} (ha : 0 < a) (u : ℝ) (z : ℂ) :
    ‖rightField a u z‖ ≤ 2 * a⁻¹ := by
  have hi : ‖(rightCenter a u z)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ ha (rightCenter_norm a u z)
  simpa only [rightField, norm_mul, norm_ofNat] using mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)

lemma rightField_lipschitz {a : ℝ} (ha : 0 < a) (u : ℝ) :
    LipschitzWith ⟨4 * a⁻¹ ^ 2, by positivity⟩ (rightField a u) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hz : ‖(rightCenter a u z)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]; exact inv_anti₀ ha (rightCenter_norm a u z)
  have hw : ‖(rightCenter a u w)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]; exact inv_anti₀ ha (rightCenter_norm a u w)
  rw [dist_eq_norm, rightField, rightField, ← mul_sub, norm_mul, norm_ofNat,
    inv_sub_inv' (rightCenter_ne_zero ha _ _) (rightCenter_ne_zero ha _ _), norm_mul, norm_mul]
  calc
    _ ≤ 2 * (a⁻¹ * (2 * dist z w) * a⁻¹) := by
      gcongr
      simpa only [← dist_eq_norm, dist_comm] using rightCenter_dist a u z w
    _ = _ := by change 2 * (a⁻¹ * (2 * dist z w) * a⁻¹) = (4 * a⁻¹ ^ 2) * dist z w; ring

lemma continuous_rightField {a : ℝ} (ha : 0 < a) :
    Continuous (fun p : ℝ × ℂ => rightField a p.1 p.2) := by
  apply continuous_const.mul
  apply Continuous.inv₀
  · exact ((Complex.continuous_ofReal.comp (continuous_const.max
      ((Complex.continuous_re.comp continuous_snd).sub continuous_fst))).add
      ((Complex.continuous_ofReal.comp (Complex.continuous_im.comp continuous_snd)).mul continuous_const))
  · intro p; exact rightCenter_ne_zero ha _ _

lemma rightField_eq {a u : ℝ} {z : ℂ} (hz : a ≤ z.re-u) :
    rightField a u z = 2/(z-(u:ℂ)) := by
  simp only [rightField,rightCenter_eq hz,div_eq_mul_inv]

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

noncomputable def reverseCenter (a u : ℝ) (z : ℂ) : ℂ :=
  ((z.re - u : ℝ) : ℂ) + ((max a z.im : ℝ) : ℂ) * I

noncomputable def reverseField (a u : ℝ) (z : ℂ) : ℂ := -2 * (reverseCenter a u z)⁻¹

lemma reverseCenter_im (a u : ℝ) (z : ℂ) : (reverseCenter a u z).im = max a z.im := by
  simp [reverseCenter]

lemma reverseCenter_norm (a u : ℝ) (z : ℂ) : a ≤ ‖reverseCenter a u z‖ :=
  (le_max_left a z.im).trans ((reverseCenter_im a u z).symm.le.trans (Complex.im_le_norm _))

lemma reverseCenter_ne_zero {a : ℝ} (ha : 0 < a) (u : ℝ) (z : ℂ) : reverseCenter a u z ≠ 0 :=
  norm_pos_iff.mp (ha.trans_le (reverseCenter_norm a u z))

lemma reverseCenter_eq {a u : ℝ} {z : ℂ} (hz : a ≤ z.im) : reverseCenter a u z = z - (u : ℂ) := by
  apply Complex.ext <;> simp [reverseCenter, max_eq_right hz]

lemma reverseCenter_dist (a u : ℝ) (z w : ℂ) :
    dist (reverseCenter a u z) (reverseCenter a u w) ≤ 2 * dist z w := by
  have hr : |z.re - w.re| ≤ ‖z - w‖ := Complex.abs_re_le_norm (z - w)
  have hi : |max a z.im - max a w.im| ≤ ‖z - w‖ := by
    have h := ((LipschitzWith.id : LipschitzWith 1 (fun x : ℝ => x)).const_max a).dist_le_mul z.im w.im
    have hh : |max a z.im - max a w.im| ≤ |z.im - w.im| := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul, id_eq] using h
    exact hh.trans (Complex.abs_im_le_norm (z - w))
  have he : reverseCenter a u z - reverseCenter a u w =
      ((z.re - w.re : ℝ) : ℂ) + ((max a z.im - max a w.im : ℝ) : ℂ) * I := by
    simp only [reverseCenter, Complex.ofReal_sub]
    ring
  rw [dist_eq_norm, he]
  have hb := norm_add_le ((z.re - w.re : ℝ) : ℂ) (((max a z.im - max a w.im : ℝ) : ℂ) * I)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hb
  rw [dist_eq_norm]
  linarith

lemma reverseField_bound {a : ℝ} (ha : 0 < a) (u : ℝ) (z : ℂ) :
    ‖reverseField a u z‖ ≤ 2 * a⁻¹ := by
  have hi : ‖(reverseCenter a u z)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ ha (reverseCenter_norm a u z)
  simpa only [reverseField, norm_mul, norm_neg, norm_ofNat] using mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)

lemma reverseField_lipschitz {a : ℝ} (ha : 0 < a) (u : ℝ) :
    LipschitzWith ⟨4 * a⁻¹ ^ 2, by positivity⟩ (reverseField a u) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hz : ‖(reverseCenter a u z)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]; exact inv_anti₀ ha (reverseCenter_norm a u z)
  have hw : ‖(reverseCenter a u w)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]; exact inv_anti₀ ha (reverseCenter_norm a u w)
  rw [dist_eq_norm, reverseField, reverseField, ← mul_sub, norm_mul, norm_neg, norm_ofNat,
    inv_sub_inv' (reverseCenter_ne_zero ha _ _) (reverseCenter_ne_zero ha _ _), norm_mul, norm_mul]
  calc
    _ ≤ 2 * (a⁻¹ * (2 * dist z w) * a⁻¹) := by
      gcongr
      simpa only [← dist_eq_norm, dist_comm] using reverseCenter_dist a u z w
    _ = _ := by change 2 * (a⁻¹ * (2 * dist z w) * a⁻¹) = (4 * a⁻¹ ^ 2) * dist z w; ring

lemma continuous_reverseField {a : ℝ} (ha : 0 < a) :
    Continuous (fun p : ℝ × ℂ => reverseField a p.1 p.2) := by
  apply continuous_const.mul
  apply Continuous.inv₀
  · exact ((Complex.continuous_ofReal.comp ((Complex.continuous_re.comp continuous_snd).sub continuous_fst)).add
      ((Complex.continuous_ofReal.comp (continuous_const.max (Complex.continuous_im.comp continuous_snd))).mul continuous_const))
  · intro p; exact reverseCenter_ne_zero ha _ _

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

lemma exists_random_initial_bounded_flow
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (V : ℝ → Ω → E → E) (q₀ : Ω → E) (hq₀ : Measurable q₀) (L K : ℝ≥0)
    (hV : Measurable (fun p : (ℝ × Ω) × E => V p.1.1 p.1.2 p.2))
    (hc : ∀ ω x, Continuous (fun t : ℝ => V t ω x))
    (hl : ∀ ω t, LipschitzWith K (V t ω))
    (hb : ∀ ω t x, ‖V t ω x‖ ≤ L) :
    ∃ X : ℝ → Ω → E,
      Measurable (fun p : ℝ × Ω => X p.1 p.2) ∧
      (∀ ω, X 0 ω = q₀ ω) ∧
      (∀ ω t, 0 ≤ t → HasDerivWithinAt (fun s => X s ω) (V t ω (X t ω)) (Ici 0) t) := by
  let W (t : ℝ) (ω : Ω) (x : E) := V t ω (q₀ ω + x)
  have hW : Measurable (fun p : (ℝ × Ω) × E => W p.1.1 p.1.2 p.2) :=
    hV.comp (measurable_fst.prodMk ((hq₀.comp (measurable_snd.comp measurable_fst)).add measurable_snd))
  have hWl (ω : Ω) (t : ℝ) : LipschitzWith K (W t ω) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [W, dist_add_left] using (hl ω t).dist_le_mul (q₀ ω + x) (q₀ ω + y)
  obtain ⟨Y, hYm, _, hY0, hYd, _⟩ := exists_measurable_global_bounded_ode_picard
    W 0 L K hW (fun ω x => hc ω (q₀ ω + x)) hWl (fun ω t x => hb ω t (q₀ ω + x))
  refine ⟨fun t ω => q₀ ω + Y t ω, (hq₀.comp measurable_snd).add hYm, ?_, ?_⟩
  · intro ω; change q₀ ω + Y 0 ω = q₀ ω; rw [hY0, add_zero]
  · intro ω t ht
    exact (hYd ω t ht).const_add (q₀ ω)

lemma exists_measurable_reverse_flow
    {Ω : Type*} [MeasurableSpace Ω]
    (U : ℝ → Ω → ℝ) (hUm : Measurable (fun p : ℝ × Ω => U p.1 p.2))
    (hUc : ∀ ω, Continuous (fun t => U t ω))
    (w : Ω → ℂ) (hwm : Measurable w) {a : ℝ} (ha : 0 < a) :
    ∃ Q : ℝ → Ω → ℂ,
      Measurable (fun p : ℝ × Ω => Q p.1 p.2) ∧
      (∀ ω, Q 0 ω = w ω) ∧
      (∀ ω t, 0 ≤ t → HasDerivWithinAt (fun s => Q s ω)
        (reverseField a (U t ω) (Q t ω)) (Ici 0) t) := by
  have hm : Measurable (fun p : (ℝ × Ω) × ℂ => reverseField a (U p.1.1 p.1.2) p.2) := by
    have hj : Measurable (fun p : (ℝ × Ω) × ℂ => (U p.1.1 p.1.2, p.2)) :=
      (hUm.comp measurable_fst).prodMk measurable_snd
    have hf : Measurable (fun q : ℝ × ℂ => reverseField a q.1 q.2) :=
      (continuous_reverseField ha).measurable
    exact Measurable.comp (g := fun q : ℝ × ℂ => reverseField a q.1 q.2)
      (f := fun p : (ℝ × Ω) × ℂ => (U p.1.1 p.1.2, p.2)) hf hj
  have hc (ω : Ω) (z : ℂ) : Continuous (fun t : ℝ => reverseField a (U t ω) z) :=
    Continuous.comp (g := fun q : ℝ × ℂ => reverseField a q.1 q.2)
      (f := fun t : ℝ => (U t ω, z)) (continuous_reverseField ha)
      ((hUc ω).prodMk continuous_const)
  exact exists_random_initial_bounded_flow (fun t ω z => reverseField a (U t ω) z)
    w hwm ⟨2 * a⁻¹, by positivity⟩ ⟨4 * a⁻¹ ^ 2, by positivity⟩ hm hc
      (fun ω t => reverseField_lipschitz ha _) (fun ω t z => reverseField_bound ha _ _)

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.reverse_path_derivative
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (w : ℂ) {a : ℝ}
    (ha : 0 < a) (haw : a ≤ w.im) (s : ℝ) (hs : s ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (fun t : ℝ => G ((T : ℝ) - t).toNNReal (F T w))
      (reverseField a (U ((T : ℝ) - s).toNNReal) (G ((T : ℝ) - s).toNNReal (F T w)))
      (Icc 0 (T : ℝ)) s := by
  have hw : w ∈ upperHalfPlane := ha.trans_le haw
  have hz : F T w ∈ survivingDomain γ T := h.2.2.2.2.2.2.1 T hw
  have hi : G T (F T w) = w := h.2.2.2.2.2.2.2.2.1 T w hw
  have hmaps : MapsTo (fun t : ℝ => (T : ℝ) - t) (Icc 0 (T : ℝ)) (Icc 0 (T : ℝ)) := by
    intro t ht; constructor <;> linarith [ht.1, ht.2]
  have hd := (h.time_derivative T (F T w) hz ((T : ℝ) - s) (hmaps hs)).scomp s
    ((hasDerivAt_id s).const_sub (T : ℝ)).hasDerivWithinAt hmaps
  have hh : a ≤ (G ((T : ℝ) - s).toNNReal (F T w)).im := by
    have hh := h.imag_antitoneOn T (F T w) hz (hmaps hs) ⟨T.coe_nonneg, le_rfl⟩ (hmaps hs).2
    simp only [Real.toNNReal_coe, hi] at hh
    exact haw.trans hh
  simp only [Function.comp_def, neg_smul, one_smul] at hd
  simpa only [reverseField, reverseCenter_eq hh, div_eq_mul_inv, neg_mul] using hd

 

theorem IsCapacityTwoWitness.reverse_flow_identifies
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (w : ℂ) {a : ℝ}
    (ha : 0 < a) (haw : a ≤ w.im) (Q : ℝ → ℂ) (hQ0 : Q 0 = w)
    (hQd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt Q
      (reverseField a (U ((T : ℝ) - t).toNNReal) (Q t)) (Icc 0 (T : ℝ)) t) :
    Q T = F T w := by
  have hw : w ∈ upperHalfPlane := ha.trans_le haw
  have hp := h.reverse_path_derivative T w ha haw
  have he : EqOn Q (fun t : ℝ => G ((T : ℝ) - t).toNNReal (F T w)) (Icc 0 (T : ℝ)) := by
    apply ODE_solution_unique (fun t => reverseField_lipschitz ha (U ((T : ℝ) - t).toNNReal))
      (fun t ht => (hQd t ht).continuousWithinAt)
      (fun t ht => hasDerivWithinAt_Ici_of_Icc ht (hQd t ⟨ht.1, ht.2.le⟩))
      (fun t ht => (hp t ht).continuousWithinAt)
      (fun t ht => hasDerivWithinAt_Ici_of_Icc ht (hp t ⟨ht.1, ht.2.le⟩))
    simpa only [sub_zero, Real.toNNReal_coe, h.2.2.2.2.2.2.2.2.1 T w hw] using hQ0
  have hh := he ⟨T.coe_nonneg, le_rfl⟩
  simpa only [sub_self, Real.toNNReal_zero, h.initial_value (F T w)
    (h.2.2.2.2.2.2.1 T hw).1.1] using hh

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma exists_measurable_right_flow
    {Ω : Type*} [MeasurableSpace Ω]
    (U : ℝ → Ω → ℝ) (hUm : Measurable (fun p : ℝ × Ω => U p.1 p.2))
    (hUc : ∀ ω, Continuous (fun t => U t ω))
    (w : Ω → ℂ) (hwm : Measurable w) {a : ℝ} (ha : 0 < a) :
    ∃ Q : ℝ → Ω → ℂ,
      Measurable (fun p : ℝ × Ω => Q p.1 p.2) ∧
      (∀ ω, Q 0 ω = w ω) ∧
      (∀ ω t, 0 ≤ t → HasDerivWithinAt (fun s => Q s ω)
        (rightField a (U t ω) (Q t ω)) (Ici 0) t) := by
  have hm : Measurable (fun p : (ℝ × Ω) × ℂ => rightField a (U p.1.1 p.1.2) p.2) := by
    have hj : Measurable (fun p : (ℝ × Ω) × ℂ => (U p.1.1 p.1.2, p.2)) :=
      (hUm.comp measurable_fst).prodMk measurable_snd
    have hf : Measurable (fun q : ℝ × ℂ => rightField a q.1 q.2) :=
      (continuous_rightField ha).measurable
    exact Measurable.comp (g := fun q : ℝ × ℂ => rightField a q.1 q.2)
      (f := fun p : (ℝ × Ω) × ℂ => (U p.1.1 p.1.2, p.2)) hf hj
  have hc (ω : Ω) (z : ℂ) : Continuous (fun t : ℝ => rightField a (U t ω) z) :=
    Continuous.comp (g := fun q : ℝ × ℂ => rightField a q.1 q.2)
      (f := fun t : ℝ => (U t ω, z)) (continuous_rightField ha)
      ((hUc ω).prodMk continuous_const)
  exact exists_random_initial_bounded_flow (fun t ω z => rightField a (U t ω) z)
    w hwm ⟨2 * a⁻¹, by positivity⟩ ⟨4 * a⁻¹ ^ 2, by positivity⟩ hm hc
      (fun ω t => rightField_lipschitz ha _) (fun ω t z => rightField_bound ha _ _)

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SLEExactGauge

 

noncomputable def positiveBoundaryField (a u x : ℝ) : ℝ :=
  2 * (max a (x-u))⁻¹

lemma positiveBoundaryField_eq {a u x : ℝ} (h : a ≤ x-u) :
    positiveBoundaryField a u x = 2/(x-u) := by
  simp only [positiveBoundaryField,max_eq_right h,div_eq_mul_inv]

lemma positiveBoundaryField_bound {a : ℝ} (ha : 0 < a) (u x : ℝ) :
    ‖positiveBoundaryField a u x‖ ≤ 2*a⁻¹ := by
  have hp : 0 < max a (x-u) := ha.trans_le (le_max_left _ _)
  simp only [positiveBoundaryField,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2),abs_inv,
    abs_of_pos hp]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ ha (le_max_left _ _)) (by norm_num)

lemma positiveBoundaryField_lipschitz {a : ℝ} (ha : 0 < a) (u : ℝ) :
    LipschitzWith ⟨2*a⁻¹^2,by positivity⟩ (positiveBoundaryField a u) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : 0 < max a (x-u) := ha.trans_le (le_max_left _ _)
  have hy : 0 < max a (y-u) := ha.trans_le (le_max_left _ _)
  have hi (z : ℝ) : ‖(max a (z-u))⁻¹‖ ≤ a⁻¹ := by
    rw [Real.norm_eq_abs,abs_inv,abs_of_pos (ha.trans_le (le_max_left _ _))]
    exact inv_anti₀ ha (le_max_left _ _)
  have hm : ‖max a (y-u)-max a (x-u)‖ ≤ dist x y := by
    have hh := ((LipschitzWith.id : LipschitzWith 1 (fun z : ℝ => z)).const_max a).dist_le_mul
      (y-u) (x-u)
    simpa only [NNReal.coe_one,one_mul,id_eq,dist_sub_right,dist_eq_norm,norm_sub_rev,sub_sub_sub_cancel_right] using hh
  rw [dist_eq_norm,positiveBoundaryField,positiveBoundaryField,← mul_sub,norm_mul,
    Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
    inv_sub_inv' hx.ne' hy.ne',norm_mul,norm_mul]
  calc
    _ ≤ 2*(a⁻¹ * dist x y * a⁻¹) := by gcongr <;> exact hi _
    _ = _ := by change 2*(a⁻¹*dist x y*a⁻¹)=(2*a⁻¹^2)*dist x y; ring

lemma continuous_positiveBoundaryField {a : ℝ} (ha : 0 < a) :
    Continuous (fun p : ℝ × ℝ => positiveBoundaryField a p.1 p.2) := by
  apply continuous_const.mul
  apply Continuous.inv₀
  · exact continuous_const.max (continuous_snd.sub continuous_fst)
  · intro p; exact (ha.trans_le (le_max_left a (p.2-p.1))).ne'

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace SLEExactGauge

 

theorem positive_boundary_global_adapted_solution
    {Ω : Type*} [MeasurableSpace Ω] (U : ℝ≥0 → Ω → ℝ)
    (hU : Measurable (fun q : ℝ≥0 × Ω => U q.1 q.2))
    (hc : ∀ ω, Continuous (fun t : ℝ≥0 => U t ω))
    (a : ℝ) (ha : 0 < a) (q₀ : ℝ) :
    ∃ (L : ℝ≥0) (Q : ℝ → Ω → ℝ),
      Measurable (fun q : ℝ × Ω => Q q.1 q.2) ∧
      (∀ ω, LipschitzWith L (fun t => Q t ω)) ∧
      (∀ ω, Q 0 ω = q₀) ∧
      (∀ ω t, 0 ≤ t →
        HasDerivWithinAt (fun s => Q s ω)
          (positiveBoundaryField a (U t.toNNReal ω) (Q t ω))
          (Ici 0) t) ∧
      Adapted (Filtration.natural U (fun t => (hU.comp (measurable_prodMk_left (x := t))).stronglyMeasurable))
        (fun t : ℝ≥0 => Q t) := by
  let L : ℝ≥0 := ⟨2*a⁻¹,by positivity⟩
  let K : ℝ≥0 := ⟨2*a⁻¹^2,by positivity⟩
  have hbound := positiveBoundaryField_bound ha
  have hlip := positiveBoundaryField_lipschitz ha
  let V (t : ℝ) (ω : Ω) (q : ℝ) := positiveBoundaryField a (U t.toNNReal ω) q
  have hF := continuous_positiveBoundaryField ha
  have hUr : Measurable (fun q : ℝ × Ω => U q.1.toNNReal q.2) :=
    hU.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun q : (ℝ × Ω) × (ℝ) => V q.1.1 q.1.2 q.2) := by
    change Measurable ((fun p : ℝ × (ℝ) => positiveBoundaryField a p.1 p.2) ∘
      (fun q : (ℝ × Ω) × (ℝ) => (U q.1.1.toNNReal q.1.2, q.2)))
    exact hF.measurable.comp ((hUr.comp measurable_fst).prodMk measurable_snd)
  have hcont (ω : Ω) (q : ℝ) : Continuous (fun t : ℝ => V t ω q) := by
    change Continuous ((fun p : ℝ × (ℝ) => positiveBoundaryField a p.1 p.2) ∘
      (fun t : ℝ => (U t.toNNReal ω, q)))
    exact hF.comp (((hc ω).comp continuous_real_toNNReal).prodMk continuous_const)
  obtain ⟨Q, hQm, hQl, hQ0, hQd, hQconv⟩ :=
    exists_measurable_global_bounded_ode_picard V q₀ L K hm hcont
      (fun ω t => hlip (U t.toNNReal ω)) (fun ω t q => hbound (U t.toNNReal ω) q)
  refine ⟨L, Q, hQm, hQl, hQ0, hQd, ?_⟩
  intro t
  have hUfrozen := measurable_driver_frozen U hU hc t
  let m := Filtration.natural U (fun t => (hU.comp measurable_prodMk_left).stronglyMeasurable) t
  let : MeasurableSpace Ω := m
  let W (s : ℝ) (ω : Ω) (q : ℝ) :=
    positiveBoundaryField a (U (min s.toNNReal t) ω) q
  have hW : Measurable (fun q : (ℝ × Ω) × (ℝ) => W q.1.1 q.1.2 q.2) := by
    change Measurable ((fun p : ℝ × (ℝ) => positiveBoundaryField a p.1 p.2) ∘
      (fun q : (ℝ × Ω) × (ℝ) => (U (min q.1.1.toNNReal t) q.1.2, q.2)))
    exact hF.measurable.comp ((hUfrozen.comp measurable_fst).prodMk measurable_snd)
  have heq (n : ℕ) (ω : Ω) : picardApprox W q₀ n (t : ℝ) ω = picardApprox V q₀ n (t : ℝ) ω := by
    apply picardApprox_congr_on q₀ (t : ℝ) _ n (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩ ω
    intro s hs ω q
    have hh : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
    simp only [W, V, min_eq_left hh]
  apply measurable_of_tendsto_metrizable (f := fun n ω => picardApprox W q₀ n (t : ℝ) ω)
  · intro n
    exact (picardApprox_measurable W q₀ hW n).comp measurable_prodMk_left
  · apply tendsto_pi_nhds.mpr
    intro ω
    simpa only [heq, max_eq_right t.coe_nonneg] using hQconv t ω

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

noncomputable def boundaryClockField (a u : ℝ) (q : ℂ) : ℂ :=
  (positiveBoundaryField a u q.re : ℂ) + ((max a (q.re-u))⁻¹^2 : ℝ) * I

lemma clipped_real_inv_bound {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ‖(max a x)⁻¹‖ ≤ a⁻¹ := by
  rw [Real.norm_eq_abs,abs_inv,abs_of_pos (ha.trans_le (le_max_left _ _))]
  exact inv_anti₀ ha (le_max_left _ _)

lemma clipped_real_inv_lipschitz {a : ℝ} (ha : 0 < a) :
    LipschitzWith ⟨a⁻¹^2,by positivity⟩ (fun x : ℝ => (max a x)⁻¹) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : max a x ≠ 0 := (ha.trans_le (le_max_left _ _)).ne'
  have hy : max a y ≠ 0 := (ha.trans_le (le_max_left _ _)).ne'
  have hmax : ‖max a y-max a x‖ ≤ dist x y := by
    have hh := ((LipschitzWith.id : LipschitzWith 1 (fun x : ℝ => x)).const_max a).dist_le_mul y x
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul,id_eq,Real.norm_eq_abs,abs_sub_comm] using hh
  rw [dist_eq_norm,inv_sub_inv' hx hy,norm_mul,norm_mul]
  calc
    _ ≤ a⁻¹*dist x y*a⁻¹ := by gcongr <;> exact clipped_real_inv_bound ha _
    _ = _ := by change a⁻¹*dist x y*a⁻¹ = a⁻¹^2*dist x y; ring

lemma boundaryClockField_bound {a : ℝ} (ha : 0 < a) (u : ℝ) (q : ℂ) :
    ‖boundaryClockField a u q‖ ≤ 2*a⁻¹+a⁻¹^2 := by
  have h0 := positiveBoundaryField_bound ha u q.re
  have h1 := clipped_real_inv_bound ha (q.re-u)
  have h2 : ‖(max a (q.re-u))⁻¹^2‖ ≤ a⁻¹^2 := by
    rw [norm_pow]
    gcongr
  have hh := norm_add_le (positiveBoundaryField a u q.re : ℂ) (((max a (q.re-u))⁻¹^2 : ℝ)*I)
  simp only [norm_mul,Complex.norm_real,Complex.norm_I,mul_one] at hh
  exact hh.trans (add_le_add h0 h2)

lemma boundaryClockField_lipschitz {a : ℝ} (ha : 0 < a) (u : ℝ) :
    LipschitzWith ⟨2*a⁻¹^2+2*a⁻¹^3,by positivity⟩ (boundaryClockField a u) := by
  apply LipschitzWith.of_dist_le_mul
  intro q w
  have hd : dist (q.re-u) (w.re-u) ≤ dist q w := by
    simpa only [dist_sub_right,dist_eq_norm,Complex.sub_re,Real.norm_eq_abs,sub_sub_sub_cancel_right] using Complex.abs_re_le_norm (q-w)
  have hi : ‖(max a (q.re-u))⁻¹-(max a (w.re-u))⁻¹‖ ≤ a⁻¹^2*dist q w := by
    exact ((clipped_real_inv_lipschitz ha).dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hd (sq_nonneg _))
  have hsum : ‖(max a (q.re-u))⁻¹+(max a (w.re-u))⁻¹‖ ≤ 2*a⁻¹ := by
    exact (norm_add_le _ _).trans (by linarith [clipped_real_inv_bound ha (q.re-u),clipped_real_inv_bound ha (w.re-u)])
  have hsq : ‖(max a (q.re-u))⁻¹^2-(max a (w.re-u))⁻¹^2‖ ≤ 2*a⁻¹^3*dist q w := by
    rw [sq_sub_sq,norm_mul,mul_comm]
    calc
      _ ≤ (a⁻¹^2*dist q w)*(2*a⁻¹) := mul_le_mul hi hsum (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hr := (positiveBoundaryField_lipschitz ha u).dist_le_mul q.re w.re
  have hr' : ‖positiveBoundaryField a u q.re-positiveBoundaryField a u w.re‖ ≤ 2*a⁻¹^2*dist q w := by
    rw [← dist_eq_norm]
    apply hr.trans
    change (2*a⁻¹^2)*dist q.re w.re ≤ (2*a⁻¹^2)*dist q w
    exact mul_le_mul_of_nonneg_left (by simpa only [dist_sub_right] using hd) (by positivity)
  rw [dist_eq_norm]
  have he : boundaryClockField a u q-boundaryClockField a u w =
    ((positiveBoundaryField a u q.re-positiveBoundaryField a u w.re:ℝ):ℂ)+
    (((max a (q.re-u))⁻¹^2-(max a (w.re-u))⁻¹^2:ℝ):ℂ)*I := by
    simp only [boundaryClockField,Complex.ofReal_sub]; ring
  rw [he]
  have hn := norm_add_le ((positiveBoundaryField a u q.re-positiveBoundaryField a u w.re:ℝ):ℂ)
    ((((max a (q.re-u))⁻¹^2-(max a (w.re-u))⁻¹^2:ℝ):ℂ)*I)
  simp only [norm_mul,Complex.norm_real,Complex.norm_I,mul_one] at hn
  calc
    _ ≤ 2*a⁻¹^2*dist q w+2*a⁻¹^3*dist q w := hn.trans (add_le_add hr' hsq)
    _ = _ := by change _ = (2*a⁻¹^2+2*a⁻¹^3)*dist q w; ring

lemma continuous_boundaryClockField {a : ℝ} (ha : 0 < a) :
    Continuous (fun p : ℝ × ℂ => boundaryClockField a p.1 p.2) := by
  apply Continuous.add
  · exact Complex.continuous_ofReal.comp ((continuous_positiveBoundaryField ha).comp
      (continuous_fst.prodMk (Complex.continuous_re.comp continuous_snd)))
  · apply Continuous.mul _ continuous_const
    apply Complex.continuous_ofReal.comp
    apply Continuous.pow
    apply Continuous.inv₀
    · exact continuous_const.max ((Complex.continuous_re.comp continuous_snd).sub continuous_fst)
    · intro p; exact (ha.trans_le (le_max_left _ _)).ne'

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace SLEExactGauge

 

theorem boundary_clock_global_adapted_solution
    {Ω : Type*} [MeasurableSpace Ω] (U : ℝ≥0 → Ω → ℝ)
    (hU : Measurable (fun q : ℝ≥0 × Ω => U q.1 q.2))
    (hc : ∀ ω, Continuous (fun t : ℝ≥0 => U t ω))
    (κ a : ℝ) (ha : 0 < a) (q₀ : ℂ) :
    ∃ (L : ℝ≥0) (Q : ℝ → Ω → ℂ),
      Measurable (fun q : ℝ × Ω => Q q.1 q.2) ∧
      (∀ ω, LipschitzWith L (fun t => Q t ω)) ∧
      (∀ ω, Q 0 ω = q₀) ∧
      (∀ ω t, 0 ≤ t →
        HasDerivWithinAt (fun s => Q s ω)
          (boundaryClockField a (Real.sqrt κ*U t.toNNReal ω) (Q t ω))
          (Ici 0) t) ∧
      Adapted (Filtration.natural U (fun t => (hU.comp (measurable_prodMk_left (x := t))).stronglyMeasurable))
        (fun t : ℝ≥0 => Q t) := by
  let L : ℝ≥0 := ⟨2*a⁻¹+a⁻¹^2,by positivity⟩
  let K : ℝ≥0 := ⟨2*a⁻¹^2+2*a⁻¹^3,by positivity⟩
  have hbound := boundaryClockField_bound ha
  have hlip := boundaryClockField_lipschitz ha
  let V (t : ℝ) (ω : Ω) (q : ℂ) := boundaryClockField a (Real.sqrt κ*U t.toNNReal ω) q
  have hF : Continuous (fun p : ℝ × ℂ => boundaryClockField a (Real.sqrt κ*p.1) p.2) :=
    (continuous_boundaryClockField ha).comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have hUr : Measurable (fun q : ℝ × Ω => U q.1.toNNReal q.2) :=
    hU.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun q : (ℝ × Ω) × (ℂ) => V q.1.1 q.1.2 q.2) := by
    change Measurable ((fun p : ℝ × (ℂ) => boundaryClockField a (Real.sqrt κ*p.1) p.2) ∘
      (fun q : (ℝ × Ω) × (ℂ) => (U q.1.1.toNNReal q.1.2, q.2)))
    exact hF.measurable.comp ((hUr.comp measurable_fst).prodMk measurable_snd)
  have hcont (ω : Ω) (q : ℂ) : Continuous (fun t : ℝ => V t ω q) := by
    change Continuous ((fun p : ℝ × (ℂ) => boundaryClockField a (Real.sqrt κ*p.1) p.2) ∘
      (fun t : ℝ => (U t.toNNReal ω, q)))
    exact hF.comp (((hc ω).comp continuous_real_toNNReal).prodMk continuous_const)
  obtain ⟨Q, hQm, hQl, hQ0, hQd, hQconv⟩ :=
    exists_measurable_global_bounded_ode_picard V q₀ L K hm hcont
      (fun ω t => hlip (Real.sqrt κ*U t.toNNReal ω)) (fun ω t q => hbound (Real.sqrt κ*U t.toNNReal ω) q)
  refine ⟨L, Q, hQm, hQl, hQ0, hQd, ?_⟩
  intro t
  have hUfrozen := measurable_driver_frozen U hU hc t
  let m := Filtration.natural U (fun t => (hU.comp measurable_prodMk_left).stronglyMeasurable) t
  let : MeasurableSpace Ω := m
  let W (s : ℝ) (ω : Ω) (q : ℂ) :=
    boundaryClockField a (Real.sqrt κ*U (min s.toNNReal t) ω) q
  have hW : Measurable (fun q : (ℝ × Ω) × (ℂ) => W q.1.1 q.1.2 q.2) := by
    change Measurable ((fun p : ℝ × (ℂ) => boundaryClockField a (Real.sqrt κ*p.1) p.2) ∘
      (fun q : (ℝ × Ω) × (ℂ) => (U (min q.1.1.toNNReal t) q.1.2, q.2)))
    exact hF.measurable.comp ((hUfrozen.comp measurable_fst).prodMk measurable_snd)
  have heq (n : ℕ) (ω : Ω) : picardApprox W q₀ n (t : ℝ) ω = picardApprox V q₀ n (t : ℝ) ω := by
    apply picardApprox_congr_on q₀ (t : ℝ) _ n (t : ℝ) ⟨t.coe_nonneg, le_rfl⟩ ω
    intro s hs ω q
    have hh : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
    simp only [W, V, min_eq_left hh]
  apply measurable_of_tendsto_metrizable (f := fun n ω => picardApprox W q₀ n (t : ℝ) ω)
  · intro n
    exact (picardApprox_measurable W q₀ hW n).comp measurable_prodMk_left
  · apply tendsto_pi_nhds.mpr
    intro ω
    simpa only [heq, max_eq_right t.coe_nonneg] using hQconv t ω

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

structure BoundaryClockSolution {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (κ a : ℝ) (q₀ : ℂ) where
  L : ℝ≥0
  Q : ℝ → Ω → ℂ
  measurable : Measurable (fun p : ℝ × Ω => Q p.1 p.2)
  lipschitz : ∀ ω, LipschitzWith L (fun t => Q t ω)
  initial : ∀ ω, Q 0 ω = q₀
  derivative : ∀ ω t, 0 ≤ t → HasDerivWithinAt (fun s => Q s ω)
    (boundaryClockField a (Real.sqrt κ * B t.toNNReal ω) (Q t ω)) (Ici 0) t
  adapted : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun t : ℝ≥0 => Q t)

lemma exists_boundaryClockSolution
    {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (κ a : ℝ) (ha : 0 < a) (q₀ : ℂ) :
    Nonempty (BoundaryClockSolution B hm κ a q₀) := by
  obtain ⟨L,Q,hQm,hQl,hQ0,hQd,hQa⟩ := boundary_clock_global_adapted_solution B hBm hBc κ a ha q₀
  exact ⟨⟨L,Q,hQm,hQl,hQ0,hQd,hQa⟩⟩

end SLEExactGauge
end

 
end

end OAI
