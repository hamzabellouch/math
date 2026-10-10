import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ProbabilityBadJet
import OAI.Geometry.SmoothYau.SphereMetric.BoundedThreePolynomialNet

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

lemma complex_gaussian_norm_tail :
    ∃ M > 0, ∀ n : ℝ, 0 < n →
      stdGaussian ℂ {z | n < ‖z‖} ≤ ENNReal.ofReal (M/n^8) := by
  have hi : Integrable (fun z : ℂ => ‖z‖^8) (stdGaussian ℂ) := by
    simpa only [id_eq] using (IsGaussian.memLp_id (stdGaussian ℂ) 8 (by norm_num)).integrable_norm_pow'
  let M₀ := ∫ z : ℂ, ‖z‖^8 ∂stdGaussian ℂ
  have hM₀ : 0 ≤ M₀ := integral_nonneg (fun z => pow_nonneg (norm_nonneg z) _)
  refine ⟨1+M₀,by linarith,?_⟩
  intro n hn
  have hMark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (stdGaussian ℂ) (fun z => pow_nonneg (norm_nonneg z) 8)) hi (n^8)
  have hs : {z : ℂ | n < ‖z‖} ⊆ {z : ℂ | n^8 ≤ ‖z‖^8} :=
    fun z hz => pow_le_pow_left₀ hn.le hz.le 8
  rw [←ENNReal.ofReal_toReal (measure_ne_top (stdGaussian ℂ) _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (stdGaussian ℂ {z | n < ‖z‖}).toReal ≤
        (stdGaussian ℂ {z | n^8 ≤ ‖z‖^8}).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hs)
    _ ≤ M₀/n^8 := by
      apply (le_div_iff₀ (pow_pos hn _)).mpr
      simpa only [Measure.real,mul_comm] using hMark
    _ ≤ (1+M₀)/n^8 := div_le_div_of_nonneg_right (by linarith) (pow_nonneg hn.le _)

theorem finite_gaussian_coefficient_tail :
    ∃ M > 0, ∀ (I : Type) [Fintype I] (n : ℝ), 0 < n →
      (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {γ | ∃ i ℓ, n < ‖γ i ℓ‖} ≤
      (Fintype.card I : ℝ≥0∞)*3*ENNReal.ofReal (M/n^8) := by
  obtain ⟨M,hM,hTail⟩ := complex_gaussian_norm_tail
  refine ⟨M,hM,?_⟩
  intro I _ n hn
  let μ := Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ))
  have hm (i : I) (ℓ : Fin 3) :
      μ {γ | n < ‖γ i ℓ‖} ≤ ENNReal.ofReal (M/n^8) := by
    have hf : MeasurePreserving (fun γ : I → Fin 3 → ℂ => γ i ℓ) μ (stdGaussian ℂ) :=
      (measurePreserving_eval (fun _ : Fin 3 => stdGaussian ℂ) ℓ).comp
        (measurePreserving_eval (fun _ : I => Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)) i)
    have he : {γ : I → Fin 3 → ℂ | n < ‖γ i ℓ‖} =
        (fun γ => γ i ℓ) ⁻¹' {z : ℂ | n < ‖z‖} := rfl
    rw [he,hf.measure_preimage (measurableSet_lt measurable_const measurable_norm).nullMeasurableSet]
    exact hTail n hn
  have hset : {γ : I → Fin 3 → ℂ | ∃ i ℓ, n < ‖γ i ℓ‖} =
      ⋃ i, ⋃ ℓ, {γ | n < ‖γ i ℓ‖} := by ext γ; simp
  rw [hset]
  calc
    μ (⋃ i, ⋃ ℓ, {γ | n < ‖γ i ℓ‖}) ≤
        ∑ i, μ (⋃ ℓ, {γ | n < ‖γ i ℓ‖}) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ∑ ℓ, μ {γ | n < ‖γ i ℓ‖} :=
      Finset.sum_le_sum (fun i _ => measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _i : I, ∑ _ℓ : Fin 3, ENNReal.ofReal (M/n^8) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun ℓ _ => hm i ℓ))
    _ = _ := by simp [mul_assoc]
end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set MeasureTheory
open scoped ENNReal
open Set MeasureTheory
open scoped ENNReal

theorem uniform_polynomial_smallBall (B C : ℝ) (hB : 0 < B) (hC : 0 < C) :
    ∃ A > 0, ∀ (Ω : Type) [MeasurableSpace Ω]
      (μ : Measure Ω) (F : Ω → (Fin 3 → ℝ) → ((Fin 1 ⊕ Fin 3) → ℝ))
      (G : Set Ω) (K : Set (Fin 3 → ℝ)) (n L : ℝ),
      1 ≤ n → 0 ≤ L → L ≤ n^4 →
      (∀ x ∈ K, ‖x‖ ≤ B) →
      (∀ outcome ∈ G, ∀ x ∈ K, ∀ y ∈ K, ‖F outcome x-F outcome y‖ ≤ (L*n^6)*dist x y) →
      (∀ x ∈ K, ∀ r : ℝ, 0 ≤ r →
        μ {outcome | ‖F outcome x‖ ≤ r} ≤ ENNReal.ofReal (C*n^28*r^4)) →
      μ {outcome | ∃ x ∈ K, ‖F outcome x‖ < 1/n^110} ≤
        μ Gᶜ+ENNReal.ofReal (A/n^52) := by
  classical
  obtain ⟨Q,hQ,hnet⟩ := bounded_three_polynomial_net B hB 1 (by norm_num)
  refine ⟨16*Q*C,by positivity,?_⟩
  intro Ω _ μ F G K n L hn hL hLn hK hLip hsmall
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hn120 : 1 ≤ n^120 := one_le_pow₀ hn
  obtain ⟨t,htK,htcard,htcover⟩ := hnet K hK (n^120) hn120
  have hδ : (L*n^6)*(1/n^120) ≤ 1/n^110 := by
    calc
      _ ≤ (n^4*n^6)*(1/n^120) := by gcongr
      _ = _ := by field_simp
  have hr : 0 ≤ 2/n^110 := by positivity
  have hnetSmall (i : t) : μ {outcome | ‖F outcome i.1‖ < 1/n^110+(L*n^6)*(1/n^120)} ≤
      ENNReal.ofReal (C*n^28*(2/n^110)^4) := by
    apply (measure_mono (show {outcome | ‖F outcome i.1‖ < 1/n^110+(L*n^6)*(1/n^120)} ⊆
        {outcome | ‖F outcome i.1‖ ≤ 2/n^110} from fun outcome hω => by
          change ‖F outcome i.1‖ < _ at hω
          change ‖F outcome i.1‖ ≤ _
          apply hω.le.trans
          calc
            _ ≤ 1/n^110+1/n^110 := add_le_add le_rfl hδ
            _ = _ := by ring)).trans
    exact hsmall i.1 (htK i.2) _ hr
  have h := probability_bad_jet_le μ F G K (fun i : t => i.1)
    (1/n^120) (1/n^110) (L*n^6) (by positivity)
    (fun x hx => by obtain ⟨y,hy,hd⟩ := htcover x hx; exact ⟨⟨y,hy⟩,hd⟩)
    (fun outcome hω x hx i => hLip outcome hω x hx i (htK i.2)) _ hnetSmall
  apply h.trans (add_le_add le_rfl ?_)
  have hcard : (Fintype.card t : ℝ) ≤ Q*n^360 := by
    simpa only [Fintype.card_coe,←pow_mul] using htcard
  rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (by positivity : 0 ≤ (Fintype.card t : ℝ))]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (Q*n^360)*(C*n^28*(2/n^110)^4) := by gcongr
    _ = _ := by field_simp; ring

theorem gaussian_uniform_polynomial_smallBall (B C Q : ℝ)
    (hB : 0 < B) (hC : 0 < C) (hQ : 0 < Q) :
    ∃ A > 0, ∀ (I : Type) [Fintype I]
      (F : (I → Fin 3 → ℂ) → (Fin 3 → ℝ) → ((Fin 1 ⊕ Fin 3) → ℝ))
      (K : Set (Fin 3 → ℝ)) (n L : ℝ),
      1 ≤ n → 0 ≤ L → L ≤ n^4 →
      (Fintype.card I : ℝ) ≤ Q*n^3 → (∀ x ∈ K, ‖x‖ ≤ B) →
      (∀ γ, (∀ i ℓ, ‖γ i ℓ‖ ≤ n) → ∀ x ∈ K, ∀ y ∈ K,
        ‖F γ x-F γ y‖ ≤ (L*n^6)*dist x y) →
      (∀ x ∈ K, ∀ r : ℝ, 0 ≤ r →
        (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => ProbabilityTheory.stdGaussian ℂ)))
          {γ | ‖F γ x‖ ≤ r} ≤ ENNReal.ofReal (C*n^28*r^4)) →
      (Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => ProbabilityTheory.stdGaussian ℂ)))
        {γ | (∃ i ℓ, n < ‖γ i ℓ‖) ∨ ∃ x ∈ K, ‖F γ x‖ < 1/n^110} ≤
        ENNReal.ofReal (A/n^5) := by
  classical
  obtain ⟨M,hM,hTail⟩ := finite_gaussian_coefficient_tail
  obtain ⟨A,hA,hNet⟩ := uniform_polynomial_smallBall B C hB hC
  refine ⟨6*Q*M+A,by positivity,?_⟩
  intro I _ F K n L hn hL hLn hcard hK hLip hsmall
  let μ := Measure.pi (fun _ : I => Measure.pi (fun _ : Fin 3 => ProbabilityTheory.stdGaussian ℂ))
  let G : Set (I → Fin 3 → ℂ) := {γ | ∀ i ℓ, ‖γ i ℓ‖ ≤ n}
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hG : Gᶜ = {γ | ∃ i ℓ, n < ‖γ i ℓ‖} := by ext γ; simp [G]
  have ht : μ Gᶜ ≤ ENNReal.ofReal (3*Q*M/n^5) := by
    rw [hG]
    apply (hTail I n hn0).trans
    rw [←ENNReal.ofReal_natCast,show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
      ←ENNReal.ofReal_mul (by positivity : 0 ≤ (Fintype.card I : ℝ)),
      ←ENNReal.ofReal_mul (by positivity : 0 ≤ (Fintype.card I : ℝ)*3)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (Q*n^3)*3*(M/n^8) := by gcongr
      _ = _ := by field_simp
  have hj := hNet _ μ F G K n L hn hL hLn hK (fun γ hγ => hLip γ hγ) hsmall
  have hset : {γ | (∃ i ℓ, n < ‖γ i ℓ‖) ∨ ∃ x ∈ K, ‖F γ x‖ < 1/n^110} =
      Gᶜ ∪ {γ | ∃ x ∈ K, ‖F γ x‖ < 1/n^110} := by rw [hG]; rfl
  rw [hset]
  apply (measure_union_le _ _).trans
  apply (add_le_add ht (hj.trans (add_le_add ht le_rfl))).trans
  rw [←ENNReal.ofReal_add (by positivity : 0 ≤ 3*Q*M/n^5) (by positivity : 0 ≤ A/n^52),
    ←ENNReal.ofReal_add (by positivity : 0 ≤ 3*Q*M/n^5) (by positivity : 0 ≤ 3*Q*M/n^5+A/n^52)]
  apply ENNReal.ofReal_le_ofReal
  have hp : n^5 ≤ n^52 := pow_le_pow_right₀ hn (by omega)
  have hd : A/n^52 ≤ A/n^5 := div_le_div_of_nonneg_left hA.le (pow_pos hn0 _) hp
  calc
    _ ≤ 3*Q*M/n^5+(3*Q*M/n^5+A/n^5) := by linarith
    _ = _ := by ring

end YauCounterexamples
end

end OAI
