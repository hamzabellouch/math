import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SpherePlaneWave2

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
namespace CurrentFalconer
open MeasureTheory Set
open scoped ComplexConjugate
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma spherePlaneWaveND_sub (r : ℝ) (x y w : V) :
    spherePlaneWaveND r (x-y) w = spherePlaneWaveND r x w * conj (spherePlaneWaveND r y w) := by
  unfold spherePlaneWaveND
  rw [← Complex.exp_conj,← Complex.exp_add]
  congr 1
  simp only [inner_sub_right,Complex.ofReal_sub,map_mul,Complex.conj_I,Complex.conj_ofReal]
  ring

lemma angular_pair_joint_integrableND (σ ρ ν : Measure V)
    [IsFiniteMeasure σ] [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (r : ℝ) {ψ : V → ℂ} {b c : V → V → ℂ}
    (hψ : Measurable ψ) (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c)) {P B C : ℝ}
    (hP : ∀ w, ‖ψ w‖ ≤ P) (hB : ∀ x w, ‖b x w‖ ≤ B)
    (hC : ∀ y w, ‖c y w‖ ≤ C) :
    Integrable (fun z : V × (V × V) => ψ z.1 * spherePlaneWaveND r (z.2.1-z.2.2) z.1 *
      b z.2.1 z.1 * conj (c z.2.2 z.1)) (σ.prod (ρ.prod ν)) := by
  have hB₀ : 0 ≤ B := (norm_nonneg (b 0 0)).trans (hB 0 0)
  have hP₀ : 0 ≤ P := (norm_nonneg (ψ 0)).trans (hP 0)
  have hm : Measurable (fun z : V × (V × V) => ψ z.1 * spherePlaneWaveND r (z.2.1-z.2.2) z.1 *
      b z.2.1 z.1 * conj (c z.2.2 z.1)) := by
    exact (((hψ.comp measurable_fst).mul
      (by unfold spherePlaneWaveND; fun_prop)).mul
        (hb.comp (measurable_snd.fst.prodMk measurable_fst))).mul
          (Complex.continuous_conj.measurable.comp
            (hc.comp (measurable_snd.snd.prodMk measurable_fst)))
  apply Integrable.of_bound hm.aestronglyMeasurable (P*B*C)
  filter_upwards with z
  simp only [norm_mul,spherePlaneWaveND_norm,Complex.norm_conj,mul_one]
  exact mul_le_mul (mul_le_mul (hP z.1) (hB z.2.1 z.1) (norm_nonneg _) hP₀)
    (hC z.2.2 z.1) (norm_nonneg _) (mul_nonneg hP₀ hB₀)

theorem angular_pair_factorizationND (σ ρ ν : Measure V)
    [IsFiniteMeasure σ] [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set V) (M N r : ℝ) {ψ : V → ℂ} {b c : V → V → ℂ}
    (hψ : Measurable ψ) (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c)) {P B C : ℝ}
    (hP : ∀ w, ‖ψ w‖ ≤ P) (hB : ∀ x w, ‖b x w‖ ≤ B)
    (hC : ∀ y w, ‖c y w‖ ≤ C) :
    ((M*N)⁻¹:ℝ) •
      (∫ z : V × V, (∫ w, ψ w*spherePlaneWaveND r (z.1-z.2) w*
        b z.1 w*conj (c z.2 w) ∂σ) ∂(ρ.restrict X).prod (ν.restrict Y)) =
      ∫ w, ψ w*sourceAngularTransformND ρ X M b r w *
        conj (sourceAngularTransformND ν Y N c r w) ∂σ := by
  have hs := integral_integral_swap (f := fun w (z : V × V) =>
    ψ w*spherePlaneWaveND r (z.1-z.2) w*b z.1 w*conj (c z.2 w))
    (angular_pair_joint_integrableND σ (ρ.restrict X) (ν.restrict Y) r hψ hb hc hP hB hC)
  have hi (w : V) :
      (∫ z : V × V, ψ w*spherePlaneWaveND r (z.1-z.2) w*b z.1 w*conj (c z.2 w)
        ∂(ρ.restrict X).prod (ν.restrict Y)) =
      ψ w*(∫ x in X, spherePlaneWaveND r x w*b x w ∂ρ) *
        conj (∫ y in Y, spherePlaneWaveND r y w*c y w ∂ν) := by
    simp_rw [spherePlaneWaveND_sub]
    have he : (fun z : V × V => ψ w*(spherePlaneWaveND r z.1 w*conj (spherePlaneWaveND r z.2 w))*
        b z.1 w*conj (c z.2 w)) =
        fun z => ψ w*((spherePlaneWaveND r z.1 w*b z.1 w)*
          conj (spherePlaneWaveND r z.2 w*c z.2 w)) := by
      funext z
      simp only [map_mul]
      ring
    rw [he,integral_const_mul,
      integral_prod_mul (fun x => spherePlaneWaveND r x w*b x w)
        (fun y => conj (spherePlaneWaveND r y w*c y w)),integral_conj]
    ring
  rw [← hs]
  simp_rw [hi]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with w
  simp only [sourceAngularTransformND,Complex.real_smul,map_mul,Complex.conj_ofReal,
    mul_inv_rev,Complex.ofReal_mul]
  ring

end CurrentFalconer
end
end

section
section
namespace CurrentFalconer
open MeasureTheory Set
open scoped ComplexConjugate
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma sourceAngularTransformND_measurable (ρ : Measure V) [IsFiniteMeasure ρ]
    (X : Set V) (M : ℝ) {b : V → V → ℂ}
    (hb : Measurable (Function.uncurry b)) :
    Measurable (fun p : ℝ × V => sourceAngularTransformND ρ X M b p.1 p.2) := by
  unfold sourceAngularTransformND
  change Measurable ((M⁻¹) • (fun p : ℝ × V => ∫ x in X, spherePlaneWaveND p.1 x p.2*b x p.2 ∂ρ))
  apply Measurable.const_smul
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  have hm : Measurable (fun z : (ℝ × V) × V => b z.2 z.1.2) :=
    hb.comp (measurable_snd.prodMk measurable_fst.snd)
  exact (show Measurable (fun z : (ℝ × V) × V => spherePlaneWaveND z.1.1 z.2 z.1.2) by
    unfold spherePlaneWaveND; fun_prop).mul hm

omit [FiniteDimensional ℝ V] [BorelSpace V] in
lemma sourceAngularTransformND_norm_le (ρ : Measure V) [IsFiniteMeasure ρ]
    (X : Set V) (M : ℝ) (b : V → V → ℂ) (r : ℝ) (w : V) {B : ℝ}
    (hb : ∀ x, ‖b x w‖≤B) :
    ‖sourceAngularTransformND ρ X M b r w‖ ≤ |M⁻¹| * (ρ X).toReal*B := by
  unfold sourceAngularTransformND
  rw [norm_smul,Real.norm_eq_abs]
  have hh : ‖∫ x in X, spherePlaneWaveND r x w*b x w ∂ρ‖ ≤
      (ρ X).toReal*B := by
    have h : ∀ᵐ x ∂ρ.restrict X, ‖spherePlaneWaveND r x w*b x w‖≤B := by
      filter_upwards with x
      simpa only [norm_mul,spherePlaneWaveND_norm,one_mul] using hb x
    simpa only [Measure.real,Measure.restrict_apply_univ,mul_comm] using norm_integral_le_of_norm_le_const h
  exact (mul_le_mul_of_nonneg_left hh (abs_nonneg _)).trans_eq (by ring)

lemma angular_pair_joint_integrableND_ae (σ ρ ν : Measure V)
    [IsFiniteMeasure σ] [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (r : ℝ) {ψ : V → ℂ} {b c : V → V → ℂ}
    (hψ : Measurable ψ) (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c)) {P B C : ℝ}
    (hP₀ : 0≤P) (hB₀ : 0≤B) (_hC₀ : 0≤C)
    (hP : ∀ᵐ w ∂σ, ‖ψ w‖≤P) (hB : ∀ᵐ w ∂σ, ∀ x, ‖b x w‖≤B)
    (hC : ∀ᵐ w ∂σ, ∀ y, ‖c y w‖≤C) :
    Integrable (fun z : V × (V × V) => ψ z.1*spherePlaneWaveND r (z.2.1-z.2.2) z.1*
      b z.2.1 z.1*conj (c z.2.2 z.1)) (σ.prod (ρ.prod ν)) := by
  have hm : Measurable (fun z : V × (V × V) => ψ z.1*spherePlaneWaveND r (z.2.1-z.2.2) z.1*
      b z.2.1 z.1*conj (c z.2.2 z.1)) := by
    exact (((hψ.comp measurable_fst).mul
      (by unfold spherePlaneWaveND; fun_prop)).mul
        (hb.comp (measurable_snd.fst.prodMk measurable_fst))).mul
          (Complex.continuous_conj.measurable.comp
            (hc.comp (measurable_snd.snd.prodMk measurable_fst)))
  apply Integrable.of_bound hm.aestronglyMeasurable (P*B*C)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hP,
    Measure.quasiMeasurePreserving_fst.ae hB, Measure.quasiMeasurePreserving_fst.ae hC] with z hz hzB hzC
  simp only [norm_mul,spherePlaneWaveND_norm,Complex.norm_conj,mul_one]
  exact mul_le_mul (mul_le_mul hz (hzB _) (norm_nonneg _) hP₀)
    (hzC _) (norm_nonneg _) (mul_nonneg hP₀ hB₀)

theorem angular_pair_factorizationND_ae (σ ρ ν : Measure V)
    [IsFiniteMeasure σ] [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X Y : Set V) (M N r : ℝ) {ψ : V → ℂ} {b c : V → V → ℂ}
    (hψ : Measurable ψ) (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c)) {P B C : ℝ}
    (hP₀ : 0≤P) (hB₀ : 0≤B) (hC₀ : 0≤C)
    (hP : ∀ᵐ w ∂σ, ‖ψ w‖≤P) (hB : ∀ᵐ w ∂σ, ∀ x, ‖b x w‖≤B)
    (hC : ∀ᵐ w ∂σ, ∀ y, ‖c y w‖≤C) :
    ((M*N)⁻¹:ℝ) •
      (∫ z : V × V, (∫ w, ψ w*spherePlaneWaveND r (z.1-z.2) w*
        b z.1 w*conj (c z.2 w) ∂σ) ∂(ρ.restrict X).prod (ν.restrict Y)) =
      ∫ w, ψ w*sourceAngularTransformND ρ X M b r w *
        conj (sourceAngularTransformND ν Y N c r w) ∂σ := by
  have hs := integral_integral_swap (f := fun w (z : V × V) =>
    ψ w*spherePlaneWaveND r (z.1-z.2) w*b z.1 w*conj (c z.2 w))
    (angular_pair_joint_integrableND_ae σ (ρ.restrict X) (ν.restrict Y) r hψ hb hc
      hP₀ hB₀ hC₀ hP hB hC)
  have hi (w : V) :
      (∫ z : V × V, ψ w*spherePlaneWaveND r (z.1-z.2) w*b z.1 w*conj (c z.2 w)
        ∂(ρ.restrict X).prod (ν.restrict Y)) =
      ψ w*(∫ x in X, spherePlaneWaveND r x w*b x w ∂ρ) *
        conj (∫ y in Y, spherePlaneWaveND r y w*c y w ∂ν) := by
    simp_rw [spherePlaneWaveND_sub]
    have he : (fun z : V × V => ψ w*(spherePlaneWaveND r z.1 w*conj (spherePlaneWaveND r z.2 w))*
        b z.1 w*conj (c z.2 w)) =
        fun z => ψ w*((spherePlaneWaveND r z.1 w*b z.1 w)*
          conj (spherePlaneWaveND r z.2 w*c z.2 w)) := by
      funext z
      simp only [map_mul]
      ring
    rw [he,integral_const_mul,
      integral_prod_mul (fun x => spherePlaneWaveND r x w*b x w)
        (fun y => conj (spherePlaneWaveND r y w*c y w)),integral_conj]
    ring
  rw [← hs]
  simp_rw [hi]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with w
  simp only [sourceAngularTransformND,Complex.real_smul,map_mul,Complex.conj_ofReal,
    mul_inv_rev,Complex.ofReal_mul]
  ring

end CurrentFalconer
end
end

section
section
namespace CurrentFalconer
open Set MeasureTheory Attempt4FullFar
open scoped ComplexConjugate RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def graphPairMoment (μ ν : Measure V) (b c : V → V → ℂ)
    (θ : V → ℂ) (r : ℝ) : ℂ :=
  ∫ w, θ w*sourceAngularTransformND μ univ 1 b r w*
    conj (sourceAngularTransformND ν univ 1 c r w) ∂canonicalSphereMeasureND V

noncomputable def graphPairAmplitude (θ : V → ℂ) (b c : V → V → ℂ)
    (z : V×V) (w : V) : ℂ := θ w*b z.1 w*conj (c z.2 w)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
lemma graphPairAmplitude_measurable {θ : V → ℂ} {b c : V → V → ℂ}
    (hθ : Measurable θ) (hb : Measurable (Function.uncurry b))
    (hc : Measurable (Function.uncurry c)) :
    Measurable (Function.uncurry (graphPairAmplitude θ b c)) := by
  exact ((hθ.comp measurable_snd).mul
    (hb.comp (measurable_fst.fst.prodMk measurable_snd))).mul
    (Complex.continuous_conj.measurable.comp (hc.comp (measurable_fst.snd.prodMk measurable_snd)))

lemma graphAxis_measurable {Z : Type*} [MeasurableSpace Z] (Q : ℝ)
    {e : Z → V} {b : Z → V → ℂ} (he : Measurable e)
    (hb : Measurable (Function.uncurry b)) :
    Measurable (fun z : ℝ×Z => sphereAxisIntegralND (Q*z.1) (e z.2) (b z.2)) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  change Measurable (fun z : (ℝ×Z)×V =>
    Attempt4FullFar.spherePlaneWaveND (Q*z.1.1) (e z.1.2) z.2*b z.1.2 z.2)
  apply Measurable.mul _ (hb.comp (measurable_fst.snd.prodMk measurable_snd))
  unfold Attempt4FullFar.spherePlaneWaveND
  fun_prop

lemma graphPairMoment_factorization (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (b c : V → V → ℂ) (θ : V → ℂ) (r : ℝ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (hθ : Measurable θ) {B C P : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hbd : ∀ x w, ‖w‖=1 → ‖b x w‖ ≤ B) (hcd : ∀ x w, ‖w‖=1 → ‖c x w‖ ≤ C)
    (hpd : ∀ w, ‖w‖=1 → ‖θ w‖ ≤ P) :
    graphPairMoment μ ν b c θ r =
      ∫ z : V×V, sphereAxisIntegralND r (z.1-z.2) (graphPairAmplitude θ b c z) ∂μ.prod ν := by
  have h := angular_pair_factorizationND_ae (canonicalSphereMeasureND V) μ ν
    univ univ 1 1 r hθ hb hc hP hB hC
    (canonicalSphereMeasureND_ae_norm.mono (fun w hw => hpd w hw))
    (canonicalSphereMeasureND_ae_norm.mono (fun w hw x => hbd x w hw))
    (canonicalSphereMeasureND_ae_norm.mono (fun w hw x => hcd x w hw))
  simp only [Measure.restrict_univ,one_mul,inv_one,one_smul] at h
  rw [graphPairMoment,←h]
  apply integral_congr_ae
  filter_upwards with z
  apply integral_congr_ae
  filter_upwards with w
  dsimp [sphereAxisIntegralND,graphPairAmplitude,Attempt4FullFar.spherePlaneWaveND,spherePlaneWaveND]
  ring

lemma graphPairMoment_measurable (μ ν : Measure V) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (b c : V → V → ℂ) (θ : V → ℂ) (Q : ℝ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (hθ : Measurable θ) : Measurable (fun r => graphPairMoment μ ν b c θ (Q*r)) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  have hm : Measurable (fun z : ℝ×V => (Q*z.1,z.2)) := by fun_prop
  have hU := (sourceAngularTransformND_measurable μ univ 1 hb).comp hm
  have hW := (sourceAngularTransformND_measurable ν univ 1 hc).comp hm
  exact ((hθ.comp measurable_snd).mul hU).mul (Complex.continuous_conj.measurable.comp hW)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma graphPairAmplitude_bound {θ : V → ℂ} {b c : V → V → ℂ} {B C P : ℝ}
    (hB : 0 ≤ B) (hP : 0 ≤ P)
    (hbd : ∀ x w, ‖w‖=1 → ‖b x w‖ ≤ B) (hcd : ∀ x w, ‖w‖=1 → ‖c x w‖ ≤ C)
    (hpd : ∀ w, ‖w‖=1 → ‖θ w‖ ≤ P) :
    ∀ z w, ‖w‖=1 → ‖graphPairAmplitude θ b c z w‖ ≤ P*B*C := by
  intro z w hw
  simp only [graphPairAmplitude,norm_mul,Complex.norm_conj]
  exact mul_le_mul (mul_le_mul (hpd w hw) (hbd z.1 w hw) (norm_nonneg _) hP)
    (hcd z.2 w hw) (norm_nonneg _) (mul_nonneg hP hB)

lemma graphAxis_integrable (μ : Measure (V×V)) [IsFiniteMeasure μ] (r : ℝ)
    {b : (V×V) → V → ℂ} (hb : Measurable (Function.uncurry b)) {B : ℝ}
    (hbd : ∀ z w, ‖w‖=1 → ‖b z w‖ ≤ B) :
    Integrable (fun z : V×V => sphereAxisIntegralND r (z.1-z.2) (b z)) μ := by
  have hm := (graphAxis_measurable 1 (measurable_fst.sub measurable_snd) hb).comp
    ((measurable_const : Measurable (fun _ : V×V => r)).prodMk measurable_id)
  simp only [one_mul] at hm
  apply Integrable.of_bound hm.aestronglyMeasurable ((canonicalSphereMeasureND V).real univ*B)
  filter_upwards with z
  exact sphereAxisIntegralND_norm_le (hbd z)

noncomputable def graphSpatialKernel (Ψ : ℝ → ℂ) (Q : ℝ)
    (θ₁ θ₂ : V → ℂ) (b₁ b₂ b₃ b₄ : V → V → ℂ)
    (z : (V×V)×(V×V)) : ℂ :=
  graphFixedSpatialTermND Ψ Q (z.1.1-z.1.2) (z.2.1-z.2.2)
    (graphPairAmplitude θ₁ b₁ b₂ z.1) (graphPairAmplitude θ₂ b₃ b₄ z.2)

end CurrentFalconer
end
end

section
section
namespace CurrentFalconer
open Set MeasureTheory Attempt4FullFar
open scoped ComplexConjugate RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma graphSpatial_integrable
    (μ₁ μ₂ : Measure (V×V)) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {Ψ : ℝ → ℂ} (hΨ : Measurable Ψ) (hiΨ : Integrable Ψ) (Q : ℝ)
    (a₁ a₂ : (V×V) → V → ℂ)
    (ha₁ : Measurable (Function.uncurry a₁)) (ha₂ : Measurable (Function.uncurry a₂))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (hbd₁ : ∀ z w, ‖w‖=1 → ‖a₁ z w‖ ≤ B₁)
    (hbd₂ : ∀ z w, ‖w‖=1 → ‖a₂ z w‖ ≤ B₂) :
    Integrable (fun z : ℝ×((V×V)×(V×V)) => Ψ z.1 *
      sphereAxisIntegralND (Q*z.1) (z.2.1.1-z.2.1.2) (a₁ z.2.1) *
      sphereAxisIntegralND (Q*z.1) (z.2.2.1-z.2.2.2) (a₂ z.2.2))
      (volume.prod (μ₁.prod μ₂)) := by
  have hm₁ : Measurable (fun z : ℝ×((V×V)×(V×V)) => (z.1,z.2.1)) := by fun_prop
  have hm₂ : Measurable (fun z : ℝ×((V×V)×(V×V)) => (z.1,z.2.2)) := by fun_prop
  have ha := (graphAxis_measurable Q (measurable_fst.sub measurable_snd) ha₁).comp hm₁
  have hb := (graphAxis_measurable Q (measurable_fst.sub measurable_snd) ha₂).comp hm₂
  have hm := ((hΨ.comp measurable_fst).mul ha).mul hb
  let S := (canonicalSphereMeasureND V).real univ
  have hmajor := (hiΨ.norm.comp_fst (μ₁.prod μ₂)).mul_const ((S*B₁)*(S*B₂))
  apply hmajor.mono' hm.aestronglyMeasurable
  filter_upwards with z
  change ‖Ψ z.1 * sphereAxisIntegralND (Q*z.1) (z.2.1.1-z.2.1.2) (a₁ z.2.1) *
    sphereAxisIntegralND (Q*z.1) (z.2.2.1-z.2.2.2) (a₂ z.2.2)‖ ≤
    ‖Ψ z.1‖*((S*B₁)*(S*B₂))
  simp only [norm_mul]
  have hh₁ := sphereAxisIntegralND_norm_le (hbd₁ z.2.1) (Λ:=Q*z.1) (e:=z.2.1.1-z.2.1.2)
  have hh₂ := sphereAxisIntegralND_norm_le (hbd₂ z.2.2) (Λ:=Q*z.1) (e:=z.2.2.1-z.2.2.2)
  change ‖Ψ z.1‖*‖_‖*‖_‖ ≤ ‖Ψ z.1‖*((S*B₁)*(S*B₂))
  rw [←mul_assoc]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hh₁ (norm_nonneg _)) hh₂
    (norm_nonneg _) (by dsimp [S]; positivity)

theorem graph_four_spatial_factorization
    (μ₁ μ₂ μ₃ μ₄ : Measure V)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    {Ψ : ℝ → ℂ} (hΨ : Measurable Ψ) (hiΨ : Integrable Ψ) (Q : ℝ)
    (θ₁ θ₂ : V → ℂ) (b₁ b₂ b₃ b₄ : V → V → ℂ)
    (hθ₁ : Measurable θ₁) (hθ₂ : Measurable θ₂)
    (hb₁ : Measurable (Function.uncurry b₁)) (hb₂ : Measurable (Function.uncurry b₂))
    (hb₃ : Measurable (Function.uncurry b₃)) (hb₄ : Measurable (Function.uncurry b₄))
    {P₁ P₂ B₁ B₂ B₃ B₄ : ℝ}
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃) (hB₄ : 0 ≤ B₄)
    (hdθ₁ : ∀ w, ‖w‖=1 → ‖θ₁ w‖ ≤ P₁) (hdθ₂ : ∀ w, ‖w‖=1 → ‖θ₂ w‖ ≤ P₂)
    (hbd₁ : ∀ x w, ‖w‖=1 → ‖b₁ x w‖ ≤ B₁) (hbd₂ : ∀ x w, ‖w‖=1 → ‖b₂ x w‖ ≤ B₂)
    (hbd₃ : ∀ x w, ‖w‖=1 → ‖b₃ x w‖ ≤ B₃) (hbd₄ : ∀ x w, ‖w‖=1 → ‖b₄ x w‖ ≤ B₄) :
    (∫ u, Ψ u*graphPairMoment μ₁ μ₂ b₁ b₂ θ₁ (Q*u)*graphPairMoment μ₃ μ₄ b₃ b₄ θ₂ (Q*u)) =
      ∫ z, graphSpatialKernel Ψ Q θ₁ θ₂ b₁ b₂ b₃ b₄ z ∂(μ₁.prod μ₂).prod (μ₃.prod μ₄) := by
  let a₁ := graphPairAmplitude θ₁ b₁ b₂
  let a₂ := graphPairAmplitude θ₂ b₃ b₄
  have ha₁ := graphPairAmplitude_measurable hθ₁ hb₁ hb₂
  have ha₂ := graphPairAmplitude_measurable hθ₂ hb₃ hb₄
  have hd₁ := graphPairAmplitude_bound hB₁ hP₁ hbd₁ hbd₂ hdθ₁
  have hd₂ := graphPairAmplitude_bound hB₃ hP₂ hbd₃ hbd₄ hdθ₂
  have ht := graphSpatial_integrable (μ₁.prod μ₂) (μ₃.prod μ₄) hΨ hiΨ Q a₁ a₂ ha₁ ha₂
    (by positivity) (by positivity) hd₁ hd₂
  have he (u : ℝ) :
      Ψ u*graphPairMoment μ₁ μ₂ b₁ b₂ θ₁ (Q*u)*graphPairMoment μ₃ μ₄ b₃ b₄ θ₂ (Q*u) =
      ∫ z : (V×V)×(V×V), Ψ u*sphereAxisIntegralND (Q*u) (z.1.1-z.1.2) (a₁ z.1)*
        sphereAxisIntegralND (Q*u) (z.2.1-z.2.2) (a₂ z.2) ∂(μ₁.prod μ₂).prod (μ₃.prod μ₄) := by
    rw [graphPairMoment_factorization μ₁ μ₂ b₁ b₂ θ₁ (Q*u) hb₁ hb₂ hθ₁ hB₁ hB₂ hP₁ hbd₁ hbd₂ hdθ₁,
      graphPairMoment_factorization μ₃ μ₄ b₃ b₄ θ₂ (Q*u) hb₃ hb₄ hθ₂ hB₃ hB₄ hP₂ hbd₃ hbd₄ hdθ₂]
    simp only [mul_assoc]
    rw [←integral_prod_mul (fun z : V×V => sphereAxisIntegralND (Q*u) (z.1-z.2) (a₁ z))
      (fun z : V×V => sphereAxisIntegralND (Q*u) (z.1-z.2) (a₂ z)),←integral_const_mul]
  simp_rw [he]
  rw [integral_integral_swap ht]
  rfl

end CurrentFalconer
end
end

end OAI
