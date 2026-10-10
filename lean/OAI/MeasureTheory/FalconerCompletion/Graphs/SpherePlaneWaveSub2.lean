import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.EuclideanPairDirection
import OAI.MeasureTheory.FalconerCompletion.Sphere.SpherePlaneWave3

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
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
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
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

lemma sourceAngularTransformND_norm_le {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (ρ : Measure V) [IsFiniteMeasure ρ]
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
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ComplexConjugate RealInnerProductSpace
variable {n : ℕ}

lemma physical_sphereWaveND (r : ℝ)
    (x : EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))
    (w : EuclideanSpace ℝ (Fin (n+1))) :
    Complex.exp (Complex.I*(r*dist x.1 x.2)*(inner ℝ w (euclideanPairDirectionND x):ℂ)) =
      spherePlaneWaveND r (x.1-x.2) w := by
  unfold euclideanPairDirectionND spherePlaneWaveND
  by_cases h : x.1-x.2=0
  · simp [h,dist_eq_norm]
  · have hn : ‖x.1-x.2‖≠0 := norm_ne_zero_iff.mpr h
    rw [inner_smul_right,dist_eq_norm]
    push_cast
    have hn' : (‖x.1-x.2‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn
    field_simp

lemma physical_sphereAxisND (r : ℝ)
    (x : EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))
    (b : EuclideanSpace ℝ (Fin (n+1)) → ℂ) :
    sphereAxisIntegralND (r*dist x.1 x.2) (euclideanPairDirectionND x) b =
      ∫ w, spherePlaneWaveND r (x.1-x.2) w*b w
        ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))) := by
  unfold sphereAxisIntegralND
  congr 1
  funext w
  rw [Complex.ofReal_mul,physical_sphereWaveND]

noncomputable def physicalAngularMomentND
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1))))
    (X : Set (EuclideanSpace ℝ (Fin (n+1)))) (M : ℝ)
    (b : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ) (r : ℝ) : ℝ :=
  ∫ w, ‖sourceAngularTransformND ρ X M b r w‖^2
    ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))

lemma physicalAngularMomentND_nonneg
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1))))
    (X : Set (EuclideanSpace ℝ (Fin (n+1)))) (M : ℝ)
    (b : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ) (r : ℝ) :
    0≤physicalAngularMomentND ρ X M b r := integral_nonneg (fun _ => sq_nonneg _)

theorem physical_pair_momentND
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ]
    (X : Set (EuclideanSpace ℝ (Fin (n+1)))) (M r : ℝ)
    (b : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) {B : ℝ} (hB : 0≤B)
    (hbd : ∀ x w, ‖w‖=1 → ‖b x w‖≤B) :
    ((M*M)⁻¹:ℝ) • (∫ x, sphereAxisIntegralND (r*dist x.1 x.2) (euclideanPairDirectionND x)
      (fun w => b x.1 w*conj (b x.2 w)) ∂(ρ.restrict X).prod (ρ.restrict X)) =
      (physicalAngularMomentND ρ X M b r : ℂ) := by
  have ha : ∀ᵐ w ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))), ∀ x, ‖b x w‖≤B := by
    filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
    exact fun x => hbd x w hw
  have h := angular_pair_factorizationND_ae (canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))))
    ρ ρ X X M M r (ψ:=fun _ => 1) measurable_const hb hb (by norm_num : (0:ℝ)≤1) hB hB
    (Filter.Eventually.of_forall (fun _ => by norm_num)) ha ha
  simp only [one_mul] at h
  simp_rw [physical_sphereAxisND]
  have he : (fun x : EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)) =>
      ∫ w, spherePlaneWaveND r (x.1-x.2) w*(b x.1 w*conj (b x.2 w))
        ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) =
      fun x => ∫ w, spherePlaneWaveND r (x.1-x.2) w*b x.1 w*conj (b x.2 w)
        ∂canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))) := by
    funext x
    simp only [mul_assoc]
  rw [he,h]
  simp only [Complex.mul_conj,Complex.normSq_eq_norm_sq,integral_complex_ofReal,physicalAngularMomentND]

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
