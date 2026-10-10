import Mathlib
import OAI.Probability.SphericalField.Sphere.Limit

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

lemma sphericalExp_field_holder (n : ℕ) (u v : Spin (n+1)) (R : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    ENNReal.ofReal (sphericalExp n (a • u+b • v) R) ≤
      ENNReal.ofReal (sphericalExp n u R)^a * ENNReal.ofReal (sphericalExp n v R)^b := by
  have he (z : Spin (n+1)) : ENNReal.ofReal (sphericalExp n z R) =
      ∫⁻ x : Metric.sphere (0 : Spin (n+1)) 1,
        ENNReal.ofReal (Real.exp (R*inner ℝ z x.val)) ∂unitSphereLaw (n+1) :=
    ofReal_integral_eq_lintegral_ofReal
      (unitSphere_continuous_integrable (by fun_prop))
      (ae_of_all _ fun _ => (Real.exp_pos _).le)
  simp_rw [he]
  have h (x : Metric.sphere (0 : Spin (n+1)) 1) :
      ENNReal.ofReal (Real.exp (R*inner ℝ (a • u+b • v) x.val)) =
        ENNReal.ofReal (Real.exp (R*inner ℝ u x.val))^a *
          ENNReal.ofReal (Real.exp (R*inner ℝ v x.val))^b := by
    simp only [inner_add_left,real_inner_smul_left]
    rw [show R*(a*inner ℝ u x.val+b*inner ℝ v x.val)=
      a*(R*inner ℝ u x.val)+b*(R*inner ℝ v x.val) by ring]
    exact ofReal_exp_affine _ _ _ _
  simp_rw [h]
  exact ENNReal.lintegral_mul_norm_pow_le (by fun_prop) (by fun_prop) ha hb hab

lemma decoratedLeafIntegral_mixed_holder {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [AddCommMonoid X] [Module ℝ X]
    (s₁ s₂ s₃ : X × S → X) (hs₁ : Measurable s₁) (hs₂ : Measurable s₂)
    (F : X → ℝ≥0∞) (hF : Measurable F) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (hstep : ∀ x y t, s₃ (a • x+b • y,t)=a • s₁ (x,t)+b • s₂ (y,t))
    (hconv : ∀ x y, F (a • x+b • y) ≤ F x^a*F y^b)
    (k : ℕ) (η : DecoratedCascade S k) (x y : X) :
    decoratedLeafIntegral s₃ F k (a • x+b • y,η) ≤
      decoratedLeafIntegral s₁ F k (x,η)^a*decoratedLeafIntegral s₂ F k (y,η)^b := by
  induction k generalizing x y with
  | zero => exact hconv x y
  | succ k ih =>
    have hm (s : X × S → X) (hs : Measurable s) (x : X) :
        Measurable (fun q : ℝ × (S × DecoratedCascade S k) =>
          ENNReal.ofReal (Real.exp q.1)*decoratedLeafIntegral s F k (s (x,q.2.1),q.2.2)) :=
      (measurable_fst.exp.ennreal_ofReal).mul
        ((decoratedLeafIntegral_measurable s hs F hF k).comp
          ((hs.comp (measurable_const.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))
    simp only [decoratedLeafIntegral,hstep]
    refine le_trans (lintegral_mono fun q => mul_le_mul_right (ih q.2.2 (s₁ (x,q.2.1)) (s₂ (y,q.2.1))) _) ?_
    calc
      _ = ∫⁻ q : ℝ × (S × DecoratedCascade S k),
          (ENNReal.ofReal (Real.exp q.1)*decoratedLeafIntegral s₁ F k (s₁ (x,q.2.1),q.2.2))^a *
          (ENNReal.ofReal (Real.exp q.1)*decoratedLeafIntegral s₂ F k (s₂ (y,q.2.1),q.2.2))^b
            ∂markedStableCountKernel η := by
        congr 1
        funext q
        rw [ENNReal.mul_rpow_of_nonneg _ _ ha,ENNReal.mul_rpow_of_nonneg _ _ hb]
        have he : ENNReal.ofReal (Real.exp q.1)^a*ENNReal.ofReal (Real.exp q.1)^b =
            ENNReal.ofReal (Real.exp q.1) := by
          rw [← ENNReal.rpow_add _ _ (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top,hab,ENNReal.rpow_one]
        calc
          _ = (ENNReal.ofReal (Real.exp q.1)^a*ENNReal.ofReal (Real.exp q.1)^b)*
              (decoratedLeafIntegral s₁ F k (s₁ (x,q.2.1),q.2.2)^a*
                decoratedLeafIntegral s₂ F k (s₂ (y,q.2.1),q.2.2)^b) := by rw [he]
          _ = _ := by ring
      _ ≤ _ := ENNReal.lintegral_mul_norm_pow_le (hm s₁ hs₁ x).aemeasurable
        (hm s₂ hs₂ y).aemeasurable ha hb hab

lemma canonicalCoordinateStep_affine (d : ℕ) (σ τ : ℕ → ℝ) (x y : Fin d → ℕ → ℝ)
    (t : Fin d → ℝ) (a b : ℝ) :
    canonicalCoordinateStep d (a • σ+b • τ) (a • x+b • y,t) =
      a • canonicalCoordinateStep d σ (x,t)+b • canonicalCoordinateStep d τ (y,t) := by
  funext i j
  simp only [canonicalCoordinateStep,gaussianShiftStep,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

lemma coordinateLeafField_affine (d : ℕ) (x y : Fin d → ℕ → ℝ) (a b : ℝ) :
    coordinateLeafField d (a • x+b • y)=a • coordinateLeafField d x+b • coordinateLeafField d y := by
  ext i
  simp [coordinateLeafField]

lemma coordinateAngularFactor_amplitude_holder (n k : ℕ) (σ τ : ℕ → ℝ)
    (x y : Fin (n+1) → ℕ → ℝ) (η : DecoratedCascade (Fin (n+1) → ℝ) k)
    (R : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    decoratedAngularFactor n (canonicalCoordinateStep (n+1) (a • σ+b • τ))
      (coordinateLeafField (n+1)) k (a • x+b • y,η) R ≤
    decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
      (coordinateLeafField (n+1)) k (x,η) R ^ a *
    decoratedAngularFactor n (canonicalCoordinateStep (n+1) τ)
      (coordinateLeafField (n+1)) k (y,η) R ^ b := by
  simp_rw [decoratedAngularFactor_eq n _ (canonicalCoordinateStep_measurable _ _)
    _ (coordinateLeafField_measurable _) ]
  apply decoratedLeafIntegral_mixed_holder _ _ _ (canonicalCoordinateStep_measurable _ _)
    (canonicalCoordinateStep_measurable _ _)
    (fun x => ENNReal.ofReal (sphericalExp n (coordinateLeafField (n+1) x) R))
    ?_ ha hb hab (fun x y t => canonicalCoordinateStep_affine _ _ _ x y t a b)
  · intro x y
    rw [coordinateLeafField_affine]
    exact sphericalExp_field_holder n _ _ R ha hb hab
  · have hm := coordinateLeafField_measurable (n+1)
    unfold sphericalExp
    apply ENNReal.measurable_ofReal.comp
    exact (show StronglyMeasurable (fun p : (Fin (n+1) → ℕ → ℝ) ×
        Metric.sphere (0:Spin (n+1)) 1 =>
      Real.exp (R*inner ℝ (coordinateLeafField (n+1) p.1) (p.2:Spin (n+1)))) from (by fun_prop)).integral_prod_right'.measurable

lemma decoratedLeafIntegral_constant_step {X Y S : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace S] (s : X × S → X) (t : Y × S → Y)
    (c : ℝ≥0∞) (k : ℕ) (η : DecoratedCascade S k) (x : X) (y : Y) :
    decoratedLeafIntegral s (fun _ => c) k (x,η)=
      decoratedLeafIntegral t (fun _ => c) k (y,η) := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
    simp only [decoratedLeafIntegral]
    congr 1
    funext q
    rw [ih q.2.2 (s (x,q.2.1)) (t (y,q.2.1))]

lemma decoratedTerminalTotal_zero_step {X Y S : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace S] (s : X × S → X) (t : Y × S → Y)
    (k : ℕ) (η : DecoratedCascade S k) (x : X) (y : Y) :
    decoratedTerminalTotal s (fun _ => 0) k (x,η)=
      decoratedTerminalTotal t (fun _ => 0) k (y,η) := by
  unfold decoratedTerminalTotal
  rw [← decoratedLeafIntegral_exp,← decoratedLeafIntegral_exp]
  exact congrArg ENNReal.toReal (decoratedLeafIntegral_constant_step s t _ k η x y)

lemma quadraticCascadePrecision_add (σ : ℕ → ℝ) (b c : ℝ) (k : ℕ) (z : Fin k → ℝ) :
    quadraticCascadePrecision σ (b+c) k z=quadraticCascadePrecision σ b k z+c := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [quadraticCascadePrecision,ih]; ring

lemma exists_positive_canonical_precision (σ : ℕ → ℝ) (k : ℕ) (z : Fin k → ℝ) :
    ∃ b : ℝ, 0 < quadraticCascadePrecision σ b k z := by
  refine ⟨0+(1-quadraticCascadePrecision σ 0 k z),?_⟩
  rw [quadraticCascadePrecision_add]
  linarith

lemma coordinateAngularLog_amplitude_convex (n k : ℕ) (σ τ : ℕ → ℝ)
    (x y : Fin (n+1) → ℕ → ℝ) (η : DecoratedCascade (Fin (n+1) → ℝ) k)
    (R : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k (x,η))
    (hσ : 0 < (decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
      (coordinateLeafField (n+1)) k (x,η) R).toReal)
    (hτ : 0 < (decoratedAngularFactor n (canonicalCoordinateStep (n+1) τ)
      (coordinateLeafField (n+1)) k (y,η) R).toReal)
    (hm : 0 < (decoratedAngularFactor n (canonicalCoordinateStep (n+1) (a • σ+b • τ))
      (coordinateLeafField (n+1)) k (a • x+b • y,η) R).toReal) :
    coordinateAngularLog n k (a • σ+b • τ) R (a • x+b • y,η) ≤
      a*coordinateAngularLog n k σ R (x,η)+b*coordinateAngularLog n k τ R (y,η) := by
  have H := coordinateAngularFactor_amplitude_holder n k σ τ x y η R ha hb hab
  have H' := ENNReal.toReal_mono (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg ha (ENNReal.toReal_pos_iff.mp hσ).2.ne)
    (ENNReal.rpow_ne_top_of_nonneg hb (ENNReal.toReal_pos_iff.mp hτ).2.ne)) H
  rw [ENNReal.toReal_mul,← ENNReal.toReal_rpow,← ENNReal.toReal_rpow] at H'
  have Hlog := Real.log_le_log hm H'
  rw [Real.log_mul (Real.rpow_pos_of_pos hσ a).ne' (Real.rpow_pos_of_pos hτ b).ne',
    Real.log_rpow hσ,Real.log_rpow hτ] at Hlog
  have he₁ := decoratedTerminalTotal_zero_step (canonicalCoordinateStep (n+1) (a • σ+b • τ))
    (canonicalCoordinateStep (n+1) σ) k η (a • x+b • y) x
  have he₂ := decoratedTerminalTotal_zero_step (canonicalCoordinateStep (n+1) τ)
    (canonicalCoordinateStep (n+1) σ) k η y x
  unfold coordinateAngularLog
  rw [he₁,he₂,Real.log_div hm.ne' h0.ne',Real.log_div hσ.ne' h0.ne',Real.log_div hτ.ne' h0.ne']
  have hh := congrArg (fun t : ℝ => t*Real.log (decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k (x,η))) hab
  nlinarith

def coordinateRootScale (d k : ℕ) (r : ℝ)
    (p : (Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k) :
    (Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k := ((fun i => r*p.1 i),p.2)

lemma coordinateRootScale_preserving (d k : ℕ) (z : Fin k → ℝ) (r : ℝ) :
    MeasurePreserving (coordinateRootScale d k r) (coordinateCascadeLaw d k z 1)
      (coordinateCascadeLaw d k z ⟨r^2,sq_nonneg r⟩) := by
  have hp : MeasurePreserving (fun x : Fin d → ℝ => fun i => r*x i)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin d => gaussianReal 0 ⟨r^2,sq_nonneg r⟩)) := by
    refine ⟨by fun_prop,?_⟩
    erw [Measure.pi_map_pi (fun _ => (measurable_id.const_mul r).aemeasurable)]
    congr 1
    funext i
    change (gaussianReal 0 1).map (fun x : ℝ => r*x)=gaussianReal 0 ⟨r^2,sq_nonneg r⟩
    rw [gaussianReal_map_const_mul,mul_zero,mul_one]
    rfl
  exact hp.prod (MeasurePreserving.id _)

def amplitudeSphereLog (n k : ℕ) (σ : ℕ → ℝ) (r : ℝ)
    (p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) : ℝ :=
  coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) ((fun i _ => r*p.1 i),p.2)/(n+1:ℕ)

def amplitudeSphereValue (n k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ) (r : ℝ) : ℝ :=
  ∫ p, amplitudeSphereLog n k σ r p ∂coordinateCascadeLaw (n+1) k z 1

lemma amplitudeSphereLog_integrable (n k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (r : ℝ) :
    Integrable (amplitudeSphereLog n k σ r) (coordinateCascadeLaw (n+1) k z 1) := by
  obtain ⟨b,hb⟩ := exists_positive_canonical_precision σ k z
  have hi := normalizedCoordinateSphereLog_integrable n k σ z hz hz0 hz1 hb ⟨r^2,sq_nonneg r⟩
  exact ((coordinateRootScale_preserving (n+1) k z r).integrable_comp hi.aestronglyMeasurable).mpr hi

lemma amplitudeSphereValue_eq (n k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ) (r : ℝ) :
    amplitudeSphereValue n k σ z r=
      expectedCoordinateSphereLog n k σ z ⟨r^2,sq_nonneg r⟩ := by
  have hp := coordinateRootScale_preserving (n+1) k z r
  have he := integral_map (μ := coordinateCascadeLaw (n+1) k z 1) hp.measurable.aemeasurable
    ((normalizedCoordinateSphereLog_measurable n k σ).aestronglyMeasurable)
  rw [hp.map_eq] at he
  exact he.symm

lemma amplitudeSphereLog_nonneg (n k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (r : ℝ) :
    0 ≤ᵐ[coordinateCascadeLaw (n+1) k z 1] amplitudeSphereLog n k σ r := by
  obtain ⟨b,hb⟩ := exists_positive_canonical_precision σ k z
  exact (coordinateRootScale_preserving (n+1) k z r).quasiMeasurePreserving.ae
    (normalizedCoordinateSphereLog_nonneg n k σ z hz hz0 hz1 hb ⟨r^2,sq_nonneg r⟩)

lemma amplitudeSphereLog_regular (n k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (r : ℝ) :
    ∀ᵐ p ∂coordinateCascadeLaw (n+1) k z 1,
      0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0)
        k ((fun i _ => r*p.1 i),p.2) ∧
      0 < (decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
        (coordinateLeafField (n+1)) k ((fun i _ => r*p.1 i),p.2) (Real.sqrt (n+1:ℕ))).toReal := by
  obtain ⟨b,hb⟩ := exists_positive_canonical_precision σ k z
  have hb0 : 0 < b := hb.trans_le (quadraticCascadePrecision_le σ b k z (fun i => (hz0 i).le))
  have he : ∀ᵐ p ∂coordinateCascadeLaw (n+1) k z ⟨r^2,sq_nonneg r⟩,
      0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0)
        k ((fun i _ => p.1 i),p.2) ∧
      0 < (decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
        (coordinateLeafField (n+1)) k ((fun i _ => p.1 i),p.2) (Real.sqrt (n+1:ℕ))).toReal := by
    filter_upwards [canonicalCoordinateBase_pos (n+1) k σ z hz hz0 hz1 ⟨r^2,sq_nonneg r⟩,
      canonicalCoordinateTotal_pos (n+1) k σ b z hz hz0 hz1 hb ⟨r^2,sq_nonneg r⟩] with p h0 hc
    exact ⟨h0,(coordinateAngularLog_regular n k σ _ hb0 _ h0 hc).1⟩
  exact (coordinateRootScale_preserving (n+1) k z r).quasiMeasurePreserving.ae he

lemma amplitudeSphereValue_convex (n k : ℕ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (σ τ : ℕ → ℝ) (r s : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    amplitudeSphereValue n k (a • σ+b • τ) z (a*r+b*s) ≤
      a*amplitudeSphereValue n k σ z r+b*amplitudeSphereValue n k τ z s := by
  have hi := amplitudeSphereLog_integrable n k (a • σ+b • τ) z hz hz0 hz1 (a*r+b*s)
  have hσ := amplitudeSphereLog_integrable n k σ z hz hz0 hz1 r
  have hτ := amplitudeSphereLog_integrable n k τ z hz hz0 hz1 s
  have he (p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) :
      (fun (i : Fin (n+1)) (_ : ℕ) => (a*r+b*s)*p.1 i)=
        a • (fun (i : Fin (n+1)) (_ : ℕ) => r*p.1 i)+b • (fun (i : Fin (n+1)) (_ : ℕ) => s*p.1 i) := by
    funext i j
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hle : amplitudeSphereLog n k (a • σ+b • τ) (a*r+b*s) ≤ᵐ[coordinateCascadeLaw (n+1) k z 1]
      (fun p => a*amplitudeSphereLog n k σ r p+b*amplitudeSphereLog n k τ s p) := by
    filter_upwards [amplitudeSphereLog_regular n k σ z hz hz0 hz1 r,
      amplitudeSphereLog_regular n k τ z hz hz0 hz1 s,
      amplitudeSphereLog_regular n k (a • σ+b • τ) z hz hz0 hz1 (a*r+b*s)] with p h1 h2 h3
    rw [he p] at h3
    have h := coordinateAngularLog_amplitude_convex n k σ τ _ _ p.2 _ ha hb hab h1.1 h1.2 h2.2 h3.2
    unfold amplitudeSphereLog
    rw [he p]
    calc
      _ ≤ (a*coordinateAngularLog n k σ (Real.sqrt (n+1:ℕ)) ((fun i _ => r*p.1 i),p.2)+
          b*coordinateAngularLog n k τ (Real.sqrt (n+1:ℕ)) ((fun i _ => s*p.1 i),p.2))/(n+1:ℕ) :=
        div_le_div_of_nonneg_right h (by positivity)
      _ = _ := by ring
  have hh := integral_mono_ae hi ((hσ.const_mul a).add (hτ.const_mul b)) hle
  change (∫ p, amplitudeSphereLog n k (a • σ+b • τ) (a*r+b*s) p ∂coordinateCascadeLaw (n+1) k z 1) ≤
    ∫ p, a*amplitudeSphereLog n k σ r p+b*amplitudeSphereLog n k τ s p ∂coordinateCascadeLaw (n+1) k z 1 at hh
  rw [integral_add (hσ.const_mul a) (hτ.const_mul b),integral_const_mul,integral_const_mul] at hh
  exact hh

end SphericalPerceptron
end
end

end OAI
