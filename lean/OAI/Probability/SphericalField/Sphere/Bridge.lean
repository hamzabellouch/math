import Mathlib
import OAI.Probability.SphericalField.Sphere.Polar
import OAI.Probability.SphericalField.Cascade.Concentration

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron

lemma decoratedLeafIntegral_exp {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) (H : X → ℝ) (n : ℕ) (p : X × DecoratedCascade S n) :
    decoratedLeafIntegral step (fun x => ENNReal.ofReal (Real.exp (H x))) n p =
      decoratedTerminalTotalE step H n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [decoratedLeafIntegral, decoratedTerminalTotalE, ih]

lemma decoratedLeafIntegral_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) (hs : Measurable step) (F : X → ℝ≥0∞)
    (hF : Measurable F) (n : ℕ) : Measurable (decoratedLeafIntegral step F n) := by
  induction n with
  | zero => exact hF.comp measurable_fst
  | succ n ih =>
    have hm : Measurable (fun p : (X × DecoratedCascade S (n+1)) ×
        (ℝ × (S × DecoratedCascade S n)) =>
        ENNReal.ofReal (Real.exp p.2.1) *
          decoratedLeafIntegral step F n (step (p.1.1,p.2.2.1),p.2.2.2)) :=
      (measurable_snd.fst.exp.ennreal_ofReal).mul
        (ih.comp ((hs.comp (measurable_fst.fst.prodMk measurable_snd.snd.fst)).prodMk
          measurable_snd.snd.snd))
    exact hm.lintegral_kernel_prod_right' (κ := markedStableCountKernel.prodMkLeft X)

lemma decoratedLeafIntegral_param_measurable {A X S : Type}
    [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) (hs : Measurable step) (F : A × X → ℝ≥0∞)
    (hF : Measurable F) (n : ℕ) :
    Measurable (fun p : A × (X × DecoratedCascade S n) =>
      decoratedLeafIntegral step (fun x => F (p.1,x)) n p.2) := by
  induction n with
  | zero => exact hF.comp (measurable_fst.prodMk measurable_snd.fst)
  | succ n ih =>
    have hm : Measurable (fun p : (A × (X × DecoratedCascade S (n+1))) ×
        (ℝ × (S × DecoratedCascade S n)) =>
        ENNReal.ofReal (Real.exp p.2.1) *
          decoratedLeafIntegral step (fun x => F (p.1.1,x)) n
            (step (p.1.2.1,p.2.2.1),p.2.2.2)) :=
      (measurable_snd.fst.exp.ennreal_ofReal).mul
        (ih.comp (measurable_fst.fst.prodMk
          ((hs.comp (measurable_fst.snd.fst.prodMk measurable_snd.snd.fst)).prodMk
            measurable_snd.snd.snd)))
    exact hm.lintegral_kernel_prod_right'
      (κ := (markedStableCountKernel.prodMkLeft X).prodMkLeft A)

lemma decoratedLeafIntegral_mono {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) {F G : X → ℝ≥0∞} (h : ∀ x, F x ≤ G x)
    (n : ℕ) (p : X × DecoratedCascade S n) :
    decoratedLeafIntegral step F n p ≤ decoratedLeafIntegral step G n p := by
  induction n with
  | zero => exact h p.1
  | succ n ih =>
    exact lintegral_mono fun q => mul_le_mul_right (ih _) _

lemma decoratedLeafIntegral_const_mul {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) (F : X → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (n : ℕ) (p : X × DecoratedCascade S n) :
    decoratedLeafIntegral step (fun x => c * F x) n p =
      c * decoratedLeafIntegral step F n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [decoratedLeafIntegral, ih, mul_left_comm _ c]
    exact lintegral_const_mul' _ _ hc

lemma decoratedLeafIntegral_lintegral {A X S : Type}
    [MeasurableSpace A] [MeasurableSpace X] [MeasurableSpace S]
    (μ : Measure A) [SFinite μ] (step : X × S → X) (hs : Measurable step)
    (F : A × X → ℝ≥0∞) (hF : Measurable F) (n : ℕ)
    (p : X × DecoratedCascade S n) :
    decoratedLeafIntegral step (fun x => ∫⁻ a, F (a,x) ∂μ) n p =
      ∫⁻ a, decoratedLeafIntegral step (fun x => F (a,x)) n p ∂μ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [decoratedLeafIntegral, ih]
    have hm : Measurable (fun q : (ℝ × (S × DecoratedCascade S n)) × A =>
        ENNReal.ofReal (Real.exp q.1.1) *
          decoratedLeafIntegral step (fun x => F (q.2,x)) n
            (step (p.1,q.1.2.1),q.1.2.2)) :=
      (measurable_fst.fst.exp.ennreal_ofReal).mul
        ((decoratedLeafIntegral_param_measurable step hs F hF n).comp
          (measurable_snd.prodMk
            ((hs.comp (measurable_const.prodMk measurable_fst.snd.fst)).prodMk
              measurable_fst.snd.snd)))
    calc
      _ = ∫⁻ q : ℝ × (S × DecoratedCascade S n), ∫⁻ a,
          ENNReal.ofReal (Real.exp q.1) *
            decoratedLeafIntegral step (fun x => F (a,x)) n
              (step (p.1,q.2.1),q.2.2) ∂μ ∂markedStableCountKernel p.2 := by
        apply lintegral_congr
        intro q
        exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = _ := lintegral_lintegral_swap hm.aemeasurable

lemma decoratedFieldFactor_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (d : ℕ) (step : X × S → X) (hs : Measurable step) (field : X → Spin d)
    (hf : Measurable field) (k : ℕ) (p : X × DecoratedCascade S k) :
    Measurable (decoratedFieldFactor d step field k p) := by
  let F : Spin d × X → ℝ≥0∞ := fun q => ENNReal.ofReal (Real.exp (inner ℝ (field q.2) q.1))
  have hF : Measurable F :=
    (((hf.comp measurable_snd).inner measurable_fst).exp.ennreal_ofReal)
  have hm : Measurable (fun q : Spin d × (X × DecoratedCascade S k) =>
      decoratedLeafIntegral step (fun y => F (q.1,y)) k q.2) :=
    decoratedLeafIntegral_param_measurable step hs F hF k
  have hp : Measurable (fun x : Spin d => (x,p)) := measurable_id.prodMk measurable_const
  change Measurable (fun x : Spin d => decoratedLeafIntegral step (fun y => F (x,y)) k p)
  have hh := hm.comp hp
  exact hh

lemma decoratedAngularFactor_eq {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (n : ℕ) (step : X × S → X) (hs : Measurable step) (field : X → Spin (n+1))
    (hf : Measurable field) (k : ℕ) (p : X × DecoratedCascade S k) (r : ℝ) :
    decoratedAngularFactor n step field k p r =
      decoratedLeafIntegral step (fun y => ENNReal.ofReal (sphericalExp n (field y) r)) k p := by
  have h := decoratedLeafIntegral_lintegral (unitSphereLaw (n+1)) step hs
    (fun q : (Metric.sphere (0:Spin (n+1)) 1) × X =>
      ENNReal.ofReal (Real.exp (inner ℝ (field q.2) (r • (q.1:Spin (n+1))))))
    (((hf.comp measurable_snd).inner (measurable_fst.subtype_coe.const_smul r)).exp.ennreal_ofReal)
    k p
  change (∫⁻ a : Metric.sphere (0:Spin (n+1)) 1,
    decoratedLeafIntegral step (fun y => ENNReal.ofReal (Real.exp (inner ℝ (field y) (r • (a:Spin (n+1)))))) k p
      ∂unitSphereLaw (n+1)) = _
  rw [← h]
  congr 1
  funext y
  simp only [inner_smul_right]
  exact (ofReal_integral_eq_lintegral_ofReal
    (unitSphere_continuous_integrable (by fun_prop))
    (Eventually.of_forall fun u => (Real.exp_pos _).le)).symm

lemma decoratedAngularFactor_mono {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (n : ℕ) (step : X × S → X) (hs : Measurable step) (field : X → Spin (n+1))
    (hf : Measurable field) (k : ℕ) (p : X × DecoratedCascade S k)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    decoratedAngularFactor n step field k p r ≤ decoratedAngularFactor n step field k p s := by
  rw [decoratedAngularFactor_eq n step hs field hf, decoratedAngularFactor_eq n step hs field hf]
  exact decoratedLeafIntegral_mono step
    (fun y => ENNReal.ofReal_le_ofReal (sphericalExp_mono n (field y) hr hrs)) k p

lemma decoratedAngularFactor_mass_le {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (n : ℕ) (step : X × S → X) (hs : Measurable step) (field : X → Spin (n+1))
    (hf : Measurable field) (k : ℕ) (p : X × DecoratedCascade S k) (r : ℝ) :
    decoratedTerminalTotalE step (fun _ => 0) k p ≤ decoratedAngularFactor n step field k p r := by
  rw [decoratedAngularFactor_eq n step hs field hf, ← decoratedLeafIntegral_exp]
  apply decoratedLeafIntegral_mono
  intro y
  simpa using ENNReal.ofReal_le_ofReal (one_le_sphericalExp n (field y) r)

theorem decoratedCanonical_band_bounds {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (n : ℕ) (step : X × S → X) (hs : Measurable step) (field : X → Spin (n+1))
    (hf : Measurable field) (k : ℕ) (p : X × DecoratedCascade S k) (b ε : ℝ) :
    decoratedAngularFactor n step field k p (Real.sqrt (((n+1:ℕ):ℝ)*(1-ε))) *
      canonicalRadialMass n b (normSquareBand n ε) ≤
        (∫⁻ x in normSquareBand n ε,
          decoratedFieldFactor (n+1) step field k p x ∂canonicalRadialMass n b) ∧
    (∫⁻ x in normSquareBand n ε,
      decoratedFieldFactor (n+1) step field k p x ∂canonicalRadialMass n b) ≤
      decoratedAngularFactor n step field k p (Real.sqrt (((n+1:ℕ):ℝ)*(1+ε))) *
        canonicalRadialMass n b (normSquareBand n ε) := by
  have hm := decoratedFieldFactor_measurable (n+1) step hs field hf k p
  have hh := polar_weighted_bounds (volume : Measure (RadialSpace n))
    (decoratedFieldFactor (n+1) step field k p) hm
    (canonicalBandRadiusWeight n b ε) (canonicalBandRadiusWeight_measurable n b ε)
    (L := decoratedAngularFactor n step field k p (Real.sqrt (((n+1:ℕ):ℝ)*(1-ε))))
    (U := decoratedAngularFactor n step field k p (Real.sqrt (((n+1:ℕ):ℝ)*(1+ε))))
  rw [canonicalBandRadiusWeight_integral n b ε _ hm,canonicalBandRadiusWeight_mass] at hh
  apply hh
  · intro r hr
    have hb : ((n+1:ℕ):ℝ)*(1-ε) ≤ (r:ℝ)^2 ∧ (r:ℝ)^2 ≤ ((n+1:ℕ):ℝ)*(1+ε) := by
      by_contra hn
      exact hr (by simp only [canonicalBandRadiusWeight,Set.indicator_apply,Set.mem_ofPred_eq,hn,ite_false])
    change _ ≤ decoratedAngularFactor n step field k p r
    apply decoratedAngularFactor_mono n step hs field hf k p (Real.sqrt_nonneg _)
    exact (Real.sqrt_le_iff).mpr ⟨r.property.le,hb.1⟩
  · intro r hr
    have hb : ((n+1:ℕ):ℝ)*(1-ε) ≤ (r:ℝ)^2 ∧ (r:ℝ)^2 ≤ ((n+1:ℕ):ℝ)*(1+ε) := by
      by_contra hn
      exact hr (by simp only [canonicalBandRadiusWeight,Set.indicator_apply,Set.mem_ofPred_eq,hn,ite_false])
    change decoratedAngularFactor n step field k p r ≤ _
    apply decoratedAngularFactor_mono n step hs field hf k p r.property.le
    exact (Real.le_sqrt' r.property).mpr hb.2

lemma canonicalRadialDensity_complete_square (n : ℕ) {b : ℝ} (hb : 0 < b)
    (z x : Spin (n+1)) :
    canonicalRadialDensity n b x * Real.exp (inner ℝ z x) =
      Real.exp (‖z‖^2/(2*b)) * canonicalRadialDensity n b (x - b⁻¹ • z) := by
  have he : -(b/2)*‖x‖^2 + inner ℝ z x = ‖z‖^2/(2*b) - (b/2)*‖x-b⁻¹ • z‖^2 := by
    rw [norm_sub_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hb),mul_pow,real_inner_comm x z]
    field_simp
    ring
  unfold canonicalRadialDensity
  calc
    _ = radialNormalizer n * Real.exp (-(b/2)*‖x‖^2 + inner ℝ z x) := by rw [Real.exp_add]; ring
    _ = _ := by rw [he,Real.exp_sub,neg_mul,Real.exp_neg]; ring

lemma canonicalRadial_linear_integral (n : ℕ) {b : ℝ} (hb : 0 < b)
    (z : Spin (n+1)) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ z x)) ∂canonicalRadialMass n b) =
      ENNReal.ofReal (Real.exp (-((n+1:ℕ):ℝ)*Real.log b/2 + ‖z‖^2/(2*b))) := by
  rw [canonicalRadialMass,lintegral_withDensity_eq_lintegral_mul _
    (canonicalRadialDensity_continuous n b).measurable.ennreal_ofReal (by fun_prop)]
  simp only [Pi.mul_apply,← ENNReal.ofReal_mul (canonicalRadialDensity_pos n b _).le,
    canonicalRadialDensity_complete_square n hb]
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (canonicalRadialDensity n b x)) (b⁻¹ • z)]
  rw [← ofReal_integral_eq_lintegral_ofReal (canonicalRadialDensity_integrable n hb)
    (Eventually.of_forall fun x => (canonicalRadialDensity_pos n b x).le),
    canonicalRadialDensity_integral n hb,← ENNReal.ofReal_mul (Real.exp_pos _).le,
    Real.rpow_def_of_pos hb,← Real.exp_add]
  congr 2
  ring

lemma coordinateLeafField_measurable (d : ℕ) : Measurable (coordinateLeafField d) := by
  apply (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply 0).comp (measurable_pi_apply i)

lemma coordinateLeafField_norm_sq (d : ℕ) (x : Fin d → ℕ → ℝ) :
    ‖coordinateLeafField d x‖^2 = ∑ i, (x i 0)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [coordinateLeafField,WithLp.ofLp_toLp,Real.norm_eq_abs,sq_abs]

lemma canonicalCoordinatePotential_eq_norm (d : ℕ) (b : ℝ) (x : Fin d → ℕ → ℝ) :
    canonicalCoordinatePotential d b x = - (d:ℝ)*Real.log b/2 + ‖coordinateLeafField d x‖^2/(2*b) := by
  rw [coordinateLeafField_norm_sq]
  simp only [canonicalCoordinatePotential,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_div]
  ring

theorem canonicalCoordinateTotalE_eq_radial (n k : ℕ) (σ : ℕ → ℝ) {b : ℝ} (hb : 0 < b)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) :
    decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ)
      (canonicalCoordinatePotential (n+1) b) k p =
      ∫⁻ x, decoratedFieldFactor (n+1) (canonicalCoordinateStep (n+1) σ)
        (coordinateLeafField (n+1)) k p x ∂canonicalRadialMass n b := by
  let : SFinite (canonicalRadialMass n b) := by
    unfold canonicalRadialMass
    infer_instance
  have hf : Measurable (fun q : Spin (n+1) × (Fin (n+1) → ℕ → ℝ) =>
      ENNReal.ofReal (Real.exp (inner ℝ (coordinateLeafField (n+1) q.2) q.1))) :=
    (((coordinateLeafField_measurable (n+1)).comp measurable_snd).inner measurable_fst).exp.ennreal_ofReal
  have h := decoratedLeafIntegral_lintegral (canonicalRadialMass n b)
    (canonicalCoordinateStep (n+1) σ) (canonicalCoordinateStep_measurable (n+1) σ) _ hf k p
  change _ = ∫⁻ x, decoratedLeafIntegral (canonicalCoordinateStep (n+1) σ)
    (fun y => ENNReal.ofReal (Real.exp (inner ℝ (coordinateLeafField (n+1) y) x))) k p
      ∂canonicalRadialMass n b
  rw [← h, ← decoratedLeafIntegral_exp]
  congr 1
  funext y
  change _ = ∫⁻ a, ENNReal.ofReal (Real.exp (inner ℝ (coordinateLeafField (n+1) y) a)) ∂canonicalRadialMass n b
  rw [canonicalRadial_linear_integral n hb,canonicalCoordinatePotential_eq_norm]

def sphericalCoordinateLog (n k : ℕ) (σ : ℕ → ℝ) (v : ℝ)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) : ℝ :=
  Real.log ((decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
    (coordinateLeafField (n+1)) k p (Real.sqrt (((n+1:ℕ):ℝ)*v))).toReal /
      decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)

lemma canonicalCoordinateLog_eq_radial (n k : ℕ) (σ : ℕ → ℝ) {b : ℝ} (hb : 0 < b)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) :
    canonicalCoordinateLog (n+1) k σ b p =
      Real.log ((∫⁻ x, decoratedFieldFactor (n+1) (canonicalCoordinateStep (n+1) σ)
        (coordinateLeafField (n+1)) k p x ∂canonicalRadialMass n b).toReal /
          decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p) := by
  unfold canonicalCoordinateLog decoratedTerminalTotal
  rw [canonicalCoordinateTotalE_eq_radial n k σ hb]

lemma decoratedLeafIntegral_holder {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) (hs : Measurable step) {F G : X → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (k : ℕ)
    (p : X × DecoratedCascade S k) :
    decoratedLeafIntegral step (fun x => F x ^ a * G x ^ b) k p ≤
      decoratedLeafIntegral step F k p ^ a * decoratedLeafIntegral step G k p ^ b := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    let H : (ℝ × (S × DecoratedCascade S k)) → X × DecoratedCascade S k :=
      fun q => (step (p.1,q.2.1),q.2.2)
    have hH : Measurable H :=
      (hs.comp (measurable_const.prodMk measurable_snd.fst)).prodMk measurable_snd.snd
    have hFm : Measurable (fun q => ENNReal.ofReal (Real.exp q.1) *
        decoratedLeafIntegral step F k (H q)) :=
      (measurable_fst.exp.ennreal_ofReal).mul
        ((decoratedLeafIntegral_measurable step hs F hF k).comp hH)
    have hGm : Measurable (fun q => ENNReal.ofReal (Real.exp q.1) *
        decoratedLeafIntegral step G k (H q)) :=
      (measurable_fst.exp.ennreal_ofReal).mul
        ((decoratedLeafIntegral_measurable step hs G hG k).comp hH)
    change (∫⁻ q, ENNReal.ofReal (Real.exp q.1) *
      decoratedLeafIntegral step (fun x => F x ^ a * G x ^ b) k (H q)
        ∂markedStableCountKernel p.2) ≤ _
    refine le_trans (lintegral_mono fun q => mul_le_mul_right (ih (H q)) _) ?_
    calc
      _ = ∫⁻ q, (ENNReal.ofReal (Real.exp q.1) * decoratedLeafIntegral step F k (H q)) ^ a *
          (ENNReal.ofReal (Real.exp q.1) * decoratedLeafIntegral step G k (H q)) ^ b
            ∂markedStableCountKernel p.2 := by
        congr 1
        funext q
        rw [ENNReal.mul_rpow_of_nonneg _ _ ha,ENNReal.mul_rpow_of_nonneg _ _ hb]
        have he : ENNReal.ofReal (Real.exp q.1) ^ a * ENNReal.ofReal (Real.exp q.1) ^ b =
            ENNReal.ofReal (Real.exp q.1) := by
          rw [← ENNReal.rpow_add _ _ (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top,hab,ENNReal.rpow_one]
        calc
          _ = (ENNReal.ofReal (Real.exp q.1) ^ a * ENNReal.ofReal (Real.exp q.1) ^ b) *
              (decoratedLeafIntegral step F k (H q) ^ a * decoratedLeafIntegral step G k (H q) ^ b) := by rw [he]
          _ = _ := by ring
      _ ≤ _ := ENNReal.lintegral_mul_norm_pow_le hFm.aemeasurable hGm.aemeasurable ha hb hab

lemma ofReal_exp_affine (x y a b : ℝ) :
    ENNReal.ofReal (Real.exp (a*x+b*y)) =
      ENNReal.ofReal (Real.exp x) ^ a * ENNReal.ofReal (Real.exp y) ^ b := by
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1 <;> rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp] <;> congr 1 <;> ring_nf

lemma sphericalExp_holder (n : ℕ) (z : Spin (n+1)) (r s : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    ENNReal.ofReal (sphericalExp n z (a*r+b*s)) ≤
      ENNReal.ofReal (sphericalExp n z r)^a * ENNReal.ofReal (sphericalExp n z s)^b := by
  have he (t : ℝ) : ENNReal.ofReal (sphericalExp n z t) =
      ∫⁻ x : Metric.sphere (0 : Spin (n+1)) 1,
        ENNReal.ofReal (Real.exp (inner ℝ z (t • x.val))) ∂unitSphereLaw (n+1) := by
    simp only [inner_smul_right]
    exact ofReal_integral_eq_lintegral_ofReal
      (unitSphere_continuous_integrable (by fun_prop))
      (ae_of_all _ fun _ => (Real.exp_pos _).le)
  simp_rw [he]
  have h (x : Metric.sphere (0 : Spin (n+1)) 1) :
      ENNReal.ofReal (Real.exp (inner ℝ z ((a*r+b*s) • x.val))) =
        ENNReal.ofReal (Real.exp (inner ℝ z (r • x.val)))^a *
          ENNReal.ofReal (Real.exp (inner ℝ z (s • x.val)))^b := by
    simp only [inner_smul_right]
    rw [show (a*r+b*s)*inner ℝ z x.val = a*(r*inner ℝ z x.val)+b*(s*inner ℝ z x.val) by ring]
    exact ofReal_exp_affine _ _ _ _
  simp_rw [h]
  exact ENNReal.lintegral_mul_norm_pow_le (by fun_prop) (by fun_prop) ha hb hab

lemma decoratedAngularFactor_holder {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (n : ℕ) (step : X × S → X) (hs : Measurable step)
    (z : X → Spin (n+1)) (hz : Measurable z) (k : ℕ) (p : X × DecoratedCascade S k)
    (r s : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    decoratedAngularFactor n step z k p (a*r+b*s) ≤
      decoratedAngularFactor n step z k p r ^ a * decoratedAngularFactor n step z k p s ^ b := by
  simp_rw [decoratedAngularFactor_eq n step hs z hz]
  refine (decoratedLeafIntegral_mono step (fun x => sphericalExp_holder n (z x) r s ha hb hab) k p).trans ?_
  apply decoratedLeafIntegral_holder step hs _ _ ha hb hab
  all_goals
    unfold sphericalExp
    apply ENNReal.measurable_ofReal.comp
    exact (show StronglyMeasurable (fun p : X × Metric.sphere (0:Spin (n+1)) 1 =>
      Real.exp (_ * inner ℝ (z p.1) (p.2:Spin (n+1)))) from (by fun_prop)).integral_prod_right'.measurable

lemma decoratedTerminalTotal_pos_of_fractional {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X × S → X) (hs : Measurable step)
    (H : X → ℝ) (hH : Measurable H) (k : ℕ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hI : finiteCascadeFractionalIntegrable ν step H k z) (x : X) :
    ∀ᵐ η ∂(decoratedCascadeLaw ν k z : Measure (DecoratedCascade S k)),
      0 < decoratedTerminalTotal step H k (x,η) := by
  have hid := decoratedWeightedTotal_identDistrib ν step hs k z hz0 hz1
    (finiteCascadeShifts ν step k z H) (finiteCascadeShifts_measurable ν step hs k z hH)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step k z
      (fun j => (hz0 j).ne') H hI i y).1)
    (fun i y => (finiteCascadeShifts_normalized_of_fractional ν step k z
      (fun j => (hz0 j).ne') H hI i y).2) x
  have hp := hid.symm.ae_snd measurableSet_Ioi (cascadeTotal_regular k z hz hz0 hz1).1
  filter_upwards [hp] with η hη
  rw [decoratedTerminalTotal_telescoping ν step H k z]
  exact mul_pos (Real.exp_pos _) hη

lemma decoratedTerminalTotal_zero_pos {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X × S → X) (hs : Measurable step)
    (k : ℕ) (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (x : X) :
    ∀ᵐ η ∂(decoratedCascadeLaw ν k z : Measure (DecoratedCascade S k)),
      0 < decoratedTerminalTotal step (fun _ => 0) k (x,η) := by
  have hid := decoratedWeightedTotal_identDistrib ν step hs k z hz0 hz1 (fun _ _ => 0)
    (fun _ => measurable_const) (by intro i y; simp only [mul_zero,Real.exp_zero]; exact integrable_const 1)
    (by intro i y; simp) x
  simpa only [decoratedTerminalTotal_zero] using
    hid.symm.ae_snd measurableSet_Ioi (cascadeTotal_regular k z hz hz0 hz1).1

instance coordinateCascadeLaw_probability (d k : ℕ) (z : Fin k → ℝ) (r : ℝ≥0) :
    IsProbabilityMeasure (coordinateCascadeLaw d k z r) := by
  unfold coordinateCascadeLaw
  infer_instance

lemma canonicalCoordinateTotal_pos (d k : ℕ) (σ : ℕ → ℝ) (b : ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b k z) (r : ℝ≥0) :
    ∀ᵐ p ∂coordinateCascadeLaw d k z r,
      0 < decoratedTerminalTotal (canonicalCoordinateStep d σ)
        (canonicalCoordinatePotential d b) k ((fun i _ => p.1 i),p.2) := by
  have hm : Measurable (fun p : (Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k =>
      decoratedTerminalTotal (canonicalCoordinateStep d σ) (canonicalCoordinatePotential d b) k
        ((fun i _ => p.1 i),p.2)) :=
    (decoratedTerminalTotal_measurable (piMarkLaw (fun _ : Fin d => standardGaussianMark)) _ (canonicalCoordinateStep_measurable d σ)
      (canonicalCoordinatePotential_measurable d b) k z).comp
        (show Measurable (fun p : (Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k =>
          ((fun (i : Fin d) (_ : ℕ) => p.1 i),p.2)) from by fun_prop)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hm)).mpr
  exact ae_of_all _ fun x => decoratedTerminalTotal_pos_of_fractional
    (piMarkLaw (fun _ : Fin d => standardGaussianMark)) (canonicalCoordinateStep d σ)
    (canonicalCoordinateStep_measurable d σ) _ (canonicalCoordinatePotential_measurable d b)
    k z hz hz0 hz1 (canonical_coordinate_recursion d σ b k z hz0 hp).2 (fun i _ => x i)

lemma canonicalCoordinateBase_pos (d k : ℕ) (σ : ℕ → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (r : ℝ≥0) :
    ∀ᵐ p ∂coordinateCascadeLaw d k z r,
      0 < decoratedTerminalTotal (canonicalCoordinateStep d σ)
        (fun _ => 0) k ((fun i _ => p.1 i),p.2) := by
  have hm : Measurable (fun p : (Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k =>
      decoratedTerminalTotal (canonicalCoordinateStep d σ) (fun _ => 0) k
        ((fun i _ => p.1 i),p.2)) :=
    (decoratedTerminalTotal_measurable (piMarkLaw (fun _ : Fin d => standardGaussianMark)) _ (canonicalCoordinateStep_measurable d σ)
      measurable_const k z).comp
        (show Measurable (fun p : (Fin d → ℝ) × DecoratedCascade (Fin d → ℝ) k =>
          ((fun (i : Fin d) (_ : ℕ) => p.1 i),p.2)) from by fun_prop)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hm)).mpr
  exact ae_of_all _ fun x => decoratedTerminalTotal_zero_pos
    (piMarkLaw (fun _ : Fin d => standardGaussianMark)) (canonicalCoordinateStep d σ)
    (canonicalCoordinateStep_measurable d σ) k z hz hz0 hz1 (fun i _ => x i)

lemma sphericalExp_le_gaussian (n : ℕ) (z : Spin (n+1)) (R : ℝ) {b : ℝ} (hb : 0 < b) :
    sphericalExp n z R ≤ Real.exp (‖z‖^2/(2*b)+b*R^2/2) := by
  have h (u : Metric.sphere (0 : Spin (n+1)) 1) :
      R * inner ℝ z (u : Spin (n+1)) ≤ ‖z‖^2/(2*b)+b*R^2/2 := by
    have hn : ‖(u : Spin (n+1))‖ = 1 := by simp
    have hh := sq_nonneg ‖z - (b*R) • (u : Spin (n+1))‖
    rw [norm_sub_sq_real,inner_smul_right,norm_smul,hn,Real.norm_eq_abs,mul_one,sq_abs] at hh
    calc
      _ ≤ (‖z‖^2+(b*R)^2)/(2*b) :=
        (le_div_iff₀ (by positivity : 0 < 2*b)).mpr (by nlinarith [hh])
      _ = _ := by field_simp
  unfold sphericalExp
  calc
    _ ≤ ∫ _ : Metric.sphere (0 : Spin (n+1)) 1,
        Real.exp (‖z‖^2/(2*b)+b*R^2/2) ∂unitSphereLaw (n+1) :=
      integral_mono (unitSphere_continuous_integrable (by fun_prop)) (integrable_const _)
        (fun u => Real.exp_le_exp.mpr (h u))
    _ = _ := by simp

lemma decoratedAngularFactor_le_canonical (n k : ℕ) (σ : ℕ → ℝ) (R : ℝ) {b : ℝ} (hb : 0 < b)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k) :
    decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ) (coordinateLeafField (n+1)) k p R ≤
      ENNReal.ofReal (Real.exp (((n+1:ℕ):ℝ)*Real.log b/2+b*R^2/2)) *
        decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p := by
  rw [decoratedAngularFactor_eq n _ (canonicalCoordinateStep_measurable (n+1) σ) _
    (coordinateLeafField_measurable (n+1)), ← decoratedLeafIntegral_exp,
    ← decoratedLeafIntegral_const_mul _ _ _ ENNReal.ofReal_ne_top]
  apply decoratedLeafIntegral_mono
  intro x
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,canonicalCoordinatePotential_eq_norm]
  apply ENNReal.ofReal_le_ofReal
  convert sphericalExp_le_gaussian n (coordinateLeafField (n+1) x) R hb using 1
  congr 1
  ring

lemma coordinateAngularLog_regular (n k : ℕ) (σ : ℕ → ℝ) (R : ℝ) {b : ℝ} (hb : 0 < b)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p) :
    0 < (decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
      (coordinateLeafField (n+1)) k p R).toReal ∧
      0 ≤ coordinateAngularLog n k σ R p ∧
      coordinateAngularLog n k σ R p ≤ canonicalCoordinateLog (n+1) k σ b p +
        ((n+1:ℕ):ℝ)*Real.log b/2+b*R^2/2 := by
  let A := decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
    (coordinateLeafField (n+1)) k p R
  let B := decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p
  let C := decoratedTerminalTotalE (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p
  let c := ((n+1:ℕ):ℝ)*Real.log b/2+b*R^2/2
  have hB : 0 < B.toReal := h0
  have hC : 0 < C.toReal := hc
  obtain ⟨hB₀,hBtop⟩ := ENNReal.toReal_pos_iff.mp hB
  obtain ⟨hC₀,hCtop⟩ := ENNReal.toReal_pos_iff.mp hC
  have hba : B ≤ A := decoratedAngularFactor_mass_le n _ (canonicalCoordinateStep_measurable (n+1) σ)
    _ (coordinateLeafField_measurable (n+1)) k p R
  have hac : A ≤ ENNReal.ofReal (Real.exp c)*C := decoratedAngularFactor_le_canonical n k σ R hb p
  have hAtop : A ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCtop.ne) hac
  have hA := ENNReal.toReal_pos (ne_of_gt (hB₀.trans_le hba)) hAtop
  have hba' := ENNReal.toReal_mono hAtop hba
  have hac' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCtop.ne) hac
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le] at hac'
  refine ⟨hA,?_,?_⟩
  · exact Real.log_nonneg ((le_div_iff₀ hB).mpr (by simpa using hba'))
  · have hh := Real.log_le_log (div_pos hA hB) (div_le_div_of_nonneg_right hac' hB.le)
    rw [Real.log_div (mul_pos (Real.exp_pos c) hC).ne' hB.ne',
      Real.log_mul (Real.exp_pos c).ne' hC.ne',Real.log_exp] at hh
    change Real.log (A.toReal/B.toReal) ≤ Real.log (C.toReal/B.toReal)+
      ((n+1:ℕ):ℝ)*Real.log b/2+b*R^2/2
    rw [Real.log_div hC.ne' hB.ne']
    dsimp only [c] at hh
    linarith

lemma coordinateAngularLog_convex (n k : ℕ) (σ : ℕ → ℝ) {b : ℝ} (hb : 0 < b)
    (p : (Fin (n+1) → ℕ → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k)
    (h0 : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p)
    (hc : 0 < decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (canonicalCoordinatePotential (n+1) b) k p) :
    ConvexOn ℝ Set.univ (fun R => coordinateAngularLog n k σ R p) := by
  let A := fun R => decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ)
    (coordinateLeafField (n+1)) k p R
  let B := decoratedTerminalTotal (canonicalCoordinateStep (n+1) σ) (fun _ => 0) k p
  have hA (R : ℝ) : 0 < (A R).toReal := (coordinateAngularLog_regular n k σ R hb p h0 hc).1
  have ht (R : ℝ) : A R ≠ ∞ := (ENNReal.toReal_pos_iff.mp (hA R)).2.ne
  refine ⟨convex_univ,?_⟩
  intro R _ S _ a c ha hc' hac
  have H := decoratedAngularFactor_holder n (canonicalCoordinateStep (n+1) σ)
    (canonicalCoordinateStep_measurable (n+1) σ) (coordinateLeafField (n+1))
    (coordinateLeafField_measurable (n+1)) k p R S ha hc' hac
  have Hr := ENNReal.toReal_mono (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg ha (ht R)) (ENNReal.rpow_ne_top_of_nonneg hc' (ht S))) H
  change (A (a*R+c*S)).toReal ≤ (A R ^ a * A S ^ c).toReal at Hr
  rw [ENNReal.toReal_mul,← ENNReal.toReal_rpow,← ENNReal.toReal_rpow] at Hr
  have Hlog := Real.log_le_log (hA (a*R+c*S)) Hr
  rw [Real.log_mul (Real.rpow_pos_of_pos (hA R) a).ne' (Real.rpow_pos_of_pos (hA S) c).ne',
    Real.log_rpow (hA R),Real.log_rpow (hA S)] at Hlog
  simp only [smul_eq_mul]
  change Real.log ((A (a*R+c*S)).toReal/B) ≤ a*Real.log ((A R).toReal/B)+c*Real.log ((A S).toReal/B)
  rw [Real.log_div (hA _).ne' h0.ne',Real.log_div (hA R).ne' h0.ne',Real.log_div (hA S).ne' h0.ne']
  have hh := congrArg (fun t : ℝ => t * Real.log B) hac
  nlinarith [Hlog, hh]

lemma coordinateAngularLog_measurable (n k : ℕ) (σ : ℕ → ℝ) (R : ℝ) :
    Measurable (coordinateAngularLog n k σ R) := by
  let X := Fin (n+1) → ℕ → ℝ
  let S := Fin (n+1) → ℝ
  let F : Spin (n+1) × X → ℝ≥0∞ := fun q => ENNReal.ofReal (Real.exp (inner ℝ (coordinateLeafField (n+1) q.2) q.1))
  have hm := decoratedLeafIntegral_param_measurable (canonicalCoordinateStep (n+1) σ)
    (canonicalCoordinateStep_measurable (n+1) σ) F
    ((((coordinateLeafField_measurable (n+1)).comp measurable_snd).inner measurable_fst).exp.ennreal_ofReal) k
  have hmap : Measurable (fun q : (X × DecoratedCascade S k) × Metric.sphere (0:Spin (n+1)) 1 =>
      (R • (q.2:Spin (n+1)),q.1)) :=
    (measurable_snd.subtype_coe.const_smul R).prodMk measurable_fst
  have hh := hm.comp hmap
  have ha : Measurable (fun p : X × DecoratedCascade S k =>
      decoratedAngularFactor n (canonicalCoordinateStep (n+1) σ) (coordinateLeafField (n+1)) k p R) :=
    hh.lintegral_prod_right'
  exact (ha.ennreal_toReal.div (decoratedTerminalTotal_measurable
    (piMarkLaw (fun _ : Fin (n+1) => standardGaussianMark)) _
    (canonicalCoordinateStep_measurable (n+1) σ) measurable_const k (fun _ => 0))).log

lemma coordinateAngularLog_integrable (n k : ℕ) (σ : ℕ → ℝ) {b : ℝ} (R : ℝ)
    (z : Fin k → ℝ) (hz : StrictMono z) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (hp : 0 < quadraticCascadePrecision σ b k z) (r : ℝ≥0) :
    Integrable (fun p => coordinateAngularLog n k σ R ((fun i _ => p.1 i),p.2))
      (coordinateCascadeLaw (n+1) k z r) := by
  have hb : 0 < b := hp.trans_le (quadraticCascadePrecision_le σ b k z (fun i => (hz0 i).le))
  have hm := (coordinateAngularLog_measurable n k σ R).comp
    (show Measurable (fun p : (Fin (n+1) → ℝ) × DecoratedCascade (Fin (n+1) → ℝ) k =>
      ((fun (i : Fin (n+1)) (_ : ℕ) => p.1 i),p.2)) from by fun_prop)
  have hi := (canonical_coordinate_joint_mean (n+1) σ b k z hz hz0 hz1 hp r).1
  apply (hi.add (integrable_const (((n+1:ℕ):ℝ)*Real.log b/2+b*R^2/2))).mono' hm.aestronglyMeasurable
  filter_upwards [canonicalCoordinateBase_pos (n+1) k σ z hz hz0 hz1 r,
    canonicalCoordinateTotal_pos (n+1) k σ b z hz hz0 hz1 hp r] with p h0 hc
  have h := coordinateAngularLog_regular n k σ R hb _ h0 hc
  simp only [Function.comp_apply, Pi.add_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg h.2.1]
  linarith [h.2.2]

end SphericalPerceptron
end
end

end OAI
