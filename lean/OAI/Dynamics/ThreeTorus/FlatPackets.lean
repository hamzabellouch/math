import OAI.Dynamics.ThreeTorus.PacketAlgebra
import OAI.Dynamics.ThreeTorus.SymmetricPackets
import OAI.Dynamics.ThreeTorus.Whitening

namespace OAI

/-! Flat support, finite packet L2 estimates, neutral selection, density invariance, and finite spectral whitening. -/

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped Topology ENNReal NNReal
namespace ThreeTorus

/-- Packets of arbitrary L² coefficients have the same norm as their coefficients. -/
lemma memLp_packet {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) (m : ℤ) : MemLp (packet m A) 2 tripleVolume := by
  have hbase : MemLp (fun x : TripleTorus => A x.2) 2 tripleVolume :=
    hA.comp_measurePreserving measurePreserving_snd
  apply hbase.congr_norm
  · exact hbase.aestronglyMeasurable.mul
      (((fourier m).continuous.comp continuous_fst).aestronglyMeasurable)
  · filter_upwards [] with x
    simp only [packet, norm_mul, fourier_apply, Circle.norm_coe, mul_one]

lemma integral_packet_pair_L2 {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) (hB : MemLp B 2 slowVolume) (m k : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*packet k B x ∂tripleVolume) =
      if m = k then ∫ ua, starRingEnd ℂ (A ua)*B ua ∂slowVolume else 0 := by
  have hi : Integrable (fun x : TripleTorus =>
      starRingEnd ℂ (packet m A x)*packet k B x) tripleVolume :=
    (memLp_packet hA m).star.integrable_mul (memLp_packet hB k)
  rw [MeasureTheory.integral_prod_symm _ hi]
  have he (ua : UnitAddCircle × UnitAddCircle) :
      (∫ θ : UnitAddCircle, starRingEnd ℂ (packet m A (θ,ua))*packet k B (θ,ua)
        ∂AddCircle.haarAddCircle) =
      (starRingEnd ℂ (A ua)*B ua)*(if m = k then 1 else 0) := by
    simp only [packet,map_mul]
    have hr (θ : UnitAddCircle) :
        starRingEnd ℂ (A ua)*starRingEnd ℂ (fourier m θ)*(B ua*fourier k θ) =
        (starRingEnd ℂ (A ua)*B ua)*(starRingEnd ℂ (fourier m θ)*fourier k θ) := by ring
    simp_rw [hr]
    rw [integral_const_mul,integral_fourier_pair]
  simp_rw [he]
  split_ifs <;> simp

lemma memLp_frequency_mul {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {A : X → ℂ} (hA : MemLp A 2 ν) {ζ : X → UnitAddCircle}
    (hζ : Measurable ζ) (n : ℤ) :
    MemLp (fun x => fourier n (ζ x)*A x) 2 ν := by
  apply hA.congr_norm
  · exact (((fourier n).continuous.measurable.comp hζ).aestronglyMeasurable).mul
      hA.aestronglyMeasurable
  · filter_upwards [] with x
    simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul]

/-- Exact correlation formula, requiring no smoothness of the coefficients. -/
lemma packet_correlation_L2 {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m n : ℤ) :
    (∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*
      packet m A (twistIter φ n x) ∂tripleVolume) =
    ∫ ua : UnitAddCircle × UnitAddCircle,
      fourier n (m • φ ua.1)*(‖A ua‖^2 : ℝ) ∂slowVolume := by
  let B : UnitAddCircle × UnitAddCircle → ℂ :=
    fun ua => fourier n (m • φ ua.1)*A ua
  have hB : MemLp B 2 slowVolume := memLp_frequency_mul hA
    ((hφ.comp measurable_fst).const_smul m) n
  have he : ∀ x, packet m A (twistIter φ n x) = packet m B x := by
    intro x
    rw [packet_twistIter]
    dsimp [packet,B]
    ring
  simp_rw [he]
  rw [integral_packet_pair_L2 hA hB,ite_eq_left rfl]
  apply integral_congr_ae
  filter_upwards [] with ua
  dsimp only [B]
  rw [show starRingEnd ℂ (A ua)*(fourier n (m • φ ua.1)*A ua) =
    fourier n (m • φ ua.1)*(starRingEnd ℂ (A ua)*A ua) by ring,normSq_complex]

/-- Exact pushforward measure even for the endpoint-discontinuous flat vector. -/
lemma packet_spectral_moment_L2 {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hAm : Measurable A)
    (hA : MemLp A 2 slowVolume) (m n : ℤ) :
    (∫ z, fourier n z ∂packetSpectralMeasure φ m A) =
      ∫ x : TripleTorus, starRingEnd ℂ (packet m A x)*
        packet m A (twistIter φ n x) ∂tripleVolume := by
  rw [packet_correlation_L2 hA hφ]
  unfold packetSpectralMeasure
  erw [integral_map ((hφ.comp measurable_fst).const_smul m).aemeasurable
    (fourier n).continuous.aestronglyMeasurable]
  erw [integral_withDensity_eq_integral_toReal_smul
    (hAm.norm.pow_const 2).ennreal_ofReal (by filter_upwards [] with ua; finiteness)]
  apply integral_congr_ae
  filter_upwards [] with ua
  simp only [Function.comp_apply,Pi.smul_apply]
  rw [ENNReal.toReal_ofReal (sq_nonneg _),Complex.real_smul,mul_comm]

lemma packet_integral_zero {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) {m : ℤ} (hm : m ≠ 0) :
    (∫ x, packet m A x ∂tripleVolume) = 0 := by
  rw [integral_prod_symm _ ((memLp_packet hA m).integrable (by norm_num))]
  have he (ua : UnitAddCircle × UnitAddCircle) :
      (∫ θ : UnitAddCircle, packet m A (θ,ua) ∂AddCircle.haarAddCircle) = 0 := by
    simp only [packet,integral_const_mul]
    have hp := integral_fourier_pair 0 m
    simp only [fourier_zero, map_one, one_mul,
      ite_eq_right (Ne.symm hm)] at hp
    rw [hp, mul_zero]
  simp_rw [he]
  simp

lemma map_jacobian_real {s : Set ℝ} {f D : ℝ → ℝ}
    (hs : MeasurableSet s) (hD : ∀ x ∈ s, HasDerivWithinAt f (D x) s x)
    (hinj : InjOn f s) :
    Measure.map f ((volume.restrict s).withDensity (fun x => ENNReal.ofReal |D x|)) =
      volume.restrict (f '' s) := by
  simpa only [ContinuousLinearMap.det_toSpanSingleton] using
    map_withDensity_abs_det_fderiv_eq_addHaar volume hs.nullMeasurableSet
      (fun x hx => (hD x hx).hasFDerivWithinAt) hinj

lemma flat_branch_mod_one {f D : ℝ → ℝ} {l u : ℝ}
    (hlu : l ≤ u) (hfm : Measurable f)
    (hD : ∀ x ∈ Icc l u, HasDerivWithinAt f (D x) (Icc l u) x)
    (hmono : StrictMonoOn f (Icc l u)) (hperiod : f u = f l+1) :
    Measure.map (fun x : ℝ => (f x : UnitAddCircle))
      ((volume.restrict (Icc l u)).withDensity (fun x => ENNReal.ofReal |D x|)) =
      AddCircle.haarAddCircle := by
  have hc : ContinuousOn f (Icc l u) := fun x hx => (hD x hx).continuousWithinAt
  change Measure.map ((fun y : ℝ => (y : UnitAddCircle)) ∘ f) _ = _
  rw [← Measure.map_map (show Measurable (fun y : ℝ => (y : UnitAddCircle)) from
      AddCircle.measurable_mk') hfm,
    map_jacobian_real measurableSet_Icc hD hmono.injOn,
    hc.image_Icc_of_monotoneOn hlu hmono.monotoneOn, hperiod,
    ← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)))]
  simpa [AddCircle.volume_eq_smul_haarAddCircle] using
    (AddCircle.measurePreserving_mk 1 (f l)).map_eq

/-- The representative in the old good-arc coordinate chart. -/
def circleRep (o : ℝ) (z : UnitAddCircle) : ℝ :=
  ((AddCircle.measurableEquivIoc 1 o) z).1

lemma measurable_circleRep (o : ℝ) : Measurable (circleRep o) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 o).measurable

lemma circleRep_coe {o x : ℝ} (hx : x ∈ Ioc o (o+1)) :
    circleRep o (x : UnitAddCircle) = x := by
  exact congrArg Subtype.val (AddCircle.equivIoc_coe_eq hx)

lemma coe_circleRep (o : ℝ) (z : UnitAddCircle) :
    (circleRep o z : UnitAddCircle) = z := by
  exact AddCircle.coe_equivIoc (p := 1) (a := o) (y := z)

lemma circle_weight_lift {o : ℝ} {q : ℝ → ℝ≥0∞} (hq : Measurable q)
    (hs : Function.support q ⊆ Ioc o (o+1)) :
    (volume.withDensity q).map (fun x : ℝ => (x : UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensity (q ∘ circleRep o) := by
  have he : (volume : Measure ℝ).withDensity q =
      (volume.restrict (Ioc o (o+1))).withDensity
        ((q ∘ circleRep o) ∘ (fun x : ℝ => (x : UnitAddCircle))) := by
    rw [← withDensity_indicator measurableSet_Ioc]
    congr 1
    funext x
    by_cases hx : x ∈ Ioc o (o+1)
    · simp [hx, circleRep_coe hx]
    · have hz : q x = 0 := by by_contra hn; exact hx (hs hn)
      simp [hx, hz]
  rw [he, map_withDensity_comp _ AddCircle.measurable_mk'
    (hq.comp (measurable_circleRep o))]
  congr 1
  simpa [AddCircle.volume_eq_smul_haarAddCircle] using
    (AddCircle.measurePreserving_mk 1 o).map_eq

/-- The branch Jacobian realizes Haar measure for any circle map agreeing with
that lifted frequency on the chosen interval. -/
lemma flat_circle_branch {f D : ℝ → ℝ} {l u o : ℝ}
    {ζ : UnitAddCircle → UnitAddCircle}
    (hlu : l ≤ u) (hfm : Measurable f) (hDm : Measurable D)
    (hD : ∀ x ∈ Icc l u, HasDerivWithinAt f (D x) (Icc l u) x)
    (hmono : StrictMonoOn f (Icc l u)) (hperiod : f u = f l+1)
    (hi : Icc l u ⊆ Ioc o (o+1)) (hζ : Measurable ζ)
    (hζf : ∀ x ∈ Icc l u, ζ (x : UnitAddCircle) = (f x : UnitAddCircle)) :
    (AddCircle.haarAddCircle.withDensity
      (((Icc l u).indicator (fun x => ENNReal.ofReal |D x|)) ∘ circleRep o)).map ζ =
      AddCircle.haarAddCircle := by
  let q : ℝ → ℝ≥0∞ := (Icc l u).indicator (fun x => ENNReal.ofReal |D x|)
  have hq : Measurable q := hDm.abs.ennreal_ofReal.indicator measurableSet_Icc
  have hqs : Function.support q ⊆ Ioc o (o+1) := by
    intro x hx
    apply hi
    by_contra hn
    exact hx (indicator_of_notMem hn _)
  change (AddCircle.haarAddCircle.withDensity (q ∘ circleRep o)).map ζ = _
  rw [← circle_weight_lift hq hqs,
    Measure.map_map hζ AddCircle.measurable_mk']
  calc
    _ = (volume.withDensity q).map (fun x : ℝ => (f x : UnitAddCircle)) := by
      apply Measure.map_congr
      change ∀ᵐ (x : ℝ) ∂volume.withDensity q, ζ (x : UnitAddCircle) = (f x : UnitAddCircle)
      rw [ae_withDensity_iff hq]
      filter_upwards [] with x hx
      exact hζf x (by
        by_contra hn
        exact hx (indicator_of_notMem hn _))
    _ = _ := by
      rw [show volume.withDensity q =
        (volume.restrict (Icc l u)).withDensity (fun x => ENNReal.ofReal |D x|) from
          withDensity_indicator measurableSet_Icc _]
      exact flat_branch_mod_one hlu hfm hD hmono hperiod

/-- The manuscript's endpoint-discontinuous coefficient. -/
def flatAmplitude (o l u : ℝ) (D : ℝ → ℝ) (z : UnitAddCircle) : ℂ :=
  ((Icc l u).indicator (fun x => Real.sqrt (|D x|/2)) (circleRep o z) : ℝ)

lemma measurable_flatAmplitude {D : ℝ → ℝ} (hD : Measurable D) (o l u : ℝ) :
    Measurable (flatAmplitude o l u D) :=
  Complex.measurable_ofReal.comp
    (((hD.abs.div_const 2).sqrt.indicator measurableSet_Icc).comp
      (measurable_circleRep o))

lemma flatAmplitude_energy (o l u : ℝ) (D : ℝ → ℝ) :
    (fun z => ENNReal.ofReal (‖flatAmplitude o l u D z‖^2)) =
      (ENNReal.ofReal (1/2 : ℝ)) •
        (((Icc l u).indicator (fun x => ENNReal.ofReal |D x|)) ∘ circleRep o) := by
  funext z
  by_cases hz : circleRep o z ∈ Icc l u
  · simp only [flatAmplitude, indicator_of_mem hz, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (div_nonneg (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)),
      Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    congr 1
    ring
  · simp [flatAmplitude, hz]

lemma flatAmplitude_pushforward {f D : ℝ → ℝ} {l u o : ℝ}
    {ζ : UnitAddCircle → UnitAddCircle}
    (hlu : l ≤ u) (hfm : Measurable f) (hDm : Measurable D)
    (hD : ∀ x ∈ Icc l u, HasDerivWithinAt f (D x) (Icc l u) x)
    (hmono : StrictMonoOn f (Icc l u)) (hperiod : f u = f l+1)
    (hi : Icc l u ⊆ Ioc o (o+1)) (hζ : Measurable ζ)
    (hζf : ∀ x ∈ Icc l u, ζ (x : UnitAddCircle) = (f x : UnitAddCircle)) :
    (AddCircle.haarAddCircle.withDensity
      (fun z => ENNReal.ofReal (‖flatAmplitude o l u D z‖^2))).map ζ =
      ENNReal.ofReal (1/2 : ℝ) • AddCircle.haarAddCircle := by
  rw [flatAmplitude_energy, withDensity_smul _
    ((hDm.abs.ennreal_ofReal.indicator measurableSet_Icc).comp (measurable_circleRep o)),
    Measure.map_smul _ hζ.aemeasurable,
    flat_circle_branch hlu hfm hDm hD hmono hperiod hi hζ hζf]

/-- Finite total pushed energy implies L² membership, even without boundedness. -/
lemma memLp_of_energy_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure ν]
    {F : X → ℂ} {ζ : X → Y} (hF : Measurable F) (hζ : Measurable ζ)
    (he : (μ.withDensity (fun x => ENNReal.ofReal (‖F x‖^2))).map ζ = ν) :
    MemLp F 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).2
  refine ⟨(hF.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, abs_pow, abs_norm]
  have ht := congrArg (fun η : Measure Y => η univ) he
  simp only [Measure.map_apply hζ MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at ht
  rw [ht]
  exact measure_lt_top ν univ

/-- Haar is invariant under reversing the additive spectral variable. -/
lemma frequency_energy_neg {A : UnitAddCircle → ℂ} {ζ : UnitAddCircle → UnitAddCircle}
    (hζ : Measurable ζ) {c : ℝ≥0∞}
    (hpush : (AddCircle.haarAddCircle.withDensity
      (fun z => ENNReal.ofReal (‖A z‖^2))).map ζ = c • AddCircle.haarAddCircle) :
    (AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (‖A z‖^2))).map
      (fun z => -(ζ z)) = c • AddCircle.haarAddCircle := by
  change Measure.map ((fun z : UnitAddCircle => -z) ∘ ζ) _ = _
  rw [← Measure.map_map measurable_neg hζ, hpush,
    Measure.map_smul _ measurable_neg.aemeasurable,
    Measure.map_neg_eq_self]

lemma packetSpectrum_first_coeff {A : UnitAddCircle → ℂ} (hA : Measurable A)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) (m : ℤ) :
    packetSpectralMeasure φ m (fun ua => A ua.1) =
      (AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (‖A z‖^2))).map
        (fun z => m • φ z) := by
  unfold packetSpectralMeasure
  change Measure.map ((fun z => m • φ z) ∘ Prod.fst)
    (slowVolume.withDensity ((fun z => ENNReal.ofReal (‖A z‖^2)) ∘ Prod.fst)) = _
  rw [← Measure.map_map (show Measurable (fun z => m • φ z) from hφ.const_smul m)
    (show Measurable (Prod.fst : UnitAddCircle × UnitAddCircle → UnitAddCircle) from measurable_fst),
    map_withDensity_comp _ measurable_fst (hA.norm.pow_const 2).ennreal_ofReal,
    measurePreserving_fst.map_eq]

/-- A pair of opposite angular modes with real coefficient. -/
def realPacketPair (m : ℤ) (A : UnitAddCircle × UnitAddCircle → ℂ) (x : TripleTorus) : ℂ :=
  packet m A x + packet (-m) A x

lemma realPacketPair_real {m : ℤ} {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ ua, starRingEnd ℂ (A ua) = A ua) (x : TripleTorus) :
    starRingEnd ℂ (realPacketPair m A x) = realPacketPair m A x := by
  simp only [realPacketPair, packet, map_add, map_mul, hA]
  have he (j : ℤ) : starRingEnd ℂ (fourier j x.1) = fourier (-j) x.1 := by
    rw [← fourier_neg]
  rw [he m,he (-m),neg_neg,add_comm]

lemma memLp_realPacketPair {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) (m : ℤ) : MemLp (realPacketPair m A) 2 tripleVolume :=
  (memLp_packet hA m).add (memLp_packet hA (-m))

lemma realPacketPair_integral_zero {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) {m : ℤ} (hm : m ≠ 0) :
    (∫ x, realPacketPair m A x ∂tripleVolume) = 0 := by
  simp only [realPacketPair]
  rw [integral_add ((memLp_packet hA m).integrable (by norm_num))
    ((memLp_packet hA (-m)).integrable (by norm_num)),
    packet_integral_zero hA hm, packet_integral_zero hA (neg_ne_zero.mpr hm), add_zero]

lemma packet_twist_memLp {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) {φ : UnitAddCircle → UnitAddCircle}
    (hφ : Measurable φ) (m n : ℤ) :
    MemLp (fun x => packet m A (twistIter φ n x)) 2 tripleVolume := by
  have hB := memLp_frequency_mul hA ((hφ.comp measurable_fst).const_smul m) n
  convert memLp_packet hB m using 1
  funext x
  rw [packet_twistIter]
  simp only [packet, Function.comp_apply, Pi.smul_apply]
  ring

lemma packet_cross_correlation {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) (hB : MemLp B 2 slowVolume)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m k : ℤ} (hmk : m ≠ k) (n : ℤ) :
    (∫ x, starRingEnd ℂ (packet m A x)*packet k B (twistIter φ n x) ∂tripleVolume) = 0 := by
  let C : UnitAddCircle × UnitAddCircle → ℂ := fun ua => fourier n (k • φ ua.1)*B ua
  have hC : MemLp C 2 slowVolume := memLp_frequency_mul hB
    ((hφ.comp measurable_fst).const_smul k) n
  have he (x : TripleTorus) : packet k B (twistIter φ n x) = packet k C x := by
    rw [packet_twistIter]
    dsimp only [packet,C]
    ring
  simp_rw [he]
  rw [integral_packet_pair_L2 hA hC, ite_eq_right hmk]

lemma realPacketPair_correlation {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : Measurable A) (hA : MemLp A 2 slowVolume)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ℤ} (hm : m ≠ 0) (n : ℤ) :
    (∫ x, starRingEnd ℂ (realPacketPair m A x)*
      realPacketPair m A (twistIter φ n x) ∂tripleVolume) =
    (∫ z, fourier n z ∂packetSpectralMeasure φ m A) +
    (∫ z, fourier n z ∂packetSpectralMeasure φ (-m) A) := by
  have hi (j k : ℤ) : Integrable (fun x => starRingEnd ℂ (packet j A x)*
      packet k A (twistIter φ n x)) tripleVolume :=
    (memLp_packet hA j).star.integrable_mul (packet_twist_memLp hA hφ k n)
  have hpm : m ≠ -m := by omega
  simp only [realPacketPair, map_add, add_mul, mul_add]
  erw [integral_add ((hi m m).add (hi (-m) m)) ((hi m (-m)).add (hi (-m) (-m))),
    integral_add (hi m m) (hi (-m) m), integral_add (hi m (-m)) (hi (-m) (-m)),
    packet_cross_correlation hA hA hφ hpm n,
    packet_cross_correlation hA hA hφ hpm.symm n, add_zero, zero_add,
    ← packet_spectral_moment_L2 hφ hAm hA m n,
    ← packet_spectral_moment_L2 hφ hAm hA (-m) n]

lemma integral_fourier_haar (n : ℤ) :
    (∫ z : UnitAddCircle, fourier n z ∂AddCircle.haarAddCircle) =
      if n = 0 then 1 else 0 := by
  have hh := integral_fourier_pair 0 n
  simpa only [fourier_zero, map_one, one_mul, eq_comm] using hh

lemma realPacketPair_flat {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : Measurable A) (hA : MemLp A 2 slowVolume)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ℤ} (hm : m ≠ 0)
    (hp : packetSpectralMeasure φ m A =
      ENNReal.ofReal (1/2:ℝ) • AddCircle.haarAddCircle)
    (hn : packetSpectralMeasure φ (-m) A =
      ENNReal.ofReal (1/2:ℝ) • AddCircle.haarAddCircle) (n : ℤ) :
    (∫ x, starRingEnd ℂ (realPacketPair m A x)*
      realPacketPair m A (twistIter φ n x) ∂tripleVolume) =
      if n = 0 then 1 else 0 := by
  rw [realPacketPair_correlation hAm hA hφ hm n, hp, hn,
    integral_smul_measure, integral_fourier_haar]
  split_ifs <;> norm_num

lemma flatAmplitude_support (o l u : ℝ) (D : ℝ → ℝ) :
    Function.support (flatAmplitude o l u D) ⊆
      (fun x : ℝ => (x : UnitAddCircle)) '' Icc l u := by
  intro z hz
  have hi : circleRep o z ∈ Icc l u := by
    by_contra hn
    apply hz
    simp [flatAmplitude, hn]
  exact ⟨circleRep o z, hi, coe_circleRep o z⟩

/-- The exact real centered two-mode flat vector on any branch of length one
in the additive spectral variable. No coefficient smoothness is assumed. -/
lemma flat_vector_of_branch {f D : ℝ → ℝ} {l u o : ℝ}
    {φ : UnitAddCircle → UnitAddCircle} {m : ℤ}
    (hm : m ≠ 0) (hlu : l ≤ u) (hfm : Measurable f) (hDm : Measurable D)
    (hD : ∀ x ∈ Icc l u, HasDerivWithinAt f (D x) (Icc l u) x)
    (hmono : StrictMonoOn f (Icc l u)) (hperiod : f u = f l+1)
    (hi : Icc l u ⊆ Ioc o (o+1)) (hφ : Measurable φ)
    (hφf : ∀ x ∈ Icc l u, m • φ (x : UnitAddCircle) = (f x : UnitAddCircle)) :
    let A := fun ua : UnitAddCircle × UnitAddCircle => flatAmplitude o l u D ua.1
    let v := realPacketPair m A
    MemLp A 2 slowVolume ∧ MemLp v 2 tripleVolume ∧
      (∀ x, starRingEnd ℂ (v x) = v x) ∧
      (∫ x, v x ∂tripleVolume) = 0 ∧
      (∀ n : ℤ, (∫ x, starRingEnd ℂ (v x)*v (twistIter φ n x) ∂tripleVolume) =
        if n = 0 then 1 else 0) ∧
      Function.support A ⊆
        ((fun x : ℝ => (x : UnitAddCircle)) '' Icc l u) ×ˢ univ := by
  dsimp only
  have hAm := measurable_flatAmplitude hDm o l u
  have hp := flatAmplitude_pushforward hlu hfm hDm hD hmono hperiod hi
    (hφ.const_smul m) hφf
  have hn := frequency_energy_neg (hφ.const_smul m) hp
  let : IsFiniteMeasure (ENNReal.ofReal (1/2:ℝ) •
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) :=
    ⟨by simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; finiteness⟩
  have hA : MemLp (flatAmplitude o l u D) 2 AddCircle.haarAddCircle :=
    memLp_of_energy_map hAm (hφ.const_smul m) hp
  have hA' : MemLp (fun ua : UnitAddCircle × UnitAddCircle => flatAmplitude o l u D ua.1)
      2 slowVolume := hA.comp_measurePreserving measurePreserving_fst
  refine ⟨hA', memLp_realPacketPair hA' m, ?_, realPacketPair_integral_zero hA' hm, ?_, ?_⟩
  · exact realPacketPair_real (fun ua => by simp [flatAmplitude])
  · apply realPacketPair_flat (hAm.comp measurable_fst) hA' hφ hm
    · erw [packetSpectrum_first_coeff hAm hφ]
      exact hp
    · erw [packetSpectrum_first_coeff hAm hφ]
      simpa only [neg_smul, Pi.smul_apply] using hn
  · intro ua hua
    exact ⟨flatAmplitude_support o l u D hua, mem_univ _⟩

/-- Increasing on a nontrivial compact interval suffices to cover one period
after multiplication by a positive integer, without changing its left endpoint. -/
lemma exists_integer_period_subinterval {ψ : ℝ → ℝ} {l u : ℝ}
    (hlu : l < u) (hc : ContinuousOn ψ (Icc l u))
    (hmono : StrictMonoOn ψ (Icc l u)) :
    ∃ m : ℕ, 0 < m ∧ ∃ t ∈ Icc l u, l < t ∧ (m:ℝ)*(ψ t-ψ l) = 1 := by
  have hgap : 0 < ψ u-ψ l := sub_pos.mpr (hmono (left_mem_Icc.mpr hlu.le)
    (right_mem_Icc.mpr hlu.le) hlu)
  obtain ⟨m,hm⟩ := exists_nat_gt (max (1/(ψ u-ψ l)) 0)
  have hmpos : (0:ℝ) < m := lt_of_le_of_lt (le_max_right _ _) hm
  have hmnat : 0 < m := Nat.cast_pos.mp hmpos
  have hsmall : 1/(m:ℝ) < ψ u-ψ l := (one_div_lt hmpos hgap).2
    (lt_of_le_of_lt (le_max_left _ _) hm)
  have hrange : ψ l+1/(m:ℝ) ∈ Icc (ψ l) (ψ u) :=
    ⟨by linarith [one_div_pos.mpr hmpos], by linarith⟩
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hlu.le hc hrange
  have hlt : l < t := by
    by_contra hh
    have htl : t = l := le_antisymm (le_of_not_gt hh) ht.1
    rw [htl] at he
    linarith [one_div_pos.mpr hmpos]
  refine ⟨m,hmnat,t,ht,hlt,?_⟩
  rw [he]
  calc
    (m:ℝ)*(ψ l+1/(m:ℝ)-ψ l) = (m:ℝ)*(1/(m:ℝ)) := by ring
    _ = 1 := mul_one_div_cancel (ne_of_gt hmpos)

/-- The full flat-vector construction on every increasing good-arc interval.
The coefficient is literally the indicator times the square root Jacobian in
the manuscript, and its support is in a compact subinterval of the good arc. -/
lemma exists_flat_vector_on_interval {φ : UnitAddCircle → ℝ} {D : ℝ → ℝ}
    {l u o : ℝ} (hφ : Measurable φ) (hDm : Measurable D) (hlu : l < u)
    (hD : ∀ x ∈ Icc l u, HasDerivWithinAt
      (fun y : ℝ => φ (y : UnitAddCircle)) (D x) (Icc l u) x)
    (hmono : StrictMonoOn (fun y : ℝ => φ (y : UnitAddCircle)) (Icc l u))
    (hi : Icc l u ⊆ Ioc o (o+1)) :
    ∃ m : ℕ, 0 < m ∧ ∃ t ∈ Icc l u, l < t ∧
      let A := fun ua : UnitAddCircle × UnitAddCircle =>
        flatAmplitude o l t (fun x => (m:ℝ)*D x) ua.1
      let v := realPacketPair (m:ℤ) A
      MemLp A 2 slowVolume ∧ MemLp v 2 tripleVolume ∧
        (∀ x, starRingEnd ℂ (v x) = v x) ∧
        (∫ x, v x ∂tripleVolume) = 0 ∧
        (∀ n : ℤ, (∫ x, starRingEnd ℂ (v x)*
          v (twistIter (fun z => (φ z : UnitAddCircle)) n x) ∂tripleVolume) =
          if n = 0 then 1 else 0) ∧
        Function.support A ⊆
          ((fun x : ℝ => (x : UnitAddCircle)) '' Icc l t) ×ˢ univ := by
  have hc : ContinuousOn (fun y : ℝ => φ (y : UnitAddCircle)) (Icc l u) :=
    fun x hx => (hD x hx).continuousWithinAt
  obtain ⟨m,hm,t,ht,hlt,hperiod⟩ := exists_integer_period_subinterval hlu hc hmono
  have hs : Icc l t ⊆ Icc l u := Icc_subset_Icc le_rfl ht.2
  have hmpos : (0:ℝ) < m := Nat.cast_pos.mpr hm
  refine ⟨m,hm,t,ht,hlt,?_⟩
  apply flat_vector_of_branch (f := fun x : ℝ => (m:ℝ)*φ (x : UnitAddCircle))
    (by exact_mod_cast (ne_of_gt hm)) hlt.le
    (measurable_const.mul (hφ.comp AddCircle.measurable_mk'))
    (measurable_const.mul hDm)
  · intro x hx
    exact ((hD x (hs hx)).mono hs).const_mul (m:ℝ)
  · intro x hx y hy hxy
    exact mul_lt_mul_of_pos_left (hmono (hs hx) (hs hy) hxy) hmpos
  · nlinarith
  · exact hs.trans hi
  · exact AddCircle.measurable_mk'.comp hφ
  · intro x _
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
    simp

end ThreeTorus
end
end

section

/-! Finite measurable packet coefficient families, needed for whitening the
actual output of reflected prediction. The physical vectors remain literal
finite packet sums, not arbitrary Hilbert-space replacements. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus

section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

abbrev coefficientVolume : Measure (ι × (UnitAddCircle × UnitAddCircle)) :=
  Measure.count.prod slowVolume

def finitePacketVector (m : ι → ℤ) (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (x : TripleTorus) : ℂ := ∑ i, packet (m i) (A i) x

def coefficientFrequency (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (x : ι × (UnitAddCircle × UnitAddCircle)) : UnitAddCircle := m x.1 • φ x.2.1

lemma measurable_coefficientFrequency {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) : Measurable (coefficientFrequency φ m) :=
  measurable_from_prod_countable_right (fun i => (hφ.comp measurable_fst).const_smul (m i))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma memLp_finitePacketVector {m : ι → ℤ} {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, MemLp (A i) 2 slowVolume) : MemLp (finitePacketVector m A) 2 tripleVolume := by
  exact memLp_finsetSum _ (fun i _ => memLp_packet (hA i) (m i))

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacketVector_sub (m : ι → ℤ) (A B : ι → UnitAddCircle × UnitAddCircle → ℂ) :
    finitePacketVector m (fun i x => A i x-B i x) =
      fun x => finitePacketVector m A x-finitePacketVector m B x := by
  funext x
  simp only [finitePacketVector,packet,sub_mul,Finset.sum_sub_distrib]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacket_inner {m : ι → ℤ} (hm : Injective m)
    {A B : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, MemLp (A i) 2 slowVolume) (hB : ∀ i, MemLp (B i) 2 slowVolume) :
    (∫ x, conj (finitePacketVector m A x)*finitePacketVector m B x ∂tripleVolume) =
      ∑ i, ∫ x, conj (A i x)*B i x ∂slowVolume := by
  classical
  have hi i j : Integrable (fun x => conj (packet (m i) (A i) x)*packet (m j) (B j) x) tripleVolume :=
    (memLp_packet (hA i) (m i)).star.integrable_mul (memLp_packet (hB j) (m j))
  simp only [finitePacketVector,map_sum,Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi j i))]
  simp_rw [integral_finsetSum _ (fun j _ => hi j _),integral_packet_pair_L2 (hA _) (hB _)]
  simp only [hm.eq_iff]
  simp

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacket_energy {m : ι → ℤ} (hm : Injective m)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    (∫ x, ‖finitePacketVector m A x‖^2 ∂tripleVolume) =
      ∑ i, ∫ x, ‖A i x‖^2 ∂slowVolume := by
  have hh := finitePacket_inner hm hA hA
  simp only [normSq_complex,integral_complex_ofReal,← Complex.ofReal_sum] at hh
  exact Complex.ofReal_injective hh

lemma integrable_coefficient_normsq {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    Integrable (fun x : ι × (UnitAddCircle × UnitAddCircle) => ‖A x.1 x.2‖^2) coefficientVolume := by
  refine (integrable_prod_iff ?_).2 ⟨?_,?_⟩
  · exact ((measurable_from_prod_countable_right hAm).norm.pow_const 2).aestronglyMeasurable
  · exact Eventually.of_forall (fun i => (hA i).integrable_norm_pow (by norm_num))
  · exact Integrable.of_finite

lemma coefficient_integral_normsq {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    (∫ x : ι × (UnitAddCircle × UnitAddCircle), ‖A x.1 x.2‖^2 ∂coefficientVolume) =
      ∑ i, ∫ x, ‖A i x‖^2 ∂slowVolume := by
  rw [integral_prod _ (integrable_coefficient_normsq hAm hA),integral_count]

lemma coefficient_memLp {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    MemLp (fun x : ι × (UnitAddCircle × UnitAddCircle) => A x.1 x.2) 2 coefficientVolume := by
  exact (memLp_two_iff_integrable_sq_norm
    (measurable_from_prod_countable_right hAm).aestronglyMeasurable).2
      (integrable_coefficient_normsq hAm hA)

end FinitePacket
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

lemma physicalDist_eLpNorm {f g : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume) :
    physicalDist f g = (eLpNorm (fun x => f x-g x) 2 tripleVolume).toReal := by
  rw [physicalDist_eq_norm hf hg,← hf.toLp_sub hg,Lp.norm_toLp]
  rfl

lemma eLpNorm_packet (m : ℤ) {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : AEStronglyMeasurable A slowVolume) :
    eLpNorm (packet m A) 2 tripleVolume = eLpNorm A 2 slowVolume := by
  have hn (x : TripleTorus) : ‖packet m A x‖ = ‖A x.2‖ := by
    simp only [packet,norm_mul,fourier_apply,Circle.norm_coe,mul_one]
  have hbase : AEStronglyMeasurable (fun point : TripleTorus => A point.2) tripleVolume :=
    hA.comp_measurePreserving measurePreserving_snd
  have hpacket : AEStronglyMeasurable (packet m A) tripleVolume :=
    hbase.mul (((fourier m).continuous.comp continuous_fst).aestronglyMeasurable)
  refine (eLpNorm_congr_norm_ae hpacket hbase (Filter.Eventually.of_forall hn)).trans ?_
  exact eLpNorm_comp_measurePreserving hA measurePreserving_snd

lemma physicalDist_packet {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) (hB : MemLp B 2 slowVolume) (m : ℤ) :
    physicalDist (packet m A) (packet m B) = (eLpNorm (fun x => A x-B x) 2 slowVolume).toReal := by
  rw [physicalDist_eLpNorm (memLp_packet hA m) (memLp_packet hB m)]
  have he : (fun x => packet m A x-packet m B x) = packet m (fun x => A x-B x) := by
    funext x; simp only [packet,sub_mul]
  rw [he]
  exact congrArg ENNReal.toReal
    (eLpNorm_packet m (hA.aestronglyMeasurable.sub hB.aestronglyMeasurable))

lemma physicalDist_packet_lt {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hA : MemLp A 2 slowVolume) (hB : MemLp B 2 slowVolume) (m : ℤ) {ε : ℝ}
    (hε : 0 < ε) (hAB : eLpNorm (fun x => A x-B x) 2 slowVolume < ENNReal.ofReal ε) :
    physicalDist (packet m A) (packet m B) < ε := by
  rw [physicalDist_packet hA hB]
  exact (ENNReal.toReal_lt_toReal (hA.sub hB).eLpNorm_ne_top ENNReal.ofReal_ne_top).2 hAB |>.trans_eq
    (ENNReal.toReal_ofReal hε.le)

lemma physicalDist_add_le {f g h j : TripleTorus → ℂ}
    (hf : MemLp f 2 tripleVolume) (hg : MemLp g 2 tripleVolume)
    (hh : MemLp h 2 tripleVolume) (hj : MemLp j 2 tripleVolume) :
    physicalDist (fun x => f x+h x) (fun x => g x+j x) ≤ physicalDist f g+physicalDist h j := by
  change physicalDist (f+h) (g+j) ≤ _
  rw [physicalDist_eq_norm (hf.add hh) (hg.add hj),hf.toLp_add hh,hg.toLp_add hj]
  rw [show hf.toLp f+hh.toLp h-(hg.toLp g+hj.toLp j) =
    (hf.toLp f-hg.toLp g)+(hh.toLp h-hj.toLp j) by abel]
  simpa only [physicalDist_eq_norm hf hg,physicalDist_eq_norm hh hj] using
    norm_add_le (hf.toLp f-hg.toLp g) (hh.toLp h-hj.toLp j)

lemma physicalDist_small_sum {ι : Type*} [Fintype ι]
    {m : ι → ℤ} {A B : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, MemLp (A i) 2 slowVolume) (hB : ∀ i, MemLp (B i) 2 slowVolume)
    {ε : ℝ} (hε : 0 < ε)
    (hAB : ∀ i, eLpNorm (fun x => A i x-B i x) 2 slowVolume <
      ENNReal.ofReal (ε/(Fintype.card ι+1))) :
    physicalDist (finitePacketVector m A) (finitePacketVector m B) < ε := by
  have hc : (0:ℝ) < Fintype.card ι+1 := by positivity
  have he : 0 < ε/(Fintype.card ι+1) := div_pos hε hc
  calc
    _ ≤ ∑ i, physicalDist (packet (m i) (A i)) (packet (m i) (B i)) :=
      physicalDist_finsum (fun i => memLp_packet (hA i) _) (fun i => memLp_packet (hB i) _)
    _ ≤ ∑ _i : ι, ε/(Fintype.card ι+1) := Finset.sum_le_sum
      (fun i _ => (physicalDist_packet_lt (hA i) (hB i) (m i) he (hAB i)).le)
    _ < ε := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hc).2
      nlinarith

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
namespace NeutralStep
variable {ι κ : Type*} {F : PassagePackets ι} (s : NeutralStep F)

/-- Restrict a simultaneously transported finite family to a chosen root
list. This is the SAME physical passage, not another existence choice. -/
def reindex (r : κ → ι) : NeutralStep (F.reindex r) where
  δ := s.δ
  cut := s.cut
  L := s.L
  δpos := s.δpos
  δsmall := s.δsmall
  Lpos := s.Lpos
  geometry := s.geometry
  jitter := s.jitter
  n := s.n
  positive := s.positive
  χ := fun k => s.χ (r k)
  S := fun k => s.S (r k)
  indices := fun k => s.indices (r k)
  final := s.final.reindex (fun p => ⟨r p.1,p.2⟩)
  spare := ⟨fun _k => s.spare.1 _,fun _k => s.spare.2 _⟩
  speed := s.speed
  mode := fun _k => s.mode _
  amplitude := fun _k => s.amplitude _
  lift := fun _k => s.lift _
  good := s.final.reindex_good _ s.good

lemma reindex_chart (r : κ → ι) : (s.reindex r).chart = s.chart := rfl
lemma reindex_nextFrame (r : κ → ι) (frame : PhysicalFrame) :
    (s.reindex r).nextFrame frame = s.nextFrame frame := rfl

lemma reindex_outputVector (r : κ → ι) (k : κ) :
    outputVector (s.reindex r).final k = outputVector s.final (r k) := by
  funext x
  rfl

lemma reindex_outputDensity (r : κ → ι) (k : κ) :
    outputDensity (s.reindex r).final k = outputDensity s.final (r k) := by
  funext x
  rfl

lemma reindex_final_injective (r : κ → ι)
    (hd : Pairwise (fun i j : κ => Disjoint (s.S (r i)) (s.S (r j)))) :
    Injective (s.reindex r).final.m := by
  intro i j hij
  apply output_index_injective hd
  simpa only [(s.reindex r).mode] using hij

/-- Exact vector regrouping of the retained coefficients over their old roots. -/
lemma finitePacketVector_output [Fintype ι] :
    finitePacketVector s.final.m s.final.A = fun x => ∑ i, outputVector s.final i x := by
  funext x
  simp only [finitePacketVector,outputVector,Fintype.sum_sigma]

lemma physicalDist_total [Fintype ι] {ε : ℝ} (hε : 0 < ε)
    (he : ∀ i, physicalError (packet (F.m i) (F.A i))
      (outputVector s.final i ∘ s.chart) < (ε/(Fintype.card ι+1))^2) :
    physicalDist (finitePacketVector F.m F.A)
      (finitePacketVector s.final.m s.final.A ∘ s.chart) < ε := by
  have hFc i : MemLp (packet (F.m i) (F.A i)) 2 tripleVolume :=
    (continuous_packet (F.continuous_amplitude i)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hGc i : MemLp (outputVector s.final i ∘ s.chart) 2 tripleVolume :=
    ((continuous_outputVector s.final i).comp (continuous_passageChart (s.geometry.Hcontinuous s.n))).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc : (0:ℝ) < Fintype.card ι+1 := by positivity
  have he' i : physicalDist (packet (F.m i) (F.A i)) (outputVector s.final i ∘ s.chart) <
      ε/(Fintype.card ι+1) := (physicalDist_lt_iff _ _ (div_pos hε hc)).2 (he i)
  rw [s.finitePacketVector_output]
  calc
    _ ≤ ∑ i, physicalDist (packet (F.m i) (F.A i)) (outputVector s.final i ∘ s.chart) :=
      physicalDist_finsum hFc hGc
    _ ≤ ∑ _i : ι, ε/(Fintype.card ι+1) := Finset.sum_le_sum (fun i _ => (he' i).le)
    _ < ε := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_div_assoc]
      apply (div_lt_iff₀ hc).2
      nlinarith

end NeutralStep
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- A simultaneous neutral passage with repeated modes. Distinct old modes
have disjoint scalar retained sets, and equal modes share the same cutoff. -/
theorem exists_grouped_neutral {ι : Type*} [Fintype ι]
    (F : PassagePackets ι) (τ : ι → ι) (hτ : Involutive τ) (hr : F.Reflection τ)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε κ ζ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ s : NeutralStep F, s.δ < κ ∧
      Q.Close ζ frame F.V (s.nextFrame frame) s.final.V ∧
      (∀ i j, F.m i ≠ F.m j → Disjoint (s.S i) (s.S j)) ∧
      (∀ i x a, s.χ (τ i) x a=s.χ i (-x) a) ∧
      (∃ σ, Involutive σ ∧ s.final.Reflection σ ∧ ∀ i, (σ i).1=τ i.1) ∧
      ∀ i, physicalError (packet (F.m i) (F.A i))
        (outputVector s.final i ∘ s.chart) < ε ∧
        (∫ z, |outputDensity s.final i z-F.marginalDensity i z| ∂phaseHaar) < ε := by
  obtain ⟨c,hc,h0,χ,hχ,hd,_he,hrχ⟩ := scalar_grouped_neutral_cutoffs F hr
  obtain ⟨s,hsχ,_hsc,hsδ,hjet,hs⟩ := exists_controlled_neutral F hc h0 (fun i x _ => χ i x)
    (fun i => (hχ i).1.comp contDiff_fst)
    (fun i => compactSupport_frequency_cylinder (hχ i).2.1)
    (fun i _ => (hχ i).2.2.1) (fun i x _ => (hχ i).2.2.2.1 x)
    (fun i => (hχ i).2.2.2.2) Q frame hε hκ hζ
  refine ⟨s,hsδ,hjet,?_,?_,?_,hs⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    obtain ⟨a,ha⟩ := (s.indices i k).mp hki
    obtain ⟨b,hb⟩ := (s.indices j k).mp hkj
    rw [hsχ] at ha hb
    exact Set.disjoint_left.mp (hd i j hij) (subset_tsupport _ ha) (subset_tsupport _ hb)
  · intro i x a
    simpa only [hsχ] using hrχ i x
  · obtain ⟨σ,hroot,hσ,hrσ⟩ := s.reflection hr hτ (by simpa only [hsχ] using fun i x _ => hrχ i x)
    exact ⟨σ,hσ,hrσ,hroot⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators
namespace ThreeTorus
namespace PassagePackets

lemma marginalDensity_congr {ι κ : Type*} {F : PassagePackets ι} {G : PassagePackets κ}
    {i : ι} {j : κ} (hm : F.m i=G.m j) (hA : F.A i=G.A j) (hV : F.V=G.V) :
    F.marginalDensity i =ᵐ[AddCircle.haarAddCircle] G.marginalDensity j := by
  have hv : F.periodic.lift=G.periodic.lift := by
    funext x
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective x
    exact congrFun hV x
  have he : AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (F.marginalDensity i z)) =
      AddCircle.haarAddCircle.withDensity (fun z => ENNReal.ofReal (G.marginalDensity j z)) := by
    rw [← F.marginalDensity_spectral i,← G.marginalDensity_spectral j,hm,hA,hv]
  have h := (withDensity_eq_iff_of_sigmaFinite
    (F.marginalDensity_measurable i).ennreal_ofReal.aemeasurable
    (G.marginalDensity_measurable j).ennreal_ofReal.aemeasurable).mp he
  filter_upwards [h] with z hz
  have hh := congrArg ENNReal.toReal hz
  simpa only [ENNReal.toReal_ofReal (F.marginalDensity_nonneg i z),
    ENNReal.toReal_ofReal (G.marginalDensity_nonneg j z)] using hh

lemma marginalDensity_reindex {ι κ : Type*} (F : PassagePackets ι) (r : κ → ι) (i : κ) :
    (F.reindex r).marginalDensity i=F.marginalDensity (r i) := rfl

lemma append_marginalDensity_left {ι κ : Type*} (F : PassagePackets ι) (G : PassagePackets κ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hgF : F.GoodArc δ) (hgG : G.GoodArc δ) (hV : G.V=F.V) (i : ι) :
    (F.append G hδ hgF hgG hV).marginalDensity (Sum.inl i) =ᵐ[AddCircle.haarAddCircle] F.marginalDensity i :=
  marginalDensity_congr rfl rfl rfl

end PassagePackets
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
lemma integral_abs_sum_sub_le_of_integrable {ι : Type*} [Fintype ι]
    {p q : ι → UnitAddCircle → ℝ} (hp : ∀ i, Integrable (p i) phaseHaar)
    (hq : ∀ i, Integrable (q i) phaseHaar) :
    (∫ z, |(∑ i, p i z)-(∑ i, q i z)| ∂phaseHaar) ≤
      ∑ i, ∫ z, |p i z-q i z| ∂phaseHaar := by
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∫ z, ∑ i, |p i z-q i z| ∂phaseHaar := integral_mono
      ((integrable_finsetSum _ (fun i _ => (hp i).sub (hq i))).abs)
      (integrable_finsetSum _ (fun i _ => ((hp i).sub (hq i)).abs))
      (fun z => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := integral_finsetSum _ (fun i _ => ((hp i).sub (hq i)).abs)

namespace NeutralStep
variable {ι : Type*} [Fintype ι] {F : PassagePackets ι} (s : NeutralStep F)

lemma density_total {ε : ℝ} (hε : 0 < ε)
    (he : ∀ i, (∫ z, |outputDensity s.final i z-F.marginalDensity i z| ∂phaseHaar) <
      ε/(Fintype.card ι+1)) :
    (∫ z, |(∑ j, s.final.marginalDensity j z)-(∑ i, F.marginalDensity i z)| ∂phaseHaar) < ε := by
  have heq (z : UnitAddCircle) : (∑ j, s.final.marginalDensity j z)=∑ i, outputDensity s.final i z := by
    simp only [s.final.marginalDensity_eq s.spare,outputDensity,Fintype.sum_sigma]
  simp_rw [heq]
  calc
    _ ≤ ∑ i, ∫ z, |outputDensity s.final i z-F.marginalDensity i z| ∂phaseHaar :=
      integral_abs_sum_sub_le_of_integrable
        (fun i => continuous_circle_integrable (continuous_outputDensity s.final i)) F.marginalDensity_integrable
    _ ≤ ∑ _i : ι, ε/(Fintype.card ι+1) := Finset.sum_le_sum (fun i _ => (he i).le)
    _ < ε := by
      have hc : (0:ℝ) < Fintype.card ι+1 := by positivity
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_div_assoc]
      apply (div_lt_iff₀ hc).2
      nlinarith

end NeutralStep

/-- Simultaneous transport of two real lists with the SAME physical passage.
The first list retains injective angular indices; no cross-list orthogonality
or disjointness is assumed. -/
theorem exists_neutral_pair {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : PassagePackets ι) (H : PassagePackets κ) (hmi : Injective F.m)
    {δ : ℝ} (hδ : 0 ≤ δ) (hgF : F.GoodArc δ) (hgH : H.GoodArc δ) (hV : H.V=F.V)
    (τ : ι → ι) (σ : κ → κ) (hτ : Involutive τ) (hσ : Involutive σ)
    (hrF : F.Reflection τ) (hrH : H.Reflection σ)
    (Q : PhysicalJetData) (frame : PhysicalFrame)
    {ε η ζ : ℝ} (hε : 0 < ε) (hη : 0 < η) (hζ : 0 < ζ) :
    ∃ s : NeutralStep (F.append H hδ hgF hgH hV),
      s.δ < η ∧ Q.Close ζ frame F.V (s.nextFrame frame) s.final.V ∧
      Injective (s.reindex Sum.inl).final.m ∧
      (∃ τ', Involutive τ' ∧ (s.reindex Sum.inl).final.Reflection τ') ∧
      (∃ σ', Involutive σ' ∧ (s.reindex Sum.inr).final.Reflection σ') ∧
      physicalDist (finitePacketVector F.m F.A)
        (finitePacketVector (s.reindex Sum.inl).final.m (s.reindex Sum.inl).final.A ∘ s.chart) < ε ∧
      physicalDist (finitePacketVector H.m H.A)
        (finitePacketVector (s.reindex Sum.inr).final.m (s.reindex Sum.inr).final.A ∘ s.chart) < ε ∧
      (∫ z, |(∑ j, (s.reindex Sum.inl).final.marginalDensity j z)-
        (∑ i, F.marginalDensity i z)| ∂phaseHaar) < ε := by
  classical
  let U := F.append H hδ hgF hgH hV
  let r : ι ⊕ κ → ι ⊕ κ := Sum.map τ σ
  have hr : U.Reflection r := F.append_reflection H hδ hgF hgH hV hrF hrH
  have hri : Involutive r := by
    intro i; cases i with
    | inl i => exact congrArg Sum.inl (hτ i)
    | inr i => exact congrArg Sum.inr (hσ i)
  let a := ε/(Fintype.card ι+1)
  let b := ε/(Fintype.card κ+1)
  have ha : 0 < a := div_pos hε (by positivity)
  have hb : 0 < b := div_pos hε (by positivity)
  have he : 0 < min (min (a^2) (b^2)) a := lt_min (lt_min (sq_pos_of_pos ha) (sq_pos_of_pos hb)) ha
  obtain ⟨s,hsδ,hjet,hd,hχ,_hr,hs⟩ := exists_grouped_neutral U r hri hr Q frame he hη hζ
  refine ⟨s,hsδ,hjet,?_,?_,?_,?_,?_,?_⟩
  · apply s.reindex_final_injective
    intro i j hij
    exact hd (Sum.inl i) (Sum.inl j) (fun he => hij (hmi he))
  · have hh : (U.reindex Sum.inl).Reflection τ := U.reindex_reflection hr (fun _ => rfl)
    obtain ⟨τ',_,hi,hh'⟩ := (s.reindex Sum.inl).reflection hh hτ (fun i x a => hχ (Sum.inl i) x a)
    exact ⟨τ',hi,hh'⟩
  · have hh : (U.reindex Sum.inr).Reflection σ := U.reindex_reflection hr (fun _ => rfl)
    obtain ⟨σ',_,hi,hh'⟩ := (s.reindex Sum.inr).reflection hh hσ (fun i x a => hχ (Sum.inr i) x a)
    exact ⟨σ',hi,hh'⟩
  · exact (s.reindex Sum.inl).physicalDist_total hε (fun i =>
      ((hs (Sum.inl i)).1.trans_le ((min_le_left _ _).trans (min_le_left _ _))))
  · exact (s.reindex Sum.inr).physicalDist_total hε (fun i =>
      ((hs (Sum.inr i)).1.trans_le ((min_le_left _ _).trans (min_le_right _ _))))
  · have hh := (s.reindex Sum.inl).density_total hε (fun i =>
      ((hs (Sum.inl i)).2.trans_le (min_le_right _ _)))
    have heq : (fun z => ∑ i, (U.reindex Sum.inl).marginalDensity i z) =ᵐ[phaseHaar]
        (fun z => ∑ i, F.marginalDensity i z) := by
      filter_upwards [ae_all_iff.2 (fun i => F.append_marginalDensity_left H hδ hgF hgH hV i)] with z hz
      exact Finset.sum_congr rfl (fun i _ => hz i)
    rwa [integral_congr_ae (heq.mono (fun z hz => congrArg (fun t => |(∑ j, (s.reindex Sum.inl).final.marginalDensity j z)-t|) hz))] at hh

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate
namespace ThreeTorus
namespace PassagePackets
variable {ι : Type*} [Fintype ι] (F : PassagePackets ι)

abbrev ModeIndex := ↥(Finset.univ.image F.m)

def modeNeg {τ : ι → ι} (hr : F.Reflection τ) : F.ModeIndex → F.ModeIndex :=
  fun k => ⟨-k.val, by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp k.property
    exact Finset.mem_image.mpr ⟨τ i,Finset.mem_univ _,by rw [hr.index,hi]⟩⟩

lemma modeNeg_involutive {τ : ι → ι} (hr : F.Reflection τ) :
    Involutive (F.modeNeg hr) := fun _k => Subtype.ext (neg_neg _)

/-- Regroup a literal weighted family by its actual nonzero angular mode.
Only algebra is used: no cross-family orthogonality is asserted. -/
def modeSum (b : ι → ℂ) : PassagePackets F.ModeIndex :=
  F.regroup (fun _ => Finset.univ) Subtype.val
    (fun k => by obtain ⟨i,_,hi⟩ := Finset.mem_image.mp k.property; rw [← hi]; exact F.nonzero i)
    (fun k i => if F.m i=k.val then b i else 0)

lemma modeSum_good (b : ι → ℂ) {δ : ℝ} (hg : F.GoodArc δ) :
    (F.modeSum b).GoodArc δ := hg

lemma modeSum_injective (b : ι → ℂ) : Injective (F.modeSum b).m := Subtype.val_injective

lemma modeSum_vector (b : ι → ℂ) :
    finitePacketVector (F.modeSum b).m (F.modeSum b).A =
      fun x => ∑ i, b i*packet (F.m i) (F.A i) x := by
  classical
  funext x
  change (∑ k : F.ModeIndex, (∑ i, (if F.m i=k.val then b i else 0)*F.A i x.2)*fourier k.val x.1) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  let k : F.ModeIndex := ⟨F.m i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  rw [Finset.sum_eq_single k]
  · simp only [k,ite_true,packet,mul_assoc]
  · intro l _ hli
    have hn : F.m i ≠ l.val := by intro h; exact hli (Subtype.ext h.symm)
    simp only [hn,ite_false,zero_mul]
  · exact fun h => (h (Finset.mem_univ _)).elim

lemma modeSum_reflection {τ : ι → ι} (hτ : Involutive τ) (hr : F.Reflection τ)
    {b : ι → ℂ} (hb : ∀ i, b (τ i)=conj (b i)) :
    (F.modeSum b).Reflection (F.modeNeg hr) := by
  classical
  have hs (C : ι → ℂ) (hC : ∀ i, C (τ i)=conj (C i)) (k : F.ModeIndex) :
      (∑ i, (if F.m i= -k.val then b i else 0)*C i) =
        conj (∑ i, (if F.m i=k.val then b i else 0)*C i) := by
    rw [← Equiv.sum_comp (hτ.toPerm τ) (fun i => (if F.m i= -k.val then b i else 0)*C i)]
    simp only [Function.Involutive.coe_toPerm,hr.index,neg_inj,hb,hC,map_sum,map_mul,apply_ite,map_zero]
  constructor
  · intro k; rfl
  · intro k p
    exact hs (fun i => F.A i p) (fun i => hr.amplitude i p) k
  · intro k a x
    exact hs (fun i => F.A₀ i a x) (fun i => hr.lift i a x) k

end PassagePackets
end ThreeTorus
end
end

section

/-! Exact measurable spectral calculus for the literal finite packets.
This is the bridge from the energy-map whitening to the
actual physical packet family. It does not assume a spectral constructor. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus

section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The spectral measure is the pushforward of the coefficients' actual energy. -/
def finitePacketSpectralMeasure (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ) : Measure UnitAddCircle :=
  (coefficientVolume.withDensity (energyWeight (fun x => A x.1 x.2))).map
    (coefficientFrequency φ m)

lemma coefficient_memLp_iff {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) :
    MemLp (fun x : ι × (UnitAddCircle × UnitAddCircle) => A x.1 x.2) 2 coefficientVolume ↔
      ∀ i, MemLp (A i) 2 slowVolume := by
  refine ⟨fun h i => ?_, coefficient_memLp hAm⟩
  apply (memLp_two_iff_integrable_sq_norm (hAm i).aestronglyMeasurable).2
  exact Measure.ae_count_iff.mp
    ((h.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).prod_right_ae) i

lemma finitePacketSpectralMeasure_eq_sum {φ : UnitAddCircle → UnitAddCircle}
    (hφ : Measurable φ) (m : ι → ℤ) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i)) :
    finitePacketSpectralMeasure φ m A = ∑ i, packetSpectralMeasure φ (m i) (A i) := by
  classical
  ext s hs
  have hz := measurable_coefficientFrequency hφ m
  have hAm : Measurable (fun x : ι × (UnitAddCircle × UnitAddCircle) => A x.1 x.2) :=
    measurable_from_prod_countable_right hA
  have he := measurable_energyWeight hAm
  rw [finitePacketSpectralMeasure, Measure.map_apply hz hs, withDensity_apply _ (hz hs),
    ← lintegral_indicator (hz hs)]
  rw [lintegral_prod _ (he.indicator (hz hs)).aemeasurable, lintegral_count, tsum_fintype,
    Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hzi : Measurable (fun ua : UnitAddCircle × UnitAddCircle => m i • φ ua.1) :=
    (hφ.comp measurable_fst).const_smul (m i)
  rw [packetSpectralMeasure, Measure.map_apply hzi hs, withDensity_apply _ (hzi hs),
    ← lintegral_indicator (hzi hs)]
  apply lintegral_congr
  intro ua
  simp only [indicator_apply, mem_preimage, coefficientFrequency, energyWeight]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacket_integral_zero {m : ι → ℤ} (hm : ∀ i, m i ≠ 0)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    (∫ x, finitePacketVector m A x ∂tripleVolume) = 0 := by
  change (∫ x, ∑ i, packet (m i) (A i) x ∂tripleVolume) = 0
  rw [integral_finsetSum _
    (fun i _ => (memLp_packet (hA i) (m i)).integrable (by norm_num))]
  simp_rw [packet_integral_zero (hA _) (hm _)]
  simp

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacket_twist (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ) (n : ℤ) (x : TripleTorus) :
    finitePacketVector m A (twistIter φ n x) =
      finitePacketVector m (fun i ua => fourier n (m i • φ ua.1) * A i ua) x := by
  apply Finset.sum_congr rfl
  intro i _
  rw [packet_twistIter]
  dsimp only [packet]
  ring

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacket_correlation {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, MemLp (A i) 2 slowVolume) (n : ℤ) :
    (∫ x, conj (finitePacketVector m A x) * finitePacketVector m A (twistIter φ n x)
      ∂tripleVolume) =
      ∑ i, ∫ ua, fourier n (m i • φ ua.1) * (‖A i ua‖^2 : ℝ) ∂slowVolume := by
  simp_rw [finitePacket_twist]
  have hB : ∀ i, MemLp (fun ua => fourier n (m i • φ ua.1) * A i ua) 2 slowVolume :=
    fun i => memLp_frequency_mul (hA i) ((hφ.comp measurable_fst).const_smul (m i)) n
  rw [finitePacket_inner hm hA hB]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with ua
  rw [show conj (A i ua) * (fourier n (m i • φ ua.1) * A i ua) =
    fourier n (m i • φ ua.1) * (conj (A i ua) * A i ua) by ring, normSq_complex]

lemma coefficient_normsq_eq_physical {m : ι → ℤ} (hm : Injective m)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    (∫ x : ι × (UnitAddCircle × UnitAddCircle), ‖A x.1 x.2‖^2 ∂coefficientVolume) =
      ∫ x, ‖finitePacketVector m A x‖^2 ∂tripleVolume := by
  rw [coefficient_integral_normsq hAm hA, finitePacket_energy hm hA]

end FinitePacket
end ThreeTorus
end
end

section

/-! Whitening in the literal finite angular-packet family. All operations act on
its actual coefficient functions; angular collisions with the flat filler are
allowed, provided both are indexed by the same injective angular list. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus
section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def whitenPackets (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (p : UnitAddCircle → ℝ) (A V : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (i : ι) (ua : UnitAddCircle × UnitAddCircle) : ℂ :=
  whitenCoefficient (coefficientFrequency φ m) p (fun x => A x.1 x.2)
    (fun x => V x.1 x.2) (i,ua)

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma measurable_whitenPackets {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {p : UnitAddCircle → ℝ} (hp : Measurable p)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i)) (hV : ∀ i, Measurable (V i)) (i : ι) :
    Measurable (whitenPackets φ m p A V i) := by
  apply Measurable.ite (measurableSet_eq_fun
    (hp.comp ((hφ.comp measurable_fst).const_smul (m i))) measurable_const) (hV i)
  exact (hA i).div (Complex.measurable_ofReal.comp
    ((hp.comp ((hφ.comp measurable_fst).const_smul (m i))).sqrt))

lemma whitenPackets_flat {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {p : UnitAddCircle → ℝ} (hp : Measurable p) (hpn : ∀ z, 0 ≤ p z)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i)) (hV : ∀ i, Measurable (V i))
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)))
    (hflat : finitePacketSpectralMeasure φ m V = phaseHaar) :
    finitePacketSpectralMeasure φ m (whitenPackets φ m p A V) = phaseHaar := by
  exact whiten_energy_map (measurable_coefficientFrequency hφ m)
    (measurable_from_prod_countable_right hA) (measurable_from_prod_countable_right hV)
    hp hpn hpush hflat

lemma memLp_whitenPackets {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {p : UnitAddCircle → ℝ} (hp : Measurable p) (hpn : ∀ z, 0 ≤ p z)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i)) (hV : ∀ i, Measurable (V i))
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)))
    (hflat : finitePacketSpectralMeasure φ m V = phaseHaar) :
    ∀ i, MemLp (whitenPackets φ m p A V i) 2 slowVolume := by
  apply (coefficient_memLp_iff (measurable_whitenPackets hφ m hp hA hV)).1
  exact whiten_memLp (measurable_coefficientFrequency hφ m)
    (measurable_from_prod_countable_right hA) (measurable_from_prod_countable_right hV)
    hp hpn hpush hflat

lemma whitenPackets_distance {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {p : UnitAddCircle → ℝ} (hp : Measurable p)
    (hpn : ∀ z, 0 ≤ p z) {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hVm : ∀ i, Measurable (V i))
    (hA : ∀ i, MemLp (A i) 2 slowVolume)
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)))
    (hflat : finitePacketSpectralMeasure φ m V = phaseHaar) :
    (∫ x, ‖finitePacketVector m (whitenPackets φ m p A V) x - finitePacketVector m A x‖^2
      ∂tripleVolume) = ∫ z, (Real.sqrt (p z)-1)^2 ∂phaseHaar := by
  have hWm := measurable_whitenPackets hφ m hp hAm hVm
  have hW := memLp_whitenPackets hφ m hp hpn hAm hVm hpush hflat
  simp_rw [← congrFun (finitePacketVector_sub m (whitenPackets φ m p A V) A)]
  rw [← coefficient_normsq_eq_physical (A := fun i ua => whitenPackets φ m p A V i ua - A i ua) hm
    (fun i => (hWm i).sub (hAm i)) (fun i => (hW i).sub (hA i))]
  exact whiten_distance_integral (measurable_coefficientFrequency hφ m)
    (measurable_from_prod_countable_right hAm) (measurable_from_prod_countable_right hVm)
    hp hpn hpush hflat

lemma whitenPackets_reconstruct {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {p : UnitAddCircle → ℝ} (hp : Measurable p) (hpn : ∀ z, 0 ≤ p z)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i))
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z))) (i : ι) :
    (fun ua => (Real.sqrt (p (m i • φ ua.1)) : ℂ) * whitenPackets φ m p A V i ua)
      =ᵐ[slowVolume] A i := by
  have he := whiten_reconstruct (V := fun x : ι × (UnitAddCircle × UnitAddCircle) => V x.1 x.2)
    (measurable_coefficientFrequency hφ m) (measurable_from_prod_countable_right hA)
    hp hpn hpush
  exact Measure.ae_count_iff.mp (Measure.ae_ae_of_ae_prod he) i

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma whitenPackets_support (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (p : UnitAddCircle → ℝ) (A V : ι → UnitAddCircle × UnitAddCircle → ℂ)
    {s : Set (UnitAddCircle × UnitAddCircle)}
    (hA : ∀ i, support (A i) ⊆ s) (hV : ∀ i, support (V i) ⊆ s) (i : ι) :
    support (whitenPackets φ m p A V i) ⊆ s := by
  intro ua hua
  by_contra hs
  have ha : A i ua = 0 := by
    by_contra ha
    exact hs (hA i ha)
  have hv : V i ua = 0 := by
    by_contra hv
    exact hs (hV i hv)
  exact hua (by simp [whitenPackets,whitenCoefficient,ha,hv])

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma whitenPackets_reflection (φ : UnitAddCircle → UnitAddCircle) {m : ι → ℤ}
    (r : ι → ι) (hm : ∀ i, m (r i) = -m i)
    {p : UnitAddCircle → ℝ} (hp : ∀ z, p (-z) = p z)
    {A V : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i ua, A (r i) ua = conj (A i ua))
    (hV : ∀ i ua, V (r i) ua = conj (V i ua)) (i : ι) (ua : UnitAddCircle × UnitAddCircle) :
    whitenPackets φ m p A V (r i) ua = conj (whitenPackets φ m p A V i ua) := by
  classical
  have he : p (m (r i) • φ ua.1) = p (m i • φ ua.1) := by rw [hm,neg_smul,hp]
  by_cases hz : p (m i • φ ua.1) = 0
  · simp [whitenPackets,whitenCoefficient,coefficientFrequency,he,hz,hV]
  · simp [whitenPackets,whitenCoefficient,coefficientFrequency,he,hz,hA]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacketVector_real {m : ι → ℤ} (r : ι → ι) (hr : Involutive r)
    (hm : ∀ i, m (r i) = -m i) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i ua, A (r i) ua = conj (A i ua)) (x : TripleTorus) :
    conj (finitePacketVector m A x) = finitePacketVector m A x := by
  classical
  have he : ∀ i, conj (packet (m i) (A i) x) = packet (m (r i)) (A (r i)) x := by
    intro i
    simp only [packet,map_mul,hm,hA,fourier_neg]
  simp only [finitePacketVector,map_sum,he]
  exact Equiv.sum_comp (Involutive.toPerm r hr) (fun i => packet (m i) (A i) x)

end FinitePacket
end ThreeTorus
end
end

end OAI
