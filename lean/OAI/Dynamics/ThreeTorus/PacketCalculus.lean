import OAI.Dynamics.ThreeTorus.FlatPackets

namespace OAI

/-! Trigonometric approximation, spectral calculus, density distances, and reflected clipping. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- Uniform Laurent approximation of a continuous spectral multiplier. -/
lemma exists_uniform_laurent {Ψ : UnitAddCircle → ℂ} (hΨ : Continuous Ψ)
    {δ : ℝ} (hd : 0 < δ) :
    ∃ c : ℤ →₀ ℂ, ∀ z, ‖Ψ z-∑ k ∈ c.support, c k*fourier k z‖ < δ := by
  let f : C(UnitAddCircle,ℂ) := ⟨Ψ,hΨ⟩
  have hf : f ∈ (Submodule.span ℂ (range (fourier (T := (1:ℝ))))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  change f ∈ closure (Submodule.span ℂ (range (fourier (T := (1:ℝ)))) : Set C(UnitAddCircle,ℂ)) at hf
  obtain ⟨g,hg,hfg⟩ := Metric.mem_closure_iff.1 hf δ hd
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hg
  refine ⟨c,?_⟩
  intro z
  have he : g z = ∑ k ∈ c.support, c k*fourier k z := by
    rw [← hc]
    simp [Finsupp.sum]
  rw [← he]
  exact (ContinuousMap.norm_coe_le_norm (f-g) z).trans_lt (by simpa only [dist_eq_norm] using hfg)

end ThreeTorus
end
end

section

/-! Literal measurable finite-packet spectral calculus and Laurent approximation.
No abstract unitary is substituted for the actual twist. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace ThreeTorus

lemma energy_map_integral_real {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F : X → ℂ} {p : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hp : Measurable p) (hpn : ∀ y, 0 ≤ p y)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y))) :
    (∫ x, ‖F x‖^2 ∂μ) = ∫ y, p y ∂ν := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun _ => sq_nonneg _))
    ((hF.norm.pow_const 2).aestronglyMeasurable),
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hpn) hp.aestronglyMeasurable]
  exact congrArg ENNReal.toReal (energy_map_total hζ hpush)

lemma finite_energy_measure {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : X → ℂ}
    (hF : MemLp F 2 μ) : IsFiniteMeasure (μ.withDensity (energyWeight F)) := by
  apply isFiniteMeasure_withDensity
  have hf := (hasFiniteIntegral_iff_norm _).1
    (hF.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).hasFiniteIntegral
  simpa only [energyWeight,Real.norm_eq_abs,abs_pow,abs_norm] using hf.ne

lemma packetSpectralMeasure_finite {φ : UnitAddCircle → UnitAddCircle} (m : ℤ)
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hA : MemLp A 2 slowVolume) :
    IsFiniteMeasure (packetSpectralMeasure φ m A) := by
  let := finite_energy_measure hA
  exact Measure.isFiniteMeasure_map (slowVolume.withDensity (energyWeight A)) _

section FinitePacket
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma finitePacket_energy_density {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume)
    {p : UnitAddCircle → ℝ} (hp : Measurable p) (hpn : ∀ z, 0 ≤ p z)
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z))) :
    (∫ x, ‖finitePacketVector m A x‖^2 ∂tripleVolume) = ∫ z, p z ∂phaseHaar := by
  rw [← coefficient_normsq_eq_physical hm hAm hA]
  exact energy_map_integral_real (measurable_coefficientFrequency hφ m)
    (measurable_from_prod_countable_right hAm) hp hpn hpush

lemma finitePacket_spectral_moment {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume) (n : ℤ) :
    (∫ x, conj (finitePacketVector m A x)*finitePacketVector m A (twistIter φ n x)
      ∂tripleVolume) = ∫ z, fourier n z ∂finitePacketSpectralMeasure φ m A := by
  rw [finitePacketSpectralMeasure_eq_sum hφ m hAm,integral_finsetSum_measure]
  · rw [finitePacket_correlation hφ hm hA n]
    apply Finset.sum_congr rfl
    intro i _
    rw [packet_spectral_moment_L2 hφ (hAm i) (hA i),packet_correlation_L2 (hA i) hφ]
  · intro i _
    let := packetSpectralMeasure_finite (φ := φ) (m i) (hA i)
    exact (fourier n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma finitePacket_flat_moment {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    {m : ι → ℤ} (hm : Injective m) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume)
    (hflat : finitePacketSpectralMeasure φ m A = phaseHaar) (n : ℤ) :
    (∫ x, conj (finitePacketVector m A x)*finitePacketVector m A (twistIter φ n x)
      ∂tripleVolume) = if n = 0 then 1 else 0 := by
  rw [finitePacket_spectral_moment hφ hm hAm hA,hflat]
  exact integral_fourier_haar n

/-- Actual spectral multiplication of every retained angular coefficient. -/
def multiplyPackets (φ : UnitAddCircle → UnitAddCircle) (m : ι → ℤ)
    (a : UnitAddCircle → ℂ) (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (i : ι) (ua : UnitAddCircle × UnitAddCircle) : ℂ := a (m i • φ ua.1)*A i ua

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma measurable_multiplyPackets {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {a : UnitAddCircle → ℂ} (ha : Measurable a)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hA : ∀ i, Measurable (A i)) (i : ι) :
    Measurable (multiplyPackets φ m a A i) :=
  (ha.comp ((hφ.comp measurable_fst).const_smul (m i))).mul (hA i)

lemma multiplyPackets_spectrum {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (m : ι → ℤ) {p : UnitAddCircle → ℝ} (hp : Measurable p) (hpn : ∀ z, 0 ≤ p z)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hA : ∀ i, Measurable (A i))
    (hpush : finitePacketSpectralMeasure φ m A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)))
    {a : UnitAddCircle → ℂ} (ha : Measurable a) :
    finitePacketSpectralMeasure φ m (multiplyPackets φ m a A) =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (p z*‖a z‖^2)) := by
  have he := energy_map_multiplier (measurable_coefficientFrequency hφ m)
    (measurable_from_prod_countable_right hA) hp.ennreal_ofReal hpush ha
  calc
    _ = phaseHaar.withDensity ((fun z => ENNReal.ofReal (p z)) * energyWeight a) := he
    _ = _ := by
      congr 1
      funext z
      simp only [Pi.mul_apply,energyWeight,ENNReal.ofReal_mul (hpn z)]

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma finitePacketVector_congr_ae {m : ι → ℤ}
    {A B : ι → UnitAddCircle × UnitAddCircle → ℂ} (hAB : ∀ i, A i =ᵐ[slowVolume] B i) :
    finitePacketVector m A =ᵐ[tripleVolume] finitePacketVector m B := by
  have he := ae_all_iff.2 hAB
  have ht := (measurePreserving_snd (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle)) (ν := slowVolume)).quasiMeasurePreserving.ae he
  filter_upwards [ht] with x hx
  exact Finset.sum_congr rfl (fun i _ => by simp only [packet,hx i])

end FinitePacket
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeTorus

lemma norm_sq_sum_single_live {ι : Type*} [Fintype ι] (a : ι → ℂ)
    (hd : ∀ i j, i ≠ j → a i=0 ∨ a j=0) :
    ‖∑ i, a i‖^2 = ∑ i, ‖a i‖^2 := by
  classical
  by_cases h : ∃ i, a i ≠ 0
  · obtain ⟨i,hi⟩ := h
    have hz (j : ι) (hj : j ≠ i) : a j=0 := (hd i j hj.symm).resolve_left hi
    rw [Finset.sum_eq_single i,Finset.sum_eq_single i]
    · intro j _ hj; simp [hz j hj]
    · simp
    · intro j _ hj; exact hz j hj
    · simp
  · have hz : ∀ i, a i=0 := by simpa using h
    simp [hz]

lemma packetSpectralMeasure_zero (φ : UnitAddCircle → UnitAddCircle) (m : ℤ) :
    packetSpectralMeasure φ m (fun _ => 0) = 0 := by
  simp [packetSpectralMeasure]

lemma packetSpectralMeasure_sum_disjoint {ι : Type*} [Fintype ι]
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ) (m : ℤ)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hA : ∀ i, Measurable (A i))
    (hd : ∀ x i j, i ≠ j → A i x=0 ∨ A j x=0) :
    packetSpectralMeasure φ m (fun x => ∑ i, A i x) = ∑ i, packetSpectralMeasure φ m (A i) := by
  classical
  ext s hs
  have hz : Measurable (fun ua : UnitAddCircle × UnitAddCircle => m • φ ua.1) :=
    (hφ.comp measurable_fst).const_smul m
  rw [packetSpectralMeasure,Measure.map_apply hz hs,withDensity_apply _ (hz hs),Measure.finsetSum_apply]
  simp_rw [packetSpectralMeasure,Measure.map_apply hz hs,withDensity_apply _ (hz hs)]
  have he : energyWeight (fun x => ∑ i, A i x) = fun x => ∑ i, energyWeight (A i) x := by
    funext x
    simp only [energyWeight,norm_sq_sum_single_live _ (hd x)]
    exact ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ‖A i x‖)
  change (∫⁻ x in (fun ua : UnitAddCircle × UnitAddCircle => m • φ ua.1) ⁻¹' s,
    energyWeight (fun x => ∑ i, A i x) x ∂slowVolume) = _
  rw [he,lintegral_finsetSum]
  · rfl
  · intro i _
    exact measurable_energyWeight (hA i)

/-- Honest gathering by angular frequency preserves the spectral measure
when repeated modes have disjoint physical coefficient supports. -/
theorem gather_spectrum {ι : Type*} [Fintype ι]
    (m : ι → ℤ) {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, Measurable (A i)) (J : Finset ℤ) (hJ : ∀ i, m i ∈ J)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Measurable φ)
    (hd : ∀ x i j, i ≠ j → m i=m j → A i x=0 ∨ A j x=0) :
    (∑ k : ↥J, packetSpectralMeasure φ k.val
      (fun x => ∑ i, if m i=k.val then A i x else 0)) =
      ∑ i, packetSpectralMeasure φ (m i) (A i) := by
  classical
  have he (k : ↥J) : packetSpectralMeasure φ k.val
      (fun x => ∑ i, if m i=k.val then A i x else 0) =
      ∑ i, if m i=k.val then packetSpectralMeasure φ (m i) (A i) else 0 := by
    rw [packetSpectralMeasure_sum_disjoint hφ k.val]
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hi : m i=k.val
      · simp [hi]
      · simp [hi,packetSpectralMeasure_zero]
    · intro i
      by_cases hi : m i=k.val <;> simp only [hi,ite_true,ite_false]
      · exact hA i
      · exact measurable_const
    · intro x i j hij
      by_cases hi : m i=k.val <;> by_cases hj : m j=k.val <;> simp only [hi,hj,ite_true,ite_false,eq_self,or_true,true_or]
      exact hd x i j hij (hi.trans hj.symm)
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  let k : ↥J := ⟨m i,hJ i⟩
  rw [Finset.sum_eq_single k]
  · simp [k]
  · intro l _ hli
    have hn : m i ≠ l.val := fun h => hli (Subtype.ext h.symm)
    simp [hn]
  · simp

namespace PassagePackets
variable {ι : Type*} [Fintype ι] (F : PassagePackets ι)

lemma amplitude_disjoint_of_cylinderCore
    (hd : ∀ i j, i ≠ j → F.m i=F.m j → Disjoint (F.cylinderCore i) (F.cylinderCore j)) :
    ∀ p i j, i ≠ j → F.m i=F.m j → F.A i p=0 ∨ F.A j p=0 := by
  have _ := (inferInstance : Fintype ι)
  intro p i j hij hm
  let x : ℝ := (AddCircle.equivIoc 1 F.o p.1).1
  have hx : x ∈ Ioc F.o (F.o+1) := (AddCircle.equivIoc 1 F.o p.1).2
  have hpx : (x:UnitAddCircle)=p.1 := (AddCircle.equivIoc 1 F.o).symm_apply_apply p.1
  by_cases hi : F.A i p=0
  · exact Or.inl hi
  · right
    by_contra hj
    have hix : F.A₀ i p.2 x ≠ 0 := by
      rw [← F.lift_matches i p.2 x hx,hpx]
      exact hi
    have hjx : F.A₀ j p.2 x ≠ 0 := by
      rw [← F.lift_matches j p.2 x hx,hpx]
      exact hj
    exact Set.disjoint_left.mp (hd i j hij hm)
      (F.support_subset_cylinderCore i p.2 hix) (F.support_subset_cylinderCore j p.2 hjx)

end PassagePackets
end ThreeTorus
end
end

section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ThreeTorus
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma l2_integral_norm_sq (f : Lp ℂ 2 μ) : (∫ x, ‖f x‖^2 ∂μ) = ‖f‖^2 := by
  have h := congrArg (RCLike.re (K := ℂ)) (L2.inner_def (𝕜 := ℂ) f f)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)] at h
  simpa only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow] using h.symm

lemma integral_norm_product_le (f g : Lp ℂ 2 μ) :
    (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ≤ ‖f‖ * ‖g‖ := by
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (show (2 : ℝ).HolderConjugate 2 from Real.holderConjugate_iff.mpr (by norm_num))
    (f := (f : Ω → ℂ)) (g := (g : Ω → ℂ)) (by simpa using Lp.memLp f) (by simpa using Lp.memLp g)
  simp_rw [← Real.sqrt_eq_rpow, Real.rpow_two] at h
  simpa only [l2_integral_norm_sq, Real.sqrt_sq (norm_nonneg _)] using h

lemma density_norm_bound_l2 (f g : Lp ℂ 2 μ) :
    (∫ x, |‖f x‖^2 - ‖g x‖^2| ∂μ) ≤ (‖f‖+‖g‖)*‖f-g‖ := by
  have hiF : Integrable (fun x => ‖f x‖^2) μ := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hiG : Integrable (fun x => ‖g x‖^2) μ := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have hid (v : Lp ℂ 2 μ) : Integrable (fun x => ‖v x‖ * ‖(f-g) x‖) μ := by
    exact memLp_one_iff_integrable.mp ((Lp.memLp v).norm.mul (Lp.memLp (f-g)).norm)
  have he : ∀ᵐ x ∂μ, |‖f x‖^2 - ‖g x‖^2| ≤
      ‖f x‖ * ‖(f-g) x‖ + ‖g x‖ * ‖(f-g) x‖ := by
    filter_upwards [Lp.coeFn_sub f g] with x hx
    rw [hx, Pi.sub_apply]
    calc
      |‖f x‖^2 - ‖g x‖^2| = |‖f x‖ - ‖g x‖| * (‖f x‖ + ‖g x‖) := by
        rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖f x‖ + ‖g x‖)]
        ring
      _ ≤ ‖f x-g x‖ * (‖f x‖ + ‖g x‖) := mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∫ x, ‖f x‖ * ‖(f-g) x‖ + ‖g x‖ * ‖(f-g) x‖ ∂μ :=
      integral_mono_ae ((hiF.sub hiG).abs) ((hid f).add (hid g)) he
    _ = (∫ x, ‖f x‖ * ‖(f-g) x‖ ∂μ) + (∫ x, ‖g x‖ * ‖(f-g) x‖ ∂μ) := integral_add (hid f) (hid g)
    _ ≤ ‖f‖ * ‖f-g‖ + ‖g‖ * ‖f-g‖ := add_le_add (integral_norm_product_le f (f-g)) (integral_norm_product_le g (f-g))
    _ = _ := by ring

lemma sq_sqrt_sub_sqrt_le_abs (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (Real.sqrt x-Real.sqrt y)^2 ≤ |x-y| := by
  have hxs := Real.sq_sqrt hx
  have hys := Real.sq_sqrt hy
  have hxp := Real.sqrt_nonneg x
  have hyp := Real.sqrt_nonneg y
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have := Real.sqrt_le_sqrt h
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have := Real.sqrt_le_sqrt h
    nlinarith

lemma memLp_sqrt_of_integrable {p : Ω → ℝ} (hp : Integrable p μ)
    (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x) : MemLp (fun x => Real.sqrt (p x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm
    (Real.continuous_sqrt.comp_aestronglyMeasurable hp.aestronglyMeasurable)).mpr
  apply hp.congr
  filter_upwards [hp0] with x hx
  simp only [Real.norm_eq_abs, sq_abs, Real.sq_sqrt hx]

lemma density_hellinger_error [IsProbabilityMeasure μ] {p q : Ω → ℝ}
    (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x) (hq0 : ∀ᵐ x ∂μ, 0 ≤ q x) :
    |(∫ x, Real.sqrt (p x) ∂μ) - ∫ x, Real.sqrt (q x) ∂μ| ≤
      Real.sqrt (∫ x, |p x-q x| ∂μ) := by
  have hps := memLp_sqrt_of_integrable hp hp0
  have hqs := memLp_sqrt_of_integrable hq hq0
  have hs := hps.sub hqs
  have hpi := hps.integrable (by norm_num)
  have hqi := hqs.integrable (by norm_num)
  have hh := integral_mul_norm_le_Lp_mul_Lq (μ := μ)
    (show (2 : ℝ).HolderConjugate 2 from Real.holderConjugate_iff.mpr (by norm_num))
    (f := fun x => Real.sqrt (p x)-Real.sqrt (q x)) (g := fun _ => (1 : ℝ))
    (by convert hs using 1; norm_num)
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ))
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow, norm_one, one_pow, mul_one,
    integral_const, probReal_univ, one_smul, Real.sqrt_one] at hh
  rw [← integral_sub hpi hqi]
  calc
    |∫ x, Real.sqrt (p x)-Real.sqrt (q x) ∂μ| ≤ ∫ x, ‖Real.sqrt (p x)-Real.sqrt (q x)‖ ∂μ :=
      by simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (fun x => Real.sqrt (p x)-Real.sqrt (q x)) (μ := μ))
    _ ≤ Real.sqrt (∫ x, ‖Real.sqrt (p x)-Real.sqrt (q x)‖^2 ∂μ) := hh
    _ ≤ _ := by
      apply Real.sqrt_le_sqrt
      apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mp hs) ((hp.sub hq).abs)
      filter_upwards [hp0,hq0] with x hpx hqx
      simpa only [Real.norm_eq_abs, sq_abs, Pi.sub_apply] using sq_sqrt_sub_sqrt_le_abs (p x) (q x) hpx hqx

end ThreeTorus

end
end

section

noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal Topology BigOperators
namespace ThreeTorus

lemma energy_integral_test {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F : X → ℂ} {p r : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hp : Measurable p) (hpn : ∀ y, 0 ≤ p y)
    (hpush : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y))) (hr : Measurable r) :
    (∫ y, p y*r y ∂ν) = ∫ x, ‖F x‖^2*r (ζ x) ∂μ := by
  have hleft : (∫ y, r y ∂ν.withDensity (fun y => ENNReal.ofReal (p y))) =
      ∫ y, p y*r y ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hpn _),smul_eq_mul]
  rw [← hleft,← hpush,integral_map hζ.aemeasurable hr.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (measurable_energyWeight hF)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [energyWeight,ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]

lemma integrable_mul_bounded_real {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : Integrable f μ) (hg : Measurable g) (hb : ∀ x, |g x| ≤ 1) :
    Integrable (fun x => f x*g x) μ := by
  apply hf.norm.mono' (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  exact .of_forall fun x => by
    change ‖f x*g x‖ ≤ ‖f x‖
    rw [norm_mul,Real.norm_eq_abs (g x)]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb x)

/-- L¹ contraction for the actual pushed coefficient energies. This proves the
paper's density estimate without postulating any abstract spectral map. -/
lemma energy_density_difference_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {ζ : X → Y} {F G : X → ℂ} {p q : Y → ℝ}
    (hζ : Measurable ζ) (hF : Measurable F) (hG : Measurable G)
    (hFl : MemLp F 2 μ) (hGl : MemLp G 2 μ)
    (hp : Measurable p) (hq : Measurable q) (hpi : Integrable p ν) (hqi : Integrable q ν)
    (hpn : ∀ y, 0 ≤ p y) (hqn : ∀ y, 0 ≤ q y)
    (hFp : (μ.withDensity (energyWeight F)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (p y)))
    (hGq : (μ.withDensity (energyWeight G)).map ζ =
      ν.withDensity (fun y => ENNReal.ofReal (q y))) :
    (∫ y, |p y-q y| ∂ν) ≤ ∫ x, |‖F x‖^2-‖G x‖^2| ∂μ := by
  let r : Y → ℝ := fun y => if p y < q y then -1 else 1
  have hr : Measurable r := measurable_const.ite (measurableSet_lt hp hq) measurable_const
  have hb (y) : |r y| ≤ 1 := by dsimp only [r]; split_ifs <;> norm_num
  have he (y) : |p y-q y| = p y*r y-q y*r y := by
    dsimp only [r]
    split_ifs with h
    · rw [abs_of_neg (sub_neg.mpr h)]; ring
    · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt h))]; ring
  have hFi : Integrable (fun x => ‖F x‖^2) μ := hFl.integrable_norm_pow (by norm_num)
  have hGi : Integrable (fun x => ‖G x‖^2) μ := hGl.integrable_norm_pow (by norm_num)
  have hfr := integrable_mul_bounded_real hFi (hr.comp hζ) (fun x => hb (ζ x))
  have hgr := integrable_mul_bounded_real hGi (hr.comp hζ) (fun x => hb (ζ x))
  calc
    _ = (∫ y, p y*r y ∂ν)-(∫ y, q y*r y ∂ν) := by
      simp_rw [he]
      exact integral_sub (integrable_mul_bounded_real hpi hr hb)
        (integrable_mul_bounded_real hqi hr hb)
    _ = ∫ x, ‖F x‖^2*r (ζ x)-‖G x‖^2*r (ζ x) ∂μ := by
      rw [energy_integral_test hζ hF hp hpn hFp hr,
        energy_integral_test hζ hG hq hqn hGq hr]
      exact (integral_sub hfr hgr).symm
    _ ≤ _ := by
      apply integral_mono (hfr.sub hgr) (hFi.sub hGi).abs
      intro x
      change ‖F x‖^2*r (ζ x)-‖G x‖^2*r (ζ x) ≤ |‖F x‖^2-‖G x‖^2|
      calc
        _ = (‖F x‖^2-‖G x‖^2)*r (ζ x) := by ring
        _ ≤ |(‖F x‖^2-‖G x‖^2)*r (ζ x)| := le_abs_self _
        _ ≤ _ := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hb _)

lemma density_norm_bound_memLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F G : X → ℂ} (hf : MemLp F 2 μ) (hg : MemLp G 2 μ) :
    (∫ x, |‖F x‖^2-‖G x‖^2| ∂μ) ≤
      (‖hf.toLp F‖+‖hg.toLp G‖)*‖hf.toLp F-hg.toLp G‖ := by
  have he : (∫ x, |‖F x‖^2-‖G x‖^2| ∂μ) =
      ∫ x, |‖hf.toLp F x‖^2-‖hg.toLp G x‖^2| ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    rw [hx,hy]
  rw [he]
  exact density_norm_bound_l2 _ _

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeTorus
section
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma coefficient_norm_eq_physical {m : ι → ℤ} (hm : Injective m)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hA : ∀ i, MemLp (A i) 2 slowVolume) :
    ‖(coefficient_memLp hAm hA).toLp (fun p : ι × (UnitAddCircle × UnitAddCircle) => A p.1 p.2)‖ =
      ‖(memLp_finitePacketVector hA).toLp (finitePacketVector m A)‖ := by
  have hh := coefficient_normsq_eq_physical hm hAm hA
  rw [← norm_toLp_sq (coefficient_memLp hAm hA),← norm_toLp_sq (memLp_finitePacketVector hA)] at hh
  nlinarith [norm_nonneg ((coefficient_memLp hAm hA).toLp (fun p : ι × (UnitAddCircle × UnitAddCircle) => A p.1 p.2)),
    norm_nonneg ((memLp_finitePacketVector hA).toLp (finitePacketVector m A))]

lemma coefficient_difference_norm {m : ι → ℤ} (hm : Injective m)
    {A B : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hBm : ∀ i, Measurable (B i))
    (hAl : ∀ i, MemLp (A i) 2 slowVolume) (hBl : ∀ i, MemLp (B i) 2 slowVolume) :
    ‖(coefficient_memLp hAm hAl).toLp (fun p : ι × (UnitAddCircle × UnitAddCircle) => A p.1 p.2)-
      (coefficient_memLp hBm hBl).toLp (fun p : ι × (UnitAddCircle × UnitAddCircle) => B p.1 p.2)‖ =
      physicalDist (finitePacketVector m A) (finitePacketVector m B) := by
  have hh := coefficient_norm_eq_physical hm (fun i => (hAm i).sub (hBm i))
    (fun i => (hAl i).sub (hBl i))
  rw [Lp.norm_toLp,Lp.norm_toLp] at hh
  change (eLpNorm (fun p : ι × (UnitAddCircle × UnitAddCircle) => A p.1 p.2-B p.1 p.2) 2 coefficientVolume).toReal =
    (eLpNorm (finitePacketVector m (fun i p => A i p-B i p)) 2 tripleVolume).toReal at hh
  rw [finitePacketVector_sub] at hh
  rw [← MemLp.toLp_sub,Lp.norm_toLp,
    physicalDist_eLpNorm (memLp_finitePacketVector hAl) (memLp_finitePacketVector hBl)]
  exact hh

/-- The source's constant-one density bound for the literal finite packets,
including a nonsmooth old admissible vector. -/
theorem finitePacket_density_distance {φ : UnitAddCircle → UnitAddCircle}
    (hφ : Measurable φ) {m : ι → ℤ} (hm : Injective m)
    {A B : ι → UnitAddCircle × UnitAddCircle → ℂ}
    (hAm : ∀ i, Measurable (A i)) (hBm : ∀ i, Measurable (B i))
    (hAl : ∀ i, MemLp (A i) 2 slowVolume) (hBl : ∀ i, MemLp (B i) 2 slowVolume)
    {p q : UnitAddCircle → ℝ} (hpm : Measurable p) (hqm : Measurable q)
    (hpi : Integrable p phaseHaar) (hqi : Integrable q phaseHaar)
    (hpn : ∀ z, 0 ≤ p z) (hqn : ∀ z, 0 ≤ q z)
    (hAp : finitePacketSpectralMeasure φ m A = phaseHaar.withDensity (fun z => ENNReal.ofReal (p z)))
    (hBq : finitePacketSpectralMeasure φ m B = phaseHaar.withDensity (fun z => ENNReal.ofReal (q z))) :
    (∫ z, |p z-q z| ∂phaseHaar) ≤
      (‖(memLp_finitePacketVector hAl).toLp (finitePacketVector m A)‖+
       ‖(memLp_finitePacketVector hBl).toLp (finitePacketVector m B)‖)*
        physicalDist (finitePacketVector m A) (finitePacketVector m B) := by
  have ha := coefficient_memLp hAm hAl
  have hb := coefficient_memLp hBm hBl
  have he := coefficient_difference_norm hm hAm hBm hAl hBl
  calc
    _ ≤ ∫ x, |‖A x.1 x.2‖^2-‖B x.1 x.2‖^2| ∂coefficientVolume :=
      energy_density_difference_le (measurable_coefficientFrequency hφ m)
        (measurable_from_prod_countable_right hAm) (measurable_from_prod_countable_right hBm)
        ha hb hpm hqm hpi hqi hpn hqn hAp hBq
    _ ≤ _ := by
      have hh := density_norm_bound_memLp ha hb
      rw [coefficient_norm_eq_physical hm hAm hAl,coefficient_norm_eq_physical hm hBm hBl,he] at hh
      exact hh

end
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeTorus

lemma gather_vector {ι : Type*} [Fintype ι] (m : ι → ℤ)
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ) (J : Finset ℤ) (hJ : ∀ i, m i ∈ J) :
    finitePacketVector (fun k : ↥J => k.val)
      (fun k x => ∑ i, if m i=k.val then A i x else 0) = finitePacketVector m A := by
  classical
  funext x
  simp only [finitePacketVector,packet,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  let k : ↥J := ⟨m i,hJ i⟩
  rw [Finset.sum_eq_single k]
  · simp [k]
  · intro l _ hli
    have hn : m i ≠ l.val := fun h => hli (Subtype.ext h.symm)
    simp [hn]
  · simp

namespace PassagePackets
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma marginalDensity_sum_spectrum (F : PassagePackets ι) :
    (∑ i, packetSpectralMeasure (fun u => (F.periodic.lift u:UnitAddCircle)) (F.m i) (F.A i)) =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (∑ i, F.marginalDensity i z)) := by
  simp_rw [F.marginalDensity_spectral]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => F.marginalDensity_nonneg i _)]
  ext s hs
  rw [Measure.finsetSum_apply,withDensity_apply _ hs]
  simp_rw [withDensity_apply _ hs]
  rw [lintegral_finsetSum]
  intro i _
  exact (F.marginalDensity_measurable i).ennreal_ofReal

/-- L1 spectral density distance for DIFFERENT finite lists. Repeated modes
are allowed only with actual disjoint coefficient supports. -/
theorem marginalDensity_distance (F : PassagePackets ι) (G : PassagePackets κ)
    (hV : G.V=F.V)
    (hF : ∀ x i j, i ≠ j → F.m i=F.m j → F.A i x=0 ∨ F.A j x=0)
    (hG : ∀ x i j, i ≠ j → G.m i=G.m j → G.A i x=0 ∨ G.A j x=0) :
    (∫ z, |(∑ i, F.marginalDensity i z)-(∑ j, G.marginalDensity j z)| ∂phaseHaar) ≤
      (physicalDist (finitePacketVector F.m F.A) 0+physicalDist (finitePacketVector G.m G.A) 0)*
        physicalDist (finitePacketVector F.m F.A) (finitePacketVector G.m G.A) := by
  classical
  let J := Finset.univ.image F.m ∪ Finset.univ.image G.m
  have hJF i : F.m i ∈ J := Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hJG j : G.m j ∈ J := Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  let A : ↥J → UnitAddCircle × UnitAddCircle → ℂ := fun k x => ∑ i, if F.m i=k.val then F.A i x else 0
  let B : ↥J → UnitAddCircle × UnitAddCircle → ℂ := fun k x => ∑ i, if G.m i=k.val then G.A i x else 0
  have hAc k : Continuous (A k) := continuous_finsetSum _ (fun i _ => by
    by_cases hi : F.m i=k.val <;> simp only [hi,ite_true,ite_false]
    · exact F.continuous_amplitude i
    · exact continuous_const)
  have hBc k : Continuous (B k) := continuous_finsetSum _ (fun i _ => by
    by_cases hi : G.m i=k.val <;> simp only [hi,ite_true,ite_false]
    · exact G.continuous_amplitude i
    · exact continuous_const)
  have hAl k : MemLp (A k) 2 slowVolume := (hAc k).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hBl k : MemLp (B k) 2 slowVolume := (hBc k).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let φ : UnitAddCircle → UnitAddCircle := fun u => (F.periodic.lift u:UnitAddCircle)
  have hφ : Measurable φ := AddCircle.measurable_mk'.comp F.speed_continuous.measurable
  have hφG : (fun u => (G.periodic.lift u:UnitAddCircle))=φ := by
    funext x
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective x
    exact congrArg (fun t : ℝ => (t:UnitAddCircle)) (congrFun hV x)
  have hp : finitePacketSpectralMeasure φ (fun k : ↥J => k.val) A =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (∑ i, F.marginalDensity i z)) := by
    rw [finitePacketSpectralMeasure_eq_sum hφ _ (fun k => (hAc k).measurable)]
    exact (gather_spectrum F.m (fun i => (F.continuous_amplitude i).measurable) J hJF hφ hF).trans
      F.marginalDensity_sum_spectrum
  have hq : finitePacketSpectralMeasure φ (fun k : ↥J => k.val) B =
      phaseHaar.withDensity (fun z => ENNReal.ofReal (∑ i, G.marginalDensity i z)) := by
    rw [finitePacketSpectralMeasure_eq_sum hφ _ (fun k => (hBc k).measurable)]
    refine (gather_spectrum G.m (fun i => (G.continuous_amplitude i).measurable) J hJG hφ hG).trans ?_
    rw [← hφG]
    exact G.marginalDensity_sum_spectrum
  have he := finitePacket_density_distance hφ Subtype.val_injective
    (fun k => (hAc k).measurable) (fun k => (hBc k).measurable) hAl hBl
    (Finset.measurable_sum _ (fun i _ => F.marginalDensity_measurable i))
    (Finset.measurable_sum _ (fun i _ => G.marginalDensity_measurable i))
    (integrable_finsetSum _ (fun i _ => F.marginalDensity_integrable i))
    (integrable_finsetSum _ (fun i _ => G.marginalDensity_integrable i))
    (fun z => Finset.sum_nonneg (fun i _ => F.marginalDensity_nonneg i z))
    (fun z => Finset.sum_nonneg (fun i _ => G.marginalDensity_nonneg i z)) hp hq
  have ha := gather_vector F.m F.A J hJF
  have hb := gather_vector G.m G.A J hJG
  have hnA : ‖(memLp_finitePacketVector hAl).toLp (finitePacketVector (fun k : ↥J => k.val) A)‖ =
      physicalDist (finitePacketVector (fun k : ↥J => k.val) A) 0 := by
    rw [physicalDist_eq_norm (memLp_finitePacketVector hAl) MemLp.zero]
    simp
  have hnB : ‖(memLp_finitePacketVector hBl).toLp (finitePacketVector (fun k : ↥J => k.val) B)‖ =
      physicalDist (finitePacketVector (fun k : ↥J => k.val) B) 0 := by
    rw [physicalDist_eq_norm (memLp_finitePacketVector hBl) MemLp.zero]
    simp
  rw [hnA,hnB,ha,hb] at he
  exact he
end PassagePackets
end ThreeTorus
end
end

section

noncomputable section
open Function
open scoped BigOperators
namespace ThreeTorus

/-- Nonzero reflected mode lists are exactly their positive half and its
negative copy. This equivalence is used BEFORE the ratio cutoff choices. -/
def reflectedIndexEquiv {ι : Type*} (m : ι → ℤ) (hm : ∀ i, m i ≠ 0)
    (τ : ι → ι) (hτ : Involutive τ) (hr : ∀ i, m (τ i) = -m i) :
    ({i : ι // 0 < m i} ⊕ {i : ι // 0 < m i}) ≃ ι where
  toFun := Sum.elim Subtype.val (fun i => τ i.val)
  invFun := fun i => if h : 0 < m i then Sum.inl ⟨i,h⟩ else
    Sum.inr ⟨τ i,by rw [hr]; have hn := hm i; omega⟩
  left_inv := by
    intro i
    rcases i with i|i
    · dsimp only [Sum.elim_inl]
      rw [dite_eq_left i.property]
    · have hn : ¬ 0 < m (τ i.val) := by rw [hr]; have hp := i.property; omega
      dsimp only [Sum.elim_inr]
      rw [dite_eq_right hn]
      exact congrArg Sum.inr (Subtype.ext (hτ i.val))
  right_inv := by
    intro i
    dsimp only
    split_ifs
    · rfl
    · exact hτ i

lemma sum_reflected_indices {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (m : ι → ℤ) (hm : ∀ i, m i ≠ 0) (τ : ι → ι) (hτ : Involutive τ)
    (hr : ∀ i, m (τ i) = -m i) (f : ι → M) :
    ∑ i, f i = (∑ i : {i : ι // 0 < m i}, f i.val)+(∑ i : {i : ι // 0 < m i}, f (τ i.val)) := by
  classical
  rw [← (reflectedIndexEquiv m hm τ hτ hr).sum_comp f,Fintype.sum_sum_type]
  rfl

end ThreeTorus
end
end

section

noncomputable section
open Function Set MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace ThreeTorus
variable {ι : Type*} [Fintype ι]

abbrev PositiveIndex (m : ι → ℤ) := {i : ι // 0 < m i}

def reflectedVector (m : ι → ℤ) (τ : ι → ι)
    (A : PositiveIndex m → UnitAddCircle × UnitAddCircle → ℂ) (x : TripleTorus) : ℂ :=
  (∑ i, packet (m i.val) (A i) x)+(∑ i, packet (m (τ i.val)) (fun p => conj (A i p)) x)

lemma reflectedVector_eq {m : ι → ℤ} (hm : ∀ i, m i ≠ 0)
    {τ : ι → ι} (hτ : Involutive τ) (hr : ∀ i, m (τ i) = -m i)
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} (hAr : ∀ i p, A (τ i) p=conj (A i p)) :
    finitePacketVector m A = reflectedVector m τ (fun i => A i.val) := by
  funext x
  rw [finitePacketVector,sum_reflected_indices m hm τ hτ hr]
  unfold reflectedVector
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact funext (hAr i.val)

lemma memLp_conj {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) : MemLp (fun x => conj (f x)) 2 μ := hf.star

lemma eLpNorm_conj {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℂ) :
    eLpNorm (fun x => conj (f x)) 2 μ = eLpNorm f 2 μ :=
  eLpNorm_star

lemma reflectedVector_memLp (m : ι → ℤ) (τ : ι → ι)
    {A : PositiveIndex m → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, MemLp (A i) 2 slowVolume) : MemLp (reflectedVector m τ A) 2 tripleVolume :=
  (memLp_finitePacketVector hA).add (memLp_finitePacketVector (fun i => memLp_conj (hA i)))

/-- A single positive-half coefficient approximation controls the entire
real physical vector; the negative half is its exact conjugate copy. -/
lemma physicalDist_reflectedVector {m : ι → ℤ} (τ : ι → ι)
    {A B : PositiveIndex m → UnitAddCircle × UnitAddCircle → ℂ}
    (hA : ∀ i, MemLp (A i) 2 slowVolume) (hB : ∀ i, MemLp (B i) 2 slowVolume)
    {ε : ℝ} (hε : 0 < ε)
    (he : ∀ i, eLpNorm (fun p => A i p-B i p) 2 slowVolume <
      ENNReal.ofReal ((ε/2)/(Fintype.card (PositiveIndex m)+1))) :
    physicalDist (reflectedVector m τ A) (reflectedVector m τ B) < ε := by
  have he2 : 0 < ε/2 := by positivity
  have hp := physicalDist_small_sum (m := fun i : PositiveIndex m => m i.val) hA hB he2 he
  have hn := physicalDist_small_sum (m := fun i : PositiveIndex m => m (τ i.val))
    (fun i => memLp_conj (hA i)) (fun i => memLp_conj (hB i)) he2 (fun i => by
      simpa only [← map_sub,eLpNorm_conj] using he i)
  have ht := physicalDist_add_le
    (memLp_finitePacketVector (m := fun i : PositiveIndex m => m i.val) hA)
    (memLp_finitePacketVector (m := fun i : PositiveIndex m => m i.val) hB)
    (memLp_finitePacketVector (m := fun i : PositiveIndex m => m (τ i.val)) (fun i => memLp_conj (hA i)))
    (memLp_finitePacketVector (m := fun i : PositiveIndex m => m (τ i.val)) (fun i => memLp_conj (hB i)))
  exact ht.trans_lt (by linarith)

end ThreeTorus
end
end

section

noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal
namespace ThreeTorus

variable {ι : Type} [Fintype ι] (F : PassagePackets ι)
variable (J : PositiveIndex F.m → Type)

abbrev RatioPositive := Σ i : PositiveIndex F.m, J i
abbrev RatioIndex := RatioPositive F J ⊕ RatioPositive F J

def ratioRoot (τ : ι → ι) : RatioIndex F J → ι :=
  Sum.elim (fun p => p.1.val) (fun p => τ p.1.val)

def ratioCut (χ : ∀ i, J i → ℝ × UnitAddCircle → ℝ) :
    RatioIndex F J → ℝ × UnitAddCircle → ℝ :=
  Sum.elim (fun p => χ p.1 p.2) (fun p => χ p.1 p.2)

def ratioTag (b : ∀ i, J i → ℂ) : RatioIndex F J → ℂ :=
  Sum.elim (fun p => b p.1 p.2) (fun p => conj (b p.1 p.2))

lemma ratioTag_reflect (b : ∀ i, J i → ℂ) (i : RatioIndex F J) :
    ratioTag F J b i.swap = conj (ratioTag F J b i) := by
  have _ := (inferInstance : Fintype ι)
  cases i <;> simp only [ratioTag,Sum.swap_inl,Sum.swap_inr,Sum.elim_inl,Sum.elim_inr,starRingEnd_self_apply]

variable {F J}

lemma clipped_reflection {τ : ι → ι} (hr : F.Reflection τ)
    {χ : ∀ i, J i → ℝ × UnitAddCircle → ℝ}
    (hχ : ∀ k, CylinderSmooth (ratioCut F J χ k))
    (hc : ∀ k, HasCompactSupport (ratioCut F J χ k))
    (hs : ∀ k, support (ratioCut F J χ k) ⊆ Ioo F.o (F.o+1) ×ˢ univ) :
    (F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).Reflection Sum.swap := by
  have _ := (inferInstance : Fintype ι)
  constructor
  · intro i
    cases i with
    | inl p => exact hr.index p.1.val
    | inr p => change F.m p.1.val = -F.m (τ p.1.val); rw [hr.index,neg_neg]
  · intro i p
    cases i <;> simp only [PassagePackets.clipped,ratioRoot,ratioCut,Sum.swap_inl,
      Sum.swap_inr,Sum.elim_inl,Sum.elim_inr,hr.amplitude,map_mul,Complex.conj_ofReal,starRingEnd_self_apply]
  · intro i a x
    cases i <;> simp only [PassagePackets.clipped,ratioRoot,ratioCut,Sum.swap_inl,
      Sum.swap_inr,Sum.elim_inl,Sum.elim_inr,hr.lift,map_mul,Complex.conj_ofReal,starRingEnd_self_apply]

lemma clipped_equal_mode_disjoint (hi : Injective F.m) {τ : ι → ι} (hr : F.Reflection τ)
    {χ : ∀ i, J i → ℝ × UnitAddCircle → ℝ}
    (hχ : ∀ k, CylinderSmooth (ratioCut F J χ k))
    (hc : ∀ k, HasCompactSupport (ratioCut F J χ k))
    (hs : ∀ k, support (ratioCut F J χ k) ⊆ Ioo F.o (F.o+1) ×ˢ univ)
    (hd : ∀ i, Pairwise (fun j k => Disjoint (tsupport (χ i j)) (tsupport (χ i k)))) :
    ∀ i j, i ≠ j →
      (F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).m i =
      (F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).m j →
      Disjoint ((F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).cylinderCore i)
        ((F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).cylinderCore j) := by
  have _ := (inferInstance : Fintype ι)
  intro i j hij he
  apply Disjoint.mono (F.clipped_core_subset _ _ hχ hc hs i)
    (F.clipped_core_subset _ _ hχ hc hs j)
  rcases i with ⟨i,r⟩|⟨i,r⟩ <;> rcases j with ⟨j,s⟩|⟨j,s⟩
  · change F.m i.val=F.m j.val at he
    have hei : i=j := Subtype.ext (hi he)
    subst j
    exact hd i (by intro h; change r=s at h; subst s; exact hij rfl)
  · change F.m i.val=F.m (τ j.val) at he
    rw [hr.index] at he
    have h1 := i.property; have h2 := j.property
    omega
  · change F.m (τ i.val)=F.m j.val at he
    rw [hr.index] at he
    have h1 := i.property; have h2 := j.property
    omega
  · change F.m (τ i.val)=F.m (τ j.val) at he
    rw [hr.index,hr.index,neg_inj] at he
    have hei : i=j := Subtype.ext (hi he)
    subst j
    exact hd i (by intro h; change r=s at h; subst s; exact hij rfl)

variable [∀ i, Fintype (J i)]

lemma tagged_clipped_vector {τ : ι → ι} (hr : F.Reflection τ)
    {χ : ∀ i, J i → ℝ × UnitAddCircle → ℝ}
    (hχ : ∀ k, CylinderSmooth (ratioCut F J χ k))
    (hc : ∀ k, HasCompactSupport (ratioCut F J χ k))
    (hs : ∀ k, support (ratioCut F J χ k) ⊆ Ioo F.o (F.o+1) ×ˢ univ)
    (b : ∀ i, J i → ℂ) :
    (fun x => ∑ k, ratioTag F J b k *
      packet ((F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).m k)
        ((F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).A k) x) =
    reflectedVector F.m τ (fun i p => ∑ j, b i j*((cylinderTorusCutoff (χ i j) p:ℂ)*F.A i.val p)) := by
  classical
  funext x
  simp only [Fintype.sum_sum_type,Fintype.sum_sigma,ratioTag,ratioRoot,ratioCut,
    PassagePackets.clipped,Sum.elim_inl,Sum.elim_inr,reflectedVector,packet,hr.amplitude,
    map_sum,map_mul,Complex.conj_ofReal,Finset.sum_mul,mul_assoc]

lemma untagged_clipped_vector {τ : ι → ι} (hr : F.Reflection τ)
    {χ : ∀ i, J i → ℝ × UnitAddCircle → ℝ}
    (hχ : ∀ k, CylinderSmooth (ratioCut F J χ k))
    (hc : ∀ k, HasCompactSupport (ratioCut F J χ k))
    (hs : ∀ k, support (ratioCut F J χ k) ⊆ Ioo F.o (F.o+1) ×ˢ univ) :
    finitePacketVector (F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).m
      (F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).A =
    reflectedVector F.m τ (fun i p => ∑ j, (cylinderTorusCutoff (χ i j) p:ℂ)*F.A i.val p) := by
  have hh := tagged_clipped_vector hr hχ hc hs (fun _ _ => 1)
  have h1 (k : RatioIndex F J) : ratioTag F J (fun _ _ => 1) k = 1 := by
    cases k <;> simp only [ratioTag,Sum.elim_inl,Sum.elim_inr,map_one]
  change (fun x => ∑ k, packet ((F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).m k)
    ((F.clipped (ratioRoot F J τ) (ratioCut F J χ) hχ hc hs).A k) x) = _
  simpa only [h1,one_mul] using hh

end ThreeTorus
end
end

end OAI
