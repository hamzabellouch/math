import OAI.Analysis.HotSpots.Douglas
import OAI.Analysis.HotSpots.GreenOperator

namespace OAI

section DouglasLipschitzBase
noncomputable section
section MainVariationalCombinedLayer
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff
namespace StrictHotSpots






def MainTheorem : Prop :=
  ∀ (Ω : Set Plane), AdmissibleDomain Ω →
    ∀ (u : Plane → ℝ), InFirstNeumannEigenspace Ω u →
      (∃ x ∈ Ω, u x ≠ 0) → MainConclusion Ω u

lemma rayleighValues_nonneg {Ω : Set Plane} {r : ℝ} (hr : r ∈ rayleighValues Ω) :
    0 ≤ r := by
  obtain ⟨v, g, _, _, hm, rfl⟩ := hr
  exact div_nonneg (integral_nonneg fun x => sq_nonneg ‖g x‖) hm.le

lemma firstPositiveNeumannValue_nonneg (Ω : Set Plane) :
    0 ≤ firstPositiveNeumannValue Ω :=
  Real.sInf_nonneg fun _ hr => rayleighValues_nonneg hr


lemma rayleigh_inequality {Ω : Set Plane} {v : Plane → ℝ} {g : Plane → Plane}
    (hv : HasH1Gradient Ω v g) (hm : (∫ x in Ω, v x) = 0)
    (hpos : 0 < ∫ x in Ω, (v x) ^ 2) :
    firstPositiveNeumannValue Ω * (∫ x in Ω, (v x) ^ 2) ≤
      ∫ x in Ω, ‖g x‖ ^ 2 := by
  apply (le_div_iff₀ hpos).mp
  apply csInf_le
  · exact ⟨0, fun _ hr => rayleighValues_nonneg hr⟩
  · exact ⟨v, g, hv, hm, hpos, rfl⟩

lemma eigenfunction_energy_identity {Ω : Set Plane} {u : Plane → ℝ}
    (hu : InFirstNeumannEigenspace Ω u) :
    (∫ x in Ω, ‖gradient u x‖ ^ 2) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, (u x) ^ 2) := by
  simpa only [real_inner_self_eq_norm_sq, pow_two] using hu.2.2.2 u (gradient u) hu.2.1



lemma strict_boundary_extrema_of_noncritical {Ω : Set Plane} {u : Plane → ℝ}
    (hne : Ω.Nonempty) (hopen : IsOpen Ω) (hbound : Bornology.IsBounded Ω)
    (hu : ContinuousOn u (closure Ω))
    (hnocrit : ∀ x ∈ Ω, gradient u x ≠ 0) : MainConclusion Ω u := by
  have hnotmin (x : Plane) (hx : x ∈ Ω) : ¬IsMinOn u (closure Ω) x := by
    intro hm
    have hl := hm.isLocalMin (Filter.mem_of_superset (hopen.mem_nhds hx) subset_closure)
    apply hnocrit x hx
    simp [gradient, hl.fderiv_eq_zero]
  have hnotmax (x : Plane) (hx : x ∈ Ω) : ¬IsMaxOn u (closure Ω) x := by
    intro hm
    have hl := hm.isLocalMax (Filter.mem_of_superset (hopen.mem_nhds hx) subset_closure)
    apply hnocrit x hx
    simp [gradient, hl.fderiv_eq_zero]
  obtain ⟨a, ha, hmin⟩ := hbound.isCompact_closure.exists_isMinOn hne.closure hu
  obtain ⟨b, hb, hmax⟩ := hbound.isCompact_closure.exists_isMaxOn hne.closure hu
  have hfa : a ∈ frontier Ω := by
    rw [frontier, hopen.interior_eq]
    exact ⟨ha, fun hx => hnotmin a hx hmin⟩
  have hfb : b ∈ frontier Ω := by
    rw [frontier, hopen.interior_eq]
    exact ⟨hb, fun hx => hnotmax b hx hmax⟩
  have hleast : IsLeast (u '' frontier Ω) (u a) := by
    refine ⟨⟨a, hfa, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmin (frontier_subset_closure hy)
  have hgreatest : IsGreatest (u '' frontier Ω) (u b) := by
    refine ⟨⟨b, hfb, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax (frontier_subset_closure hy)
  refine ⟨hnocrit, ?_⟩
  intro x hx
  rw [hleast.csInf_eq, hgreatest.csSup_eq]
  constructor
  · by_contra hlt
    apply hnotmin x hx
    intro y hy
    exact (le_of_not_gt hlt).trans (hmin hy)
  · by_contra hlt
    apply hnotmax x hx
    intro y hy
    exact (hmax hy).trans (le_of_not_gt hlt)


lemma eigenfunction_mass_pos {Ω : Set Plane} {u : Plane → ℝ}
    (hopen : IsOpen Ω) (hu : InFirstNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) : 0 < ∫ x in Ω, (u x) ^ 2 := by
  have hn : 0 ≤ ∫ x in Ω, (u x) ^ 2 := integral_nonneg fun x => sq_nonneg (u x)
  by_contra hp
  have hz : (∫ x in Ω, (u x) ^ 2) = 0 := le_antisymm (le_of_not_gt hp) hn
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (u x))
    hu.2.1.1.integrable_sq).mp hz
  have hu0 : u =ᵐ[volume.restrict Ω] 0 := by
    filter_upwards [hae] with x hx
    simpa using (eq_zero_of_pow_eq_zero hx : u x = 0)
  have hall := Measure.eqOn_open_of_ae_eq hu0 hopen
    (hu.1.continuousOn.mono subset_closure) continuousOn_const
  obtain ⟨x, hx, hux⟩ := hne
  exact hux (hall hx)

lemma eigenfunction_gradient_continuous {Ω : Set Plane} {u : Plane → ℝ}
    (hopen : IsOpen Ω) (hu : InFirstNeumannEigenspace Ω u) :
    ContinuousOn (gradient u) Ω := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
    ((hu.1.mono subset_closure).continuousOn_fderiv_of_isOpen hopen (by simp))


lemma firstPositiveNeumannValue_pos_of_eigenfunction {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : AdmissibleDomain Ω) (hu : InFirstNeumannEigenspace Ω u)
    (hne : ∃ x ∈ Ω, u x ≠ 0) : 0 < firstPositiveNeumannValue Ω := by
  have hμ := firstPositiveNeumannValue_nonneg Ω
  by_contra hp
  have hz : firstPositiveNeumannValue Ω = 0 := le_antisymm (le_of_not_gt hp) hμ
  have he : (∫ x in Ω, ‖gradient u x‖ ^ 2) = 0 := by
    rw [eigenfunction_energy_identity hu, hz, zero_mul]
  have hi : Integrable (fun x => ‖gradient u x‖ ^ 2) (volume.restrict Ω) :=
    hu.2.1.2.1.integrable_norm_pow (by norm_num)
  have hg2 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg ‖gradient u x‖) hi).mp he
  have hg : gradient u =ᵐ[volume.restrict Ω] 0 := by
    filter_upwards [hg2] with x hx
    simpa using (eq_zero_of_pow_eq_zero hx : ‖gradient u x‖ = 0)
  have hg0 := Measure.eqOn_open_of_ae_eq hg hΩ.2.1
    (eigenfunction_gradient_continuous hΩ.2.1 hu) continuousOn_const
  have hd0 : Ω.EqOn (fderiv ℝ u) 0 := by
    intro x hx
    have hh := hg0 hx
    change (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ u x) = 0 at hh
    simpa using congrArg (InnerProductSpace.toDual ℝ Plane) hh
  obtain ⟨x, hx, hux⟩ := hne
  have hc : Ω.EqOn u (fun _ => u x) := fun y hy =>
    hΩ.2.1.is_const_of_fderiv_eq_zero
      hΩ.2.2.2.1.isPathConnected.isConnected.isPreconnected
      ((hu.1.mono subset_closure).differentiableOn (by simp)) hd0 hy hx
  have hmean : (∫ y in Ω, u x) = 0 :=
    (setIntegral_congr_fun hΩ.2.1.measurableSet hc).symm.trans hu.2.2.1
  have hv : 0 < (volume Ω).toReal :=
    ENNReal.toReal_pos (ne_of_gt (hΩ.2.1.measure_pos volume hΩ.1))
      hΩ.2.2.1.measure_lt_top.ne
  simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at hmean
  exact hux ((mul_eq_zero.mp hmean).resolve_left hv.ne')

lemma integrable_inner_of_memLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure Plane} {f g : Plane → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  exact (hf.norm.integrable_mul hg.norm).mono' (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => norm_inner_le_norm _ _)

lemma integral_norm_add_smul_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure Plane} {f g : Plane → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (t : ℝ) :
    (∫ x, ‖f x + t • g x‖ ^ 2 ∂μ) = (∫ x, ‖f x‖ ^ 2 ∂μ) +
      2 * t * (∫ x, inner ℝ (f x) (g x) ∂μ) + t ^ 2 * (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ := hf.integrable_norm_pow (by norm_num)
  have hg2 : Integrable (fun x => ‖g x‖ ^ 2) μ := hg.integrable_norm_pow (by norm_num)
  have hfg := integrable_inner_of_memLp hf hg
  calc
    _ = ∫ x, ‖f x‖ ^ 2 + 2 * t * inner ℝ (f x) (g x) + t ^ 2 * ‖g x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, real_inner_comm (g x) (f x)]
      ring
    _ = _ := by
      have hi12 : Integrable (fun x => ‖f x‖ ^ 2 + 2 * t * inner ℝ (f x) (g x)) μ :=
        hf2.add (hfg.const_mul (2 * t))
      rw [integral_add hi12 (hg2.const_mul (t ^ 2)),
        integral_add hf2 (hfg.const_mul (2 * t)), integral_const_mul, integral_const_mul]

lemma integral_sq_add_mul {μ : Measure Plane} {v w : Plane → ℝ}
    (hv : MemLp v 2 μ) (hw : MemLp w 2 μ) (t : ℝ) :
    (∫ x, (v x + t * w x) ^ 2 ∂μ) = (∫ x, (v x) ^ 2 ∂μ) +
      2 * t * (∫ x, v x * w x ∂μ) + t ^ 2 * (∫ x, (w x) ^ 2 ∂μ) := by
  simpa only [smul_eq_mul, Real.norm_eq_abs, sq_abs, RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm] using
    integral_norm_add_smul_sq hv hw t

lemma rayleigh_inequality_all {Ω : Set Plane} {v : Plane → ℝ} {g : Plane → Plane}
    (hv : HasH1Gradient Ω v g) (hm : (∫ x in Ω, v x) = 0) :
    firstPositiveNeumannValue Ω * (∫ x in Ω, (v x) ^ 2) ≤ ∫ x in Ω, ‖g x‖ ^ 2 := by
  have hnn : 0 ≤ ∫ x in Ω, (v x) ^ 2 := integral_nonneg fun x => sq_nonneg (v x)
  rcases eq_or_lt_of_le hnn with hz | hp
  · rw [← hz, mul_zero]
    exact integral_nonneg fun x => sq_nonneg ‖g x‖
  · exact rayleigh_inequality hv hm hp



lemma minimizer_euler_mean_zero {Ω : Set Plane} {u v : Plane → ℝ}
    {g k : Plane → Plane} (hb : Bornology.IsBounded Ω)
    (hu : HasH1Gradient Ω u g) (hv : HasH1Gradient Ω v k)
    (hmu : (∫ x in Ω, u x) = 0) (hmv : (∫ x in Ω, v x) = 0)
    (he : (∫ x in Ω, ‖g x‖ ^ 2) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, (u x) ^ 2)) :
    (∫ x in Ω, inner ℝ (g x) (k x)) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, u x * v x) := by
  let : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top⟩
  have hui : Integrable u (volume.restrict Ω) := hu.1.integrable (by norm_num)
  have hvi : Integrable v (volume.restrict Ω) := hv.1.integrable (by norm_num)
  have hvar (t : ℝ) := rayleigh_inequality_all (hu.add (hv.smul t)) (by
    show (∫ x in Ω, u x + t * v x) = 0
    rw [integral_add hui (hvi.const_mul t), integral_const_mul, hmu, hmv]
    ring)
  have hpoly : ∀ t : ℝ, 0 ≤
      ((∫ x in Ω, ‖k x‖ ^ 2) - firstPositiveNeumannValue Ω * (∫ x in Ω, (v x) ^ 2)) * (t * t) +
      (2 * ((∫ x in Ω, inner ℝ (g x) (k x)) -
        firstPositiveNeumannValue Ω * (∫ x in Ω, u x * v x))) * t + 0 := by
    intro t
    have ht := hvar t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht
    rw [integral_norm_add_smul_sq hu.2.1 hv.2.1 t,
      integral_sq_add_mul hu.1 hv.1 t, he] at ht
    nlinarith
  have hd := discrim_le_zero hpoly
  simp only [discrim, mul_zero, sub_zero] at hd
  nlinarith [sq_nonneg ((∫ x in Ω, inner ℝ (g x) (k x)) -
    firstPositiveNeumannValue Ω * (∫ x in Ω, u x * v x))]



lemma minimizer_euler {Ω : Set Plane} {u v : Plane → ℝ} {g k : Plane → Plane}
    (hb : Bornology.IsBounded Ω) (hvol : 0 < (volume Ω).toReal)
    (hu : HasH1Gradient Ω u g) (hv : HasH1Gradient Ω v k)
    (hmu : (∫ x in Ω, u x) = 0)
    (he : (∫ x in Ω, ‖g x‖ ^ 2) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, (u x) ^ 2)) :
    (∫ x in Ω, inner ℝ (g x) (k x)) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, u x * v x) := by
  let : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top⟩
  let c := (∫ x in Ω, v x) / (volume Ω).toReal
  have hui : Integrable u (volume.restrict Ω) := hu.1.integrable (by norm_num)
  have hvi : Integrable v (volume.restrict Ω) := hv.1.integrable (by norm_num)
  have hw : HasH1Gradient Ω (fun x => v x - c) k := by
    change HasH1Gradient Ω (v - fun _ => c) k
    simpa only [sub_zero] using hv.sub (HasH1Gradient.const hb c)
  have hm : (∫ x in Ω, v x - c) = 0 := by
    rw [integral_sub hvi (integrable_const c)]
    simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
    change (∫ x in Ω, v x) - (volume Ω).toReal * c = 0
    dsimp [c]
    field_simp
    ring
  have hh := minimizer_euler_mean_zero hb hu hw hmu hm he
  have hi : (∫ x in Ω, u x * (v x - c)) = (∫ x in Ω, u x * v x) := by
    simp only [mul_sub]
    have huv : Integrable (fun x => u x * v x) (volume.restrict Ω) := hu.1.integrable_mul hv.1
    rw [integral_sub huv (hui.mul_const c),
      integral_mul_const, hmu, zero_mul, sub_zero]
  rwa [hi] at hh

lemma inFirstNeumannEigenspace_of_minimizer {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : AdmissibleDomain Ω) (hs : ContDiffOn ℝ ∞ u (closure Ω))
    (hu : HasH1Gradient Ω u (gradient u)) (hm : (∫ x in Ω, u x) = 0)
    (he : (∫ x in Ω, ‖gradient u x‖ ^ 2) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, (u x) ^ 2)) :
    InFirstNeumannEigenspace Ω u := by
  refine ⟨hs, hu, hm, fun v g hv => minimizer_euler hΩ.2.2.1 ?_ hu hv hm he⟩
  exact ENNReal.toReal_pos (ne_of_gt (hΩ.2.1.measure_pos volume hΩ.1))
    hΩ.2.2.1.measure_lt_top.ne


end StrictHotSpots
end MainVariationalCombinedLayer

section C1WeakGradientWeightedCombinedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots
lemma integral_mul_test_hasFDerivAt {Ω : Set Plane} {f φ : Plane → ℝ}
    {D : Plane → Plane →L[ℝ] ℝ} (ho : IsOpen Ω)
    (hcF : ContinuousOn f Ω) (hcD : ContinuousOn D Ω)
    (hd : ∀ x ∈ Ω, HasFDerivAt f (D x) x)
    (hφ : ContDiff ℝ ∞ φ) (hk : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω)
    (e : Plane) :
    (∫ x in Ω, f x * (fderiv ℝ φ x) e) = -(∫ x in Ω, D x e * φ x) := by
  have hdφ : Continuous (fun x => (fderiv ℝ φ x) e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcDf : ContinuousOn (fun x => fderiv ℝ f x e) Ω := by
    apply (hcD.clm_apply continuousOn_const).congr
    intro x hx
    exact congrArg (fun A : Plane →L[ℝ] ℝ => A e) (hd x hx).fderiv
  have hds : tsupport (fun x => (fderiv ℝ φ x) e) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ e).trans hs
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_test ho hcDf hφ.continuous hk hs)
    (integrable_mul_test ho hcF hdφ (hk.fderiv_apply ℝ e) hds)
    (integrable_mul_test ho hcF hφ.continuous hk hs)
    (fun x hx => (hd x (hs hx)).differentiableAt)
    (fun x _ => hφ.differentiable (by simp) x)
  rw [setIntegral_mul_test hds]
  rw [hi,← setIntegral_mul_test hs]
  congr 1
  apply setIntegral_congr_fun ho.measurableSet
  intro x hx
  change fderiv ℝ f x e * φ x = D x e * φ x
  rw [(hd x hx).fderiv]

lemma HasH1Gradient.of_hasFDerivAt {Ω : Set Plane} {f : Plane → ℝ} {g : Plane → Plane}
    (ho : IsOpen Ω) (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω)
    (hd : ∀ x ∈ Ω, HasFDerivAt f (InnerProductSpace.toDual ℝ Plane (g x)) x)
    (hmf : MemLp f 2 (volume.restrict Ω)) (hmg : MemLp g 2 (volume.restrict Ω)) :
    HasH1Gradient Ω f g := by
  refine ⟨hmf,hmg,fun φ hφ hk hs e => ?_⟩
  exact integral_mul_test_hasFDerivAt ho hf
    ((InnerProductSpace.toDual ℝ Plane).continuous.comp_continuousOn hg) hd hφ hk hs e
end StrictHotSpots
end C1WeakGradientWeightedCombinedLayer

section DouglasH1CombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10

def planeSeries (a : ℤ → ℂ) (x : Plane) : ℝ :=
  (harmonicSeries a (complexIso.symm x)).re

def planeD (a : ℤ → ℂ) (x : Plane) : Plane →L[ℝ] ℝ :=
  (Complex.reCLM.comp (harmonicD a (complexIso.symm x))).comp
    complexIso.symm.toContinuousLinearEquiv.toContinuousLinearMap

def planeGrad (a : ℤ → ℂ) (x : Plane) : Plane :=
  (InnerProductSpace.toDual ℝ Plane).symm (planeD a x)

lemma planeSeries_continuousOn {a : ℤ → ℂ} (ha : Summable (fun m => ‖a m‖)) :
    ContinuousOn (planeSeries a) (closedBall 0 1) := by
  apply Complex.continuous_re.comp_continuousOn
  apply (harmonicSeries_continuousOn ha).comp complexIso.symm.continuous.continuousOn
  intro x hx
  simpa only [mem_closedBall_zero_iff,LinearIsometryEquiv.norm_map] using hx

lemma planeD_continuousOn {a : ℤ → ℂ}
    (ha : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    ContinuousOn (planeD a) (closedBall 0 1) := by
  have hc : ContinuousOn (fun x : Plane => harmonicD a (complexIso.symm x)) (closedBall 0 1) := by
    apply (harmonicD_continuousOn ha).comp complexIso.symm.continuous.continuousOn
    intro x hx
    simpa only [mem_closedBall_zero_iff,LinearIsometryEquiv.norm_map] using hx
  exact (continuousOn_const.clm_comp hc).clm_comp continuousOn_const

lemma planeGrad_continuousOn {a : ℤ → ℂ}
    (ha : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    ContinuousOn (planeGrad a) (closedBall 0 1) :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn (planeD_continuousOn ha)

lemma planeSeries_hasFDerivAt {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) {x : Plane} (hx : x ∈ disk) :
    HasFDerivAt (planeSeries a) (planeD a x) x := by
  have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
    simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
  exact (Complex.reCLM.hasFDerivAt.comp _ (harmonicSeries_hasFDerivAt h0 h1 hz)).comp x
    complexIso.symm.toContinuousLinearEquiv.hasFDerivAt

lemma disk_memLp_of_continuousOn {F : Type*} [NormedAddCommGroup F]
    {f : Plane → F} (hf : ContinuousOn f (closedBall 0 1)) : MemLp f 2 (volume.restrict disk) := by
  let : IsFiniteMeasure (volume.restrict (ball (0:Plane) 1)) :=
    isFiniteMeasure_restrict.mpr (isBounded_ball (x := (0:Plane)) (r := 1)).measure_lt_top.ne
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:Plane) 1).exists_bound_of_continuousOn hf
  apply MemLp.of_bound ((hf.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball) C
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact hC x (ball_subset_closedBall hx)



theorem planeSeries_hasH1Gradient {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    HasH1Gradient disk (planeSeries a) (planeGrad a) := by
  apply HasH1Gradient.of_hasFDerivAt isOpen_ball
    ((planeSeries_continuousOn h0).mono ball_subset_closedBall)
    ((planeGrad_continuousOn h1).mono ball_subset_closedBall)
  · intro x hx
    simpa only [planeGrad,LinearIsometryEquiv.apply_symm_apply] using planeSeries_hasFDerivAt h0 h1 hx
  · exact disk_memLp_of_continuousOn (planeSeries_continuousOn h0)
  · exact disk_memLp_of_continuousOn (planeGrad_continuousOn h1)

lemma planeSeries_gradient {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    HasH1Gradient disk (planeSeries a) (gradient (planeSeries a)) := by
  have h := planeSeries_hasH1Gradient h0 h1
  have he : planeGrad a =ᵐ[volume.restrict disk] gradient (planeSeries a) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    unfold planeGrad gradient
    rw [(planeSeries_hasFDerivAt h0 h1 hx).fderiv]
  exact ⟨h.1,h.2.1.ae_eq he,fun φ hφ hc hs e => by
    rw [h.2.2 φ hφ hc hs e]
    congr 1
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]⟩

end StrictHotSpots.Douglas
end DouglasH1CombinedLayer

section DouglasInteriorCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10

lemma harmonicSeries_re_poisson {a : ℤ → ℂ} (ha : Summable (fun m => ‖a m‖))
    {z : ℂ} (hz : z ∈ ball 0 1) :
    Real.circleAverage (poissonKernel 0 z • (fun w => (harmonicSeries a w).re)) 0 1 =
      (harmonicSeries a z).re := by
  have hc := (harmonicSeries_continuousOn ha).mono sphere_subset_closedBall
  have hi := ((poissonKernel_continuousOn_sphere hz).smul hc).circleIntegrable (by norm_num : (0:ℝ) ≤ 1)
  have he := Complex.reCLM.circleAverage_comp_comm hi
  calc
    _ = (Real.circleAverage (poissonKernel 0 z • harmonicSeries a) 0 1).re := by
      convert he using 1
      · congr 1
        funext w
        simp [Pi.smul_apply']
      · rfl
    _ = _ := congrArg Complex.re (harmonicSeries_poisson ha hz)

lemma poissonAverage_contDiffOn {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1) :
    ContDiffOn ℝ ∞ (fun z => Real.circleAverage (poissonKernel 0 z • f) 0 1) (ball 0 1) := by
  have hfc : CircleIntegrable (fun z => (f z : ℂ)) 0 1 := by
    simp only [CircleIntegrable,intervalIntegrable_iff] at hf ⊢
    exact Complex.ofRealCLM.integrable_comp hf
  have hball : ball (0 : ℂ) 1 ⊆ (sphere (0 : ℂ) |(1 : ℝ)|)ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff, abs_one, Metric.mem_sphere]
    exact ne_of_lt (Metric.mem_ball.mp hz)
  have ha := (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hfc).mono hball
  have hc : ContDiffOn ℝ ∞ (fun z =>
      (Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ • (f ζ : ℂ)) 0 1).re)
        (ball 0 1) :=
    Complex.reCLM.contDiff.comp_contDiffOn (ha.contDiffOn_of_completeSpace.restrict_scalars ℝ)
  apply hc.congr
  intro z hz
  rw [re_circleAverage_herglotzRieszKernel_smul hf (hball hz)]
  congr 1
  funext ζ
  simp only [poissonKernel_eq_re_herglotzRieszKernel]

lemma harmonicSeries_re_contDiffOn {a : ℤ → ℂ} (ha : Summable (fun m => ‖a m‖)) :
    ContDiffOn ℝ ∞ (fun z => (harmonicSeries a z).re) (ball 0 1) := by
  have hc := Complex.continuous_re.comp_continuousOn
    ((harmonicSeries_continuousOn ha).mono sphere_subset_closedBall)
  apply (poissonAverage_contDiffOn (hc.circleIntegrable (by norm_num : (0:ℝ) ≤ 1))).congr
  intro z hz
  exact (harmonicSeries_re_poisson ha hz).symm

lemma planeSeries_contDiffOn {a : ℤ → ℂ} (ha : Summable (fun m => ‖a m‖)) :
    ContDiffOn ℝ ∞ (planeSeries a) disk := by
  apply (harmonicSeries_re_contDiffOn ha).comp complexIso.symm.contDiff.contDiffOn
  intro x hx
  simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx

end StrictHotSpots.Douglas
end DouglasInteriorCombinedLayer

section PlaneWavesCombinedLayer
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff Laplacian
namespace StrictHotSpots.PlaneWaves

def cosine (k : Plane) (x : Plane) : ℝ := Real.cos (inner ℝ k x)
def sine (k : Plane) (x : Plane) : ℝ := Real.sin (inner ℝ k x)

lemma cosine_smooth (k : Plane) : ContDiff ℝ ∞ (cosine k) :=
  (innerSL ℝ k).contDiff.cos
lemma sine_smooth (k : Plane) : ContDiff ℝ ∞ (sine k) :=
  (innerSL ℝ k).contDiff.sin

lemma fderiv_cosine (k x : Plane) :
    fderiv ℝ (cosine k) x = (-sine k x) • innerSL ℝ k := by
  exact ((innerSL ℝ k).hasFDerivAt.cos).fderiv
lemma fderiv_sine (k x : Plane) :
    fderiv ℝ (sine k) x = cosine k x • innerSL ℝ k := by
  exact ((innerSL ℝ k).hasFDerivAt.sin).fderiv

lemma gradient_cosine (k x : Plane) : gradient (cosine k) x = (-sine k x) • k := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,fderiv_cosine]
  rfl
lemma gradient_sine (k x : Plane) : gradient (sine k) x = cosine k x • k := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,fderiv_sine]
  rfl

lemma cosine_memLp {Ω : Set Plane} (hb : Bornology.IsBounded Ω) (k : Plane) :
    MemLp (cosine k) 2 (volume.restrict Ω) := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  exact MemLp.of_bound (cosine_smooth k).continuous.aestronglyMeasurable 1
    (Eventually.of_forall fun x => Real.norm_eq_abs _ ▸ Real.abs_cos_le_one _)
lemma sine_memLp {Ω : Set Plane} (hb : Bornology.IsBounded Ω) (k : Plane) :
    MemLp (sine k) 2 (volume.restrict Ω) := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  exact MemLp.of_bound (sine_smooth k).continuous.aestronglyMeasurable 1
    (Eventually.of_forall fun x => Real.norm_eq_abs _ ▸ Real.abs_sin_le_one _)

lemma cosine_h1 {Ω : Set Plane} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (k : Plane) :
    HasH1Gradient Ω (cosine k) (fun x => (-sine k x) • k) := by
  have he : gradient (cosine k) = fun x => (-sine k x) • k := funext (gradient_cosine k)
  rw [← he]
  apply HasH1Gradient.of_contDiffOn hΩ (cosine_smooth k).contDiffOn (cosine_memLp hb k)
  rw [he]
  exact (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) k).comp_memLp' (sine_memLp hb k).neg
lemma sine_h1 {Ω : Set Plane} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (k : Plane) :
    HasH1Gradient Ω (sine k) (fun x => cosine k x • k) := by
  have he : gradient (sine k) = fun x => cosine k x • k := funext (gradient_sine k)
  rw [← he]
  apply HasH1Gradient.of_contDiffOn hΩ (sine_smooth k).contDiffOn (sine_memLp hb k)
  rw [he]
  exact (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) k).comp_memLp' (cosine_memLp hb k)

lemma cosine_sine_sq (k x : Plane) : cosine k x ^ 2 + sine k x ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq _

lemma laplacian_cosine (k x : Plane) : Δ (cosine k) x = -‖k‖^2 * cosine k x := by
  let b := stdOrthonormalBasis ℝ Plane
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  have hd : ∀ i, iteratedFDeriv ℝ 2 (cosine k) x ![b i, b i] =
      -(inner ℝ k (b i))^2 * cosine k x := by
    intro i
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hc : fderiv ℝ (cosine k) = fun y => (-sine k y) • innerSL ℝ k :=
      funext (fderiv_cosine k)
    rw [hc, fderiv_smul_const (c := fun y : Plane => -(sine k y)) ((sine_smooth k).differentiable (by simp) x).neg (innerSL ℝ k : Plane →L[ℝ] ℝ),
      fderiv_fun_neg, fderiv_sine]
    simp
    ring
  change (∑ i, iteratedFDeriv ℝ 2 _ x ![b i, b i]) = _
  simp_rw [hd]
  rw [← Finset.sum_mul]
  have hs : ∑ i, (inner ℝ k (b i))^2 = ‖k‖^2 := by
    simpa only [pow_two,real_inner_self_eq_norm_sq,real_inner_comm (b _) k] using (b.sum_inner_mul_inner k k)
  rw [Finset.sum_neg_distrib,hs]

lemma laplacian_sine (k x : Plane) : Δ (sine k) x = -‖k‖^2 * sine k x := by
  let b := stdOrthonormalBasis ℝ Plane
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  have hd : ∀ i, iteratedFDeriv ℝ 2 (sine k) x ![b i, b i] =
      -(inner ℝ k (b i))^2 * sine k x := by
    intro i
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hc : fderiv ℝ (sine k) = fun y => cosine k y • innerSL ℝ k :=
      funext (fderiv_sine k)
    rw [hc, fderiv_smul_const ((cosine_smooth k).differentiable (by simp) x) (innerSL ℝ k : Plane →L[ℝ] ℝ),
      fderiv_cosine]
    simp
    ring
  change (∑ i, iteratedFDeriv ℝ 2 _ x ![b i, b i]) = _
  simp_rw [hd]
  rw [← Finset.sum_mul]
  have hs : ∑ i, (inner ℝ k (b i))^2 = ‖k‖^2 := by
    simpa only [pow_two,real_inner_self_eq_norm_sq,real_inner_comm (b _) k] using (b.sum_inner_mul_inner k k)
  rw [Finset.sum_neg_distrib,hs]

end StrictHotSpots.PlaneWaves
end PlaneWavesCombinedLayer

section LowerEulerCombinedLayer
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace StrictHotSpots
lemma lower_rayleigh {Ω : Set Plane} {v : Plane → ℝ} {g : Plane → Plane} {lam : ℝ}
    (hle : lam ≤ firstPositiveNeumannValue Ω)
    (hv : HasH1Gradient Ω v g) (hm : (∫ x in Ω, v x) = 0) :
    lam * (∫ x in Ω, (v x)^2) ≤ ∫ x in Ω, ‖g x‖^2 :=
  (mul_le_mul_of_nonneg_right hle (integral_nonneg fun x => sq_nonneg (v x))).trans
    (rayleigh_inequality_all hv hm)


lemma lower_euler_mean_zero {Ω : Set Plane} {u v : Plane → ℝ}
    {g k : Plane → Plane} {lam : ℝ}
    (hle : lam ≤ firstPositiveNeumannValue Ω) (hb : Bornology.IsBounded Ω)
    (hu : HasH1Gradient Ω u g) (hv : HasH1Gradient Ω v k)
    (hmu : (∫ x in Ω, u x) = 0) (hmv : (∫ x in Ω, v x) = 0)
    (he : (∫ x in Ω, ‖g x‖ ^ 2) =
      lam * (∫ x in Ω, (u x) ^ 2)) :
    (∫ x in Ω, inner ℝ (g x) (k x)) =
      lam * (∫ x in Ω, u x * v x) := by
  let : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top⟩
  have hui : Integrable u (volume.restrict Ω) := hu.1.integrable (by norm_num)
  have hvi : Integrable v (volume.restrict Ω) := hv.1.integrable (by norm_num)
  have hvar (t : ℝ) := lower_rayleigh hle (hu.add (hv.smul t)) (by
    show (∫ x in Ω, u x + t * v x) = 0
    rw [integral_add hui (hvi.const_mul t), integral_const_mul, hmu, hmv]
    ring)
  have hpoly : ∀ t : ℝ, 0 ≤
      ((∫ x in Ω, ‖k x‖ ^ 2) - lam * (∫ x in Ω, (v x) ^ 2)) * (t * t) +
      (2 * ((∫ x in Ω, inner ℝ (g x) (k x)) -
        lam * (∫ x in Ω, u x * v x))) * t + 0 := by
    intro t
    have ht := hvar t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ht
    rw [integral_norm_add_smul_sq hu.2.1 hv.2.1 t,
      integral_sq_add_mul hu.1 hv.1 t, he] at ht
    nlinarith
  have hd := discrim_le_zero hpoly
  simp only [discrim, mul_zero, sub_zero] at hd
  nlinarith [sq_nonneg ((∫ x in Ω, inner ℝ (g x) (k x)) -
    lam * (∫ x in Ω, u x * v x))]



lemma lower_euler {Ω : Set Plane} {u v : Plane → ℝ} {g k : Plane → Plane} {lam : ℝ}
    (hle : lam ≤ firstPositiveNeumannValue Ω)
    (hb : Bornology.IsBounded Ω) (hvol : 0 < (volume Ω).toReal)
    (hu : HasH1Gradient Ω u g) (hv : HasH1Gradient Ω v k)
    (hmu : (∫ x in Ω, u x) = 0)
    (he : (∫ x in Ω, ‖g x‖ ^ 2) =
      lam * (∫ x in Ω, (u x) ^ 2)) :
    (∫ x in Ω, inner ℝ (g x) (k x)) =
      lam * (∫ x in Ω, u x * v x) := by
  let : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top⟩
  let c := (∫ x in Ω, v x) / (volume Ω).toReal
  have hui : Integrable u (volume.restrict Ω) := hu.1.integrable (by norm_num)
  have hvi : Integrable v (volume.restrict Ω) := hv.1.integrable (by norm_num)
  have hw : HasH1Gradient Ω (fun x => v x - c) k := by
    change HasH1Gradient Ω (v - fun _ => c) k
    simpa only [sub_zero] using hv.sub (HasH1Gradient.const hb c)
  have hm : (∫ x in Ω, v x - c) = 0 := by
    rw [integral_sub hvi (integrable_const c)]
    simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
    change (∫ x in Ω, v x) - (volume Ω).toReal * c = 0
    dsimp [c]
    field_simp
    ring
  have hh := lower_euler_mean_zero hle hb hu hw hmu hm he
  have hi : (∫ x in Ω, u x * (v x - c)) = (∫ x in Ω, u x * v x) := by
    simp only [mul_sub]
    have huv : Integrable (fun x => u x * v x) (volume.restrict Ω) := hu.1.integrable_mul hv.1
    rw [integral_sub huv (hui.mul_const c),
      integral_mul_const, hmu, zero_mul, sub_zero]
  rwa [hi] at hh


end StrictHotSpots
end LowerEulerCombinedLayer

section L2InnerToLpCombinedLayer
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.L2Inner
lemma toLp_pair {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
  rw [hx,hy]
lemma toLp_left {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : α → E} (hf : MemLp f 2 μ) (g : Lp E 2 μ) :
    inner ℝ (hf.toLp f) g = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]
lemma toLp_right {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g : α → E} (f : Lp E 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ f (hg.toLp g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]
end StrictHotSpots.L2Inner
end L2InnerToLpCombinedLayer

section H1RayleighFormCombinedLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace Topology
namespace StrictHotSpots
private lemma two_inner_sub_left {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] (lam : ℝ) (a b c : A) (x y z : B) :
    inner ℝ (a-b) c - lam * inner ℝ (x-y) z =
      (inner ℝ a c - lam * inner ℝ x z) - (inner ℝ b c - lam * inner ℝ y z) := by
  rw [inner_sub_left,inner_sub_left]
  ring
private lemma two_inner_sub_right {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] (lam : ℝ) (a b c : A) (x y z : B) :
    inner ℝ a (b-c) - lam * inner ℝ x (y-z) =
      (inner ℝ a b - lam * inner ℝ x y) - (inner ℝ a c - lam * inner ℝ x z) := by
  rw [inner_sub_right,inner_sub_right]
  ring
end StrictHotSpots
namespace StrictHotSpots.H1
variable {Ω : Set Plane}
local instance : NormedSpace ℝ (H1 Ω) := (h1Graph Ω).normedSpace
def form (lam : ℝ) (u v : H1 Ω) : ℝ :=
  inner ℝ (grad u) (grad v) - lam * inner ℝ (value u) (value v)

lemma form_symm (lam : ℝ) (u v : H1 Ω) : form lam u v = form lam v u := by
  exact congrArg₂ (fun a b : ℝ => a - lam * b)
    (real_inner_comm (grad u) (grad v)).symm (real_inner_comm (value u) (value v)).symm
lemma form_sub_left (lam : ℝ) (u v w : H1 Ω) :
    form lam (u-v) w = form lam u w - form lam v w := by
  exact StrictHotSpots.two_inner_sub_left lam (grad u) (grad v) (grad w) (value u) (value v) (value w)
lemma form_sub_right (lam : ℝ) (u v w : H1 Ω) :
    form lam u (v-w) = form lam u v - form lam u w := by
  exact StrictHotSpots.two_inner_sub_right lam (grad u) (grad v) (grad w) (value u) (value v) (value w)
lemma form_smul_left (lam c : ℝ) (u v : H1 Ω) :
    form lam (c • u) v = c * form lam u v := by
  unfold form
  change inner ℝ (c • grad u) (grad v) - lam * inner ℝ (c • value u) (value v) = _
  rw [real_inner_smul_left,real_inner_smul_left]
  ring
lemma form_smul_right (lam c : ℝ) (u v : H1 Ω) :
    form lam u (c • v) = c * form lam u v := by
  unfold form
  change inner ℝ (grad u) (c • grad v) - lam * inner ℝ (value u) (c • value v) = _
  rw [real_inner_smul_right,real_inner_smul_right]
  ring
lemma form_diag_sub (lam c : ℝ) (u v : H1 Ω)
    (hv : form lam v v = 0) (huv : form lam u v = 0) :
    form lam (u-c•v) (u-c•v) = form lam u u := by
  rw [form_sub_left,form_sub_right,form_sub_right,form_smul_right,
    form_smul_left,form_smul_left,form_smul_right,hv,huv,← form_symm lam u v,huv]
  ring

variable (hb : Bornology.IsBounded Ω)
def mean : H1 Ω →L[ℝ] ℝ := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  exact (innerSL ℝ ((memLp_const (1 : ℝ)).toLp (fun _ : Plane => (1 : ℝ)))).comp value

lemma mean_eq (u : H1 Ω) : mean hb u = ∫ x in Ω, value u x := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  change inner ℝ ((memLp_const (1 : ℝ)).toLp _) (value u) = _
  rw [L2Inner.toLp_left]
  simp only [RCLike.inner_apply,RCLike.conj_to_real,mul_one]

lemma form_self_integral (lam : ℝ) (u : H1 Ω) :
    form lam u u = (∫ x in Ω, ‖grad u x‖^2) - lam * (∫ x in Ω, (value u x)^2) := by
  simp only [form,L2.inner_def,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

lemma form_nonneg {lam : ℝ} (hle : lam ≤ firstPositiveNeumannValue Ω)
    (u : H1 Ω) (hm : mean hb u = 0) : 0 ≤ form lam u u := by
  rw [form_self_integral]
  exact sub_nonneg.mpr (lower_rayleigh hle (hasH1Gradient u) ((mean_eq hb u).symm.trans hm))

lemma form_zero_euler {lam : ℝ} (hle : lam ≤ firstPositiveNeumannValue Ω)
    (hvol : 0 < (volume Ω).toReal) (u : H1 Ω) (hm : mean hb u = 0)
    (hz : form lam u u = 0) (v : H1 Ω) : form lam u v = 0 := by
  rw [form_self_integral,sub_eq_zero] at hz
  have he := lower_euler hle hb hvol (hasH1Gradient u) (hasH1Gradient v)
    ((mean_eq hb u).symm.trans hm) hz
  rw [form,L2.inner_def,L2.inner_def]
  simp only [RCLike.inner_apply,RCLike.conj_to_real]
  rw [show (fun x => value v x * value u x) = (fun x => value u x * value v x) by funext; ring,he,sub_self]

end StrictHotSpots.H1
end H1RayleighFormCombinedLayer

section CompactRowsCombinedLayer

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.CompactRows
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def rowOperator : Lp H 2 μ →L[ℝ] H →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.compLpL₂ 2 μ (innerSL ℝ)).flip

lemma rowOperator_apply_ae (r : Lp H 2 μ) (v : H) :
    rowOperator r v =ᵐ[μ] fun x => inner ℝ v (r x) :=
  (innerSL ℝ v).coeFn_compLp r

lemma rowOperator_compact_simple (r : Lp.simpleFunc H 2 μ) :
    IsCompactOperator (rowOperator (r : Lp H 2 μ)) := by
  let V : Submodule ℝ H := Submodule.span ℝ (Set.range (Lp.simpleFunc.toSimpleFunc r))
  have : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Lp.simpleFunc.toSimpleFunc r).finite_range
  have he : rowOperator (r : Lp H 2 μ) =
      ((rowOperator (r : Lp H 2 μ)).comp V.subtypeL).comp V.orthogonalProjectionOnto := by
    apply ContinuousLinearMap.ext
    intro v
    apply Lp.ext
    filter_upwards [rowOperator_apply_ae (r : Lp H 2 μ) v,
      rowOperator_apply_ae (r : Lp H 2 μ) (V.orthogonalProjectionOnto v),
      Lp.simpleFunc.toSimpleFunc_eq_toFun r] with x hx hy hr
    change rowOperator (r : Lp H 2 μ) v x =
      rowOperator (r : Lp H 2 μ) (V.orthogonalProjectionOnto v) x
    rw [hx, hy, ← hr]
    have hmem : (Lp.simpleFunc.toSimpleFunc r) x ∈ V := Submodule.subset_span ⟨x, rfl⟩
    exact (V.inner_orthogonalProjectionOnto_eq_of_mem_right ⟨_,hmem⟩ v).symm
  rw [he]
  exact (isCompactOperator_of_locallyCompactSpace_dom V.orthogonalProjectionOnto).clm_comp
    ((rowOperator (r : Lp H 2 μ)).comp V.subtypeL)



theorem rowOperator_compact (r : Lp H 2 μ) : IsCompactOperator (rowOperator r) := by
  have hc : IsClosed {f : Lp H 2 μ | IsCompactOperator (rowOperator f)} :=
    isClosed_setOfPred_isCompactOperator.preimage
      (rowOperator (μ := μ) (H := H)).continuous
  apply closure_minimal (fun f hf => rowOperator_compact_simple ⟨f,hf⟩) hc
  exact Lp.simpleFunc.dense (by norm_num) r

end StrictHotSpots.CompactRows
end CompactRowsCombinedLayer

section MeasurableRowsCombinedLayer

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.CompactRows

lemma measurable_of_dist {α E : Type*} [MeasurableSpace α] [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : α → E} (h : ∀ y, Measurable (fun x => dist (f x) y)) : Measurable f := by
  let B : Set (Set E) := {s | ∃ y r, s = Metric.ball y r}
  have hb : TopologicalSpace.IsTopologicalBasis B :=
    TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
      (by rintro s ⟨y,r,rfl⟩; exact Metric.isOpen_ball)
      (by intro x s hx hs
          obtain ⟨r,hr,hrs⟩ := Metric.isOpen_iff.mp hs x hx
          exact ⟨Metric.ball x r, ⟨x,r,rfl⟩, Metric.mem_ball_self hr, hrs⟩)
  rw [BorelSpace.measurable_eq (α := E), hb.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro s ⟨y,r,rfl⟩
  exact measurableSet_lt (h y) measurable_const

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure Y} [SFinite ν] [IsSeparable ν]

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

local instance : MeasurableSpace (Lp ℝ 2 ν) := borel _
local instance : BorelSpace (Lp ℝ 2 ν) := ⟨rfl⟩

lemma measurable_toLp_rows (K : X × Y → ℝ) (hK : Measurable K)
    (hrow : ∀ x, MemLp (fun y => K (x,y)) 2 ν) :
    Measurable (fun x => (hrow x).toLp (fun y => K (x,y))) := by
  apply measurable_of_dist
  intro f
  let R := fun x => (hrow x).toLp (fun y => K (x,y))
  have he (x : X) : dist (R x) f = Real.sqrt (∫ y, (K (x,y) - f y)^2 ∂ν) := by
    rw [dist_eq_norm]
    have hs : ∫ y, (K (x,y) - f y)^2 ∂ν = ‖R x - f‖^2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (R x) f, (hrow x).coeFn_toLp] with y hy hz
      simp only [Pi.sub_apply] at hy
      rw [real_inner_self_eq_norm_sq, hy, hz, Real.norm_eq_abs, sq_abs]
    rw [hs, Real.sqrt_sq (norm_nonneg _)]
  have hm : Measurable (fun p : X × Y => (K p - f p.2)^2) :=
    (hK.sub ((Lp.stronglyMeasurable f).measurable.comp measurable_snd)).pow_const 2
  simpa only [← he] using ((hm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable).sqrt

end StrictHotSpots.CompactRows
end MeasurableRowsCombinedLayer

section CompactCoerciveCombinedLayer
open Set
open scoped InnerProductSpace Topology
namespace StrictHotSpots.CompactCoercive
variable {E H V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma finite_projection_approx (T : E →L[ℝ] H) (hT : IsCompactOperator T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Submodule ℝ H, ∃ _ : FiniteDimensional ℝ U,
      ‖T - U.starProjection.comp T‖ ≤ ε := by
  obtain ⟨s,hs,hcover⟩ := Metric.totallyBounded_iff.mp
    (hT.isCompact_closure_image_closedBall 1).totallyBounded ε hε
  let U := Submodule.span ℝ s
  let : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ hs
  refine ⟨U,inferInstance,ContinuousLinearMap.opNorm_le_of_unit_norm hε.le ?_⟩
  intro x hx
  have hmem : T x ∈ closure (T '' Metric.closedBall 0 1) :=
    subset_closure ⟨x,by simpa using hx.le,rfl⟩
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hcover hmem)
  change ‖T x - U.starProjection (T x)‖ ≤ ε
  have hmin := U.starProjection_minimal (T x)
  rw [hmin]
  exact (ciInf_le (by exact ⟨0, by rintro _ ⟨z,rfl⟩; exact norm_nonneg _⟩)
    (⟨y,Submodule.subset_span hy⟩ : U)).trans (by exact (show ‖T x - y‖ < ε by simpa [Metric.mem_ball, dist_eq_norm] using hxy).le)



lemma observation_compact [CompleteSpace H] (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : V →L[ℝ] H) (S : H →L[ℝ] V)
    (hS : ∀ f v, B (S f) v = inner ℝ f (J v))
    (hc : IsCompactOperator (J.comp S)) : IsCompactOperator J := by
  obtain ⟨C,hC,hcoer⟩ := hB
  have hcl : J ∈ closure {A : V →L[ℝ] H | IsCompactOperator A} := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    let q : ℝ := δ / (2 * (‖B‖ + 1))
    have hq : 0 < q := div_pos hδ (mul_pos (by norm_num) (by positivity))
    obtain ⟨U,hU,happrox⟩ := finite_projection_approx (J.comp S) hc
      (mul_pos hC (sq_pos_of_pos hq))
    let : FiniteDimensional ℝ U := hU
    let A : V →L[ℝ] H := U.starProjection.comp J
    have hAc : IsCompactOperator A :=
      ((isCompactOperator_of_locallyCompactSpace_rng U.subtypeL).comp_clm
        U.orthogonalProjectionOnto).comp_clm J
    refine ⟨A,hAc,?_⟩
    have ha : ‖J - A‖ ≤ ‖B‖ * q := by
      apply ContinuousLinearMap.opNorm_le_bound (J - A) (mul_nonneg (norm_nonneg B) hq.le)
      intro v
      let w := J v - U.starProjection (J v)
      have hwproj : inner ℝ w (U.starProjection (J v)) = 0 :=
        U.starProjection_inner_eq_zero (J v) _ (U.orthogonalProjectionOnto (J v)).property
      have hwJ : inner ℝ w (J v) = ‖w‖^2 := by
        calc
          _ = inner ℝ w (w + U.starProjection (J v)) := by
            congr 1; dsimp [w]; abel
          _ = _ := by rw [inner_add_right, hwproj, add_zero, real_inner_self_eq_norm_sq]
      have hwTproj : inner ℝ w (U.starProjection ((J.comp S) w)) = 0 :=
        U.starProjection_inner_eq_zero (J v) _ (U.orthogonalProjectionOnto ((J.comp S) w)).property
      have ht : inner ℝ w ((J.comp S) w) ≤ C * q^2 * ‖w‖^2 := by
        calc
          _ = inner ℝ w (((J.comp S) - U.starProjection.comp (J.comp S)) w) := by
            change inner ℝ w (J (S w)) = inner ℝ w (J (S w) - U.starProjection (J (S w)))
            have hz : inner ℝ w (U.starProjection (J (S w))) = 0 := hwTproj
            rw [inner_sub_right, hz, sub_zero]
          _ ≤ ‖w‖ * ‖((J.comp S) - U.starProjection.comp (J.comp S)) w‖ :=
            real_inner_le_norm _ _
          _ ≤ ‖w‖ * ((C * q^2) * ‖w‖) := by
            gcongr
            exact (((J.comp S) - U.starProjection.comp (J.comp S)).le_opNorm w).trans
              (mul_le_mul_of_nonneg_right happrox (norm_nonneg _))
          _ = _ := by ring
      have hs : ‖S w‖ ≤ q * ‖w‖ := by
        have h0 := (hcoer (S w)).trans (by simpa only [hS, ContinuousLinearMap.comp_apply] using ht)
        have h1 : ‖S w‖^2 ≤ (q * ‖w‖)^2 := by nlinarith
        nlinarith [norm_nonneg (S w), mul_nonneg hq.le (norm_nonneg w)]
      have hv : ‖w‖^2 ≤ ‖B‖ * ‖S w‖ * ‖v‖ := by
        calc
          _ = B (S w) v := (hS w v).trans hwJ |>.symm
          _ ≤ ‖B (S w) v‖ := le_abs_self _
          _ ≤ ‖B (S w)‖ * ‖v‖ := (B (S w)).le_opNorm v
          _ ≤ _ := mul_le_mul_of_nonneg_right (B.le_opNorm (S w)) (norm_nonneg _)
      have hv' : ‖w‖^2 ≤ (‖B‖ * q * ‖v‖) * ‖w‖ := by
        calc
          _ ≤ ‖B‖ * ‖S w‖ * ‖v‖ := hv
          _ ≤ ‖B‖ * (q * ‖w‖) * ‖v‖ := by gcongr
          _ = _ := by ring
      change ‖w‖ ≤ ‖B‖ * q * ‖v‖
      by_cases hw0 : ‖w‖ = 0
      · rw [hw0]; positivity
      · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
        rw [pow_two] at hv'
        exact (mul_le_mul_iff_left₀ hwpos).mp (by simpa only [mul_comm] using hv')
    rw [dist_eq_norm]
    have he : ‖B‖ * q < δ := by
      dsimp [q]
      have hd : 0 < 2 * (‖B‖ + 1) := by positivity
      rw [← mul_div_assoc, div_lt_iff₀ hd]
      nlinarith [norm_nonneg B]
    simpa only [norm_sub_rev] using ha.trans_lt he
  exact isClosed_setOfPred_isCompactOperator.closure_subset hcl

end StrictHotSpots.CompactCoercive
end CompactCoerciveCombinedLayer

section DiskCompactEmbeddingCombinedLayer
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

private def boundedKernel (p : Plane × Plane) : ℝ := by
  classical
  exact if p.1 ∈ disk then kernel p.1 p.2 else 0

private lemma boundedKernel_measurable : Measurable boundedKernel :=
  Measurable.ite (diskOpen.measurableSet.preimage measurable_fst) measurable_kernel measurable_const

private lemma boundedKernel_memLp (x : Plane) :
    MemLp (fun y => boundedKernel (x,y)) 2 (volume.restrict disk) := by
  by_cases hx : x ∈ disk
  · simpa only [boundedKernel, ite_eq_left hx] using kernel_memLp x hx
  · simp only [boundedKernel, ite_eq_right hx]
    exact MemLp.zero

private def compactRow (x : Plane) : Lp ℝ 2 (volume.restrict disk) :=
  (boundedKernel_memLp x).toLp (fun y => boundedKernel (x,y))

private lemma compactRow_memLp : MemLp compactRow 2 (volume.restrict disk) := by
  let : MeasurableSpace (Lp ℝ 2 (volume.restrict disk)) := borel _
  let : BorelSpace (Lp ℝ 2 (volume.restrict disk)) := ⟨rfl⟩
  have hm : Measurable compactRow := CompactRows.measurable_toLp_rows boundedKernel
    boundedKernel_measurable boundedKernel_memLp
  apply MemLp.of_bound hm.aestronglyMeasurable kernel_bound.choose
  filter_upwards [ae_restrict_mem diskOpen.measurableSet] with x hx
  rw [compactRow, Lp.norm_toLp]
  simpa only [boundedKernel, ite_eq_left hx] using kernel_bound.choose_spec.2 x hx



lemma integralOperator_compact : IsCompactOperator integralOperator := by
  let r := compactRow_memLp.toLp compactRow
  have he : integralOperator = CompactRows.rowOperator r := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [integralOperator_ae f, CompactRows.rowOperator_apply_ae r f,
      compactRow_memLp.coeFn_toLp, ae_restrict_mem diskOpen.measurableSet] with x hx hy hr hxd
    rw [hx,hy,hr,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(boundedKernel_memLp x).coeFn_toLp] with y hxy
    change kernel x y * f y = inner ℝ (f y) (compactRow x y)
    rw [RCLike.inner_apply]
    change kernel x y * f y = compactRow x y * f y
    congr 1
    have ht : compactRow x y = kernel x y := by
      simpa only [compactRow, boundedKernel, ite_eq_left hxd] using hxy
    exact ht.symm
  rw [he]
  exact CompactRows.rowOperator_compact r



lemma value_compact : IsCompactOperator (H10.value diskOpen) := by
  let B := H10.energy diskOpen
  let hB := H10.energy_coercive diskOpen diskBounded
  let J := H10.value diskOpen
  let S := DirichletOperator.solution B hB J
  apply CompactCoercive.observation_compact B hB J S
  · exact DirichletOperator.solution_spec B hB J
  · change IsCompactOperator variationalOperator
    rw [← integralOperator_eq_variationalOperator]
    exact integralOperator_compact

end StrictHotSpots.PlaneGreen
end DiskCompactEmbeddingCombinedLayer

section H10InclusionCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots

def smoothTestToH10 {Ω : Set Plane} (hΩ : IsOpen Ω) : smoothTestSpace Ω →ₗ[ℝ] H10 hΩ :=
  (smoothTestToH1 hΩ).codRestrict (h10Submodule hΩ)
    (fun f => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ f))

lemma dense_smoothTestToH10 {Ω : Set Plane} (hΩ : IsOpen Ω) :
    DenseRange (smoothTestToH10 hΩ) := by
  intro u
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hu : (u : H1 Ω) ∈ closure (Set.range (smoothTestToH1 hΩ)) := u.property
  obtain ⟨v,⟨f,rfl⟩,hv⟩ := Metric.mem_closure_iff.mp hu ε hε
  exact ⟨smoothTestToH10 hΩ f, ⟨f,rfl⟩, hv⟩

namespace H10
variable {Ω Λ : Set Plane} (hΩ : IsOpen Ω) (hΛ : IsOpen Λ) (hsub : Ω ⊆ Λ)

def includeTest : smoothTestSpace Ω →ₗ[ℝ] smoothTestSpace Λ where
  toFun f := ⟨f.val,f.property.1,f.property.2.1,f.property.2.2.trans hsub⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma includeTest_norm (f : smoothTestSpace Ω) :
    ‖smoothTestToH10 hΛ (includeTest hsub f)‖ = ‖smoothTestToH10 hΩ f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(smoothTestToH1 hΛ (includeTest hsub f))‖^2 = ‖smoothTestToH1 hΩ f‖^2
  rw [H1.norm_sq, H1.norm_sq]
  rw [smoothTestToH1_value_norm, smoothTestToH1_grad_norm,
    smoothTestToH1_value_norm, smoothTestToH1_grad_norm]
  have hf : Function.support (f : Plane → ℝ) ⊆ Ω := (subset_tsupport _).trans f.property.2.2
  have hg : Function.support (gradient (f : Plane → ℝ)) ⊆ Ω := by
    intro x hx
    apply f.property.2.2
    by_contra hn
    apply hx
    rw [gradient, fderiv_of_notMem_tsupport ℝ hn, map_zero]
  dsimp [includeTest]
  have hfm := f.property.1.continuous.aestronglyMeasurable (μ := volume)
  have hgm : AEStronglyMeasurable (gradient (f : Plane → ℝ)) volume :=
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp
      (f.property.1.continuous_fderiv (by simp))).aestronglyMeasurable
  rw [eLpNorm_restrict_eq_of_support_subset hfm (hf.trans hsub),
      eLpNorm_restrict_eq_of_support_subset hgm (hg.trans hsub),
      eLpNorm_restrict_eq_of_support_subset hfm hf, eLpNorm_restrict_eq_of_support_subset hgm hg]

def inclusion : H10 hΩ →L[ℝ] H10 hΛ :=
  ((smoothTestToH10 hΛ).comp (includeTest hsub)).extendOfNorm (smoothTestToH10 hΩ)

lemma inclusion_test (f : smoothTestSpace Ω) :
    inclusion hΩ hΛ hsub (smoothTestToH10 hΩ f) =
      smoothTestToH10 hΛ (includeTest hsub f) :=
  LinearMap.extendOfNorm_eq (dense_smoothTestToH10 hΩ)
    ⟨1,fun f => by
      rw [one_mul]
      change ‖smoothTestToH10 hΛ (includeTest hsub f)‖ ≤ ‖smoothTestToH10 hΩ f‖
      exact le_of_eq (includeTest_norm hΩ hΛ hsub f)⟩ f

def restriction : Lp ℝ 2 (volume.restrict Λ) →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  Lp.LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
    (by simpa using Measure.restrict_mono hsub (le_refl (volume : Measure Plane)))

lemma value_inclusion : value hΩ =
    (restriction hsub).comp ((value hΛ).comp (inclusion hΩ hΛ hsub)) := by
  apply DFunLike.coe_injective
  apply (dense_smoothTestToH10 hΩ).equalizer (value hΩ).continuous
    ((restriction hsub).comp ((value hΛ).comp (inclusion hΩ hΛ hsub))).continuous
  funext f
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, inclusion_test]
  apply Lp.ext
  have hs := Lp.coeFn_LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
    (show volume.restrict Ω ≤ (1 : ℝ≥0∞) • volume.restrict Λ by
      simpa using Measure.restrict_mono hsub (le_refl (volume : Measure Plane)))
    (value hΛ (smoothTestToH10 hΛ (includeTest hsub f)))
  have hf := (test_memLp (Ω := Ω) f.property.1 f.property.2.1).coeFn_toLp
  have hg := ((Measure.absolutelyContinuous_of_le (Measure.restrict_mono hsub le_rfl)).ae_eq
    (test_memLp (Ω := Λ) f.property.1 f.property.2.1).coeFn_toLp)
  exact hf.trans (hg.symm.trans hs.symm)

include hsub in
lemma value_compact_of_subset (hc : IsCompactOperator (value hΛ)) :
    IsCompactOperator (value hΩ) := by
  rw [value_inclusion hΩ hΛ hsub]
  exact (hc.comp_clm (inclusion hΩ hΛ hsub)).clm_comp (restriction hsub)

end H10
end StrictHotSpots
end H10InclusionCombinedLayer

section H10HelmholtzCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace Laplacian ContDiff
namespace StrictHotSpots.H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω)
local instance : NormedSpace ℝ (H10 hΩ) := (H10.innerProductSpace hΩ).toNormedSpace



lemma helmholtz_pair {f : Plane → ℝ} {lam : ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω)
    (hv : MemLp f 2 (volume.restrict Ω))
    (hg : MemLp (gradient f) 2 (volume.restrict Ω))
    (hp : ∀ x ∈ Ω, Δ f x = -lam * f x) (u : H10 hΩ) :
    inner ℝ (hg.toLp _) (grad hΩ u) = lam * inner ℝ (hv.toLp _) (value hΩ u) := by
  let A : H10 hΩ →L[ℝ] ℝ := (innerSL ℝ (hg.toLp _)).comp (grad hΩ)
  let B : H10 hΩ →L[ℝ] ℝ := lam • (innerSL ℝ (hv.toLp _)).comp (value hΩ)
  change A u = B u
  apply isClosed_property (dense_smoothTestToH10 hΩ) (isClosed_eq A.continuous B.continuous) _ u
  intro t
  change inner ℝ (hg.toLp _) ((test_gradient_memLp t.property.1 t.property.2.1).toLp _) =
    lam * inner ℝ (hv.toLp _) ((test_memLp t.property.1 t.property.2.1).toLp _)
  rw [L2Inner.toLp_pair, L2Inner.toLp_pair]
  rw [integral_inner_gradient_test hΩ hf t.property.1 t.property.2.1 t.property.2.2]
  have he : (∫ x in Ω, Δ f x * (t : Plane → ℝ) x) =
      -lam * ∫ x in Ω, f x * (t : Plane → ℝ) x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    rw [hp x hx]
    ring
  rw [he]
  simp only [RCLike.inner_apply, RCLike.conj_to_real]
  rw [show (fun x => (t : Plane → ℝ) x * f x) = (fun x => f x * (t : Plane → ℝ) x) by funext; ring]
  ring

end StrictHotSpots.H10
end H10HelmholtzCombinedLayer


end

end DouglasLipschitzBase

end OAI
