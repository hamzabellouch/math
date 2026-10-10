import OAI.Geometry.Symplectic.MorseBounds.FlowLinearization

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.Dynamics
open Filter Topology
noncomputable section

theorem exp_sub_one_isUnit_small {R : Type*} [NormedRing R]
    [NormedAlgebra ℝ R] [CompleteSpace R] (A : R) (hA : IsUnit A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      IsUnit (NormedSpace.exp (t • A) - 1) := by
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A)) A 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const A (0 : ℝ)
  have ht : Tendsto (fun t : ℝ => t⁻¹ • (NormedSpace.exp (t • A) - 1))
      (𝓝[≠] 0) (𝓝 A) := by
    have h := hd.tendsto_slope
    change Tendsto (fun t => slope (fun u : ℝ => NormedSpace.exp (u • A)) 0 t) _ _ at h
    simpa only [slope_def_module, sub_zero, zero_smul, NormedSpace.exp_zero] using h
  have he : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      IsUnit (t⁻¹ • (NormedSpace.exp (t • A) - 1)) :=
    ht (Units.isOpen.mem_nhds hA)
  obtain ⟨U, hU, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp he
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨δ, hδ, ?_⟩
  intro t ht0 htδ
  have hscaled : IsUnit (t⁻¹ • (NormedSpace.exp (t • A) - 1)) := by
    apply hsub
    refine ⟨hball ?_, ?_⟩
    · simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0] using htδ
    · simpa using ht0.ne'
  have htu : IsUnit (algebraMap ℝ R t) :=
    (isUnit_iff_ne_zero.mpr ht0.ne').map (algebraMap ℝ R)
  have h := htu.mul hscaled
  rw [← Algebra.smul_def, smul_inv_smul₀ ht0.ne'] at h
  exact h

theorem exp_sub_one_isUnit_small_finite {R ι : Type*} [NormedRing R]
    [NormedAlgebra ℝ R] [CompleteSpace R] (S : Finset ι) (A : ι → R)
    (hA : ∀ i ∈ S, IsUnit (A i)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ S, ∀ t : ℝ, 0 < t → t < δ →
      IsUnit (NormedSpace.exp (t • A i) - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨δ, hδ, hδA⟩ := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
    obtain ⟨ε, hε, hεA⟩ := exp_sub_one_isUnit_small (A i) (hA i (Finset.mem_insert_self _ _))
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro j hj t ht htδ
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hεA t ht (lt_of_lt_of_le htδ (min_le_right _ _))
    · exact hδA j hj t ht (lt_of_lt_of_le htδ (min_le_left _ _))

theorem short_loop_constant {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {w : ℝ → E} {V : E → E} {τ C : ℝ}
    (hτ : 0 < τ) (hC : 0 ≤ C) (hsmall : τ * C < 1)
    (hw : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt w (τ • V (w t)) t)
    (hV : ContinuousOn (fun t => V (w t)) (Set.Icc (0 : ℝ) 1))
    (hLip : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ a ∈ Set.Icc (0 : ℝ) 1,
      ‖V (w t) - V (w a)‖ ≤ C * ‖w t - w a‖)
    (hloop : w 1 = w 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, V (w t) = 0 ∧ w t = w 0 := by
  have hiV : IntervalIntegrable (fun t => V (w t)) MeasureTheory.volume 0 1 :=
    hV.intervalIntegrable_of_Icc zero_le_one
  have hi : IntervalIntegrable (fun t => τ • V (w t)) MeasureTheory.volume 0 1 :=
    hiV.smul τ
  have havgτ : τ • (∫ t in (0 : ℝ)..1, V (w t)) = 0 := by
    rw [← intervalIntegral.integral_smul]
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hw t (by simpa using ht)) hi
    simpa only [hloop, sub_self] using h
  have havg : (∫ t in (0 : ℝ)..1, V (w t)) = 0 := (smul_eq_zero.mp havgτ).resolve_left hτ.ne'
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)) hV.norm
  let S : ℝ := ‖V (w t₀)‖
  have hS : 0 ≤ S := norm_nonneg _
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖V (w t)‖ ≤ S := hmax
  have hwbound : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖w t - w a‖ ≤ τ * S := by
    intro a ha t ht
    have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u hu => (hw u hu).hasDerivWithinAt)
      (C := τ * S) (fun u hu => ?_) (convex_Icc (0 : ℝ) 1) ha ht
    · have hab : ‖t - a‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [ha.1, ha.2, ht.1, ht.2]
      exact hm.trans (mul_le_of_le_one_right (mul_nonneg hτ.le hS) hab)
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
      exact mul_le_mul_of_nonneg_left (hbound u hu) hτ.le
  have hvbound : ‖V (w t₀)‖ ≤ C * τ * S := by
    have hb : ∀ a ∈ Set.uIoc (0 : ℝ) 1,
        ‖V (w t₀) - V (w a)‖ ≤ C * τ * S := by
      intro a ha
      have ha' : a ∈ Set.Icc (0 : ℝ) 1 := by
        simp only [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at ha
        exact ⟨ha.1.le, ha.2⟩
      exact (hLip t₀ ht₀ a ha').trans (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hwbound a ha' t₀ ht₀) hC)
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [intervalIntegral.integral_sub (intervalIntegrable_const) hiV,
      intervalIntegral.integral_const, havg, sub_zero] at hn
    simpa only [sub_zero, one_smul, abs_one, mul_one] using hn
  have hS0 : S = 0 := by
    change S ≤ C * τ * S at hvbound
    nlinarith
  intro t ht
  constructor
  · apply norm_eq_zero.mp
    exact le_antisymm (hS0 ▸ hbound t ht) (norm_nonneg _)
  · apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hh := hwbound 0 ⟨le_rfl, zero_le_one⟩ t ht
    rw [hS0, mul_zero] at hh
    exact le_antisymm hh (norm_nonneg _)

end
end MorseArnold.Dynamics

namespace MorseArnold.Dynamics
open scoped Manifold ContDiff
open Filter Topology Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def coordinateVectorField (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (p : M) (y : E) : E :=
  tangentCoordChange 𝓘(ℝ, E) ((extChartAt 𝓘(ℝ, E) p).symm y) p
    ((extChartAt 𝓘(ℝ, E) p).symm y) (V ((extChartAt 𝓘(ℝ, E) p).symm y))

omit [CompleteSpace E] in
theorem coordinateVectorField_contDiffAt
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) (p : M) :
    ContDiffAt ℝ ∞ (coordinateVectorField V p) ((extChartAt 𝓘(ℝ, E) p) p) := by
  have hs := (contMDiffAt_iff.mp (hV.contMDiffAt (x := p))).2
  exact (hs.contDiffAt (by simp)).snd

omit [CompleteSpace E] in
theorem coordinateVectorField_apply
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (p x : M)
    (hx : x ∈ (extChartAt 𝓘(ℝ, E) p).source) :
    coordinateVectorField V p ((extChartAt 𝓘(ℝ, E) p) x) =
      tangentCoordChange 𝓘(ℝ, E) x p x (V x) := by
  exact congrArg (fun y : M => tangentCoordChange 𝓘(ℝ, E) y p y (V y : E))
    ((extChartAt 𝓘(ℝ, E) p).left_inv hx)

omit [CompleteSpace E] in
theorem integralCurve_coordinate_derivative
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ V) (p : M) (t : ℝ)
    (hsrc : γ t ∈ (extChartAt 𝓘(ℝ, E) p).source) :
    HasDerivAt ((extChartAt 𝓘(ℝ, E) p) ∘ γ)
      (coordinateVectorField V p ((extChartAt 𝓘(ℝ, E) p) (γ t))) t := by
  rw [coordinateVectorField_apply V p (γ t) hsrc]
  have ht := (hγ.isMIntegralCurveAt t).hasMFDerivAt
  have hc := hasMFDerivAt_extChartAt (I := 𝓘(ℝ, E))
    (extChartAt_source 𝓘(ℝ, E) p ▸ hsrc)
  erw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (hc.comp t ht).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  rw [mfderiv_chartAt_eq_tangentCoordChange
    (extChartAt_source 𝓘(ℝ, E) p ▸ hsrc)]
  exact map_smul (tangentCoordChange 𝓘(ℝ, E) (γ t) p (γ t))
    (show ℝ from a) (show E from V (γ t))

omit [CompleteSpace E] in
theorem coordinateVectorField_eq_zero_iff
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (p x : M)
    (hx : x ∈ (extChartAt 𝓘(ℝ, E) p).source) :
    coordinateVectorField V p ((extChartAt 𝓘(ℝ, E) p) x) = 0 ↔ V x = 0 := by
  rw [coordinateVectorField_apply V p x hx]
  constructor
  · intro h
    have hh := congrArg (tangentCoordChange 𝓘(ℝ, E) p x x) h
    erw [tangentCoordChange_comp ⟨⟨mem_extChartAt_source x, hx⟩,
      mem_extChartAt_source x⟩, tangentCoordChange_self (mem_extChartAt_source x), map_zero] at hh
    exact hh
  · intro h
    erw [h, map_zero]

theorem local_short_period
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (K : Set M) (Φ : ℝ × K → M)
    (hΦ : Continuous Φ) (h0 : ∀ x : K, Φ (0, x) = (x : M))
    (hCurve : ∀ x : K, IsMIntegralCurve (fun t => Φ (t, x)) V) (p : K) :
    ∃ U : Set K, U ∈ 𝓝 p ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ U, ∀ τ : ℝ, 0 < τ → τ < δ →
        Φ (τ, x) = (x : M) → V x = 0 := by
  let c := extChartAt 𝓘(ℝ, E) (p : M)
  let W := coordinateVectorField V (p : M)
  obtain ⟨C, s, hs, hLip⟩ :=
    ((coordinateVectorField_contDiffAt V hV p).of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
  let O : Set M := c.source ∩ c ⁻¹' s
  have hO : O ∈ 𝓝 (p : M) :=
    inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) (p : M))
      ((continuousAt_extChartAt (I := 𝓘(ℝ, E)) (p : M)).preimage_mem_nhds hs)
  have hpre : Φ ⁻¹' O ∈ 𝓝 (0, p) := by
    apply hΦ.continuousAt.preimage_mem_nhds
    rwa [h0]
  obtain ⟨T, hT, U, hU, hTU⟩ := mem_nhds_prod_iff.mp hpre
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hT
  refine ⟨U, hU, min ε (1 / ((C : ℝ) + 1)), lt_min hε (by positivity), ?_⟩
  intro x hx τ hτ hτε hloop
  have hτC : τ * (C : ℝ) < 1 := by
    have hp : 0 < (C : ℝ) + 1 := by positivity
    have ht := (lt_div_iff₀ hp).mp (lt_of_lt_of_le hτε (min_le_right _ _))
    nlinarith [C.coe_nonneg]
  have hm : ∀ t ∈ Icc (0 : ℝ) 1, Φ (τ * t, x) ∈ O := by
    intro t ht
    apply hTU
    exact ⟨hball (by
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hτ.le ht.1)]
      exact (mul_le_of_le_one_right hτ.le ht.2).trans_lt
        (lt_of_lt_of_le hτε (min_le_left _ _))), hx⟩
  let w : ℝ → E := fun t => c (Φ (τ * t, x))
  have hw : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt w (τ • W (w t)) t := by
    intro t ht
    exact (integralCurve_coordinate_derivative V (hCurve x) p (τ * t) (hm t ht).1).scomp t
      (by simpa using (hasDerivAt_id t).const_mul τ)
  have hws : MapsTo w (Icc (0 : ℝ) 1) s := fun t ht => (hm t ht).2
  have hcont : ContinuousOn w (Icc (0 : ℝ) 1) :=
    fun t ht => (hw t ht).continuousAt.continuousWithinAt
  have hwloop : w 1 = w 0 := by simp only [w, mul_one, mul_zero, hloop, h0]
  have hz := (short_loop_constant hτ C.coe_nonneg hτC hw
    (hLip.continuousOn.comp hcont hws) (fun t ht a ha => hLip.norm_sub_le (hws ht) (hws ha))
    hwloop) 0 ⟨le_rfl, zero_le_one⟩
  apply (coordinateVectorField_eq_zero_iff V p x ?_).mp
  · simpa only [w, mul_zero, h0, W, c] using hz.1
  · simpa only [mul_zero, h0] using (hm 0 ⟨le_rfl, zero_le_one⟩).1

theorem compact_short_period [T2Space M]
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (K : Set M) (hK : IsCompact K) (Φ : ℝ × K → M)
    (hΦ : Continuous Φ) (h0 : ∀ x : K, Φ (0, x) = (x : M))
    (_hInv : ∀ t (x : K), Φ (t, x) ∈ K)
    (hCurve : ∀ x : K, IsMIntegralCurve (fun t => Φ (t, x)) V) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ x : K, ∀ τ : ℝ, 0 < τ → τ < τ₀ →
      (Φ (τ, x) = (x : M) ↔ V x = 0) := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  choose U hU δ hδ hlocal using (fun p : K => local_short_period V hV K Φ hΦ h0 hCurve p)
  obtain ⟨T, hcover⟩ := CompactSpace.elim_nhds_subcover U hU
  have hb : ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ p ∈ T, τ₀ ≤ δ p := by
    clear hcover
    induction T using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert p T hp ih =>
      obtain ⟨a, ha, hle⟩ := ih
      refine ⟨min a (δ p), lt_min ha (hδ p), ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hle q hq)
  obtain ⟨τ₀, hτ₀, hle⟩ := hb
  refine ⟨τ₀, hτ₀, ?_⟩
  intro x τ hτ ht
  constructor
  · intro hfix
    have hx : x ∈ ⋃ p ∈ T, U p := by rw [hcover]; trivial
    obtain ⟨p, hp⟩ := mem_iUnion.mp hx
    obtain ⟨hpT, hxp⟩ := mem_iUnion.mp hp
    exact hlocal p x hxp τ hτ (ht.trans_le (hle p hpT)) hfix
  · intro hz
    have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
      (hV.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)) (hCurve x)
      (isMIntegralCurve_const hz) (h0 x)
    exact congrFun heq τ

end
end MorseArnold.Dynamics
namespace MorseArnold.Dynamics
open scoped Manifold ContDiff
open Filter Topology Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [CompleteSpace E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem coordinate_flow_smooth (Φ : ℝ × M → M)
    (hΦ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Φ)
    (hzero : ∀ x, Φ (0, x) = x) (p : M) :
    let c := extChartAt 𝓘(ℝ, E) p
    ContDiffAt ℝ ∞ (fun q : ℝ × E => c (Φ (q.1, c.symm q.2))) (0, c p) := by
  let c := extChartAt 𝓘(ℝ, E) p
  have hcp : c.symm (c p) = p := c.left_inv (mem_extChartAt_source p)
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c.symm (c p) :=
    (contMDiffWithinAt_extChartAt_symm_target_self p).contMDiffAt (extChartAt_target_mem_nhds p)
  have hg : ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × E => (q.1, c.symm q.2)) ((0 : ℝ), c p) :=
    contMDiffAt_fst.prodMk (hc.comp ((0 : ℝ), c p) contMDiffAt_snd)
  have hf := (hΦ.contMDiffAt (x := (0, c.symm (c p)))).comp (0, c p) hg
  have hout : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c (Φ (0, c.symm (c p))) := by
    rw [hzero, hcp]
    exact contMDiffAt_extChartAt
  have h := hout.comp (0, c p) hf
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.contDiffAt

theorem manifold_small_time_nondegenerate
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (Φ : ℝ × M → M)
    (hΦ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Φ)
    (hzero : ∀ x, Φ (0, x) = x)
    (hODE : ∀ x, IsMIntegralCurve (fun t => Φ (t, x)) V)
    (p : M) (hA : IsUnit (fderiv ℝ (coordinateVectorField V p) ((extChartAt 𝓘(ℝ, E) p) p))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ →
      let c := extChartAt 𝓘(ℝ, E) p
      IsUnit (fderiv ℝ (c ∘ (fun x => Φ (t, x)) ∘ c.symm) (c p) - ContinuousLinearMap.id ℝ E) := by
  let c := extChartAt 𝓘(ℝ, E) p
  let Ψ : ℝ × E → E := fun q => c (Φ (q.1, c.symm q.2))
  have h0 : ∀ᶠ y in 𝓝 (c p), Ψ (0, y) = y := by
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℝ, E)) p] with y hy
    dsimp [Ψ]
    rw [hzero, c.right_inv hy]
  have hΨODE : ∀ᶠ y in 𝓝 (c p),
      HasDerivAt (fun t => Ψ (t, y)) (coordinateVectorField V p (Ψ (0, y))) 0 := by
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℝ, E)) p] with y hy
    apply integralCurve_coordinate_derivative V (hODE (c.symm y)) p 0
    rw [hzero]
    exact c.map_target hy
  exact MorseArnold.FlowLinearization.small_time_nondegenerate_local
    (coordinateVectorField V p) Ψ (c p) (coordinate_flow_smooth Φ hΦ hzero p) h0 hΨODE hA

end
end MorseArnold.Dynamics

end

end OAI
