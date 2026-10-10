import Mathlib
import OAI.Geometry.NearbyLagrangian.FiniteTransport
import OAI.Geometry.NearbyLagrangian.GeneratingGeometry

namespace OAI

/-! Smooth nondegenerate critical sections at zero-section endpoints. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian

open Filter Set ContinuousLinearMap
open scoped Topology

variable {D V Z : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem derivative_zero_on_regular_level
    {f : D → V} {f' : D →L[ℝ] V} {q : D}
    (hf : HasStrictFDerivAt f f' q) (hs : Function.Surjective f')
    {g : D → Z} {g' : D →L[ℝ] Z} (hg : HasFDerivAt g g' q)
    (hzero : ∀ᶠ x in 𝓝 q, f x = f q → g x = 0)
    {v : D} (hv : f' v = 0) : g' v = 0 := by
  have hr : f'.range = ⊤ := LinearMap.range_eq_top.mpr hs
  let φ := hf.implicitFunction f f' hr (f q)
  have hφ : HasFDerivAt φ f'.ker.subtypeL 0 :=
    (hf.to_implicitFunction hr).hasFDerivAt
  have hφ0 : φ 0 = q := hf.implicitFunction_apply_image hr
  have ht : Tendsto φ (𝓝 0) (𝓝 q) := hφ0 ▸ hφ.continuousAt
  have hlevel : ∀ᶠ u : f'.ker in 𝓝 0, f (φ u) = f q := by
    have hp : Tendsto (fun u : f'.ker => (f q, u)) (𝓝 0) (𝓝 (f q, 0)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    exact hp.eventually (hf.map_implicitFunction_eq hr)
  have hz : (fun u => g (φ u)) =ᶠ[𝓝 (0 : f'.ker)] fun _ => 0 := by
    filter_upwards [ht.eventually hzero, hlevel] with u hu hfu
    exact hu hfu
  have hd : HasFDerivAt (fun u => g (φ u)) (g'.comp f'.ker.subtypeL) 0 := by
    apply HasFDerivAt.comp 0 _ hφ
    simpa only [hφ0] using hg
  have he : g'.comp f'.ker.subtypeL = 0 :=
    hd.unique ((hasFDerivAt_const (0 : Z) (0 : f'.ker)).congr_of_eventuallyEq hz)
  have := congrArg (fun A : f'.ker →L[ℝ] Z => A ⟨v,hv⟩) he
  simpa using this

end NearbyLagrangian

namespace NearbyLagrangian.Generating
open Filter ContinuousLinearMap
open scoped Topology ContDiff
variable {Q W : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [FiniteDimensional ℝ Q] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ Q] [FiniteDimensional ℝ W] in
lemma contDiffAt_vertical {f : Q × W → ℝ} {x : Q × W}
    (hf : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (vertical f) x := by
  exact (((compL ℝ W (Q × W) ℝ).flip (inr ℝ Q W)).contDiff.contDiffAt).comp x
    (hf.fderiv_right (m:=∞) (by simp))

theorem vertical_hessian_injective_of_zero_momentum
    {f : Q × W → ℝ} {x : Q × W} (hf : ContDiffAt ℝ ∞ f x)
    (hreg : Function.Surjective (fderiv ℝ (vertical f) x))
    (hx : vertical f x = 0)
    (hzero : ∀ᶠ y in 𝓝 x, vertical f y = 0 → momentum f y = 0) :
    Function.Injective ((fderiv ℝ (vertical f) x).comp (inr ℝ Q W)) := by
  have hvd := (contDiffAt_vertical hf).hasStrictFDerivAt (by simp)
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m:=1) (by exact WithTop.coe_le_coe.mpr le_top)).differentiableAt one_ne_zero
  have hpd := (momentum_hasFDerivAt hfd).differentiableAt.hasFDerivAt
  have hpk (v : Q × W) (hv : fderiv ℝ (vertical f) x v = 0) :
      fderiv ℝ (momentum f) x v = 0 := by
    apply NearbyLagrangian.derivative_zero_on_regular_level hvd hreg hpd _ hv
    filter_upwards [hzero] with y hy hyx
    exact hy (hyx.trans hx)
  have hi := generatingMap_ker_injective hf hreg
  intro u v huv
  have hk : fderiv ℝ (vertical f) x (0,u-v) = 0 := by
    have he := map_sub ((fderiv ℝ (vertical f) x).comp (inr ℝ Q W)) u v
    simpa only [comp_apply,inr_apply,huv,sub_self] using he
  have hg : fderiv ℝ (generatingMap f) x (0,u-v) = 0 := by
    rw [generatingMap_fderiv hfd, hpk _ hk]
    rfl
  have he : (⟨(0,u-v),hk⟩ : LinearMap.ker (fderiv ℝ (vertical f) x).toLinearMap) = 0 := by
    apply hi
    simpa only [ZeroMemClass.coe_zero,map_zero] using hg
  have he' := congrArg (fun z : LinearMap.ker (fderiv ℝ (vertical f) x).toLinearMap => z.val.2) he
  exact sub_eq_zero.mp he'

theorem vertical_hessian_bijective_of_zero_momentum
    {f : Q × W → ℝ} {x : Q × W} (hf : ContDiffAt ℝ ∞ f x)
    (hreg : Function.Surjective (fderiv ℝ (vertical f) x))
    (hx : vertical f x = 0)
    (hzero : ∀ᶠ y in 𝓝 x, vertical f y = 0 → momentum f y = 0) :
    Function.Bijective ((fderiv ℝ (vertical f) x).comp (inr ℝ Q W)) := by
  have hi := vertical_hessian_injective_of_zero_momentum hf hreg hx hzero
  have hdim : Module.finrank ℝ W = Module.finrank ℝ (W →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap : (W →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (W →L[ℝ] ℝ)).finrank_eq]
    exact Subspace.dual_finrank_eq.symm
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩

theorem contDiff_criticalSection_of_zero_momentum
    {f : Q × W → ℝ} (hf : ContDiff ℝ ∞ f) {s : Q → W}
    (hs : ∀ x, vertical f (x,s x) = 0)
    (hunique : ∀ x w, vertical f (x,w) = 0 → w = s x)
    (hreg : ∀ x, Function.Surjective (fderiv ℝ (vertical f) (x,s x)))
    (hzero : ∀ y, vertical f y = 0 → momentum f y = 0) :
    ContDiff ℝ ∞ s := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hv := contDiffAt_vertical (hf.contDiffAt (x:=(x,s x)))
  have hb := vertical_hessian_bijective_of_zero_momentum
    (hf.contDiffAt (x:=(x,s x))) (hreg x) (hs x) (Eventually.of_forall hzero)
  have hi : ((fderiv ℝ (vertical f) (x,s x)).comp (inr ℝ Q W)).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr hb.1)
      (LinearMap.range_eq_top.mpr hb.2), rfl⟩
  let σ : Q → W := hv.implicitFunction (by simp) hi
  have hσ : ContDiffAt ℝ ∞ σ x := hv.contDiffAt_implicitFunction (by simp) hi
  have heq : s =ᶠ[𝓝 x] σ := by
    filter_upwards [hv.eventually_apply_implicitFunction (by simp) hi] with y hy
    exact (hunique y (σ y) (hy.trans (hs x))).symm
  exact hσ.congr_of_eventuallyEq heq

theorem exists_smooth_nondegenerate_criticalSection
    {f : Q × W → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcritical : ∀ x, ∃! w, vertical f (x,w) = 0)
    (hreg : ∀ y, vertical f y = 0 →
      Function.Surjective (fderiv ℝ (vertical f) y))
    (hzero : ∀ y, vertical f y = 0 → momentum f y = 0) :
    ∃ s : Q → W, ContDiff ℝ ∞ s ∧
      (∀ x w, vertical f (x,w) = 0 ↔ w = s x) ∧
      ∀ x, Function.Bijective
        ((fderiv ℝ (vertical f) (x,s x)).comp (inr ℝ Q W)) := by
  classical
  choose s hs hsu using hcritical
  refine ⟨s,contDiff_criticalSection_of_zero_momentum hf hs hsu
    (fun x => hreg (x,s x) (hs x)) hzero,?_,?_⟩
  · intro x w
    exact ⟨hsu x w,fun h => h ▸ hs x⟩
  · intro x
    exact vertical_hessian_bijective_of_zero_momentum hf.contDiffAt
      (hreg (x,s x) (hs x)) (hs x) (Eventually.of_forall hzero)

end NearbyLagrangian.Generating

namespace NearbyLagrangian.Transport
open ContinuousLinearMap Set Filter
open scoped ContDiff Topology InnerProductSpace
variable {E W : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

omit [FiniteDimensional ℝ W] in
lemma phase_zero_momentum {U : Set E} {F : E × W → ℝ}
    (himage : Set.range (fun q : PhaseCritical U F => phaseGenerate F q.val) =
      Set.range (fun x : U => ((x:E),(0:E)))) :
    ∀ q : E × W, q.1 ∈ U → verticalDifferential F q.1 q.2 = 0 → baseDifferential F q.1 q.2 = 0 := by
  intro q hq hc
  have hh : phaseGenerate F q ∈ Set.range (fun x : U => ((x:E),(0:E))) := by
    rw [← himage]
    exact ⟨⟨q,hq,hc⟩,rfl⟩
  obtain ⟨x,hx⟩ := hh
  have hz : baseGradient F q.1 q.2 = 0 := (congrArg Prod.snd hx).symm
  rw [← innerSL_baseGradient,hz,map_zero]

omit [FiniteDimensional ℝ W] in
lemma phase_unique_critical {U : Set E} {F : E × W → ℝ}
    (hinj : Function.Injective (fun q : PhaseCritical U F => phaseGenerate F q.val))
    (himage : Set.range (fun q : PhaseCritical U F => phaseGenerate F q.val) =
      Set.range (fun x : U => ((x:E),(0:E)))) :
    ∀ x ∈ U, ∃! w, verticalDifferential F x w = 0 := by
  have hp := phase_zero_momentum himage
  intro x hx
  have hh : (x,(0:E)) ∈ Set.range (fun q : PhaseCritical U F => phaseGenerate F q.val) := by
    rw [himage]
    exact ⟨⟨x,hx⟩,rfl⟩
  obtain ⟨q,hq⟩ := hh
  have hqx : q.val.1 = x := congrArg Prod.fst hq
  have hc : verticalDifferential F x q.val.2 = 0 := by
    rw [← hqx]
    exact q.property.2
  refine ⟨q.val.2,hc,?_⟩
  intro w hw
  let r : PhaseCritical U F := ⟨(x,w),hx,hw⟩
  have he : phaseGenerate F r.val = phaseGenerate F q.val := by
    apply Prod.ext
    · exact hqx.symm
    · change baseGradient F x w = baseGradient F q.val.1 q.val.2
      apply (innerSL_inj (𝕜 := ℝ)).mp
      rw [innerSL_baseGradient,innerSL_baseGradient,hp (x,w) hx hw,hp q.val q.property.1 q.property.2]
  exact congrArg (fun a : PhaseCritical U F => a.val.2) (hinj he)

theorem open_zeroSection_endpoint {U : Set E} (hU : IsOpen U) {F : E × W → ℝ}
    (hF : ∀ x ∈ U, ∀ w, ContDiffAt ℝ ∞ F (x,w)) (hM : MorseOn U F)
    (hinj : Function.Injective (fun q : PhaseCritical U F => phaseGenerate F q.val))
    (himage : Set.range (fun q : PhaseCritical U F => phaseGenerate F q.val) =
      Set.range (fun x : U => ((x:E),(0:E)))) :
    ∃ s : E → W, (∀ x ∈ U, ContDiffAt ℝ ∞ s x) ∧
      (∀ x ∈ U, ∀ w, verticalDifferential F x w = 0 ↔ w = s x) ∧
      ∀ x ∈ U, Function.Bijective
        ((fderiv ℝ (fun q : E × W => verticalDifferential F q.1 q.2) (x,s x)).comp (inr ℝ E W)) := by
  classical
  have hc := phase_unique_critical hinj himage
  have he : ∀ x : E, ∃ w : W, x ∈ U →
      verticalDifferential F x w = 0 ∧ ∀ v, verticalDifferential F x v = 0 → v = w := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨w,hw,hu⟩ := hc x hx
      exact ⟨w,fun _ => ⟨hw,hu⟩⟩
    · exact ⟨0,fun hh => (hx hh).elim⟩
  choose s hs using he
  have hz (x : E) (hx : x ∈ U) :
      ∀ᶠ q : E × W in 𝓝 (x,s x), Generating.vertical F q = 0 → Generating.momentum F q = 0 := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)] with q hq hcrit
    exact phase_zero_momentum himage q hq hcrit
  have hb (x : E) (hx : x ∈ U) : Function.Bijective
      ((fderiv ℝ (Generating.vertical F) (x,s x)).comp (inr ℝ E W)) :=
    Generating.vertical_hessian_bijective_of_zero_momentum (hF x hx (s x))
      (hM x hx (s x) (hs x hx).1) (hs x hx).1 (hz x hx)
  refine ⟨s,?_,?_,hb⟩
  · intro x hx
    have hv := Generating.contDiffAt_vertical (hF x hx (s x))
    have hi : ((fderiv ℝ (Generating.vertical F) (x,s x)).comp (inr ℝ E W)).IsInvertible :=
      ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr (hb x hx).1)
        (LinearMap.range_eq_top.mpr (hb x hx).2),rfl⟩
    let σ : E → W := hv.implicitFunction (by simp) hi
    have hσ : ContDiffAt ℝ ∞ σ x := hv.contDiffAt_implicitFunction (by simp) hi
    have heq : s =ᶠ[𝓝 x] σ := by
      filter_upwards [hU.mem_nhds hx,hv.eventually_apply_implicitFunction (by simp) hi] with y hy hσy
      exact ((hs y hy).2 (σ y) (hσy.trans (hs x hx).1)).symm
    exact hσ.congr_of_eventuallyEq heq
  · intro x hx w
    exact ⟨(hs x hx).2 w,fun hh => hh ▸ (hs x hx).1⟩

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ W] in
lemma TameOn.mono {U V : Set E} {F g : E × W → ℝ} (T : TameOn U F g) (hVU : V ⊆ U) :
    TameOn V F g := by
  obtain ⟨c,C,M₀,M₁,hc,hC,hM₀,hM₁,hv,hb,hval,hder⟩ := T.estimates
  exact ⟨fun x hx w => T.smooth_F x (hVU hx) w,
    fun x hx w => T.smooth_g x (hVU hx) w,
    fun x hx => T.homogeneous x (hVU hx),
    c,C,M₀,M₁,hc,hC,hM₀,hM₁,fun x hx => hv x (hVU hx),
    fun x hx => hb x (hVU hx),fun q hq => hval q (hVU hq),fun q hq => hder q (hVU hq)⟩

omit [FiniteDimensional ℝ W] in
lemma phase_range_restrict {U V : Set E} {F : E × W → ℝ} (hVU : V ⊆ U) :
    Set.range (fun q : PhaseCritical V F => phaseGenerate F q.val) =
      Set.range (fun q : PhaseCritical U F => phaseGenerate F q.val) ∩ (V ×ˢ univ) := by
  ext z
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨⟨⟨q.val,hVU q.property.1,q.property.2⟩,rfl⟩,q.property.1,mem_univ _⟩
  · rintro ⟨⟨q,rfl⟩,hq⟩
    exact ⟨⟨q.val,hq.1,q.property.2⟩,rfl⟩

omit [FiniteDimensional ℝ W] in
lemma phase_injective_restrict {U V : Set E} {F : E × W → ℝ} (hVU : V ⊆ U)
    (hF : Function.Injective (fun q : PhaseCritical U F => phaseGenerate F q.val)) :
    Function.Injective (fun q : PhaseCritical V F => phaseGenerate F q.val) := by
  intro x y hxy
  have hh := hF (a₁ := ⟨x.val,hVU x.property.1,x.property.2⟩)
    (a₂ := ⟨y.val,hVU y.property.1,y.property.2⟩) hxy
  exact Subtype.ext (congrArg (fun q : PhaseCritical U F => q.val) hh)

theorem transported_central_zeroSection_endpoint {U V : Set E} (hU : IsOpen U)
    (hV : IsOpen V) (hVU : V ⊆ U)
    {S : Set (E × E)} (hS : IsCompact S) (hSU : ∀ z ∈ S, z.1 ∈ U)
    {H : ℝ × (E × E) → ℝ}
    (hH : ContDiffOn ℝ ∞ H (Icc (0:ℝ) 1 ×ˢ univ))
    (hs : ∀ t ∈ Icc (0:ℝ) 1, Function.support (fun x => H (t,x)) ⊆ S)
    {ψ : ℝ → E × E → E × E}
    (hψ : ∀ z, ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivWithinAt (fun s => ψ s z) (hamiltonianField H (t,ψ t z)) (Icc (0:ℝ) 1) t)
    (hψ₀ : ∀ z, ψ 0 z = z) (hψ₁ : Function.Injective (ψ 1))
    {F g : E × W → ℝ} (T : TameOn U F g) (hM : MorseOn U F)
    (hinj : Function.Injective (fun q : PhaseCritical U F => phaseGenerate F q.val))
    (hcentral : Set.range (fun q : PhaseCritical U F => ψ 1 (phaseGenerate F q.val)) ∩
      (V ×ˢ univ) = Set.range (fun x : V => ((x:E),(0:E)))) :
    ∃ (n : ℕ) (F' : E × TransportFiber E W n → ℝ) (s : E → TransportFiber E W n),
      TameOn V F' (iterReference g n) ∧ MorseOn V F' ∧
      (∀ x ∈ V, ContDiffAt ℝ ∞ s x) ∧
      (∀ x ∈ V, ∀ w, verticalDifferential F' x w = 0 ↔ w = s x) ∧
      ∀ x ∈ V, Function.Bijective
        ((fderiv ℝ (fun q : E × TransportFiber E W n => verticalDifferential F' q.1 q.2)
          (x,s x)).comp (inr ℝ E (TransportFiber E W n))) := by
  obtain ⟨n,F',T',M',e,he⟩ := tame_hamiltonian_transport_endpoint hU hS hSU hH hs T hM
  have hconj (q : PhaseCritical U F) : phaseGenerate F' (e q).val = ψ 1 (phaseGenerate F q.val) :=
    he q (fun t => ψ t (phaseGenerate F q.val)) (hψ _) (hψ₀ _)
  have hnewinj := phaseGenerate_injective_of_conjugacy e hψ₁ hconj hinj
  have hrange : Set.range (fun q : PhaseCritical U F' => phaseGenerate F' q.val) =
      Set.range (fun q : PhaseCritical U F => ψ 1 (phaseGenerate F q.val)) := by
    ext z
    constructor
    · rintro ⟨q,rfl⟩
      obtain ⟨r,rfl⟩ := e.surjective q
      exact ⟨r,(hconj r).symm⟩
    · rintro ⟨q,rfl⟩
      exact ⟨e q,hconj q⟩
  have hnewimage : Set.range (fun q : PhaseCritical V F' => phaseGenerate F' q.val) =
      Set.range (fun x : V => ((x:E),(0:E))) := by
    rw [phase_range_restrict hVU,hrange]
    exact hcentral
  have TV := T'.mono hVU
  have MV : MorseOn V F' := fun x hx => M' x (hVU hx)
  obtain ⟨s,hsm,hsc,hsh⟩ := open_zeroSection_endpoint hV TV.smooth_F MV
    (phase_injective_restrict hVU hnewinj) hnewimage
  exact ⟨n,F',s,TV,MV,hsm,hsc,hsh⟩

end NearbyLagrangian.Transport

end

end OAI
