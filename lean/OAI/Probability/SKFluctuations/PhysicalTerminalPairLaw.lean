import Mathlib
import OAI.Probability.SKFluctuations.PhysicalOverlapClockSchedule

namespace OAI

/-! Physical Terminal Pair Law. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

 def terminalPairTest {P : Type} (steps : List (GaussianStep ι)) (Q : S → S → ℝ)
    (z : (P × ForwardPath (ι → ℝ) S steps.length) ×
      (P × ForwardPath (ι → ℝ) S steps.length)) : ℝ :=
  Q (ForwardPath.spin steps.length z.1.2) (ForwardPath.spin steps.length z.2.2)

 omit [Fintype ι] [Nonempty S] in
 theorem terminalPairTest_measurable [Fintype ι] [Nonempty S] {P : Type} [MeasurableSpace P]
    (steps : List (GaussianStep ι)) (Q : S → S → ℝ) :
    Measurable (terminalPairTest (P:=P) steps Q) :=
  (measurable_of_countable (Function.uncurry Q)).comp
    (((ForwardPath.spin_measurable steps.length).comp (measurable_snd.comp measurable_fst)).prodMk
      ((ForwardPath.spin_measurable steps.length).comp (measurable_snd.comp measurable_snd)))

 omit [Fintype ι] [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S] in
 theorem terminalPairTest_abs_le [Fintype ι] [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S]
    {P : Type} (steps : List (GaussianStep ι))
    (Q : S → S → ℝ) (z : (P × ForwardPath (ι → ℝ) S steps.length) ×
      (P × ForwardPath (ι → ℝ) S steps.length)) :
    |terminalPairTest steps Q z| ≤ ∑ σ, ∑ τ, |Q σ τ| := by
  let σ := ForwardPath.spin steps.length z.1.2
  let τ := ForwardPath.spin steps.length z.2.2
  exact (Finset.single_le_sum (fun ρ _ => abs_nonneg (Q σ ρ)) (Finset.mem_univ τ)).trans
    (Finset.single_le_sum (fun ρ _ => Finset.sum_nonneg fun η _ => abs_nonneg (Q ρ η)) (Finset.mem_univ σ))

 theorem integral_terminalFork_zero {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x)
    (Q : S → S → ℝ) :
    (∫ p, conditionalForkTest w φ steps x 0 (terminalPairTest steps Q) p
      ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) =
      ∫ p, hierarchyPairMean w φ Q steps (x p) ∂μ := by
  have := hierarchyPathKernel_markov hw φ steps ha
  rw [Measure.integral_compProd
    (conditionalForkTest_integrable hw φ steps ha μ x hx 0
      (terminalPairTest_measurable steps Q) (terminalPairTest_abs_le steps Q))]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro p
  simp only [Kernel.comap_apply,conditionalForkTest]
  have hz (t : P × ForwardPath (ι → ℝ) S steps.length) :
      conditionalPathAverage w φ steps x 0 (fun q => terminalPairTest steps Q (t,q)) t =
        gaussianHierarchyMean w φ (Q (ForwardPath.spin steps.length t.2)) steps (x t.1) := by
    cases steps with
    | nil => simpa only [conditionalPathAverage,terminalPairTest] using
        integral_hierarchyPathKernel hw φ (Q (ForwardPath.spin [].length t.2)) [] ha (x t.1)
    | cons st tail => simpa only [conditionalPathAverage,terminalPairTest] using
        integral_hierarchyPathKernel hw φ (Q (ForwardPath.spin (st::tail).length t.2)) (st::tail) ha (x t.1)
  simp_rw [hz]
  rw [integral_hierarchyPathKernel hw φ
    (fun σ => gaussianHierarchyMean w φ (Q σ) steps (x p)) steps ha,
    hierarchyPairMean_eq_nested hw φ Q steps ha]

 theorem integral_terminalFork_eq_levelPairMean {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x)
    (j : ℕ) (hj : j ≤ steps.length) (Q : S → S → ℝ) :
    (∫ p, conditionalForkTest w φ steps x j (terminalPairTest steps Q) p
      ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) =
      ∫ p, levelPairMean w φ Q steps j (x p) ∂μ := by
  induction steps generalizing P a j with
  | nil =>
    have : j=0 := by simpa using hj
    subst j
    exact integral_terminalFork_zero hw φ [] ha μ x hx Q
  | cons st tail ih =>
    cases j with
    | zero => exact integral_terminalFork_zero hw φ (st::tail) ha μ x hx Q
    | succ j =>
      rcases st with ⟨m,q⟩
      have := hierarchyPathKernel_markov hw φ ((m,q)::tail) ha
      have := hierarchyPathKernel_markov hw φ tail ha.2.2.2
      have := plantedStepKernel_markov hw φ m q tail ha
      let ν := μ ⊗ₘ (hierarchyPathKernel w φ ((m,q)::tail)).comap x hx
      let μ' := μ ⊗ₘ (plantedStepKernel w φ m q tail).comap x hx
      let x' : P × (ι → ℝ) → ι → ℝ := fun p => x p.1+p.2
      have hx' : Measurable x' := (hx.comp measurable_fst).add measurable_snd
      let e : (P × ForwardPath (ι → ℝ) S (((m,q)::tail).length)) ≃ᵐ
          ((P × (ι → ℝ)) × ForwardPath (ι → ℝ) S tail.length) := MeasurableEquiv.prodAssoc.symm
      have hmap : ν.map e = μ' ⊗ₘ (hierarchyPathKernel w φ tail).comap x' hx' :=
        hierarchyPathLaw_cons hw φ m q tail ha μ x hx
      have he := ih ha.2.2.2 μ' x' hx' j (by simpa using hj)
      rw [←hmap,integral_map e.measurable.aemeasurable
        (conditionalForkTest_measurable hw φ tail ha.2.2.2 x' hx' j
          (terminalPairTest_measurable tail Q)).aestronglyMeasurable] at he
      change (∫ p, conditionalForkTest w φ ((m,q)::tail) x (j+1)
        (terminalPairTest ((m,q)::tail) Q) p ∂ν) = _ at he
      rw [he]
      have hs := levelPairMean_smooth hw φ Q tail ha.2.2.2 j 0
      obtain ⟨R,hR0,hR⟩ := hs.bound
      have hi : Integrable (fun p => levelPairMean w φ Q tail j (x' p)) μ' :=
        Integrable.of_bound (hs.continuous.measurable.comp hx').aestronglyMeasurable R
          (Eventually.of_forall fun p => hR (x' p))
      rw [Measure.integral_compProd hi]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro p
      simp only [Kernel.comap_apply]
      rw [plantedStepKernel_eq_tilted hw φ m q tail ha,
        integral_tiltedLaw (F:=fun z => gaussianHierarchy w φ tail (x p+z))
          ((gaussianHierarchy_continuous hw φ tail ha.2.2.2).comp
            (continuous_const.add continuous_id)).measurable
          (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q (x p))]
      rfl
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem physicalOverlapMoment_eq_stepPairDisorder (n l : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 (pre++tail))
    (q₀ : FeatureIndex n → ℝ≥0) :
    physicalOverlapMoment n l (pre++tail) (Measure.pi fun i => gaussianReal 0 (q₀ i))
      id measurable_id pre.length =
      stepPairDisorder (uniformWeight n) (finiteFeature n) q₀ pre tail
        (fun σ τ => |orderedOverlap n σ τ|^(2*l)) 0 := by
  have he := integral_terminalFork_eq_levelPairMean (uniformWeight_pos n) (finiteFeature n)
    (pre++tail) ha (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id
    pre.length (by simp) (fun σ τ => |orderedOverlap n σ τ|^(2*l))
  unfold physicalOverlapMoment physicalPathLaw
  change (∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) (pre++tail) id pre.length
    (terminalPairTest (pre++tail) (fun σ τ => |orderedOverlap n σ τ|^(2*l))) p
    ∂(Measure.pi fun i => gaussianReal 0 (q₀ i)) ⊗ₘ
      (hierarchyPathKernel (uniformWeight n) (finiteFeature n) (pre++tail)).comap id measurable_id) = _
  rw [he]
  unfold stepPairDisorder zeroContinuation
  rw [stepPairMean_eq_levelPairMean (uniformWeight_pos n) (finiteFeature n) _ pre tail (ha.suffix pre tail)]
  simp only [zero_add,id_eq]

 theorem physicalOverlapMoment_eq_stepPairMoment (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (u : ℝ) :
    physicalOverlapMoment n l steps (Measure.pi fun i => gaussianReal 0 (q₀ i))
      id measurable_id (splitClockSteps u steps).1.length =
      stepPairMoment (uniformWeight n) (finiteFeature n) q₀ steps ha.mem_pos
        (fun σ τ => |orderedOverlap n σ τ|^(2*l)) u := by
  have ho : OrderedSteps 0 ((splitClockSteps u steps).1++(splitClockSteps u steps).2) := by
    simpa only [splitClockSteps_append] using ha
  have he := physicalOverlapMoment_eq_stepPairDisorder n l (splitClockSteps u steps).1
    (splitClockSteps u steps).2 ho q₀
  rw [splitClockSteps_append] at he
  rw [stepPairMoment_eq_split (uniformWeight_pos n) (finiteFeature n) q₀ steps ha]
  exact he

 theorem physicalRetainedOverlapMoment_tendsto (n l : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀ k, MassOrdered 0 (as k)) (hm : ∀ k, PartitionMesh (mesh k) 0 (as k))
    (he : ∀ k, partitionEnd 0 (as k)=1) (hmesh : Tendsto mesh atTop (𝓝 0))
    (u : PositiveMass) (hu : u.val≤1) (hnode : ∀ k, u ∈ as k) :
    let q := completedPathClock n b h
    Tendsto (fun k => let steps := sampleClockSteps q 0 (as k)
      physicalOverlapMoment n l steps (Measure.pi fun i => gaussianReal 0 (q 0 i))
        id measurable_id (splitClockSteps u.val steps).1.length)
      atTop (𝓝 (pathPairMoment (uniformWeight n) (finiteFeature n) q
        (fun σ τ => |orderedOverlap n σ τ|^(2*l)) u.val)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  dsimp only
  simp_rw [physicalOverlapMoment_eq_stepPairMoment n l _ (sampleClockSteps_ordered _ _ (ho _))]
  exact retainedMoment_tendsto_all (uniformWeight_pos n) (finiteFeature n) (completedPathClock n b h)
    (completedPathClock_monotone n hb hh) as mesh ho hm he hmesh u hu hnode
      (fun σ τ => |orderedOverlap n σ τ|^(2*l))

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem eventually_comparison_retained_overlap_band (l : ℕ) (Bclock : ℝ)
    {m C₀ Ct A F cl cu κ₀ : ℝ}
    (hm₀ : 0 < m) (hC₀ : 0 < C₀) (hCt : 0 ≤ Ct) (hA : 0 ≤ A)
    (hF : 0 ≤ F) (hcl : 0 < cl) (hcu : 0 ≤ cu) (hκ₀ : 0 < κ₀) :
    ∀ᶠ n : ℕ in atTop, ∀ (_hn : 0 < n) (E d xs s R H : ℝ) (e : ℝ → ℝ),
    0 < E → 0 < d → 0 < xs → xs ≤ s → 0 < e s → 0 < R → 0 ≤ H →
    Real.sqrt (n:ℝ)*E ≤ d^2 → (n:ℝ)^(-(2:ℝ)/3+m)*d ≤ C₀*E →
    comparisonLowerScale n E d ≤ s → (n:ℝ)*E^2 ≤ Ct*e xs*xs^2 →
    MonotoneOn (fun r => e r*r^2) (Icc xs s) →
    1+2*cu ≤ F → 1+1/R ≤ F →
    ∀ (J : ℕ), 1 ≤ J → ((J+3:ℕ):ℝ)^2 ≤ A*(Real.log (n:ℝ))^2 →
    R ≤ (2:ℝ)^J*s → (2:ℝ)^J*s ≤ 1 →
    ∀ (b h : ℝ → ℝ≥0), MonotoneOn b (Icc (0:ℝ) 1) → MonotoneOn h (Icc (0:ℝ) 1) →
    (h 1:ℝ)-(h 0:ℝ) ≤ Bclock →
    ∀ (us : List PositiveMass), (∀ v ∈ us, v.val ≤ 1) →
    ∀ (u : PositiveMass), u ∈ us → u.val < (cl/2)*s →
    ∀ {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (_hr : r₀ ≤ 1) (_hu : u₀ ≤ 1) (_hu₀ : 0 ≤ u₀) (_hc : 0 < c)
    (_hk : ContinuousOn k (Icc r₀ 1)) (_hkc : ∀ t ∈ Icc r₀ 1, c ≤ k t)
    (_hm : MonotoneOn M (Icc (0:ℝ) 1)) (_hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M),
    r₀ < s/2 →
    (∀ v ∈ Icc (s/2) ((2:ℝ)^J*s), cl*v ≤ α.val.val v ∧ α.val.val v ≤ cu*v) →
    (∀ v ∈ Icc (s/2) ((2:ℝ)^J*s), 0 ≤ e v) →
    AntitoneOn e (Icc (s/2) ((2:ℝ)^J*s)) →
    MonotoneOn (fun v => v*e v) (Icc (s/2) ((2:ℝ)^J*s)) →
    (∀ x ∈ Icc (s/2) ((2:ℝ)^J*s), ∀ y ∈ Icc (s/2) ((2:ℝ)^J*s), x ≤ y →
      (κ₀/Real.log (n:ℝ))*e y*(y-x) ≤ (h (α.val.val y):ℝ)-(h (α.val.val x):ℝ)) →
    (∀ᶠ j : ℕ in atTop,
      (physicalRawRatio n (l+1) (sampleClockSteps (completedPathClock n b h) 0 (finiteCutMasses us j))
        0 xs (Measure.pi fun i => gaussianReal 0 (completedPathClock n b h 0 i)) id measurable_id)^2 ≤ H) →
    pathPairMoment (uniformWeight n) (finiteFeature n) (completedPathClock n b h)
      (fun σ τ => |orderedOverlap n σ τ|^(2*(l+1))) u.val ≤
        ((2:ℝ)^(2*(l+1)-1)*(2*F^(2*(l+1))+1))*H^(2*(l+1))*s^(2*(l+1)) := by
  have hlog : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop 0)
  filter_upwards [eventually_comparison_physical_overlap_raw l Bclock hm₀ hC₀ hCt hA hF
    (show 0 < cl/2 by positivity) (show 0 < κ₀/16 by positivity),hlog] with n hnraw hnlog
  intro hn E d xs s R H e hE hd hxs hxss hes hR hH hupper hlower hscale htest hmono
    hFmass hFradius J hJ hdepth hRend hT b h hb hh hB us hus u humem hucl
    r₀ u₀ c k M hr hu hu₀ hc hk hkc hm hM α hr₀ hreg he hem her hgrowth hraw
  have hs : 0 < s := hxs.trans_le hxss
  have hκ : 0 < κ₀/Real.log (n:ℝ) := div_pos hκ₀ hnlog
  have h2s : 2*s ≤ (2:ℝ)^J*s := by
    exact mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hJ) hs.le
  have hu1 : u.val ≤ 1 := hus u humem
  have ht := physicalRetainedOverlapMoment_tendsto n (l+1) hn b h hb hh
    (finiteCutMasses us) (fun j => (((j+1:ℕ):ℝ)⁻¹))
    (finiteCutMasses_ordered us hus) (finiteCutMasses_mesh us hus)
    (finiteCutMasses_end us hus) uniformMasses_mesh_tendsto u hu1
    (fun j => finiteCutMasses_nodes us j humem)
  have hmesh : ∀ᶠ j : ℕ in atTop, (((j+1:ℕ):ℝ)⁻¹)/c ≤ s/8 := by
    have ht : Tendsto (fun j : ℕ => (((j+1:ℕ):ℝ)⁻¹)/c) atTop (𝓝 0) := by
      simpa using uniformMasses_mesh_tendsto.div_const c
    exact (ht.eventually (gt_mem_nhds (show (0:ℝ) < s/8 by positivity))).mono (fun j hj => hj.le)
  apply le_of_tendsto ht
  filter_upwards [hmesh,hraw] with j hj hQ
  let as := finiteCutMasses us j
  let has := finiteCutMasses_ordered us hus j
  let q := completedPathClock n b h
  let steps := sampleClockSteps q 0 as
  let hsteps := sampleClockSteps_ordered q as has
  let r := physicalQuantileGrid hr hu hc hk hkc hm hM α steps hsteps
  let df := fun st : GaussianStep (FeatureIndex n) => st.2 (Sum.inl ⟨0,hn⟩)
  have hgm : ∀ z : Fin (steps.length+1), r z.succ-r z.castSucc ≤ s/8 := by
    intro z
    exact (physicalQuantileGrid_mesh hr hu hc hk hkc hm hM α steps hsteps
      (sampled_physicalMass_mesh _ _ (finiteCutMasses_mesh us hus j)) z).trans hj
  have hclock := physicalConstrainedOverlapClocks n hn b h hb hh as has hr hu hu₀ hc hk hkc hm hM α
    hs h2s hT hr₀ hκ.le (show 0 ≤ s/8 by positivity) le_rfl hcl.le hcu hreg he hem her hgrowth hgm
  obtain ⟨hmass,hfirst,hdyad⟩ := hclock
  have hss : s ∈ Icc s ((2:ℝ)^J*s) := ⟨le_rfl,by linarith⟩
  have hfork : (splitClockSteps u.val steps).1.length ≤ radiusGridCut r s := by
    by_contra hle
    have horder := physicalCutMass_monotone steps hsteps (Nat.le_of_lt (lt_of_not_ge hle))
    rw [sampled_retained_mass q as has u (finiteCutMasses_nodes us j humem)] at horder
    exact (not_le_of_gt hucl) ((hmass s hss).1.trans horder)
  have htotal : physicalFieldDuration df steps ≤ Bclock := by
    rw [sampledFieldDuration_total n hn b h hb hh as has (finiteCutMasses_end us hus j)]
    exact hB
  let D₀ := ((κ₀/Real.log (n:ℝ))/16)*e s*s
  have hD : 0 < D₀ := by dsimp [D₀]; positivity
  have hresult := hnraw E d xs s D₀ e hE hd hxs hxss hes hD hupper hlower hscale htest hmono
    (by dsimp [D₀]; apply le_of_eq; ring) _ steps 0 cu R hsteps hcu hR hFmass hFradius
    J hJ hdepth (radiusGridCut r) (radiusGridCut_monotone r) (radiusGridCut_le r) hRend
    _ hfork df (sampledFieldClock_aligned n hn b h as 0) htotal
    (fun v hv => (hmass v hv).1) (fun v hv => (hmass v hv).2) hfirst hdyad
    (Measure.pi fun i => gaussianReal 0 (q 0 i)) id measurable_id
  have hpow := pow_le_pow_left₀ (sq_nonneg _) hQ (2*(l+1))
  rw [← pow_mul,show 2*(2*(l+1))=4*(l+1) by omega] at hpow
  apply hresult.trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)

end SKFluctuations

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable

 theorem completedPathOverlapMoment_le_one (n l : ℕ) (hn : 0 < n)
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (u : PositiveMass) (hu : u.val ≤ 1) :
    pathPairMoment (uniformWeight n) (finiteFeature n) (completedPathClock n b h)
      (fun σ τ => |orderedOverlap n σ τ|^(2*l)) u.val ≤ 1 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  classical
  let D : FeatureIndex n → ℝ := fun i => ∑ σ, |finiteFeature n σ (Pi.single i 1)|
  have hD : ∀ i, 0 ≤ D i := by intro i; exact Finset.sum_nonneg fun σ _ => abs_nonneg _
  have hφ : ∀ σ i, |finiteFeature n σ (Pi.single i 1)| ≤ D i := by
    intro σ i
    exact Finset.single_le_sum (fun τ _ => abs_nonneg (finiteFeature n τ (Pi.single i 1))) (Finset.mem_univ σ)
  have htest : ∀ σ τ : Spin n, abs (|orderedOverlap n σ τ|^(2*l)) ≤ 1 := by
    intro σ τ
    rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact pow_le_one₀ (abs_nonneg _) (orderedOverlap_abs_le_one n σ τ)
  exact (le_abs_self _).trans (pathPairMoment_bound (uniformWeight_pos n) (finiteFeature n) D hD (fun σ i => by
      simpa [finiteFeature_apply, Pi.single_apply] using hφ σ i)
    (completedPathClock n b h) (completedPathClock_monotone n hb hh) _ (by norm_num) htest ⟨u.property,hu⟩)

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem comparison_minimum_retained_overlap_moment_normalized
    (ℓ : ℕ) (Bclock : ℝ) {m δ cl cu Az κ₀ C₀ Ct D : ℝ}
    (hm₀ : 0 < m) (hδ : 0 < δ) (hδm : δ < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hκ₀ : 0 < κ₀) (hC₀ : 0 < C₀) (hCt : 0 ≤ Ct) :
    ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop, ∀ {E d r₀ u₀ : ℝ}
    (hn : 0 < n) (hE : 0 < E) (hd : 0 < d)
    (hr₀ : r₀ ∈ Icc (0:ℝ) (1/4)) (hu₀ : u₀ ∈ Icc (0:ℝ) (1/4)) (g : ℝ → ℝ),
    let N := (n:ℝ)
    let U := comparisonSmallMass N E
    let L := comparisonConstraintLength N E d
    let hN : 0 < N := by dsimp only [N]; exact_mod_cast hn
    let hU := comparisonSmallMass_pos hN hE
    let hL := comparisonConstraintLength_pos hN hE hd
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let c := k 1
    let hr : r₀ ≤ 1 := le_trans hr₀.2 (by norm_num)
    let hu : u₀ ∈ Icc (0:ℝ) 1 := ⟨hu₀.1,le_trans hu₀.2 (by norm_num)⟩
    let hc : 0 < c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
    let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
    let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd.le
    let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd.le (show (0:ℝ) ≤ 1 by norm_num)
    ∀ (α : inverseIntegralConstraints r₀ u₀ k M)
    (hg : ContDiff ℝ 1 g)
    (hgpos : ∀ r ∈ Icc r₀ 1, 0<g r)
    (hp : ∀ r ∈ Ioc r₀ 1, comparisonLogSlope g r ∈ Icc (0:ℝ) 1)
    (b h : ℝ → ℝ)
    (hb : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => b u-omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) u) (Icc (0:ℝ) 1))
    (hh : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => h u+omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
          (hg.continuous.mul continuous_id) β) u) (Icc (0:ℝ) 1))
    (hbn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ b 0-omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) 0)
    (hhn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ h 0+omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) β) 0)
    (hmin : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 α ≤
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 β),
    let b' := fun u => (b u-omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) u).toNNReal
    let h' := fun u => (h u+omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) α) u).toNNReal
    ∀ (u : PositiveMass) (huobs : u.val ≤ 1) (xs z : ℝ),
      0 < xs → comparisonLowerScale n E d ≤ xs → u₀ ≤ xs → r₀ ≤ U →
      z ∈ Icc r₀ 1 → z ≤ Az*xs → d ≤ D →
      Real.sqrt (n:ℝ)*E ≤ d^2 → (n:ℝ)^(-(2:ℝ)/3+m)*d ≤ C₀*E →
      (n:ℝ)*E^2 ≤ Ct*g xs*xs^2 →
      (∀ r ∈ Icc z 1, cl*r ≤ α.val.val r ∧ α.val.val r ≤ cu*r) →
      (∀ r ∈ Icc z 1, κ₀/Real.log (n:ℝ) ≤ 1-comparisonLogSlope g r) →
      MonotoneOn h (Icc u₀ 1) → (h' 1:ℝ)-(h' 0:ℝ) ≤ Bclock →
      pathPairMoment (uniformWeight n) (finiteFeature n) (completedPathClock n b' h')
        (fun σ τ => |orderedOverlap n σ τ|^(2*(ℓ+1))) u.val ≤ C*(xs+u.val)^(2*(ℓ+1)) := by
  obtain ⟨C,hC,hraw⟩ := comparison_minimum_finite_raw_ratio (D:=D) ℓ Bclock hm₀ hδ hδm
    hcl hcu hAz hκ₀ hC₀ hCt
  let B := 2+2*Az+4/cl
  have hB : 1 ≤ B := by dsimp [B]; have := div_pos (by norm_num : (0:ℝ) < 4) hcl; linarith
  have hBA : 2*Az < B := by dsimp [B]; have := div_pos (by norm_num : (0:ℝ) < 4) hcl; linarith
  have hBcl : 1 < (cl/2)*B := by
    have he : cl*(4/cl)=4 := mul_div_cancel₀ (4:ℝ) hcl.ne'
    dsimp [B]
    nlinarith only [he,hcl,mul_nonneg hcl.le hAz]
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  let F := 5+2*cu
  have hF : 0 ≤ F := by dsimp [F]; linarith
  have hFmass : 1+2*cu ≤ F := by dsimp [F]; linarith
  have hFradius : 1+1/(1/4:ℝ) ≤ F := by dsimp [F]; norm_num; linarith
  let L := (2:ℝ)^(2*(ℓ+1)-1)*(2*F^(2*(ℓ+1))+1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let K := (4*B)^(2*(ℓ+1))+L*(2*C)^(2*(ℓ+1))*B^(2*(ℓ+1))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hraw,eventually_comparison_retained_overlap_band ℓ Bclock
      hm₀ hC₀ hCt (sq_nonneg (1/Real.log 2+4)) hF hcl hcu.le hκ₀,
    eventually_comparisonSmallMass_small hC₀ hm₀ (show (0:ℝ) < 1 by norm_num),
    eventually_comparisonLowerScale_depth hC₀ hm₀,hlog] with n hnraw hnov hnsmall hndepth hnlog
  intro E d r₀ u₀ hn hE hd hr₀ hu₀ g
  dsimp only
  intro α hg hgpos hp b h hb hh hbn hhn hmin
  let N := (n:ℝ)
  let U := comparisonSmallMass N E
  let Len := comparisonConstraintLength N E d
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast hn
  have hU := comparisonSmallMass_pos hN hE
  have hLen := comparisonConstraintLength_pos hN hE hd
  let k := comparisonFloor N δ U
  let M := comparisonCap N δ U Len E d
  let c := k 1
  let hr : r₀ ≤ 1 := le_trans hr₀.2 (by norm_num)
  let hu : u₀ ≤ 1 := le_trans hu₀.2 (by norm_num)
  let hc : 0 < c := comparisonFloor_pos hN hU (by norm_num)
  let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
  let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
  let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hLen hE hd.le
  let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hLen hE hd.le (show (0:ℝ) ≤ 1 by norm_num)
  let b' := fun w => (b w-omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) w).toNNReal
  let h' := fun w => (h w+omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
      (hg.continuous.mul continuous_id) α) w).toNNReal
  intro u huobs xs z hxs hscale hu₀xs hr₀U hz hzxs hdD hupper hlower htest hreg hslow hbare hBclock
  have hb' : MonotoneOn b' (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact Real.toNNReal_mono (hb α hu hv huv)
  have hh' : MonotoneOn h' (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact Real.toNNReal_mono (hh α hu hv huv)
  let v := xs+u.val
  have hv : 0 < v := add_pos hxs u.property
  let s := B*v
  have hs : 0 < s := mul_pos hB0 hv
  have hxss : xs ≤ s := by
    have hvs : v ≤ s := by dsimp [s]; nlinarith only [hB,hv]
    exact (show xs ≤ v by dsimp [v]; linarith only [u.property]).trans hvs
  have hmain : pathPairMoment (uniformWeight n) (finiteFeature n) (completedPathClock n b' h')
      (fun σ τ => |orderedOverlap n σ τ|^(2*(ℓ+1))) u.val ≤ K*v^(2*(ℓ+1)) := by
    by_cases hsmall : s ≤ 1/4
    · have hrx : r₀ < xs := by
        have hh := hnsmall E d hE hd hupper hlower
        simp only [one_mul] at hh
        exact hr₀U.trans_lt (hh.trans_le hscale)
      have hzs : z < s/2 := by
        have hzv : z ≤ Az*v := hzxs.trans (mul_le_mul_of_nonneg_left (by dsimp [v]; linarith only [u.property]) hAz)
        have hBv := mul_lt_mul_of_pos_right hBA hv
        dsimp [s]
        linarith only [hzv,hBv]
      have hr₀s : r₀ < s/2 := hz.1.trans_lt hzs
      have hs1 : s ≤ 1 := hsmall.trans (by norm_num)
      have hder : ∀ t ∈ Icc r₀ 1, DifferentiableAt ℝ g t :=
        fun t _ => (hg.differentiable (by norm_num)).differentiableAt
      have hmonSmall := strength_radial_monotonicities hxs hxss
        (fun t ht => hder t ⟨hrx.le.trans ht.1,ht.2.trans hs1⟩)
        (fun t ht => hgpos t ⟨hrx.le.trans ht.1,ht.2.trans hs1⟩)
        (fun t ht => hp t ⟨hrx.trans_le ht.1,ht.2.trans hs1⟩)
      obtain ⟨J,hJ,hreach,hstop,hJlog⟩ := exists_rawWindowDepth hs hsmall (K:=1) (b:=s)
        (by simp) (by norm_num) (by norm_num) hN ((hndepth E d hE hd hlower).trans (hscale.trans hxss))
      have hstop' : (2:ℝ)^J*s ≤ 1 := by linarith only [hstop]
      have hsT : s/2 ≤ (2:ℝ)^J*s := by
        have hp := pow_pos (by norm_num : (0:ℝ) < 2) J
        have hp1 := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=J)
        nlinarith only [hp1,hs]
      have hJlog' : ((J+3:ℕ):ℝ) ≤ (1/Real.log 2+4)*Real.log (n:ℝ) := by
        have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
        have he : Real.log (n:ℝ)/Real.log 2+4 ≤ (1/Real.log 2+4)*Real.log (n:ℝ) := by
          have hfour := mul_le_mul_of_nonneg_left hnlog (show (0:ℝ) ≤ 4 by norm_num)
          have heq : (1/Real.log 2+4)*Real.log (n:ℝ) =
              Real.log (n:ℝ)/Real.log 2+4*Real.log (n:ℝ) := by ring
          rw [heq]
          linarith only [hfour]
        exact hJlog.trans he
      have hJsq : ((J+3:ℕ):ℝ)^2 ≤ (1/Real.log 2+4)^2*(Real.log (n:ℝ))^2 := by
        simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hJlog' 2
      have hsub : Icc (s/2) ((2:ℝ)^J*s) ⊆ Icc r₀ 1 :=
        fun t ht => ⟨hr₀s.le.trans ht.1,ht.2.trans hstop'⟩
      have hsubz : Icc (s/2) ((2:ℝ)^J*s) ⊆ Icc z 1 :=
        fun t ht => ⟨hzs.le.trans ht.1,ht.2.trans hstop'⟩
      have hmon := strength_radial_monotonicities (show 0 < s/2 by positivity) hsT
        (fun t ht => hder t (hsub ht)) (fun t ht => hgpos t (hsub ht))
        (fun t ht => hp t ⟨hr₀s.trans_le ht.1,ht.2.trans hstop'⟩)
      have hgrowth : ∀ x ∈ Icc (s/2) ((2:ℝ)^J*s), ∀ y ∈ Icc (s/2) ((2:ℝ)^J*s), x ≤ y →
          (κ₀/Real.log (n:ℝ))*g y*(y-x) ≤ (h' (α.val.val y):ℝ)-(h' (α.val.val x):ℝ) := by
        intro x hx y hy hxy
        have hi : Icc x y ⊆ Icc (s/2) ((2:ℝ)^J*s) := fun w hw => ⟨hx.1.trans hw.1,hw.2.trans hy.2⟩
        exact changedField_toNNReal_radius_growth hr hu hu₀.1 hc hk hkc hm hM α g h hg.continuous
          hbare (hh α) (hhn α) (hsub hx) (hsub hy) hxy
          (fun w hw => hder w (hsub (hi hw))) (fun w hw => hgpos w (hsub (hi hw)))
          (hmon.1.mono hi) (by positivity) (fun w hw => hslow w (hsubz (hi hw)))
      obtain ⟨us,hus,humem,hQ⟩ := hnraw hn hE hd hr₀ hu₀ g α hg hgpos hp b h hb hh hbn hhn hmin
        u huobs xs z hxs hscale hu₀xs hr₀U hz hzxs hdD hupper hlower htest hreg hslow hbare hBclock
      have hucl : u.val < (cl/2)*s := by
        have hh := mul_lt_mul_of_pos_right hBcl hv
        dsimp [s,v] at *
        nlinarith only [hh,hxs,u.property]
      have hbound := hnov hn E d xs s (1/4) (2*C) g hE hd hxs hxss
        (hgpos s ⟨hrx.le.trans hxss,hs1⟩) (by norm_num) (by positivity)
        hupper hlower (hscale.trans hxss) htest hmonSmall.2.2 hFmass hFradius
        J hJ hJsq hreach hstop' b' h' hb' hh' hBclock us hus u humem hucl
        hr hu hu₀.1 hc hk hkc hm hM α hr₀s (fun t ht => hreg t (hsubz ht))
        (fun t ht => (hgpos t (hsub ht)).le) hmon.1 hmon.2.1 hgrowth hQ
      apply hbound.trans
      change L*(2*C)^(2*(ℓ+1))*(B*v)^(2*(ℓ+1)) ≤ K*v^(2*(ℓ+1))
      calc
        _ = (L*(2*C)^(2*(ℓ+1))*B^(2*(ℓ+1)))*v^(2*(ℓ+1)) := by
          simp only [mul_pow]; ring
        _ ≤ K*v^(2*(ℓ+1)) := mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (pow_nonneg (show 0 ≤ 4*B by positivity) _)) (pow_nonneg hv.le _)
    · have hbound := completedPathOverlapMoment_le_one n (ℓ+1) hn b' h' hb' hh' u huobs
      have h4 : 1 ≤ 4*B*v := by dsimp [s] at hsmall; linarith only [lt_of_not_ge hsmall]
      have hpow : 1 ≤ (4*B)^(2*(ℓ+1))*v^(2*(ℓ+1)) := by
        simpa only [mul_pow] using one_le_pow₀ h4 (n:=2*(ℓ+1))
      apply hbound.trans (hpow.trans ?_)
      exact mul_le_mul_of_nonneg_right (by dsimp only [K]; exact le_add_of_nonneg_right (by positivity)) (pow_nonneg hv.le _)
  exact hmain

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 omit [Nonempty ι] in
 theorem stepPairDisorder_zero_eq_root [Nonempty ι] {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q₀ : ι → ℝ≥0)
    (pre post : List (GaussianStep ι)) (ho : OrderedSteps 0 (pre++post)) (P : S → S → ℝ) :
    stepPairDisorder w φ q₀ pre post P 0 = rootLevelPairMean w φ q₀ P (pre++post) pre.length := by
  unfold stepPairDisorder rootLevelPairMean
  rw [stepPairMean_eq_levelPairMean hw φ P pre post (ho.suffix pre post)]

 theorem pathPairMoment_mono_test {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    {P Q : S → S → ℝ} (hPQ : ∀ σ τ, P σ τ ≤ Q σ τ)
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    pathPairMoment w φ q P u ≤ pathPairMoment w φ q Q u := by
  simp only [pathPairMoment,dite_eq_left hu.1]
  apply le_of_tendsto_of_tendsto
    (retainedPairSample_tendsto_all hw φ q hq ⟨u,hu.1⟩ hu.2 P 0)
    (retainedPairSample_tendsto_all hw φ q hq ⟨u,hu.1⟩ hu.2 Q 0)
  apply Eventually.of_forall
  intro k
  have ho := retainedPairSample_ordered q ⟨u,hu.1⟩ hu.2 _ (uniformMasses_ordered k)
  change stepPairDisorder _ _ _ _ _ _ 0 ≤ stepPairDisorder _ _ _ _ _ _ 0
  rw [stepPairDisorder_zero_eq_root hw φ _ _ _ ho,stepPairDisorder_zero_eq_root hw φ _ _ _ ho]
  exact rootLevelPairMean_mono hw φ _ hPQ _ ho _

 theorem pathPairMoment_const_test {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (c : ℝ) {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    pathPairMoment w φ q (fun _ _ => c) u = c := by
  simp only [pathPairMoment,dite_eq_left hu.1]
  have ht := retainedPairSample_tendsto_all hw φ q hq ⟨u,hu.1⟩ hu.2 (fun _ _ => c) 0
  have he (k : ℕ) : retainedPairSample w φ q ⟨u,hu.1⟩ (uniformMasses k) (fun _ _ => c) 0 = c := by
    have ho := retainedPairSample_ordered q ⟨u,hu.1⟩ hu.2 _ (uniformMasses_ordered k)
    change stepPairDisorder _ _ _ _ _ _ 0 = c
    rw [stepPairDisorder_zero_eq_root hw φ _ _ _ ho]
    exact rootLevelPairMean_const hw φ _ _ ho _ c
  simp_rw [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

 theorem raw_rpow_normalized_interpolation {z t p : ℝ} (hz : 0 ≤ z) (ht : 0 < t)
    (hp : 0 ≤ p) (k : ℕ) (hpk : p ≤ k) :
    z^p ≤ t^p + t^(p-(k:ℝ))*z^k := by
  have hn : (z/t)^p ≤ 1+(z/t)^(k:ℝ) := by
    by_cases hh : z/t ≤ 1
    · exact (Real.rpow_le_one (div_nonneg hz ht.le) hh hp).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (div_nonneg hz ht.le) _))
    · exact (Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hh)) hpk).trans
        (le_add_of_nonneg_left (by norm_num))
  have hb := mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg ht.le p)
  rw [Real.div_rpow hz ht.le,Real.div_rpow hz ht.le] at hb
  rw [Real.rpow_natCast,Real.rpow_natCast] at hb
  have he : t^p*(z^p/t^p)=z^p := mul_div_cancel₀ _ (Real.rpow_pos_of_pos ht p).ne'
  rw [he,mul_add,mul_one] at hb
  rw [Real.rpow_sub ht,Real.rpow_natCast]
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using hb

 theorem pathPairMoment_rpow_from_nat {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (P : S → S → ℝ) (hP : ∀ σ τ, 0 ≤ P σ τ)
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) {t p C : ℝ} (ht : 0 < t) (hp : 0 ≤ p)
    (k : ℕ) (hpk : p ≤ k)
    (hbound : pathPairMoment w φ q (fun σ τ => P σ τ^k) u ≤ C*t^k) :
    pathPairMoment w φ q (fun σ τ => P σ τ^p) u ≤ (1+C)*t^p := by
  have hb := pathPairMoment_mono_test hw φ q hq
    (fun σ τ => raw_rpow_normalized_interpolation (hP σ τ) ht hp k hpk) hu
  rw [pathPairMoment_add hw φ q hq _ _ hu,pathPairMoment_const_test hw φ q hq _ hu,
    pathPairMoment_const_mul hw φ q hq _ _ hu] at hb
  have hm := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg ht.le (p-(k:ℝ)))
  have he : t^(p-(k:ℝ))*(C*t^k)=C*t^p := by
    rw [Real.rpow_sub ht,Real.rpow_natCast]
    field_simp [ht.ne']
  rw [he] at hm
  nlinarith

end SKFluctuations.Hierarchy

end

end OAI
