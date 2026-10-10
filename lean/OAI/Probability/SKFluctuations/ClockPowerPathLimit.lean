import Mathlib
import OAI.Probability.SKFluctuations.FiniteRetainedGridReady

namespace OAI

/-! Clock Power Path Limit. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 def stepPathPowerDistance (D : ι → ℝ) (q₀ : ι → ℝ≥0) (A B : List (GaussianStep ι))
    (q : ℝ → ι → ℝ≥0) (u : ℝ) (l : ℕ) : ℝ :=
    (2*l:ℕ)*clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) A A.length) (fun i => (q u i:ℝ))+
      2*stepPathClockDistance D q₀ (A++B) q+
    clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) (A++B) (A++B).length)
      (fun i => (q 1 i:ℝ))

 theorem stepPowerDisorder_sample_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q₀ : ι → ℝ≥0) (A B : List (GaussianStep ι)) {u : ℝ}
    (hu : 0≤u) (hA : OrderedSteps 0 A) (hB : OrderedSteps u B) (hAu : ∀ s ∈ A, s.1≤u)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (as bs : List PositiveMass) (ha : MassOrdered 0 as) (hb : MassOrdered u bs)
    (hau : ∀ a ∈ as, a.val≤u) (heA : partitionEnd 0 as=u) (hetB : partitionEnd u bs=1)
    {h : ℝ} (hmesh : PartitionMesh h 0 (as++bs))
    (l : ℕ) (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |stepPowerDisorder w φ q₀ A B P l x-sampledPowerDisorder w φ q u as bs P l x| ≤
      ClockTree.errorJetVariation (2*l+1) 0 0*K^l*
        (stepPathPowerDistance D q₀ A B q u l+2*h*clockVariationBound D q) := by
  have hoa : MassOrdered 0 (as++bs) := ha.append_end (heA.symm ▸ hb)
  have ht := stepPowerDisorder_l1_comparison hw φ D hD hφ q₀ (q 0)
    A B (sampleClockSteps q 0 as) (sampleClockSteps q u bs) hu hA hB
    (sampleClockSteps_ordered q as ha) (sampleClockSteps_ordered q bs hb)
    hAu (sampleClockSteps_mass_le q 0 as hau) l P hK hP x
  rw [sampleClockSteps_terminal q hq 0 as ha,heA] at ht
  have hAB : sampleClockSteps q 0 as++sampleClockSteps q u bs=sampleClockSteps q 0 (as++bs) := by
    rw [sampleClockSteps_append,heA]
  rw [hAB,sampleClockSteps_terminal q hq 0 (as++bs) hoa,
    partitionEnd_append,heA,hetB] at ht
  have hfun : stepClockFunction (fun i => (q 0 i:ℝ)) (sampleClockSteps q 0 (as++bs)) =
      fun u i => partitionSample (fun v => (q v i:ℝ)) 0 (as++bs) u := by
    funext u i
    exact sampleClockSteps_function q hq _ hoa u i
  rw [hfun] at ht
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (ClockTree.errorJetVariation_nonneg (2*l+1) 0 0) (pow_nonneg hK l))
  have hh := stepClock_sample_distance D q₀ (A++B) (hA.append_bound hu hAu hB) q hq (as++bs) hoa hmesh
  dsimp only [stepPathPowerDistance]
  linarith

 theorem stepPowerDisorder_path_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q₀ : ι → ℝ≥0) (A B : List (GaussianStep ι)) (u : PositiveMass) (hu : u.val≤1)
    (hA : OrderedSteps 0 A) (hB : OrderedSteps u.val B) (hAu : ∀ s ∈ A, s.1≤u.val)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (l : ℕ) (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |stepPowerDisorder w φ q₀ A B P l x-pathPowerDisorder w φ q u P l x| ≤
      ClockTree.errorJetVariation (2*l+1) 0 0*K^l*stepPathPowerDistance D q₀ A B q u.val l := by
  have hb (n : ℕ) : |stepPowerDisorder w φ q₀ A B P l x-
      retainedPowerSample w φ q u (uniformMasses n) P l x| ≤
      ClockTree.errorJetVariation (2*l+1) 0 0*K^l*
        (stepPathPowerDistance D q₀ A B q u.val l+2*((n+1:ℕ):ℝ)⁻¹*clockVariationBound D q) := by
    have ho := retainedMasses_ordered u hu (uniformMasses n) (uniformMasses_ordered n)
    exact stepPowerDisorder_sample_comparison hw φ D hD hφ q₀ A B u.property.le hA hB hAu
      q hq _ _ ho.1 ho.2 (retainedBefore_bounds u _) (retainedBefore_end u _) (retainedAfter_end u _)
      (retainedMasses_mesh u hu _ (uniformMasses_ordered n) (by positivity) (uniformMasses_mesh n)) l P hK hP x
  have hl := ((tendsto_const_nhds (x := stepPowerDisorder w φ q₀ A B P l x)).sub (retainedPowerSample_tendsto hw φ D hD hφ q hq u hu l P hK hP x)).abs
  have hr : Tendsto (fun n : ℕ => ClockTree.errorJetVariation (2*l+1) 0 0*K^l*
      (stepPathPowerDistance D q₀ A B q u.val l+2*((n+1:ℕ):ℝ)⁻¹*clockVariationBound D q)) atTop
      (𝓝 (ClockTree.errorJetVariation (2*l+1) 0 0*K^l*stepPathPowerDistance D q₀ A B q u.val l)) := by
    simpa using (tendsto_const_nhds.add ((uniformMasses_mesh_tendsto.const_mul 2).mul_const
      (clockVariationBound D q))).const_mul (ClockTree.errorJetVariation (2*l+1) 0 0*K^l)
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall hb)

 theorem stepPowerDisorder_tendsto_path {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q₀ : ℕ → ι → ℝ≥0) (A B : ℕ → List (GaussianStep ι)) (u : PositiveMass) (hu : u.val≤1)
    (hA : ∀ n, OrderedSteps 0 (A n)) (hB : ∀ n, OrderedSteps u.val (B n))
    (hAu : ∀ n s, s ∈ A n → s.1≤u.val)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (l : ℕ)
    (hpath : Tendsto (fun n => stepPathPowerDistance D (q₀ n) (A n) (B n) q u.val l) atTop (𝓝 0))
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    Tendsto (fun n => stepPowerDisorder w φ (q₀ n) (A n) (B n) P l x) atTop
      (𝓝 (pathPowerDisorder w φ q u P l x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _) (fun n =>
    stepPowerDisorder_path_comparison hw φ D hD hφ (q₀ n) (A n) (B n) u hu (hA n) (hB n) (hAu n) q hq l P hK hP x)
  simpa using hpath.const_mul (ClockTree.errorJetVariation (2*l+1) 0 0*K^l)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 def stepPowerMoment (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q₀ : ι → ℝ≥0) (L : List (GaussianStep ι)) (P : S → S → ℝ) (l : ℕ) (u : ℝ) : ℝ :=
    stepPowerDisorder w φ q₀ (splitClockSteps u L).1 (splitClockSteps u L).2 P l 0

 def pathPowerMoment (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (P : S → S → ℝ) (l : ℕ) (u : ℝ) : ℝ :=
  if h : 0<u then pathPowerDisorder w φ q ⟨u,h⟩ P l 0 else 0

 theorem stepPowerMoment_path_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q₀ : ι → ℝ≥0) (L : List (GaussianStep ι)) (hL : OrderedSteps 0 L)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (l : ℕ) (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K)
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    |stepPowerMoment w φ q₀ L P l u-pathPowerMoment w φ q P l u| ≤
      ClockTree.errorJetVariation (2*l+1) 0 0*K^l*(
        (2*l:ℕ)*clockCoordinateDistance D (stepClockFunction (fun i => (q₀ i:ℝ)) L u)
          (fun i => (q u i:ℝ))+2*stepPathClockDistance D q₀ L q+
        clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) L L.length)
          (fun i => (q 1 i:ℝ))) := by
  have ho := splitClockSteps_ordered u ⟨hu.1.le,hu.2⟩ L hL hu.1.le
  rw [stepPowerMoment, pathPowerMoment,dite_eq_left hu.1]
  have hb := stepPowerDisorder_path_comparison hw φ D hD hφ q₀
    (splitClockSteps u L).1 (splitClockSteps u L).2 ⟨u,hu.1⟩ hu.2
    ho.1 ho.2.1 ho.2.2 q hq l P hK hP 0
  simpa only [stepPathPowerDistance,splitClockSteps_append,←stepClockFunction_split _ _ _ hL] using hb

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 theorem retainedPowerMoment_tendsto {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (as : ℕ → List PositiveMass) (h : ℕ → ℝ)
    (ho : ∀ n, MassOrdered 0 (as n)) (hm : ∀ n, PartitionMesh (h n) 0 (as n))
    (he : ∀ n, partitionEnd 0 (as n)=1) (hh : Tendsto h atTop (𝓝 0))
    (u : PositiveMass) (hu : u.val≤1) (hnode : ∀ n, u ∈ as n)
    (l : ℕ) (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) :
    Tendsto (fun n => stepPowerMoment w φ (q 0) (sampleClockSteps q 0 (as n))
      P l u.val)
      atTop (𝓝 (pathPowerMoment w φ q P l u.val)) := by
  have ht (n : ℕ) : clockCoordinateDistance D
      (stepClockFunction (fun i => (q 0 i:ℝ)) (sampleClockSteps q 0 (as n)) u.val)
      (fun i => (q u.val i:ℝ))=0 := by
    unfold clockCoordinateDistance
    simp_rw [sampleClockSteps_function q hq _ (ho n),partitionSample_at_node _ _ (ho n) (hnode n)]
    simp
  have hl : Tendsto (fun n => stepPathClockDistance D (q 0)
      (sampleClockSteps q 0 (as n)) q) atTop (𝓝 0) :=
    squeeze_zero (fun _ => stepPathClockDistance_nonneg _ _ _ _) (fun n =>
      sample_stepPathClockDistance_le D q hq _ (ho n) (hm n))
      (by simpa using hh.mul_const (clockVariationBound D q))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _) (fun n => stepPowerMoment_path_comparison hw φ D hD hφ
    (q 0) _ (sampleClockSteps_ordered q _ (ho n)) q hq l P hK hP ⟨u.property,hu⟩)
  simp_rw [ht,sampleClockSteps_terminal q hq _ _ (ho _),he]
  simpa [clockCoordinateDistance] using (hl.const_mul 2).const_mul (ClockTree.errorJetVariation (2*l+1) 0 0*K^l)

 theorem retainedPowerMoment_tendsto_all {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (as : ℕ → List PositiveMass) (h : ℕ → ℝ)
    (ho : ∀ n, MassOrdered 0 (as n)) (hm : ∀ n, PartitionMesh (h n) 0 (as n))
    (he : ∀ n, partitionEnd 0 (as n)=1) (hh : Tendsto h atTop (𝓝 0))
    (u : PositiveMass) (hu : u.val≤1) (hnode : ∀ n, u ∈ as n) (l : ℕ) (P : S → S → ℝ) :
    Tendsto (fun n => stepPowerMoment w φ (q 0) (sampleClockSteps q 0 (as n))
      P l u.val)
      atTop (𝓝 (pathPowerMoment w φ q P l u.val)) := by
  let D : ι → ℝ := fun i => ∑ σ, |φ σ (Pi.single i 1)|
  have hD : ∀ i, 0≤D i := by intro i; exact Finset.sum_nonneg fun σ _ => abs_nonneg _
  have hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i := by
    intro σ i
    exact Finset.single_le_sum (fun τ _ => abs_nonneg (φ τ (Pi.single i 1))) (Finset.mem_univ σ)
  let K : ℝ := ∑ σ, ∑ τ, |P σ τ|
  have hK : 0≤K := by dsimp [K]; positivity
  have hP (σ τ : S) : |P σ τ|≤K := by
    exact (Finset.single_le_sum (fun ρ _ => abs_nonneg (P σ ρ)) (Finset.mem_univ τ)).trans
      (Finset.single_le_sum (fun ρ _ => Finset.sum_nonneg fun η _ => abs_nonneg (P ρ η)) (Finset.mem_univ σ))
  exact retainedPowerMoment_tendsto hw φ D hD hφ q hq as h ho hm he hh u hu hnode l P hK hP

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 def physicalPathPowerMoment (n l : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (q₀ : FeatureIndex n → ℝ≥0) (j : ℕ) : ℝ :=
    ∫ p, ‖actualSpinPath n steps id j p‖^(2*l)
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps

 theorem physicalPowerMoment_eq_stepPowerMoment (n l : ℕ) (hn : 0<n)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (u : ℝ) :
    physicalPathPowerMoment n l steps q₀ (splitClockSteps u steps).1.length=
      stepPowerMoment (uniformWeight n) (finiteFeature n) q₀ steps (orderedOverlap n) l u := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have ho : OrderedSteps 0 ((splitClockSteps u steps).1++(splitClockSteps u steps).2) := by
    simpa only [splitClockSteps_append] using ha
  have he := physicalPowerMoment_eq_stepPowerDisorder n l (splitClockSteps u steps).1
    (splitClockSteps u steps).2 ho q₀
  change physicalPathPowerMoment n l ((splitClockSteps u steps).1++(splitClockSteps u steps).2)
    q₀ (splitClockSteps u steps).1.length = _ at he
  rw [splitClockSteps_append] at he
  exact he

 theorem physicalRetainedPowerMoment_tendsto (n l : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀ k, MassOrdered 0 (as k)) (hm : ∀ k, PartitionMesh (mesh k) 0 (as k))
    (he : ∀ k, partitionEnd 0 (as k)=1) (hmesh : Tendsto mesh atTop (𝓝 0))
    (u : PositiveMass) (hu : u.val≤1) (hnode : ∀ k, u ∈ as k) :
    let q := completedPathClock n b h
    Tendsto (fun k => let steps := sampleClockSteps q 0 (as k)
      physicalPathPowerMoment n l steps (q 0) (splitClockSteps u.val steps).1.length)
      atTop (𝓝 (pathPowerMoment (uniformWeight n) (finiteFeature n) q (orderedOverlap n) l u.val)) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  dsimp only
  simp_rw [physicalPowerMoment_eq_stepPowerMoment n l hn _ (sampleClockSteps_ordered _ _ (ho _))]
  exact retainedPowerMoment_tendsto_all (uniformWeight_pos n) (finiteFeature n) (completedPathClock n b h)
    (completedPathClock_monotone n hb hh) as mesh ho hm he hmesh u hu hnode l (orderedOverlap n)

end SKFluctuations

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 theorem eventually_physical_band_window (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (_ha : OrderedSteps 0 steps)
      (xs : ℝ) (_hxs : 0 < xs) (w : PhysicalBandWindow n steps xs)
      (μ : Measure P) [IsProbabilityMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
      (d : GaussianStep (FeatureIndex n) → ℝ≥0),
      (∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i) = d st) →
      physicalFieldDuration d steps ≤ B →
      (∀ s ∈ Ioc w.a w.b, w.D₀ ≤
        physicalFieldDuration d (steps.take (radiusGridCut w.radius (s+w.η))) -
          physicalFieldDuration d (steps.take (radiusGridCut w.radius s))) →
      (∀ r ∈ Icc (2*w.a) ((2:ℝ)^w.depth*w.b), w.D₀ ≤
        physicalFieldDuration d (steps.take (radiusGridCut w.radius r)) -
          physicalFieldDuration d (steps.take (radiusGridCut w.radius (3*r/4)))) →
    (∫ p, (physicalSusceptibilityMassIntegral n steps x w.measure (radiusGridCut w.radius) p)^(k+1)
      ∂physicalPathLaw μ n steps x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
        w.coefficient k*(physicalRawRatio n (k+1) steps 0 xs μ x hx)^4 := by
  filter_upwards [eventually_physical_dyadic_band k B] with n hn
  intro P _ steps ha xs hxs w μ _ x hx d hd hB hfirst hdyad
  have hh := hn P steps 0 w.c₀ xs w.D₀ w.C w.R w.F ha w.c₀_pos hxs w.D₀_pos
    w.C_nonneg w.R_pos w.F_mass w.F_radius μ x hx (radiusGridCut w.radius)
    (radiusGridCut_monotone w.radius) (radiusGridCut_le w.radius)
    w.a w.b w.η w.xa w.ab w.η_pos w.η_le w.depth w.depth_pos w.last_radius
    w.measure w.A w.A_nonneg w.measure_cap d hd hB w.mass_comparable hfirst hdyad
  rw [w.measure_mass ha] at hh
  let Q := physicalRawRatio n (k+1) steps 0 xs μ x hx
  have hQ : 1 ≤ Q := physicalRawRatio_one_le n (k+1) steps 0 xs μ x hx
  have h24 : Q^2 ≤ Q^4 := by nlinarith [sq_nonneg (Q^2-1)]
  have hfar : 0 ≤ w.mass*w.farCoefficient k :=
    mul_nonneg w.mass_pos.le (w.farCoefficient_nonneg k)
  calc
    _ ≤ (w.depth+3:ℕ)^3*(w.nearCoefficient k*Q^4 +
        w.mass*w.farCoefficient k*Q^2) := by
      convert hh using 1; dsimp [PhysicalBandWindow.nearCoefficient,PhysicalBandWindow.farCoefficient]; ring
    _ ≤ (w.depth+3:ℕ)^3*(w.nearCoefficient k*Q^4 +
        w.mass*w.farCoefficient k*Q^4) := by
      exact mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left h24 hfar) _) (by positivity)
    _ = _ := by unfold PhysicalBandWindow.coefficient; ring

end SKFluctuations

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem physical_window_bound_of_energy (n k : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) {xs : ℝ} (hxs : 0 < xs)
    (w : PhysicalBandWindow n steps xs) {i : ℕ} (hi : ∀ j ∈ w.selected, i ≤ j.val)
    {M Q : ℝ}
    (hS : ∀ j ∈ w.selected, (∫ z, ‖actualSpinPath n steps id j.val z‖^2
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤ M)
    (hE : (∫ z, (physicalSusceptibilityMassIntegral n steps id w.measure
      (radiusGridCut w.radius) z)^(k+1)
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps)^(((k+1:ℕ):ℝ)⁻¹) ≤
        w.coefficient k*Q^4) :
    ((∫ z, ‖actualSpinPath n steps id i z‖^(4*(k+1))
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps)^(((4*(k+1):ℕ):ℝ)⁻¹))^2 ≤
      M+w.loss k*Q^2 := by
  have hh := physical_raw_window_bound n (k+1) (by omega) steps ha q₀ w.selected w.mass_pos
    w.radius w.radius_mono w.cell_pos hi hS
  dsimp only at hh
  change _ ≤ M+2*Real.sqrt ((1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2*
    (∫ z, (physicalSusceptibilityMassIntegral n steps id w.measure (radiusGridCut w.radius) z)^(k+1)
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps)^(((k+1:ℕ):ℝ)⁻¹)) at hh
  have hpos : 0 ≤ (1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2 := by positivity
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hE hpos)
  have hroot : Real.sqrt ((1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2*(w.coefficient k*Q^4)) =
      Real.sqrt ((1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2*w.coefficient k)*Q^2 := by
    rw [← mul_assoc,Real.sqrt_mul (mul_nonneg hpos (w.coefficient_nonneg hxs k))]
    congr 1
    rw [show Q^4=(Q^2)^2 by ring,Real.sqrt_sq (sq_nonneg Q)]
  rw [hroot] at hs
  calc
    _ ≤ M+2*Real.sqrt ((1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2*
      (∫ z, (physicalSusceptibilityMassIntegral n steps id w.measure (radiusGridCut w.radius) z)^(k+1)
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps)^(((k+1:ℕ):ℝ)⁻¹)) := hh
    _ ≤ M+2*(Real.sqrt ((1+(2*((k+1:ℕ):ℝ))^2/3)*w.mass⁻¹^2*w.coefficient k)*Q^2) := by linarith
    _ = _ := by unfold PhysicalBandWindow.loss; push_cast; ring

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem physicalRawRatio_close (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    {xs C : ℝ} (hxs : 0 < xs) (hC : 1 ≤ C)
    {P : Type} [MeasurableSpace P] (μ : Measure P)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (h : ∀ i ≤ steps.length+1,
      ((∫ p, ‖actualSpinPath n steps x i p‖^(4*l) ∂physicalPathLaw μ n steps x hx)
        ^(((4*l:ℕ):ℝ)⁻¹))^2 ≤
      C*(xs+physicalCutMass 0 steps i)+
        (physicalRawRatio n l steps 0 xs μ x hx)^2/2*(xs+physicalCutMass 0 steps i)) :
    (physicalRawRatio n l steps 0 xs μ x hx)^2 ≤ 2*C := by
  let f : ℕ → ℝ := fun i =>
    (∫ p, ‖actualSpinPath n steps x i p‖^(4*l) ∂physicalPathLaw μ n steps x hx)
      ^(((4*l:ℕ):ℝ)⁻¹)/Real.sqrt (xs+physicalCutMass 0 steps i)
  let S := (Finset.range (steps.length+2)).sup' (by simp) f
  by_cases hS : S ≤ 1
  · have hQ : physicalRawRatio n l steps 0 xs μ x hx = 1 := max_eq_left hS
    rw [hQ]; nlinarith
  · obtain ⟨i,hi,hei⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (steps.length+2)) (by simp) f
    have hi' : i ≤ steps.length+1 := by have hh := Finset.mem_range.mp hi; omega
    have hQ : physicalRawRatio n l steps 0 xs μ x hx = f i := by
      change max 1 S = f i
      rw [max_eq_right (le_of_not_ge hS)]
      exact hei
    have hs : 0 < xs+physicalCutMass 0 steps i :=
      add_pos_of_pos_of_nonneg hxs (physicalCutMass_mem steps ha i).1
    have hh := h i hi'
    have hf : (f i)^2 =
        ((∫ p, ‖actualSpinPath n steps x i p‖^(4*l) ∂physicalPathLaw μ n steps x hx)
          ^(((4*l:ℕ):ℝ)⁻¹))^2/(xs+physicalCutMass 0 steps i) := by
      dsimp [f]
      rw [div_pow,Real.sq_sqrt hs.le]
    have hiB : (physicalRawRatio n l steps 0 xs μ x hx)^2 ≤
        C+(physicalRawRatio n l steps 0 xs μ x hx)^2/2 := by
      conv_lhs => rw [hQ,hf]
      apply (div_le_iff₀ hs).2
      nlinarith
    nlinarith

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem physical_moment_le_one (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (i : ℕ) :
    (∫ z, ‖actualSpinPath n steps id i z‖^(4*l)
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps)^(((4*l:ℕ):ℝ)⁻¹) ≤ 1 := by
  rw [rootedHierarchyPathLaw_eq_physical]
  let μ := Measure.pi fun j => gaussianReal 0 (q₀ j)
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ha
  let : IsProbabilityMeasure (physicalPathLaw μ n steps id measurable_id) := by
    unfold physicalPathLaw
    infer_instance
  have hI : (∫ z, ‖actualSpinPath n steps id i z‖^(4*l)
      ∂physicalPathLaw μ n steps id measurable_id) ≤ 1 := by
    calc
      _ ≤ ∫ _, (1:ℝ) ∂physicalPathLaw μ n steps id measurable_id := by
        apply integral_mono (physicalCutNormPower_integrable n steps ha μ id measurable_id i (4*l)) (integrable_const 1)
        intro z
        exact (pow_le_pow_left₀ (norm_nonneg _) (actualSpinPath_norm_le n steps ha id i z) _).trans_eq (one_pow _)
      _ = 1 := by simp
  exact (Real.rpow_le_rpow (integral_nonneg fun z => pow_nonneg (norm_nonneg _) _) hI (by positivity)).trans_eq (by simp)

theorem eventually_physical_raw_bootstrap (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (steps : List (GaussianStep (FeatureIndex n)))
      (_ha : OrderedSteps 0 steps) (q₀ : FeatureIndex n → ℝ≥0) (xs C : ℝ)
      (_hxs : 0 < xs) (_hC : 1 ≤ C)
      (d : GaussianStep (FeatureIndex n) → ℝ≥0),
      (∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i) = d st) →
      physicalFieldDuration d steps ≤ B →
      (∀ i ≤ steps.length+1, 1 ≤ C*(xs+physicalCutMass 0 steps i) ∨
        ∃ w : PhysicalBandWindow n steps xs,
          (∀ j ∈ w.selected, i ≤ j.val) ∧
          (∀ j ∈ w.selected, (∫ z, ‖actualSpinPath n steps id j.val z‖^2
            ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤
              C*(xs+physicalCutMass 0 steps i)) ∧
          w.loss k ≤ (xs+physicalCutMass 0 steps i)/2 ∧
          (∀ s ∈ Ioc w.a w.b, w.D₀ ≤
            physicalFieldDuration d (steps.take (radiusGridCut w.radius (s+w.η))) -
              physicalFieldDuration d (steps.take (radiusGridCut w.radius s))) ∧
          (∀ r ∈ Icc (2*w.a) ((2:ℝ)^w.depth*w.b), w.D₀ ≤
            physicalFieldDuration d (steps.take (radiusGridCut w.radius r)) -
              physicalFieldDuration d (steps.take (radiusGridCut w.radius (3*r/4))))) →
      (physicalRawRatio n (k+1) steps 0 xs (Measure.pi fun j => gaussianReal 0 (q₀ j)) id measurable_id)^2 ≤ 2*C := by
  filter_upwards [eventually_physical_band_window k B] with n hn
  intro steps ha q₀ xs C hxs hC d hd hB hcover
  let μ := Measure.pi fun j => gaussianReal 0 (q₀ j)
  let Q := physicalRawRatio n (k+1) steps 0 xs μ id measurable_id
  apply physicalRawRatio_close n (k+1) steps ha hxs hC μ id measurable_id
  intro i hi
  rcases hcover i hi with hlarge | ⟨w,hw,hS,hloss,hfirst,hdyad⟩
  · have hh := physical_moment_le_one n (k+1) steps ha q₀ i
    rw [rootedHierarchyPathLaw_eq_physical] at hh
    have h0 : 0 ≤ (∫ z, ‖actualSpinPath n steps id i z‖^(4*(k+1))
        ∂physicalPathLaw μ n steps id measurable_id)^(((4*(k+1):ℕ):ℝ)⁻¹) := by positivity
    have hscale : 0 ≤ xs+physicalCutMass 0 steps i :=
      add_nonneg hxs.le (physicalCutMass_mem steps ha i).1
    have heps : 0 ≤ Q^2/2*(xs+physicalCutMass 0 steps i) := by positivity
    dsimp [μ] at h0
    change _ ≤ C*(xs+physicalCutMass 0 steps i)+Q^2/2*(xs+physicalCutMass 0 steps i)
    nlinarith
  · have he := hn (FeatureIndex n → ℝ) steps ha xs hxs w μ id measurable_id d hd hB hfirst hdyad
    rw [← rootedHierarchyPathLaw_eq_physical] at he
    have hh := physical_window_bound_of_energy n k steps ha q₀ hxs w hw hS he
    rw [rootedHierarchyPathLaw_eq_physical] at hh
    have heps := mul_le_mul_of_nonneg_right hloss (sq_nonneg Q)
    change _ ≤ C*(xs+physicalCutMass 0 steps i)+Q^2/2*(xs+physicalCutMass 0 steps i)
    exact hh.trans (by nlinarith)

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 def PhysicalRawWindowCover (n k : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (q₀ : FeatureIndex n → ℝ≥0) (xs C B : ℝ) : Prop :=
    ∃ d : GaussianStep (FeatureIndex n) → ℝ≥0,
      (∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i) = d st) ∧
      physicalFieldDuration d steps ≤ B ∧
      (∀ i ≤ steps.length+1, 1 ≤ C*(xs+physicalCutMass 0 steps i) ∨
        ∃ w : PhysicalBandWindow n steps xs,
          (∀ j ∈ w.selected, i ≤ j.val) ∧
          (∀ j ∈ w.selected, (∫ z, ‖actualSpinPath n steps id j.val z‖^2
            ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤
              C*(xs+physicalCutMass 0 steps i)) ∧
          w.loss k ≤ (xs+physicalCutMass 0 steps i)/2 ∧
          (∀ s ∈ Ioc w.a w.b, w.D₀ ≤
            physicalFieldDuration d (steps.take (radiusGridCut w.radius (s+w.η))) -
              physicalFieldDuration d (steps.take (radiusGridCut w.radius s))) ∧
          (∀ r ∈ Icc (2*w.a) ((2:ℝ)^w.depth*w.b), w.D₀ ≤
            physicalFieldDuration d (steps.take (radiusGridCut w.radius r)) -
              physicalFieldDuration d (steps.take (radiusGridCut w.radius (3*r/4)))))

 theorem physicalPathPowerMoment_le_of_rawRatio (n l : ℕ) (hl : 0<l)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) {xs C : ℝ} (hxs : 0<xs)
    (hQ : (physicalRawRatio n l steps 0 xs (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id)^2≤2*C)
    (j : ℕ) (hj : j ≤ steps.length+1) :
    physicalPathPowerMoment n (2*l) steps q₀ j ≤ (2*C*(xs+physicalCutMass 0 steps j))^(2*l) := by
  have hbound := physicalRawRatio_moment n l hl steps ha hxs
    (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id hj
  rw [←rootedHierarchyPathLaw_eq_physical] at hbound
  have hpow := pow_le_pow_left₀ (sq_nonneg _) hQ (2*l)
  rw [←pow_mul,show 2*(2*l)=4*l by omega] at hpow
  have hmul := mul_le_mul_of_nonneg_right hpow
    (pow_nonneg (add_nonneg hxs.le (physicalCutMass_mem steps ha j).1) (2*l))
  unfold physicalPathPowerMoment
  rw [show 2*(2*l)=4*l by omega,mul_pow]
  exact hbound.trans hmul

 theorem eventually_physical_path_raw_bootstrap (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (b h : ℝ → ℝ≥0)
      (_hb : MonotoneOn b (Icc (0:ℝ) 1)) (_hh : MonotoneOn h (Icc (0:ℝ) 1))
      (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
      (_ho : ∀ j, MassOrdered 0 (as j)) (_hm : ∀ j, PartitionMesh (mesh j) 0 (as j))
      (_he : ∀ j, partitionEnd 0 (as j)=1) (_hmesh : Tendsto mesh atTop (𝓝 0))
      (xs C : ℝ) (_hxs : 0<xs) (_hC : 1≤C)
      (u : PositiveMass) (_hu : u.val≤1) (_hnode : ∀ j, u ∈ as j),
      (∀ᶠ j : ℕ in atTop, PhysicalRawWindowCover n k
        (sampleClockSteps (completedPathClock n b h) 0 (as j))
        (completedPathClock n b h 0) xs C B) →
      pathPowerMoment (uniformWeight n) (finiteFeature n) (completedPathClock n b h)
        (orderedOverlap n) (2*(k+1)) u.val ≤ (2*C*(xs+u.val))^(2*(k+1)) := by
  filter_upwards [eventually_physical_raw_bootstrap k B,eventually_ge_atTop 1] with n hn hnpos
  intro b h hb hh as mesh ho hm he hmesh xs C hxs hC u hu hnode hcover
  have hn0 : 0<n := by omega
  have ht := physicalRetainedPowerMoment_tendsto n (2*(k+1)) hn0 b h hb hh as mesh
    ho hm he hmesh u hu hnode
  apply le_of_tendsto ht
  filter_upwards [hcover] with j hj
  obtain ⟨d,hd,hB,hcovers⟩ := hj
  let q := completedPathClock n b h
  let steps := sampleClockSteps q 0 (as j)
  have hs := sampleClockSteps_ordered q (as j) (ho j)
  have hQ := hn steps hs (q 0) xs C hxs hC d hd hB hcovers
  have hjlen : (splitClockSteps u.val steps).1.length ≤ steps.length+1 :=
    (splitClockSteps_length_le steps u.val).trans (Nat.le_succ _)
  have hh := physicalPathPowerMoment_le_of_rawRatio n (k+1) (by omega) steps hs (q 0) hxs hQ _ hjlen
  rw [sampled_retained_mass q (as j) (ho j) u (hnode j)] at hh
  exact hh

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal

 theorem eventually_physicalRetainedBand (n : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hus : ∀ u ∈ us, u.val≤1)
    {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀≤1) (hu : u₀≤1) (hu₀ : 0≤u₀) (hc : 0<c)
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ t ∈ Icc r₀ 1, c≤k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : ∀ u ∈ Icc (0:ℝ) 1, 0≤M u)
    (α : inverseIntegralConstraints r₀ u₀ k M)
    (p q : PositiveMass) (hpu : p ∈ us) (hqu : q ∈ us)
    (hp₀ : u₀≤p.val) (hq₁ : q.val≤1) (hpq : p.val<q.val)
    (xs η cl cu R F κ K Ca v C : ℝ) (J ℓ : ℕ) (e : ℝ → ℝ)
    (hxs : 0<xs) (hcl : 0<cl) (hcu : 0≤cu) (hR : 0<R)
    (hκ : 0<κ) (hK : 1≤K) (hCa : 0<Ca) (hC : 0≤C)
    (hFmass : 1+2*cu≤F) (hFradius : 1+1/R≤F) (hJ : 1≤J)
    (hmean : orderedPathS n b h q.val<C*v) :
    let hM₁ := hM 1 (by norm_num)
    let a := (constrainedQuantile hr hc hk hkc hm hM₁ α ⟨p.val,hp₀,hpq.le.trans hq₁⟩).val
    let ab := (constrainedQuantile hr hc hk hkc hm hM₁ α ⟨q.val,hp₀.trans hpq.le,hq₁⟩).val
    let T := (2:ℝ)^J*ab
    let L := 8*(K+1)/κ
    xs≤a → a≤Ca*v → ab≤K*a → cl*a≤q.val-p.val → q.val-p.val≤K*cu*a →
    0<M q.val → 0<e a → 0<η → η≤a → r₀<a/2 →
    η=(1/Real.sqrt (M q.val*((n:ℝ)*e a*a^4)))*a →
    T≤1 → R≤(2:ℝ)^J*a →
    (∀ t ∈ Icc (a/2) T, cl*t≤α.val.val t ∧ α.val.val t≤cu*t) →
    (∀ t ∈ Icc (a/2) T, 0≤e t) → AntitoneOn e (Icc (a/2) T) →
    MonotoneOn (fun t => t*e t) (Icc (a/2) T) →
    (∀ z ∈ Icc (a/2) T, ∀ t ∈ Icc (a/2) T, z≤t →
      κ*e t*(t-z)≤(h (α.val.val t):ℝ)-(h (α.val.val z):ℝ)) →
    ((J+3:ℕ):ℝ)^3*(4*(K+1)*cu*nearPairMomentConstant (ℓ+1)^(((ℓ+1:ℕ):ℝ)⁻¹)*
       (1+(K+1)*cu)^2 +
       4*K*cu*(projectionLpConstant ℓ)^2*(Real.log (n:ℝ))^4*(F^2/((cl/2)/4)^2)*L)*
       Real.sqrt (M q.val/((n:ℝ)*e a*a^4)) ≤
       (cl/(4*Ca))^2/(1+(2*(ℓ+1:ℕ):ℝ)^2/3) →
    ∀ᶠ j : ℕ in atTop,
      let steps := sampleClockSteps (completedPathClock n b h) 0 (finiteCutMasses us j)
      let d := fun st : GaussianStep (FeatureIndex n) => st.2 (Sum.inl ⟨0,hn⟩)
      ∀ i : ℕ, v≤xs+physicalCutMass 0 steps i → physicalCutMass 0 steps i<p.val →
        ∃ w : PhysicalBandWindow n steps xs,
          (∀ z ∈ w.selected, i≤z.val) ∧
          (∀ z ∈ w.selected, (∫ t, ‖actualSpinPath n steps id z.val t‖^2
            ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n)
              (completedPathClock n b h 0) steps) ≤ C*(xs+physicalCutMass 0 steps i)) ∧
          w.loss ℓ≤(xs+physicalCutMass 0 steps i)/2 ∧
          (∀ s ∈ Ioc w.a w.b, w.D₀≤
            physicalFieldDuration d (steps.take (radiusGridCut w.radius (s+w.η)))-
              physicalFieldDuration d (steps.take (radiusGridCut w.radius s))) ∧
          (∀ s ∈ Icc (2*w.a) ((2:ℝ)^w.depth*w.b), w.D₀≤
            physicalFieldDuration d (steps.take (radiusGridCut w.radius s))-
              physicalFieldDuration d (steps.take (radiusGridCut w.radius (3*s/4)))) := by
  dsimp only
  intro hxa hav hba hmasslo hmasshi hA hea hη hηa hr₀ hηeq hT hRJ hreg he hem her hH hmargin
  let hM₁ := hM 1 (by norm_num)
  have hmesh : ∀ᶠ j : ℕ in atTop, (((j+1:ℕ):ℝ)⁻¹)/c≤η/8 := by
    have ht : Tendsto (fun j : ℕ => (((j+1:ℕ):ℝ)⁻¹)/c) atTop (𝓝 0) := by
      simpa using (uniformMasses_mesh_tendsto.div_const c)
    exact (ht.eventually (gt_mem_nhds (show (0:ℝ)<η/8 by positivity))).mono
      (fun j hj => hj.le)
  have hmeans := physicalRetainedSecondMoment_eventually_uniform n hn b h hb hh
    (finiteCutMasses us) (fun j => (((j+1:ℕ):ℝ)⁻¹))
    (finiteCutMasses_ordered us hus) (finiteCutMasses_mesh us hus)
    (finiteCutMasses_end us hus) uniformMasses_mesh_tendsto q hq₁
    (fun j => finiteCutMasses_nodes us j hqu) hmean
  filter_upwards [hmesh,hmeans] with j hj hmeanj
  dsimp only at hmeanj ⊢
  let as := finiteCutMasses us j
  let has := finiteCutMasses_ordered us hus j
  let steps := sampleClockSteps (completedPathClock n b h) 0 as
  let hs := sampleClockSteps_ordered (completedPathClock n b h) as has
  have hgm : ∀ z : Fin (steps.length+1),
      physicalQuantileGrid hr hu hc hk hkc hm hM₁ α steps hs z.succ-
      physicalQuantileGrid hr hu hc hk hkc hm hM₁ α steps hs z.castSucc≤η/8 := by
    intro z
    exact (physicalQuantileGrid_mesh hr hu hc hk hkc hm hM₁ α steps hs
      (sampled_physicalMass_mesh _ _ (finiteCutMasses_mesh us hus j)) z).trans hj
  obtain ⟨w,hws,hwa,hwb,hwm,hwA,hloss,hclock₀,hclock₁⟩ :=
    physicalReadyRetainedWindow n hn b h hb hh as has hr hu hu₀ hc hk hkc hm hM α p q
      (finiteCutMasses_nodes us j hpu) (finiteCutMasses_nodes us j hqu) hp₀ hq₁ hpq
      xs η cl cu R F (η/8) κ K Ca v J ℓ e hxs hcl hcu hR hκ hK hCa hFmass hFradius hJ
      (by positivity) hgm hxa hav hba hmasslo hmasshi hA hea hη hηa le_rfl hr₀ hηeq hT hRJ
      hreg he hem her hH hmargin
  intro i hiv hip
  have hmn : ∀ z≤(physicalRetainedIndex steps q.val).val,
      physicalPathSecondMoment n steps (completedPathClock n b h 0) z≤C*v := by
    intro z hz
    exact (hmeanj z hz).le
  obtain ⟨hfut,hmns⟩ := retainedWindow_future_means n (completedPathClock n b h) as has p q
    (finiteCutMasses_nodes us j hpu) i hip hmn
  refine ⟨w,?_,?_,?_,hclock₀,hclock₁⟩
  · rwa [hws]
  · intro z hz
    rw [hws] at hz
    exact (hmns z hz).trans (mul_le_mul_of_nonneg_left hiv hC)
  · exact hloss.trans (div_le_div_of_nonneg_right hiv (by norm_num))

end SKFluctuations

end

end OAI
