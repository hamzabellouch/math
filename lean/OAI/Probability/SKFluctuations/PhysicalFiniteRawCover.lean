import Mathlib
import OAI.Probability.SKFluctuations.ClockPowerPathLimit

namespace OAI

/-! Physical Finite Raw Cover. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal

 def PhysicalRawWindowAt (n k : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    (q₀ : FeatureIndex n → ℝ≥0) (xs C : ℝ)
    (d : GaussianStep (FeatureIndex n) → ℝ≥0) (i : ℕ) : Prop :=
    ∃ w : PhysicalBandWindow n steps xs,
      (∀ z ∈ w.selected, i≤z.val) ∧
      (∀ z ∈ w.selected, (∫ t, ‖actualSpinPath n steps id z.val t‖^2
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤
        C*(xs+physicalCutMass 0 steps i)) ∧
      w.loss k≤(xs+physicalCutMass 0 steps i)/2 ∧
      (∀ s ∈ Ioc w.a w.b, w.D₀≤
        physicalFieldDuration d (steps.take (radiusGridCut w.radius (s+w.η)))-
          physicalFieldDuration d (steps.take (radiusGridCut w.radius s))) ∧
      (∀ s ∈ Icc (2*w.a) ((2:ℝ)^w.depth*w.b), w.D₀≤
        physicalFieldDuration d (steps.take (radiusGridCut w.radius s))-
          physicalFieldDuration d (steps.take (radiusGridCut w.radius (3*s/4))))

 theorem partitionPoint_length (a : ℝ) (as : List PositiveMass) :
    partitionPoint a as as.length=partitionEnd a as := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih => exact ih b.val

 theorem sampledFieldDuration_total (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as=1) :
    physicalFieldDuration (fun st => st.2 (Sum.inl ⟨0,hn⟩))
      (sampleClockSteps (completedPathClock n b h) 0 as)=(h 1:ℝ)-(h 0:ℝ) := by
  have ht := sampledFieldDuration_index n hn b h hb hh as ha as.length le_rfl
  dsimp only at ht
  rw [physicalCutMass_sampleClockSteps _ _ _ _ le_rfl,partitionPoint_length,he] at ht
  have hl := sampleClockSteps_length (completedPathClock n b h) 0 as
  rw [←hl,List.take_length] at ht
  exact ht

 theorem physicalRawWindowCover_of_finite (n k : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) {xs C μ B : ℝ} (_hxs : 0<xs) (hC : 0≤C)
    (hmacro : 1≤C*μ) (d : GaussianStep (FeatureIndex n) → ℝ≥0)
    (hd : ∀ st ∈ steps, ∀ i : Fin n, st.2 (Sum.inl i)=d st)
    (hB : physicalFieldDuration d steps≤B) (vs : Finset ℝ)
    (hcover : ∀ y : ℝ, xs≤y → μ≤y ∨ ∃ v ∈ vs, v≤y ∧ y<2*v)
    (hband : ∀ v ∈ vs, ∀ i ≤ steps.length+1,
      v≤xs+physicalCutMass 0 steps i → xs+physicalCutMass 0 steps i<2*v →
      PhysicalRawWindowAt n k steps q₀ xs C d i) :
    PhysicalRawWindowCover n k steps q₀ xs C B := by
  refine ⟨d,hd,hB,?_⟩
  intro i hi
  rcases hcover (xs+physicalCutMass 0 steps i)
    (by have hh := (physicalCutMass_mem steps ha i).1; linarith) with hlarge|⟨v,hv,hlo,hhi⟩
  · exact Or.inl (hmacro.trans (mul_le_mul_of_nonneg_left hlarge hC))
  · exact Or.inr (hband v hv i hi hlo hhi)

 theorem eventually_physicalRawWindowCover_of_finite (n k : ℕ) (hn : 0<n)
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (us : List PositiveMass) (hus : ∀ u ∈ us, u.val≤1)
    {xs C μ B : ℝ} (hxs : 0<xs) (hC : 0≤C) (hmacro : 1≤C*μ)
    (hB : (h 1:ℝ)-(h 0:ℝ)≤B) (vs : Finset ℝ)
    (hcover : ∀ y : ℝ, xs≤y → μ≤y ∨ ∃ v ∈ vs, v≤y ∧ y<2*v)
    (hband : ∀ v ∈ vs, ∀ᶠ j : ℕ in atTop,
      let steps := sampleClockSteps (completedPathClock n b h) 0 (finiteCutMasses us j)
      let d := fun st : GaussianStep (FeatureIndex n) => st.2 (Sum.inl ⟨0,hn⟩)
      ∀ i ≤ steps.length+1, v≤xs+physicalCutMass 0 steps i →
        xs+physicalCutMass 0 steps i<2*v →
        PhysicalRawWindowAt n k steps (completedPathClock n b h 0) xs C d i) :
    ∀ᶠ j : ℕ in atTop, PhysicalRawWindowCover n k
      (sampleClockSteps (completedPathClock n b h) 0 (finiteCutMasses us j))
      (completedPathClock n b h 0) xs C B := by
  have hbnd : ∀ᶠ j : ℕ in atTop, ∀ v ∈ (vs:Set ℝ),
      let steps := sampleClockSteps (completedPathClock n b h) 0 (finiteCutMasses us j)
      let d := fun st : GaussianStep (FeatureIndex n) => st.2 (Sum.inl ⟨0,hn⟩)
      ∀ i ≤ steps.length+1, v≤xs+physicalCutMass 0 steps i →
        xs+physicalCutMass 0 steps i<2*v →
        PhysicalRawWindowAt n k steps (completedPathClock n b h 0) xs C d i :=
    (eventually_all_finite vs.finite_toSet).mpr hband
  filter_upwards [hbnd] with j hj
  have ha := finiteCutMasses_ordered us hus j
  have he := finiteCutMasses_end us hus j
  apply physicalRawWindowCover_of_finite n k _ (sampleClockSteps_ordered _ _ ha)
    _ hxs hC hmacro (fun st => st.2 (Sum.inl ⟨0,hn⟩))
    (sampledFieldClock_aligned n hn b h _ 0) _ vs hcover hj
  rwa [sampledFieldDuration_total n hn b h hb hh _ ha he]

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

 theorem comparison_minimum_retained_raw_band {N δ U L E d r₀ u₀ : ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hLU : L≤U) (hE : 0<E) (hd : 0≤d)
    (hq : 2≤N^δ) (hr₀ : r₀ ∈ Icc (0:ℝ) (1/4)) (hu₀ : u₀ ∈ Icc (0:ℝ) (1/4))
    (n : ℕ) (hn : 0<n) (g : ℝ → ℝ) :
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let _M' := comparisonCapSlope N δ U L E d
    let c := k 1
    let hr : r₀ ≤ 1 := le_trans hr₀.2 (by norm_num)
    let hu : u₀ ∈ Icc (0:ℝ) 1 := ⟨hu₀.1,le_trans hu₀.2 (by norm_num)⟩
    let hc : 0<c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
    let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
    let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd
    let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd (show (0:ℝ)≤1 by norm_num)
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
    ∀ (us : List PositiveMass) (hus : ∀ u ∈ us, u.val≤1)
    (p q t : PositiveMass) (hpu : p ∈ us) (hqu : q ∈ us)
    (hp₀ : u₀<p.val) (hpq : p.val<q.val) (hqt : q.val<t.val) (ht₁ : t.val≤1)
    (xs η cl cu R F κ K Ca v C : ℝ) (J ℓ : ℕ)
    (hxs : 0<xs) (hcl : 0<cl) (hcu : 0≤cu) (hR : 0<R)
    (hκ : 0<κ) (hK : 1≤K) (hCa : 0<Ca) (hC : 0≤C)
    (hFmass : 1+2*cu≤F) (hFradius : 1+1/R≤F) (hJ : 1≤J)
    (hbare : MonotoneOn h (Icc u₀ 1)),
    let a := (constrainedQuantile hr hc hk hkc hm hM α ⟨p.val,hp₀.le,hpq.le.trans (hqt.le.trans ht₁)⟩).val
    let ab := (constrainedQuantile hr hc hk hkc hm hM α ⟨q.val,hp₀.le.trans hpq.le,hqt.le.trans ht₁⟩).val
    let ac := (constrainedQuantile hr hc hk hkc hm hM α ⟨t.val,hp₀.le.trans (hpq.le.trans hqt.le),ht₁⟩).val
    let T := (2:ℝ)^J*ab
    let Lclock := 8*(K+1)/κ
    N^(-δ)*U<t.val-q.val → ac+(L/N^δ)*Real.log ((1+U)/U)<C*v →
    xs≤a → a≤Ca*v → ab≤K*a → cl*a≤q.val-p.val → q.val-p.val≤K*cu*a →
    0<M q.val → 0<η → η≤a → r₀<a/2 →
    η=(1/Real.sqrt (M q.val*((n:ℝ)*g a*a^4)))*a →
    T≤1 → R≤(2:ℝ)^J*a →
    (∀ z ∈ Icc (a/2) T, cl*z≤α.val.val z ∧ α.val.val z≤cu*z) →
    (∀ z ∈ Icc (a/2) T, κ≤1-comparisonLogSlope g z) →
    ((J+3:ℕ):ℝ)^3*(4*(K+1)*cu*nearPairMomentConstant (ℓ+1)^(((ℓ+1:ℕ):ℝ)⁻¹)*
       (1+(K+1)*cu)^2 +
       4*K*cu*(projectionLpConstant ℓ)^2*(Real.log (n:ℝ))^4*(F^2/((cl/2)/4)^2)*Lclock)*
       Real.sqrt (M q.val/((n:ℝ)*g a*a^4)) ≤
       (cl/(4*Ca))^2/(1+(2*(ℓ+1:ℕ):ℝ)^2/3) →
    ∀ᶠ j : ℕ in atTop,
      let steps := sampleClockSteps (completedPathClock n b' h') 0 (finiteCutMasses us j)
      let d := fun st : GaussianStep (FeatureIndex n) => st.2 (Sum.inl ⟨0,hn⟩)
      ∀ i : ℕ, v≤xs+physicalCutMass 0 steps i → physicalCutMass 0 steps i<p.val →
        PhysicalRawWindowAt n ℓ steps (completedPathClock n b' h' 0) xs C d i := by
  dsimp only
  intro α hg hgpos hp b h hb hh hbn hhn hmin
  let k := comparisonFloor N δ U
  let M := comparisonCap N δ U L E d
  let c := k 1
  let hr : r₀≤1 := le_trans hr₀.2 (by norm_num)
  let hu : u₀≤1 := le_trans hu₀.2 (by norm_num)
  let hc : 0<c := comparisonFloor_pos hN hU (by norm_num)
  let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
  let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
  let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd
  let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd (show (0:ℝ)≤1 by norm_num)
  let b' := fun u => (b u-omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) u).toNNReal
  let h' := fun u => (h u+omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
      (hg.continuous.mul continuous_id) α) u).toNNReal
  intro us hus p q t hpu hqu hp₀ hpq hqt ht₁ xs η cl cu R F κ K Ca v C J ℓ
    hxs hcl hcu hR hκ hK hCa hC hFmass hFradius hJ hbare
  let Q := constrainedQuantile hr hc hk hkc hm hM α
  let pm : Icc u₀ 1 := ⟨p.val,hp₀.le,hpq.le.trans (hqt.le.trans ht₁)⟩
  let qm : Icc u₀ 1 := ⟨q.val,hp₀.le.trans hpq.le,hqt.le.trans ht₁⟩
  let tm : Icc u₀ 1 := ⟨t.val,hp₀.le.trans (hpq.le.trans hqt.le),ht₁⟩
  let a := (Q pm).val
  let ab := (Q qm).val
  let T := (2:ℝ)^J*ab
  intro hfloor hcenter hxa hav hba hmasslo hmasshi hA hη hηa hr₀a hηeq hT hRJ hreg hslope hmargin
  have hmean := (comparison_minimum_mass_center hN hU hL hLU hE hd hq hr₀ hu₀ n hn g
    α hg hgpos hp b h hb hh hbn hhn hmin qm tm (hp₀.trans hpq) hfloor).trans_lt hcenter
  have hb' : MonotoneOn b' (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact Real.toNNReal_mono (hb α hu hv huv)
  have hh' : MonotoneOn h' (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact Real.toNNReal_mono (hh α hu hv huv)
  have ha : 0<a := hxs.trans_le hxa
  have hab : a≤ab := (inverseConstraintOrderIso hr hc hk hkc hm hM α).symm.monotone hpq.le
  have habT : a/2≤T := by
    have hjp : (1:ℝ)≤2^J := one_le_pow₀ (by norm_num)
    have hh : ab≤T := by dsimp [T]; nlinarith [ha.le.trans hab]
    linarith
  have hsub : Icc (a/2) T ⊆ Icc r₀ 1 := fun z hz => ⟨hr₀a.le.trans hz.1,hz.2.trans hT⟩
  have hsub' : Icc (a/2) T ⊆ Ioc r₀ 1 := fun z hz => ⟨hr₀a.trans_le hz.1,hz.2.trans hT⟩
  have hder : ∀ z ∈ Icc (a/2) T, DifferentiableAt ℝ g z :=
    fun z _ => (hg.differentiable (by norm_num)).differentiableAt
  have hpos : ∀ z ∈ Icc (a/2) T, 0<g z := fun z hz => hgpos z (hsub hz)
  have hmon := strength_radial_monotonicities (by linarith : 0<a/2) habT hder hpos
    (fun z hz => hp z (hsub' hz))
  have hgrowth : ∀ z ∈ Icc (a/2) T, ∀ t ∈ Icc (a/2) T, z≤t →
      κ*g t*(t-z)≤(h' (α.val.val t):ℝ)-(h' (α.val.val z):ℝ) := by
    intro z hz t ht hzt
    have hst : Icc z t ⊆ Icc (a/2) T := fun w hw => ⟨hz.1.trans hw.1,hw.2.trans ht.2⟩
    exact changedField_toNNReal_radius_growth hr hu hu₀.1 hc hk hkc hm hM α g h
      hg.continuous hbare (hh α) (hhn α) (hsub hz) (hsub ht) hzt
      (fun w hw => hder w (hst hw)) (fun w hw => hpos w (hst hw))
      (hmon.1.mono hst) hκ.le (fun w hw => hslope w (hst hw))
  have hMabs : ∀ u ∈ Icc (0:ℝ) 1, 0≤M u :=
    fun u hu => comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd hu.1
  have hstep := eventually_physicalRetainedBand n hn b' h' hb' hh' us hus hr hu hu₀.1
    hc hk hkc hm hMabs α p q hpu hqu hp₀.le (hqt.le.trans ht₁) hpq
    xs η cl cu R F κ K Ca v C J ℓ g hxs hcl hcu hR hκ hK hCa hC hFmass hFradius hJ hmean
    hxa hav hba hmasslo hmasshi hA (hgpos a (Q pm).property) hη hηa hr₀a hηeq hT hRJ
    hreg (fun z hz => (hpos z hz).le) hmon.1 hmon.2.1 hgrowth hmargin
  exact hstep

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem eventually_comparison_minimum_raw_moment_of_finite_margins
    (ℓ : ℕ) (Bclock : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ {N δ U L E d r₀ u₀ : ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hLU : L≤U) (hE : 0<E) (hd : 0≤d)
    (hq : 2≤N^δ) (hr₀ : r₀ ∈ Icc (0:ℝ) (1/4)) (hu₀ : u₀ ∈ Icc (0:ℝ) (1/4))
    (hn : 0<n) (g : ℝ → ℝ),
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let M' := comparisonCapSlope N δ U L E d
    let c := k 1
    let hr : r₀ ≤ 1 := le_trans hr₀.2 (by norm_num)
    let hu : u₀ ∈ Icc (0:ℝ) 1 := ⟨hu₀.1,le_trans hu₀.2 (by norm_num)⟩
    let hc : 0<c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
    let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
    let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd
    let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd (show (0:ℝ)≤1 by norm_num)
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
    ∀ (us : List PositiveMass) (hus : ∀ u ∈ us, u.val≤1)
    (u : PositiveMass) (huobs : u ∈ us)
    (xs C μ cl cu R F κ K Ca : ℝ) (hxs : 0<xs) (hC : 1≤C)
    (hmacro : 1≤C*μ) (hcl : 0<cl) (hcu : 0≤cu) (hR : 0<R)
    (hκ : 0<κ) (hK : 1≤K) (hCa : 0<Ca)
    (hFmass : 1+2*cu≤F) (hFradius : 1+1/R≤F)
    (hbare : MonotoneOn h (Icc u₀ 1))
    (hB : (h' 1:ℝ)-(h' 0:ℝ)≤Bclock)
    (vs : Finset ℝ) (pp qq tt : ℝ → PositiveMass) (η : ℝ → ℝ) (J : ℝ → ℕ)
    (hcover : ∀ y : ℝ, xs≤y → μ≤y ∨ ∃ v ∈ vs, v≤y ∧ y<2*v)
    (hcuts : ∀ v ∈ vs, pp v ∈ us ∧ qq v ∈ us ∧ u₀<(pp v).val ∧
      (pp v).val<(qq v).val ∧ (qq v).val<(tt v).val ∧ (tt v).val≤1 ∧
      2*v≤(pp v).val ∧ 1≤J v),
    (∀ v (hv : v ∈ vs),
      let hp₀ := (hcuts v hv).2.2.1
      let hpq := (hcuts v hv).2.2.2.1
      let hqt := (hcuts v hv).2.2.2.2.1
      let ht₁ := (hcuts v hv).2.2.2.2.2.1
      let a := (constrainedQuantile hr hc hk hkc hm hM α
        ⟨(pp v).val,hp₀.le,hpq.le.trans (hqt.le.trans ht₁)⟩).val
      let ab := (constrainedQuantile hr hc hk hkc hm hM α
        ⟨(qq v).val,hp₀.le.trans hpq.le,hqt.le.trans ht₁⟩).val
      let ac := (constrainedQuantile hr hc hk hkc hm hM α
        ⟨(tt v).val,hp₀.le.trans (hpq.le.trans hqt.le),ht₁⟩).val
      let T := (2:ℝ)^(J v)*ab
      let Lclock := 8*(K+1)/κ
      N^(-δ)*U<(tt v).val-(qq v).val ∧
      ac+(L/N^δ)*Real.log ((1+U)/U)<C*v ∧
      xs≤a ∧ a≤Ca*v ∧ ab≤K*a ∧ cl*a≤(qq v).val-(pp v).val ∧
      (qq v).val-(pp v).val≤K*cu*a ∧ 0<M (qq v).val ∧ 0<η v ∧ η v≤a ∧ r₀<a/2 ∧
      η v=(1/Real.sqrt (M (qq v).val*((n:ℝ)*g a*a^4)))*a ∧ T≤1 ∧ R≤(2:ℝ)^(J v)*a ∧
      (∀ z ∈ Icc (a/2) T, cl*z≤α.val.val z ∧ α.val.val z≤cu*z) ∧
      (∀ z ∈ Icc (a/2) T, κ≤1-comparisonLogSlope g z) ∧
      ((J v+3:ℕ):ℝ)^3*(4*(K+1)*cu*nearPairMomentConstant (ℓ+1)^(((ℓ+1:ℕ):ℝ)⁻¹)*
        (1+(K+1)*cu)^2 +
        4*K*cu*(projectionLpConstant ℓ)^2*(Real.log (n:ℝ))^4*(F^2/((cl/2)/4)^2)*Lclock)*
        Real.sqrt (M (qq v).val/((n:ℝ)*g a*a^4)) ≤
        (cl/(4*Ca))^2/(1+(2*(ℓ+1:ℕ):ℝ)^2/3)) →
      pathPowerMoment (uniformWeight n) (finiteFeature n) (completedPathClock n b' h')
        (orderedOverlap n) (2*(ℓ+1)) u.val ≤ (2*C*(xs+u.val))^(2*(ℓ+1)) := by
  filter_upwards [eventually_physical_path_raw_bootstrap ℓ Bclock] with n hnraw
  intro N δ U L E d r₀ u₀ hN hU hL hLU hE hd hq hr₀ hu₀ hn g
  dsimp only
  intro α hg hgpos hp b h hb hh hbn hhn hmin
  let k := comparisonFloor N δ U
  let M := comparisonCap N δ U L E d
  let c := k 1
  let hr : r₀≤1 := le_trans hr₀.2 (by norm_num)
  let hu : u₀≤1 := le_trans hu₀.2 (by norm_num)
  let hc : 0<c := comparisonFloor_pos hN hU (by norm_num)
  let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
  let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
  let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd
  let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd (show (0:ℝ)≤1 by norm_num)
  let b' := fun u => (b u-omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) u).toNNReal
  let h' := fun u => (h u+omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
      (hg.continuous.mul continuous_id) α) u).toNNReal
  intro us hus u huobs xs C μ cl cu R F κ K Ca hxs hC hmacro hcl hcu hR hκ hK hCa hFmass hFradius
    hbare hB vs pp qq tt η J hcover hcuts hmargin
  have hb' : MonotoneOn b' (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact Real.toNNReal_mono (hb α hu hv huv)
  have hh' : MonotoneOn h' (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact Real.toNNReal_mono (hh α hu hv huv)
  have hC0 : 0≤C := zero_le_one.trans hC
  have hband : ∀ v ∈ vs, ∀ᶠ j : ℕ in atTop,
      let steps := sampleClockSteps (completedPathClock n b' h') 0 (finiteCutMasses us j)
      let d := fun st : GaussianStep (FeatureIndex n) => st.2 (Sum.inl ⟨0,hn⟩)
      ∀ i ≤ steps.length+1, v≤xs+physicalCutMass 0 steps i → xs+physicalCutMass 0 steps i<2*v →
        PhysicalRawWindowAt n ℓ steps (completedPathClock n b' h' 0) xs C d i := by
    intro v hv
    obtain ⟨hpu,hqu,hp₀,hpq,hqt,ht₁,h2v,hJ⟩ := hcuts v hv
    obtain ⟨hfloor,hcenter,hxa,hav,hba,hmasslo,hmasshi,hA,hη,hηa,hr₀a,hηeq,hT,hRJ,hreg,hslope,hloss⟩ := hmargin v hv
    have hh := comparison_minimum_retained_raw_band hN hU hL hLU hE hd hq hr₀ hu₀ n hn g
      α hg hgpos hp b h hb hh hbn hhn hmin us hus (pp v) (qq v) (tt v) hpu hqu hp₀ hpq hqt ht₁
      xs (η v) cl cu R F κ K Ca v C (J v) ℓ hxs hcl hcu hR hκ hK hCa hC0 hFmass hFradius hJ hbare
      hfloor hcenter hxa hav hba hmasslo hmasshi hA hη hηa hr₀a hηeq hT hRJ hreg hslope hloss
    filter_upwards [hh] with j hj
    dsimp only
    intro i hi hlo hhi
    exact hj i hlo (by linarith)
  have hfinalcover := eventually_physicalRawWindowCover_of_finite n ℓ hn b' h' hb' hh' us hus
    hxs hC0 hmacro hB vs hcover hband
  apply hnraw b' h' hb' hh' (finiteCutMasses us) (fun j => ((j+1:ℕ):ℝ)⁻¹)
    (finiteCutMasses_ordered us hus) (finiteCutMasses_mesh us hus)
    (finiteCutMasses_end us hus) uniformMasses_mesh_tendsto xs C hxs hC u (hus u huobs)
    (fun j => finiteCutMasses_nodes us j huobs) hfinalcover

end SKFluctuations

 

 

namespace SKFluctuations
open Set

 theorem exists_rawWindowDepth {a b R K N : ℝ} (ha : 0<a) (haR : a≤R)
    (hb : b≤K*a) (hK : 0≤K) (hR : R≤1) (hN : 0<N) (hNa : 1/N≤a) :
    ∃ J : ℕ, 1≤J ∧ R≤(2:ℝ)^J*a ∧ (2:ℝ)^J*b≤2*K*R ∧
      (J+3:ℕ)≤Real.log N/Real.log 2+4 := by
  have hr : 1≤R/a := (le_div_iff₀ ha).mpr (by simpa using haR)
  obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near hr (show (1:ℝ)<2 by norm_num)
  refine ⟨j+1,by omega,?_,?_,?_⟩
  · exact ((div_lt_iff₀ ha).mp hhi).le
  · have hj : (2:ℝ)^(j+1)*a≤2*R := by
      have hh := (le_div_iff₀ ha).mp hlo
      rw [pow_succ]
      nlinarith
    calc (2:ℝ)^(j+1)*b≤(2:ℝ)^(j+1)*(K*a) := mul_le_mul_of_nonneg_left hb (by positivity)
         _=K*((2:ℝ)^(j+1)*a) := by ring
         _≤K*(2*R) := mul_le_mul_of_nonneg_left hj hK
         _=2*K*R := by ring
  · have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
    have hRaN : R/a≤N := by
      apply (div_le_iff₀ ha).mpr
      have hNa' := (div_le_iff₀ hN).mp hNa
      nlinarith
    have hjN : (2:ℝ)^j≤N := hlo.trans hRaN
    have hlog := Real.log_le_log (by positivity : (0:ℝ)<2^j) hjN
    rw [Real.log_pow] at hlog
    have hj : (j:ℝ)≤Real.log N/Real.log 2 := (le_div_iff₀ hlog2).mpr hlog
    push_cast
    linarith

end SKFluctuations

 

 

namespace SKFluctuations
open Filter
open scoped Topology

 theorem rawWindowLogFactor {z A B U V L : ℝ} {J : ℕ}
    (hz : 1 ≤ z) (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hJ : (J+3:ℕ) ≤ A*z) (hL : L ≤ B*z) :
    ((J+3:ℕ):ℝ)^3*(U+V*z^4*L) ≤ A^3*(U+V*B)*z^8 := by
  have hz0 : 0 ≤ z := le_trans (by norm_num) hz
  have hJ0 : 0 ≤ ((J+3:ℕ):ℝ) := by positivity
  have hc := pow_le_pow_left₀ hJ0 hJ 3
  have hz5 : 1 ≤ z^5 := one_le_pow₀ hz
  have hUm : U ≤ U*z^5 := by nlinarith
  have hLm := mul_le_mul_of_nonneg_left hL (show 0 ≤ V*z^4 by positivity)
  have hterm : U+V*z^4*L ≤ (U+V*B)*z^5 := by nlinarith [hUm,hLm]
  have hright : 0 ≤ (U+V*B)*z^5 := by positivity
  calc
    _ ≤ ((J+3:ℕ):ℝ)^3*((U+V*B)*z^5) :=
      mul_le_mul_of_nonneg_left hterm (by positivity)
    _ ≤ (A*z)^3*((U+V*B)*z^5) :=
      mul_le_mul hc le_rfl hright (pow_nonneg (mul_nonneg hA hz0) _)
    _ = _ := by ring

 theorem eventually_rawWindow_scalar_margin {κ A B U V R ε : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hR : 0 ≤ R) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (J : ℕ) (L ratio : ℝ),
      (J+3:ℕ) ≤ A*Real.log (n:ℝ) → L ≤ B*Real.log (n:ℝ) →
      ratio ≤ R*(n:ℝ)^(-κ) →
      ((J+3:ℕ):ℝ)^3*(U+V*(Real.log (n:ℝ))^4*L)*Real.sqrt ratio ≤ ε := by
  have ht := tendsto_raw_balanced_margin hκ (A^3*(U+V*B)) R hR
  have hz : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n:ℝ) := by
    have hh := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1:ℝ))
    exact hh
  filter_upwards [ht.eventually (gt_mem_nhds hε),hz] with n hn hlog
  intro J L ratio hJ hL hr
  have hf := rawWindowLogFactor hlog hA hB hU hV hJ hL
  have hm := mul_le_mul hf (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _)
    (show 0 ≤ A^3*(U+V*B)*(Real.log (n:ℝ))^8 by positivity)
  exact hm.trans hn.le

end SKFluctuations

 

 

namespace SKFluctuations
open Filter Set
open scoped Topology

 theorem balanced_first_layer {a A B : ℝ} (ha : 0<a) (hA : 1≤A) (hB : 0<B)
    (hr : A/B≤1) :
    0<(1/Real.sqrt (A*B))*a ∧ (1/Real.sqrt (A*B))*a≤a := by
  have hAB : A≤B := by simpa using (div_le_iff₀ hB).mp hr
  have hA0 : 0<A := lt_of_lt_of_le zero_lt_one hA
  have hs : 0<Real.sqrt (A*B) := Real.sqrt_pos.mpr (mul_pos hA0 hB)
  have hs1 : 1≤Real.sqrt (A*B) := by
    apply (Real.le_sqrt (by norm_num) (mul_nonneg hA0.le hB.le)).2
    nlinarith [hA,hAB]
  refine ⟨by positivity,?_⟩
  have hi : 1/Real.sqrt (A*B)≤1 := (div_le_one hs).mpr hs1
  simpa using mul_le_mul_of_nonneg_right hi ha.le

 theorem eventually_balancedRawParameters {κ K R κ₀ U V C ε : ℝ}
    (hκ : 0<κ) (hK : 1≤K) (hR : R≤1) (hκ₀ : 0<κ₀)
    (hU : 0≤U) (hV : 0≤V) (hC : 0≤C) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ a ab A B : ℝ,
      0<a → a≤R → ab≤K*a → 1/(n:ℝ)≤a → 1≤A → 0<B →
      A/B≤C*(n:ℝ)^(-κ) →
      ∃ J : ℕ, 1≤J ∧ R≤(2:ℝ)^J*a ∧ (2:ℝ)^J*ab≤2*K*R ∧
        0<(1/Real.sqrt (A*B))*a ∧ (1/Real.sqrt (A*B))*a≤a ∧
        ((J+3:ℕ):ℝ)^3*(U+V*(Real.log (n:ℝ))^4*(8*(K+1)/(κ₀/Real.log (n:ℝ))))*
          Real.sqrt (A/B) ≤ ε := by
  let DA : ℝ := 1/Real.log 2+4
  let DL : ℝ := 8*(K+1)/κ₀
  have hDA : 0≤DA := by dsimp [DA]; positivity
  have hDL : 0≤DL := by dsimp [DL]; positivity
  have ht : Tendsto (fun n : ℕ => C*(n:ℝ)^(-κ)) atTop (𝓝 0) := by
    simpa using (((tendsto_rpow_neg_atTop hκ).comp tendsto_natCast_atTop_atTop).const_mul C)
  have hz : ∀ᶠ n : ℕ in atTop, 1≤Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_rawWindow_scalar_margin hκ hDA hDL hU hV hC hε,
    ht.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),hz,eventually_gt_atTop (0:ℕ)] with n hn ht hnlog hn0
  intro a ab A B ha haR hab hNa hA hB hratio
  have hN : 0<(n:ℝ) := by exact_mod_cast hn0
  obtain ⟨J,hJ,hreach,hstop,hdepth⟩ := exists_rawWindowDepth ha haR hab
    (show 0≤K by linarith) hR hN hNa
  obtain ⟨hη,hηa⟩ := balanced_first_layer ha hA hB (hratio.trans ht.le)
  refine ⟨J,hJ,hreach,hstop,hη,hηa,?_⟩
  have hJ' : (J+3:ℕ)≤DA*Real.log (n:ℝ) := by
    apply hdepth.trans
    dsimp [DA]
    simp only [div_eq_mul_inv,one_mul]
    nlinarith [hnlog]
  have hL : 8*(K+1)/(κ₀/Real.log (n:ℝ))≤DL*Real.log (n:ℝ) := by
    apply le_of_eq
    dsimp [DL]
    rw [div_div_eq_mul_div]
    ring
  exact hn J _ _ hJ' hL hratio

end SKFluctuations

 

 

namespace SKFluctuations
open Set Hierarchy

 theorem comparisonLowerScale_pos {N E d : ℝ} (hN : 0<N) (hE : 0<E) (hd : 0<d) :
    0<comparisonLowerScale N E d := by unfold comparisonLowerScale; positivity

 theorem comparisonSmallMass_pos {N E : ℝ} (hN : 0<N) (hE : 0<E) :
    0<comparisonSmallMass N E := by unfold comparisonSmallMass; positivity

 theorem comparison_scale_ratios {N E d : ℝ} (hN : 0<N) (hE : 0<E) (hd : 0<d)
    (hupper : Real.sqrt N*E ≤ d^2) :
    comparisonSmallMass N E/comparisonLowerScale N E d ≤ d^3/(N^2*E^3) ∧
    (comparisonSmallMass N E)^2*d^2/(comparisonLowerScale N E d)^4 = (d^3/(N^2*E^3))^2 := by
  have hs : 0<Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsq := Real.sq_sqrt hN.le
  constructor
  · unfold comparisonSmallMass comparisonLowerScale
    have hp : 0<N^2*E^3 := by positivity
    apply (le_div_iff₀ hp).mpr
    have hid : 1/(N*E)/(Real.sqrt N*E/d)*(N^2*E^3) = d*(Real.sqrt N*E) := by
      field_simp
      nlinarith [hsq]
    rw [hid]
    calc d*(Real.sqrt N*E) ≤ d*d^2 := mul_le_mul_of_nonneg_left hupper hd.le
         _ = d^3 := by ring
  · unfold comparisonSmallMass comparisonLowerScale
    have hfour : (Real.sqrt N)^4=N^2 := by nlinarith [sq_nonneg ((Real.sqrt N)^2-N)]
    field_simp
    nlinarith [hfour]

 theorem comparison_cubic_margin {N E d m C : ℝ}
    (hN : 0<N) (hE : 0<E) (hd : 0<d) (hC : 0<C)
    (hlower : N^(-(2:ℝ)/3+m)*d ≤ C*E) :
    d^3/(N^2*E^3) ≤ C^3*N^(-3*m) := by
  have hr : 0<N^(-(2:ℝ)/3+m) := Real.rpow_pos_of_pos hN _
  have hp := (pow_le_pow_iff_left₀ (mul_nonneg hr.le hd.le)
    (mul_nonneg hC.le hE.le) (by decide : 3 ≠ 0)).mpr hlower
  have heq : (N^(-(2:ℝ)/3+m))^3=N^(-2+3*m) := by
    rw [← Real.rpow_mul_natCast hN.le]
    congr 1
    ring
  rw [mul_pow,heq,mul_pow] at hp
  have heq' : N^(-3*m)*N^(-2+3*m)=N^(-(2:ℝ)) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have hp' := mul_le_mul_of_nonneg_left hp (show 0≤N^(-3*m) by positivity)
  have hr2 : N^(-(2:ℝ))=(N^2)⁻¹ := by rw [Real.rpow_neg hN.le,Real.rpow_two]
  have hden : 0<N^2*E^3 := by positivity
  apply (div_le_iff₀ hden).mpr
  have hcancel : N^(-3*m)*(N^(-2+3*m)*d^3) = d^3/(N^2) := by
    rw [← mul_assoc,heq',hr2]
    ring
  rw [hcancel] at hp'
  have hmul := mul_le_mul_of_nonneg_left hp' (show 0≤N^2 by positivity)
  have hdiv : N^2*(d^3/N^2)=d^3 := mul_div_cancel₀ _ (pow_ne_zero _ hN.ne')
  rw [hdiv] at hmul
  nlinarith

end SKFluctuations

 

 

namespace SKFluctuations
open Set Hierarchy

 theorem comparisonCap_ratio (N E d δ v C : ℝ) (hN : 0<N) (hE : 0<E)
    (hd : 0<d) (hC : 0≤C) (hv : comparisonLowerScale N E d≤v)
    (hU : comparisonSmallMass N E≤comparisonLowerScale N E d) :
    comparisonCap N δ (comparisonSmallMass N E) (comparisonConstraintLength N E d) E d (C*v) /
      (N*E*v)^2 ≤
    N^δ*((C+1)*(comparisonSmallMass N E/comparisonLowerScale N E d+
      (comparisonSmallMass N E)^2*d^2/(comparisonLowerScale N E d)^4)+
      (C+1)^2*(d^3/(N^2*E^3))) := by
  let a := comparisonLowerScale N E d
  let U := comparisonSmallMass N E
  have ha : 0<a := comparisonLowerScale_pos hN hE hd
  have hu : 0<U := comparisonSmallMass_pos hN hE
  have hv0 : 0<v := ha.trans_le hv
  have hL : 0<a^3/d^2 := by positivity
  have hx : 0≤C*v+U := by positivity
  have hsize : C*v+U≤(C+1)*v := by dsimp only [U,a] at *; nlinarith
  have hden : 0<(N*E*v)^2 := by positivity
  have hrec : (C*v+U)/min U (a^3/d^2) ≤ (C*v+U)/U+(C*v+U)*d^2/a^3 := by
    by_cases h : U≤a^3/d^2
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (by positivity)
    · rw [min_eq_right (le_of_not_ge h)]
      have heq : (C*v+U)/(a^3/d^2)=(C*v+U)*d^2/a^3 := by field_simp
      rw [heq]
      exact le_add_of_nonneg_left (by positivity)
  have hterm1 : ((C*v+U)/U)/(N*E*v)^2 ≤ (C+1)*U/a := by
    calc _ ≤ (((C+1)*v)/U)/(N*E*v)^2 := by gcongr
         _ = (C+1)*U/v := by dsimp [U,comparisonSmallMass]; field_simp
         _ ≤ (C+1)*U/a := div_le_div_of_nonneg_left (by positivity) ha hv
  have hterm2 : ((C*v+U)*d^2/a^3)/(N*E*v)^2 ≤ (C+1)*(U^2*d^2/a^4) := by
    calc _ ≤ (((C+1)*v)*d^2/a^3)/(N*E*v)^2 := by gcongr
         _ = ((C+1)*U^2*d^2/a^3)/v := by dsimp [U,comparisonSmallMass]; field_simp
         _ ≤ ((C+1)*U^2*d^2/a^3)/a := div_le_div_of_nonneg_left (by positivity) ha hv
         _ = (C+1)*(U^2*d^2/a^4) := by field_simp
  have hterm3 : ((d^3/E)*(C*v+U)^2)/(N*E*v)^2 ≤ (C+1)^2*(d^3/(N^2*E^3)) := by
    calc _ ≤ ((d^3/E)*((C+1)*v)^2)/(N*E*v)^2 := by gcongr
         _ = _ := by field_simp
  change (N^δ*((C*v+U)/min U (a^3/d^2)+(d^3/E)*(C*v+U)^2))/(N*E*v)^2 ≤ _
  have hnδ : 0≤N^δ := Real.rpow_nonneg hN.le _
  calc _ ≤ N^δ*((C*v+U)/U+(C*v+U)*d^2/a^3+(d^3/E)*(C*v+U)^2)/(N*E*v)^2 := by gcongr
       _ = N^δ*(((C*v+U)/U)/(N*E*v)^2+((C*v+U)*d^2/a^3)/(N*E*v)^2+
          ((d^3/E)*(C*v+U)^2)/(N*E*v)^2) := by ring
       _ ≤ N^δ*((C+1)*U/a+(C+1)*(U^2*d^2/a^4)+(C+1)^2*(d^3/(N^2*E^3))) :=
          mul_le_mul_of_nonneg_left (add_le_add (add_le_add hterm1 hterm2) hterm3) hnδ
       _ = _ := by change _ = N^δ*((C+1)*(U/a+U^2*d^2/a^4)+(C+1)^2*(d^3/(N^2*E^3))); ring

end SKFluctuations

end

end OAI
