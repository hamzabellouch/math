import Mathlib
import OAI.Probability.SKFluctuations.PhysicalRetainedCut

namespace OAI

/-! Raw Loss Logarithms. -/

noncomputable section


namespace SKFluctuations
open Filter Set Hierarchy
open scoped Topology

 theorem tendsto_raw_log_margin (p : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => (Real.log (n:ℝ))^p*(n:ℝ)^(-κ)) atTop (𝓝 0) := by
  have hh := ((isLittleO_log_rpow_rpow_atTop (p:ℝ) hκ).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop
  convert hh using 1
  funext n
  dsimp only [Function.comp_apply]
  rw [Real.rpow_natCast,Real.rpow_neg (Nat.cast_nonneg n),div_eq_mul_inv]

namespace PhysicalBandWindow
variable {n : ℕ} {steps : List (GaussianStep (FeatureIndex n))} {xs : ℝ}

 def generalFarBaseConstant (k : ℕ) (w : PhysicalBandWindow n steps xs) (K : ℝ) : ℝ :=
    4*K*w.C*(projectionLpConstant k)^2*(w.F^2/(w.c₀/4)^2)

 theorem generalScaleFactor_log_bound (k : ℕ) (w : PhysicalBandWindow n steps xs)
    {K L D L₀ : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D) (hL₀ : 0 ≤ L₀)
    (hlog : 1 ≤ Real.log (n:ℝ)) (hJ : (w.depth+3:ℕ) ≤ D*Real.log (n:ℝ))
    (hL : L ≤ L₀*Real.log (n:ℝ)) :
    w.generalScaleFactor k K L ≤ D^3*(w.generalNearScaleConstant k K+
      w.generalFarBaseConstant k K*L₀)*(Real.log (n:ℝ))^8 := by
  have hn : 0 ≤ w.generalNearScaleConstant k K := by
    unfold generalNearScaleConstant
    have hc := w.C_nonneg
    have hk := nearPairMomentConstant_nonneg (k+1)
    positivity
  have hf : 0 ≤ w.generalFarBaseConstant k K := by
    unfold generalFarBaseConstant
    have hc := w.C_nonneg
    have hk := nearPairMomentConstant_nonneg (k+1)
    positivity
  have hlog0 : 0 ≤ Real.log (n:ℝ) := by linarith
  have hpow : 1 ≤ (Real.log (n:ℝ))^5 := one_le_pow₀ hlog
  have hl : w.generalFarScaleConstant k K*L ≤
      w.generalFarBaseConstant k K*L₀*(Real.log (n:ℝ))^5 := by
    calc _ = (w.generalFarBaseConstant k K*(Real.log (n:ℝ))^4)*L := by
          unfold generalFarScaleConstant generalFarBaseConstant; ring
         _ ≤ (w.generalFarBaseConstant k K*(Real.log (n:ℝ))^4)*(L₀*Real.log (n:ℝ)) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
         _ = _ := by ring
  have hnear : w.generalNearScaleConstant k K ≤ w.generalNearScaleConstant k K*(Real.log (n:ℝ))^5 := by
    simpa using mul_le_mul_of_nonneg_left hpow hn
  have hsum := add_le_add hnear hl
  have hdp : (w.depth+3:ℕ)^3 ≤ (D*Real.log (n:ℝ))^3 :=
    pow_le_pow_left₀ (by positivity) hJ _
  unfold generalScaleFactor
  calc _ ≤ (w.depth+3:ℕ)^3*((w.generalNearScaleConstant k K+w.generalFarBaseConstant k K*L₀)*
        (Real.log (n:ℝ))^5) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [hsum]
       _ ≤ (D*Real.log (n:ℝ))^3*((w.generalNearScaleConstant k K+w.generalFarBaseConstant k K*L₀)*
        (Real.log (n:ℝ))^5) := mul_le_mul hdp le_rfl (by positivity)
          (pow_nonneg (mul_nonneg hD hlog0) _)
       _ = _ := by ring

end PhysicalBandWindow
end SKFluctuations

 

 

namespace SKFluctuations
open Filter Set Hierarchy
open scoped Topology

 theorem tendsto_raw_balanced_margin {κ : ℝ} (hκ : 0 < κ) (D R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun n : ℕ => D*(Real.log (n:ℝ))^8*Real.sqrt (R*(n:ℝ)^(-κ)))
      atTop (𝓝 0) := by
  have ht := (tendsto_raw_log_margin 8 (show 0 < κ/2 by positivity)).const_mul (D*Real.sqrt R)
  convert ht using 1
  · funext n
    simp only [Real.sqrt_mul hR,Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul (Nat.cast_nonneg n)]
    have he : -κ*(1/2:ℝ)=-(κ/2) := by ring
    rw [he]
    ring
  · simp

namespace PhysicalBandWindow
variable {n : ℕ} {steps : List (GaussianStep (FeatureIndex n))} {xs : ℝ}

 theorem loss_le_half_scale (hxs : 0 < xs) (k : ℕ) (w : PhysicalBandWindow n steps xs)
    {c Ca y : ℝ} (hc : 0 < c) (hCa : 0 < Ca) (hm : c*w.a ≤ w.mass)
    (ha : w.a ≤ Ca*y)
    (hcoeff : w.coefficient k ≤ ((c/(4*Ca))^2/(1+(2*(k+1:ℕ):ℝ)^2/3))*w.a^4) :
    w.loss k ≤ y/2 := by
  let Q : ℝ := 1+(2*(k+1:ℕ):ℝ)^2/3
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have he : 0 ≤ (c/(4*Ca))^2/Q := by positivity
  have hh := w.loss_bound hxs k hc he hm hcoeff
  have heq : Q*((c/(4*Ca))^2/Q)=(c/(4*Ca))^2 := by field_simp
  change w.loss k ≤ (2/c)*Real.sqrt (Q*((c/(4*Ca))^2/Q))*w.a at hh
  rw [heq,Real.sqrt_sq (by positivity)] at hh
  have heq' : (2/c)*(c/(4*Ca))*w.a = w.a/(2*Ca) := by field_simp; ring
  rw [heq'] at hh
  exact hh.trans ((div_le_iff₀ (by positivity)).2 (by nlinarith [ha]))

 theorem eventually_coefficient_small (k : ℕ) {ε κ D R : ℝ}
    (hε : 0 < ε) (hκ : 0 < κ) (hD : 0 ≤ D) (hR : 0 ≤ R) :
    ∀ᶠ n : ℕ in atTop, ∀ (steps : List (GaussianStep (FeatureIndex n)))
      (_ha : OrderedSteps 0 steps) (xs : ℝ) (_hxs : 0 < xs)
      (w : PhysicalBandWindow n steps xs) (K e L : ℝ),
      1 ≤ K → w.b ≤ K*w.a → w.mass ≤ K*w.C*w.a → 0 < e → 0 < L → 0 < w.A →
      w.η=(1/Real.sqrt (w.A*((n:ℝ)*e*w.a^4)))*w.a →
      (1/Real.sqrt (w.A*((n:ℝ)*e*w.a^4)))*w.a*e/L ≤ w.D₀ →
      w.generalScaleFactor k K L ≤ D*(Real.log (n:ℝ))^8 →
      w.A/((n:ℝ)*e*w.a^4) ≤ R*(n:ℝ)^(-κ) →
      w.coefficient k ≤ ε*w.a^4 := by
  have ht := tendsto_raw_balanced_margin hκ D R hR
  filter_upwards [ht.eventually (gt_mem_nhds hε),eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro steps ha xs hxs w K e L hK hb hm he hL hA hη hD₀ hscale hratio
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hh := w.coefficient_balanced_general ha hxs k hK hb hm hnp he hL hA hη hD₀
  have hB : 0 ≤ D*(Real.log (n:ℝ))^8 := by positivity
  have hprod := mul_le_mul hscale (Real.sqrt_le_sqrt hratio) (Real.sqrt_nonneg _) hB
  exact hh.trans ((mul_le_mul_of_nonneg_right (hprod.trans hn.le) (by positivity)))

end PhysicalBandWindow
end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped NNReal

 theorem physicalReadyRetainedWindow (n : ℕ) (hn : 0 < n)
    (b h : ℝ → ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (has : MassOrdered 0 as)
    {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀ ≤ 1) (hu : u₀ ≤ 1) (hu₀ : 0 ≤ u₀) (hc : 0 < c)
    (hk : ContinuousOn k (Icc r₀ 1)) (hkc : ∀ t ∈ Icc r₀ 1, c ≤ k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ M u)
    (α : inverseIntegralConstraints r₀ u₀ k M)
    (p q : PositiveMass) (hpm : p ∈ as) (hqm : q ∈ as)
    (hp₀ : u₀ ≤ p.val) (hq₁ : q.val ≤ 1) (hpq : p.val < q.val)
    (xs η cl cu R F ε κ K Ca y : ℝ) (J ℓ : ℕ) (e : ℝ → ℝ)
    (hxs : 0 < xs) (hcl : 0 < cl) (hcu : 0 ≤ cu) (hR : 0 < R)
    (hκ : 0 < κ) (hK : 1 ≤ K) (hCa : 0 < Ca)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/R ≤ F) (hJ : 1 ≤ J)
    (hε : 0 ≤ ε) :
    let hM₁ := hM 1 (by norm_num)
    let a := (constrainedQuantile hr hc hk hkc hm hM₁ α ⟨p.val,hp₀,hpq.le.trans hq₁⟩).val
    let ab := (constrainedQuantile hr hc hk hkc hm hM₁ α ⟨q.val,hp₀.trans hpq.le,hq₁⟩).val
    let steps := sampleClockSteps (completedPathClock n b h) 0 as
    let hs := sampleClockSteps_ordered (completedPathClock n b h) as has
    let r := physicalQuantileGrid hr hu hc hk hkc hm hM₁ α steps hs
    let T := (2:ℝ)^J*ab
    let L := 8*(K+1)/κ
    let d := fun st : GaussianStep (FeatureIndex n) => st.2 (Sum.inl ⟨0,hn⟩)
    (∀ j : Fin (steps.length+1), r j.succ-r j.castSucc ≤ ε) →
    xs ≤ a → a ≤ Ca*y → ab ≤ K*a → cl*a ≤ q.val-p.val → q.val-p.val ≤ K*cu*a →
    0 < M q.val → 0 < e a → 0 < η → η ≤ a → ε ≤ η/8 → r₀ < a/2 →
    η=(1/Real.sqrt (M q.val*((n:ℝ)*e a*a^4)))*a →
    T ≤ 1 → R ≤ (2:ℝ)^J*a →
    (∀ t ∈ Icc (a/2) T, cl*t ≤ α.val.val t ∧ α.val.val t ≤ cu*t) →
    (∀ t ∈ Icc (a/2) T, 0 ≤ e t) → AntitoneOn e (Icc (a/2) T) →
    MonotoneOn (fun t => t*e t) (Icc (a/2) T) →
    (∀ z ∈ Icc (a/2) T, ∀ t ∈ Icc (a/2) T, z ≤ t →
      κ*e t*(t-z) ≤ (h (α.val.val t):ℝ)-(h (α.val.val z):ℝ)) →
    ((J+3:ℕ):ℝ)^3*(4*(K+1)*cu*nearPairMomentConstant (ℓ+1)^(((ℓ+1:ℕ):ℝ)⁻¹)*
       (1+(K+1)*cu)^2 +
       4*K*cu*(projectionLpConstant ℓ)^2*(Real.log (n:ℝ))^4*(F^2/((cl/2)/4)^2)*L)*
       Real.sqrt (M q.val/((n:ℝ)*e a*a^4)) ≤
       (cl/(4*Ca))^2/(1+(2*(ℓ+1:ℕ):ℝ)^2/3) →
    ∃ w : PhysicalBandWindow n steps xs,
      w.selected=physicalIntervalCells steps
        (physicalRetainedIndex steps p.val).val (physicalRetainedIndex steps q.val).val ∧
      w.a=a ∧ w.b=ab ∧ w.mass=q.val-p.val ∧ w.A=M q.val ∧
      w.loss ℓ ≤ y/2 ∧
      (∀ s ∈ Ioc w.a w.b, w.D₀ ≤ physicalFieldDuration d (steps.take (radiusGridCut w.radius (s+w.η)))-
        physicalFieldDuration d (steps.take (radiusGridCut w.radius s))) ∧
      (∀ s ∈ Icc (2*w.a) ((2:ℝ)^w.depth*w.b), w.D₀ ≤
        physicalFieldDuration d (steps.take (radiusGridCut w.radius s))-
        physicalFieldDuration d (steps.take (radiusGridCut w.radius (3*s/4)))) := by
  dsimp only
  intro hmesh hxa hay hba hmasslo hmasshi hA hea hη hηa hεη hr₀ hηeq hT hRJ hreg he hem her hH hmargin
  let hM₁ := hM 1 (by norm_num)
  let a := (constrainedQuantile hr hc hk hkc hm hM₁ α ⟨p.val,hp₀,hpq.le.trans hq₁⟩).val
  let ab := (constrainedQuantile hr hc hk hkc hm hM₁ α ⟨q.val,hp₀.trans hpq.le,hq₁⟩).val
  let steps := sampleClockSteps (completedPathClock n b h) 0 as
  let hs := sampleClockSteps_ordered (completedPathClock n b h) as has
  let r := physicalQuantileGrid hr hu hc hk hkc hm hM₁ α steps hs
  let T := (2:ℝ)^J*ab
  let L := 8*(K+1)/κ
  let D₀ := κ*e a*η/(8*(K+1))
  have hD₀ : 0 < D₀ := by dsimp [D₀]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hεa : ε ≤ a/2 := by change η ≤ a at hηa; linarith
  obtain ⟨w,hwr,hws,hwa,hwb,hwm,hwA,hwη,hwD,hwc,hwC,hwR,hwF,hwJ⟩ :=
    retainedConstrainedWindow n (completedPathClock n b h) as has hr hu hu₀ hc hk hkc hm hM α p q
      hpm hqm hp₀ hq₁ hpq xs η D₀ cl cu R F ε J hcl hcu hD₀ hR hFmass hFradius hJ hε
      hmesh hxa hη hηa hεa hr₀ hT hRJ hreg
  have ha : 0 < a := hxs.trans_le hxa
  have hab : a ≤ ab := by simpa only [hwa,hwb] using w.ab
  have hTab : 2*ab ≤ T := by
    have hp : (2:ℝ) ≤ 2^J := by simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hJ
    exact mul_le_mul_of_nonneg_right hp (ha.le.trans hab)
  have hclock := physicalConstrainedClockLengths n hn b h hb hh as has hr hu hu₀ hc hk hkc hm hM₁ α
    ha hab hK hba hTab hT hr₀ hκ.le hη hηa hε hεη he hem her hH hmesh
  have hbalanceD : (1/Real.sqrt (w.A*((n:ℝ)*e a*w.a^4)))*w.a*e a/L ≤ w.D₀ := by
    rw [hwA,hwa,← hηeq,hwD]
    dsimp [D₀,L]
    have hK0 : K+1 ≠ 0 := by linarith
    have hκ0 := ne_of_gt hκ
    apply le_of_eq
    field_simp
  have hcoeff := w.coefficient_balanced_general hs hxs ℓ hK
    (by simpa only [hwa,hwb] using hba) (by simpa only [hwm,hwC,hwa] using hmasshi)
    (by exact_mod_cast hn) hea hL (by rwa [hwA])
    (by simpa only [hwη,hwA,hwa] using hηeq) hbalanceD
  have hcoeff' : w.coefficient ℓ ≤ ((cl/(4*Ca))^2/(1+(2*(ℓ+1:ℕ):ℝ)^2/3))*w.a^4 := by
    apply hcoeff.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa only [PhysicalBandWindow.generalScaleFactor,PhysicalBandWindow.generalNearScaleConstant,
      PhysicalBandWindow.generalFarScaleConstant,hwJ,hwC,hwF,hwc,hwA,hwa] using hmargin
  have hloss := w.loss_le_half_scale hxs ℓ hcl hCa
    (by simpa only [hwa,hwm] using hmasslo) (by simpa only [hwa] using hay) hcoeff'
  refine ⟨w,hws,hwa,hwb,hwm,hwA,hloss,?_,?_⟩
  · simpa only [hwa,hwb,hwD,hwr,hwη] using hclock.1
  · simpa only [hwa,hwb,hwD,hwr,hwJ] using hclock.2

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 theorem physicalSusceptibility_bound (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps) :
    ∃ C : ℝ, ∀ x p, |physicalSusceptibility n steps x p| ≤ C := by
  choose C hC using fun σ : Spin n =>
    (driverEnergy_smooth (uniformWeight_pos n) (finiteFeature n) steps ha
      (.id ℝ _) (spinSource n) σ 0).bound
  refine ⟨∑ σ, |C σ|,fun x p => ?_⟩
  rw [← driverEnergy_spin n steps ha x p]
  exact ((hC (ForwardPath.spin steps.length p)).2 x).trans
    ((le_abs_self _).trans (Finset.single_le_sum (fun σ _ => abs_nonneg (C σ)) (Finset.mem_univ _)))

 theorem physicalSusceptibility_measurable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    Measurable (fun p : PhysicalPathState P n steps => physicalSusceptibility n steps (x p.1) p.2) := by
  have hnode := physicalNodePair_measurable (uniformWeight_pos n) (finiteFeature n)
    (spinSource n) steps ha 1
  have hin : Measurable (fun p : PhysicalPathState P n steps =>
      (x p.1,ForwardPath.spin steps.length p.2)) :=
    (hx.comp measurable_fst).prodMk ((ForwardPath.spin_measurable steps.length).comp measurable_snd)
  have h := hnode.snd.comp hin
  have he : (fun p : PhysicalPathState P n steps => physicalSusceptibility n steps (x p.1) p.2) =
      (fun p : PhysicalPathState P n steps => (physicalNodePair (uniformWeight n) (finiteFeature n)
        (spinSource n) steps 1 (x p.1) (ForwardPath.spin steps.length p.2)).2) := by
    funext p
    simp only [physicalNodePair,one_pow,one_mul,driverEnergy_spin n steps ha]
  rw [he]
  exact h

 theorem physicalCutSusceptibility_measurable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (k : ℕ) : Measurable (physicalCutSusceptibility n steps x k) := by
  induction steps generalizing a P k with
  | nil => cases k with
    | zero => exact physicalSusceptibility_measurable n [] ha x hx
    | succ k => exact measurable_const
  | cons st steps ih =>
    cases k with
    | zero => exact physicalSusceptibility_measurable n (st::steps) ha x hx
    | succ k =>
      exact (ih ha.2.2.2 (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2)
        ((hx.comp measurable_fst).add measurable_snd) k).comp
        ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd))

 theorem physicalCutSusceptibility_bound (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps) :
    ∃ C : ℝ, ∀ {P : Type} (x : P → FeatureIndex n → ℝ) k p,
      |physicalCutSusceptibility n steps x k p| ≤ C := by
  induction steps generalizing a with
  | nil =>
    obtain ⟨C,hC⟩ := physicalSusceptibility_bound n [] ha
    refine ⟨max 0 C,fun {P} x k p => ?_⟩
    cases k with
    | zero => exact (hC _ _).trans (le_max_right _ _)
    | succ k => exact (by simp [physicalCutSusceptibility])
  | cons st steps ih =>
    obtain ⟨C,hC⟩ := physicalSusceptibility_bound n (st::steps) ha
    obtain ⟨D,hD⟩ := ih ha.2.2.2
    refine ⟨max C D,fun {P} x k p => ?_⟩
    cases k with
    | zero => exact (hC _ _).trans (le_max_left _ _)
    | succ k => exact (hD (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2) k
        ((p.1,p.2.1),p.2.2)).trans (le_max_right _ _)

 theorem physicalCutSusceptibility_memLp (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (μ : Measure (PhysicalPathState P n steps)) [IsFiniteMeasure μ] (k : ℕ) (p : ℝ≥0∞) :
    MemLp (physicalCutSusceptibility n steps x k) p μ := by
  obtain ⟨C,hC⟩ := physicalCutSusceptibility_bound n steps ha
  exact MemLp.of_bound (physicalCutSusceptibility_measurable n steps ha x hx k).aestronglyMeasurable C
    (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC x k z)

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›} {X : ℕ → Ω → E}

 
def terminalScore (X : ℕ → Ω → E) (N j : ℕ) (ω : Ω) : ℝ :=
  inner ℝ (X j ω) (X N ω) - (1/2:ℝ)*‖X j ω‖^2

 theorem terminalScore_integrable (hX : Martingale X 𝒢 μ) {R : ℝ}
    (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) (N j : ℕ) :
    Integrable (terminalScore X N j) μ := by
  have hm k := (hX.stronglyAdapted k).mono (𝒢.le k)
  have hi : Integrable (fun ω => inner ℝ (X j ω) (X N ω)) μ := by
    apply Integrable.of_bound ((hm j).aestronglyMeasurable.inner
      (hm N).aestronglyMeasurable) (R^2)
    filter_upwards [hR j,hR N] with ω hω hω'
    calc
      _ ≤ ‖X j ω‖*‖X N ω‖ := norm_inner_le_norm _ _
      _ ≤ R*R := mul_le_mul hω hω' (norm_nonneg _) ((norm_nonneg _).trans hω)
      _ = R^2 := by ring
  exact hi.sub (((boundedMartingale_sq_submartingale hX hR).integrable j).const_mul (1/2))

 theorem condExp_terminalScore_self (hX : Martingale X 𝒢 μ) {R : ℝ}
    (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) {N j : ℕ} (hj : j ≤ N) :
    μ[terminalScore X N j | 𝒢 j] =ᵐ[μ] fun ω => (1/2:ℝ)*‖X j ω‖^2 := by
  let I : Ω → ℝ := fun ω => inner ℝ (X j ω) (X N ω)
  let U : Ω → ℝ := fun ω => ‖X j ω‖^2
  have hU : Integrable U μ := (boundedMartingale_sq_submartingale hX hR).integrable j
  have hi : Integrable I μ := by
    apply ((terminalScore_integrable hX hR N j).add (hU.smul (1/2:ℝ))).congr
    exact Eventually.of_forall (fun ω => by dsimp [I,U,terminalScore]; ring)
  have hpull : μ[I | 𝒢 j] =ᵐ[μ] fun ω => inner ℝ (X j ω) (μ[X N | 𝒢 j] ω) :=
    condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) (hX.stronglyAdapted j) hi
      (hX.integrable N)
  have hfix : μ[U | 𝒢 j] = U := condExp_of_stronglyMeasurable (𝒢.le j)
    ((hX.stronglyAdapted j).norm.pow 2) hU
  have he : terminalScore X N j = I-(1/2:ℝ) • U := rfl
  rw [he]
  filter_upwards [condExp_sub hi (hU.smul (1/2:ℝ)) (𝒢 j),
    condExp_smul (μ := μ) (1/2:ℝ) U (𝒢 j), hpull, hX.condExp_ae_eq hj] with ω h1 h2 h3 h4
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  rw [h1,h2,h3,h4,real_inner_self_eq_norm_sq,hfix]
  dsimp [U]
  ring

 theorem condExp_terminalScore (hX : Martingale X 𝒢 μ) {R : ℝ}
    (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) {N i j : ℕ} (hi : i ≤ j) (hj : j ≤ N) :
    μ[terminalScore X N j | 𝒢 i] =ᵐ[μ]
      fun ω => (1/2:ℝ)*μ[(fun ω => ‖X j ω‖^2) | 𝒢 i] ω := by
  calc
    μ[terminalScore X N j | 𝒢 i] =ᵐ[μ]
        μ[μ[terminalScore X N j | 𝒢 j] | 𝒢 i] :=
      (condExp_condExp_of_le (𝒢.mono hi) (𝒢.le j)).symm
    _ =ᵐ[μ] μ[(fun ω => (1/2:ℝ)*‖X j ω‖^2) | 𝒢 i] :=
      condExp_congr_ae (condExp_terminalScore_self hX hR hj)
    _ =ᵐ[μ] _ := condExp_smul (μ := μ) (1/2:ℝ) (fun ω => ‖X j ω‖^2) (𝒢 i)

 theorem integral_terminalScore (hX : Martingale X 𝒢 μ) {R : ℝ}
    (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) {N j : ℕ} (hj : j ≤ N) :
    (∫ ω, terminalScore X N j ω ∂μ) = (1/2:ℝ)*∫ ω, ‖X j ω‖^2 ∂μ := by
  rw [← integral_condExp (𝒢.le j),
    integral_congr_ae (condExp_terminalScore_self hX hR hj), integral_const_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 
def terminalWindow (X : ℕ → Ω → E) (N : ℕ) (J : Finset ι) (τ : ι → ℕ) (α : ι → ℝ) : Ω → ℝ :=
  ∑ j ∈ J, α j • terminalScore X N (τ j)

omit [Fintype ι] [DecidableEq ι] in
 theorem terminalWindow_integrable [Fintype ι] [DecidableEq ι]
    (hX : Martingale X 𝒢 μ) {R : ℝ}
    (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) (N : ℕ) (J : Finset ι) (τ : ι → ℕ) (α : ι → ℝ) :
    Integrable (terminalWindow X N J τ α) μ := by
  unfold terminalWindow
  exact integrable_finsetSum' _ (fun j _ => (terminalScore_integrable hX hR N (τ j)).smul (α j))

 theorem condExp_terminalWindow (hX : Martingale X 𝒢 μ) {R : ℝ}
    (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) {N i : ℕ} {J : Finset ι} (τ : ι → ℕ) (α : ι → ℝ)
    (hJ : ∀ j ∈ J, i ≤ τ j ∧ τ j ≤ N) :
    μ[terminalWindow X N J τ α | 𝒢 i] =ᵐ[μ]
      fun ω => (1/2:ℝ)*(∑ j ∈ J, α j*μ[(fun ω => ‖X (τ j) ω‖^2) | 𝒢 i] ω) := by
  have hsum := condExp_finsetSum (s := J)
    (f := fun j => α j • terminalScore X N (τ j))
    (fun j _ => (terminalScore_integrable hX hR N (τ j)).const_mul (α j)) (𝒢 i)
  have hall : ∀ᵐ ω ∂μ, ∀ j ∈ J,
      μ[α j • terminalScore X N (τ j) | 𝒢 i] ω =
        α j*((1/2:ℝ)*μ[(fun ω => ‖X (τ j) ω‖^2) | 𝒢 i] ω) := by
    apply (ae_all_iff).mpr
    intro j
    by_cases hj : j ∈ J
    · filter_upwards [condExp_smul (μ := μ) (α j) (terminalScore X N (τ j)) (𝒢 i),
        condExp_terminalScore hX hR (hJ j hj).1 (hJ j hj).2] with ω h1 h2
      intro _
      rw [h1]
      change α j * μ[terminalScore X N (τ j) | 𝒢 i] ω = _
      rw [h2]
    · exact Eventually.of_forall fun _ h => False.elim (hj h)
  filter_upwards [hsum,hall] with ω h1 h2
  change (μ[∑ j ∈ J, α j • terminalScore X N (τ j) | 𝒢 i]) ω = _
  rw [h1]
  simp only [Finset.sum_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [h2 j hj]
  ring

 theorem sqnorm_le_condExp_window (hX : Martingale X 𝒢 μ) {R : ℝ}
    (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) {N i : ℕ} {J : Finset ι} {τ : ι → ℕ} {α : ι → ℝ}
    (hα : ∀ j ∈ J, 0 ≤ α j) (hαsum : ∑ j ∈ J, α j = 1)
    (hJ : ∀ j ∈ J, i ≤ τ j ∧ τ j ≤ N) :
    (fun ω => ‖X i ω‖^2) ≤ᵐ[μ] fun ω => 2*μ[terminalWindow X N J τ α | 𝒢 i] ω := by
  have hsq := boundedMartingale_sq_submartingale hX hR
  have hall : ∀ᵐ ω ∂μ, ∀ j ∈ J,
      ‖X i ω‖^2 ≤ μ[(fun ω => ‖X (τ j) ω‖^2) | 𝒢 i] ω := by
    apply (ae_all_iff).mpr
    intro j
    by_cases hj : j ∈ J
    · filter_upwards [hsq.ae_le_condExp (hJ j hj).1] with ω hω
      exact fun _ => hω
    · exact Eventually.of_forall fun _ h => False.elim (hj h)
  filter_upwards [hall,condExp_terminalWindow hX hR τ α hJ] with ω hω he
  have hh := Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hω j hj) (hα j hj))
  rw [← Finset.sum_mul,hαsum,one_mul] at hh
  rw [he]
  linarith

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
variable {Ω E : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
 theorem momentNorm_le_of_norm_le [IsProbabilityMeasure μ] {f g : Ω → ℝ} {p : ℝ}
    (hg : MemLp g (ENNReal.ofReal p) μ) (hfg : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ ‖g ω‖) :
    momentNorm μ f p ≤ momentNorm μ g p := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact ENNReal.toReal_mono hg.eLpNorm_ne_top (eLpNorm_mono_ae hf hfg)
  · unfold momentNorm
    rw [eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.toReal_top]
    exact ENNReal.toReal_nonneg

omit [IsProbabilityMeasure μ] in
 theorem momentNorm_smul [IsProbabilityMeasure μ] (f : Ω → ℝ) (c p : ℝ) :
    momentNorm μ (c • f) p = |c| *momentNorm μ f p := by
  simp only [momentNorm, eLpNorm_const_smul, ENNReal.toReal_mul]
  simp [enorm_eq_nnnorm]

omit [IsProbabilityMeasure μ] in
 theorem momentNorm_condExp_le [IsProbabilityMeasure μ] (f : Ω → ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hf : MemLp f (ENNReal.ofReal p) μ) (m : MeasurableSpace Ω) :
    @momentNorm Ω m0 μ μ[f | m] p ≤ @momentNorm Ω m0 μ f p := by
  let : MeasurableSpace Ω := m0
  apply ENNReal.toReal_mono hf.eLpNorm_ne_top
  apply eLpNorm_condExp_le_eLpNorm
  exact_mod_cast ENNReal.ofReal_le_ofReal hp

 theorem momentNorm_centering_le (f : Ω → ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hf : MemLp f (ENNReal.ofReal p) μ) (c : ℝ) :
    momentNorm μ f p ≤ momentNorm μ (fun ω => f ω-c) p + |c| := by
  have hpc : 1 ≤ ENNReal.ofReal p := by exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have hc : MemLp (fun _ : Ω => c) (ENNReal.ofReal p) μ := memLp_const c
  have hfc : MemLp (fun ω => f ω-c) (ENNReal.ofReal p) μ := hf.sub hc
  have he : f = (fun ω => f ω-c)+(fun _ : Ω => c) := by funext ω; simp
  have hh := eLpNorm_add_le (f := fun ω => f ω-c) (g := fun _ : Ω => c) (μ := μ) hpc
  rw [←he] at hh
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨hfc.eLpNorm_ne_top,hc.eLpNorm_ne_top⟩) hh
  rw [ENNReal.toReal_add hfc.eLpNorm_ne_top hc.eLpNorm_ne_top] at h
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  simpa [eLpNorm_const c hp0 (NeZero.ne μ), enorm_eq_nnnorm, momentNorm] using h

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›} {X : ℕ → Ω → E}

 theorem terminalScore_memLp (hX : Martingale X 𝒢 μ) {R : ℝ}
    (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) (N j : ℕ) (p : ℝ≥0∞) :
    MemLp (terminalScore X N j) p μ := by
  apply MemLp.of_bound (terminalScore_integrable hX hR N j).aestronglyMeasurable
    ((3/2:ℝ)*R^2)
  filter_upwards [hR j,hR N] with ω hj hN
  have hRp : 0 ≤ R := (norm_nonneg _).trans hj
  have hmul : ‖X j ω‖*‖X N ω‖ ≤ R^2 := by
    calc
      _ ≤ R*R := mul_le_mul hj hN (norm_nonneg _) hRp
      _ = R^2 := by ring
  have hsq : ‖X j ω‖^2 ≤ R^2 := sq_le_sq₀ (norm_nonneg _) hRp |>.mpr hj
  calc
    ‖terminalScore X N j ω‖ ≤ ‖inner ℝ (X j ω) (X N ω)‖ +
        ‖(1/2:ℝ)*‖X j ω‖^2‖ := norm_sub_le _ _
    _ ≤ ‖X j ω‖*‖X N ω‖ + (1/2:ℝ)*‖X j ω‖^2 := by
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ (1/2:ℝ)*‖X j ω‖^2)]
      have hb : ‖inner ℝ (X j ω) (X N ω)‖ ≤ ‖X j ω‖*‖X N ω‖ := norm_inner_le_norm _ _
      linarith [hb]
    _ ≤ (3/2:ℝ)*R^2 := by nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι] in
 theorem terminalWindow_memLp [Fintype ι] [DecidableEq ι]
    (hX : Martingale X 𝒢 μ) {R : ℝ}
    (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) (N : ℕ) (J : Finset ι)
    (τ : ι → ℕ) (α : ι → ℝ) (p : ℝ≥0∞) :
    MemLp (terminalWindow X N J τ α) p μ := by
  exact memLp_finsetSum' _ (fun j _ => (terminalScore_memLp hX hR N (τ j) p).const_smul (α j))

 theorem window_square_moment_le (hX : Martingale X 𝒢 μ) {R : ℝ}
    (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) {N i : ℕ} {J : Finset ι}
    {τ : ι → ℕ} {α : ι → ℝ} (hα : ∀ j ∈ J, 0 ≤ α j)
    (hαsum : ∑ j ∈ J, α j = 1) (hJ : ∀ j ∈ J, i ≤ τ j ∧ τ j ≤ N)
    {p : ℝ} (hp : 1 ≤ p) :
    momentNorm μ (fun ω => ‖X i ω‖^2) p ≤
      2*(momentNorm μ (fun ω => terminalWindow X N J τ α ω -
        ∫ z, terminalWindow X N J τ α z ∂μ) p +
        |∫ z, terminalWindow X N J τ α z ∂μ|) := by
  let V := terminalWindow X N J τ α
  have hV := terminalWindow_memLp hX hR N J τ α (ENNReal.ofReal p)
  have hpc : 1 ≤ ENNReal.ofReal p := by exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have he := sqnorm_le_condExp_window hX hR hα hαsum hJ
  have hh : momentNorm μ (fun ω => ‖X i ω‖^2) p ≤
      momentNorm μ ((2:ℝ) • μ[V | 𝒢 i]) p := by
    apply momentNorm_le_of_norm_le ((hV.condExp hpc).const_smul (2:ℝ))
    filter_upwards [he] with ω hω
    change ‖‖X i ω‖^2‖ ≤ ‖2*μ[V | 𝒢 i] ω‖
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg ((sq_nonneg _).trans hω)]
    exact hω
  rw [momentNorm_smul, abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  calc
    _ ≤ 2*momentNorm μ μ[V | 𝒢 i] p := hh
    _ ≤ 2*momentNorm μ V p := mul_le_mul_of_nonneg_left
      (momentNorm_condExp_le V hp hV (𝒢 i)) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (momentNorm_centering_le V hp hV (∫ z, V z ∂μ)) (by norm_num)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}

 theorem momentNorm_nat_eq {f : Ω → ℝ} (hf : ∀ z, 0 ≤ f z) {l : ℕ} (hl : 0 < l)
    (hm : MemLp f (ENNReal.ofReal l) μ) :
    momentNorm μ f l = (∫ z, f z^l ∂μ)^((l:ℝ)⁻¹) := by
  unfold momentNorm
  rw [MemLp.eLpNorm_eq_integral_rpow_norm
    (ENNReal.ofReal_ne_zero_iff.mpr (Nat.cast_pos.mpr hl)) ENNReal.ofReal_ne_top hm]
  simp only [ENNReal.toReal_ofReal (Nat.cast_nonneg l),Real.norm_of_nonneg (hf _),
    Real.rpow_natCast]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun z => pow_nonneg (hf z) _) _)]

 theorem momentNorm_sqnorm_nat {E : Type} [NormedAddCommGroup E] {f : Ω → E}
    {l : ℕ} (hl : 0 < l) (hm : MemLp (fun z => ‖f z‖^2) (ENNReal.ofReal (2*l:ℕ)) μ) :
    momentNorm μ (fun z => ‖f z‖^2) (2*l:ℕ) =
      ((∫ z, ‖f z‖^(4*l) ∂μ)^(((4*l:ℕ):ℝ)⁻¹))^2 := by
  rw [momentNorm_nat_eq (fun z => sq_nonneg _) (by omega : 0 < 2*l) hm]
  simp_rw [← pow_mul,show 2*(2*l)=4*l by omega]
  rw [← Real.rpow_natCast,← Real.rpow_mul (integral_nonneg fun z => pow_nonneg (norm_nonneg _) _)]
  congr 1
  push_cast
  field_simp
  norm_num

end SKFluctuations.Hierarchy

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

 theorem physical_radius_window_integral_memLp (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (J : Finset (Fin (steps.length+1))) (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass steps a J j ≠ 0 → r j.castSucc < r j.succ)
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (μ : Measure (PhysicalPathState P n steps)) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (physicalSusceptibilityMassIntegral n steps x
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass steps a J)) (radiusGridCut r)) p μ := by
  have he : physicalSusceptibilityMassIntegral n steps x
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass steps a J)) (radiusGridCut r) =
      ∑ j, physicalWindowCellMass steps a J j • physicalCutSusceptibility n steps x j.val := by
    funext z
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,physicalSusceptibilityMassIntegral]
    exact integral_radiusCellMeasure_allow_zero _ _ _ (fun j => or_iff_not_imp_left.mpr (hc j))
      (physicalWindowCellMass_nonneg steps ha J) _ _
      (fun j s hs => by rw [radiusGridCut_cell r hr j hs])
  rw [he]
  exact memLp_finsetSum' _ (fun j _ => (physicalCutSusceptibility_memLp n steps ha x hx μ j.val p).const_smul _)

 theorem physical_radius_window_energy_moment (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (J : Finset (Fin (steps.length+1)))
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass steps a J j ≠ 0 → r j.castSucc < r j.succ)
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (μ : Measure (PhysicalPathState P n steps)) [IsProbabilityMeasure μ] :
    momentNorm μ (fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps a (physicalWindowWeight steps a J) (x z.1) z.2).2) l =
      (physicalWindowMass steps a J)⁻¹^2*
        (∫ z, (physicalSusceptibilityMassIntegral n steps x
          (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
            (physicalWindowCellMass steps a J)) (radiusGridCut r) z)^l ∂μ)^((l:ℝ)⁻¹) := by
  have he : (fun z : PhysicalPathState P n steps =>
      (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
        steps a (physicalWindowWeight steps a J) (x z.1) z.2).2) =
      (physicalWindowMass steps a J)⁻¹^2 • physicalSusceptibilityMassIntegral n steps x
        (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
          (physicalWindowCellMass steps a J)) (radiusGridCut r) := by
    funext z
    exact physical_radius_window_energy n steps ha J r hr hc x z
  rw [he,momentNorm_smul,abs_of_nonneg (sq_nonneg _)]
  congr 1
  exact momentNorm_nat_eq (fun z => integral_nonneg fun s =>
    physicalCutSusceptibility_nonneg n steps ha x _ z) hl
    (physical_radius_window_integral_memLp n steps ha J r hr hc x hx μ _)

 theorem physical_sqnorm_memLp (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (μ : Measure (PhysicalPathState P n steps)) [IsFiniteMeasure μ] (i : ℕ) (p : ℝ≥0∞) :
    MemLp (fun z => ‖actualSpinPath n steps x i z‖^2) p μ := by
  apply MemLp.of_bound ((actualSpinPath_measurable n steps ha x hx i).norm.pow_const 2).aestronglyMeasurable 1
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact (pow_le_pow_left₀ (norm_nonneg _) (actualSpinPath_norm_le n steps ha x i z) 2).trans_eq (by norm_num)

end SKFluctuations

end

end OAI
