import Mathlib
import OAI.Probability.SKFluctuations.ComparisonMinimumRegularRawMoment

namespace OAI

/-! Comparison Minimum Regular Raw Ratio. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem eventually_comparison_minimum_raw_ratio_regular
    (ℓ : ℕ) (Bclock : ℝ) {m δ B cl cu Az Ca K R C μ F κ₀ C₀ Ct D : ℝ}
    (hm₀ : 0 < m) (hδ : 0 < δ) (hδm : δ < 3*m)
    (hB : 2 ≤ B) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hBcu : cu ≤ B) (hBA : 2*cu*Az < B) (hCa : 0 < Ca) (hCaB : B/cl ≤ Ca)
    (hK : 1 ≤ K) (hKcu : 2*cu/cl ≤ K)
    (hR : 0 < R) (hR1 : R ≤ 1) (hKR : 2*K*R ≤ 1) (hcuR : 2*cu*R ≤ 1)
    (hC : 3*B/cl+1 < C) (hC1 : 1 ≤ C) (hmacro : 1 ≤ C*μ)
    (hμ : 0 < μ) (hμR : Ca*μ ≤ R) (hμB : 3*B*μ ≤ 1)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/R ≤ F)
    (hκ₀ : 0 < κ₀) (hC₀ : 0 < C₀) (hCt : 0 ≤ Ct) :
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
      ∃ us : List PositiveMass, (∀ v ∈ us, v.val ≤ 1) ∧ u ∈ us ∧
        ∀ᶠ j : ℕ in atTop,
          (physicalRawRatio n (ℓ+1) (sampleClockSteps (completedPathClock n b' h') 0 (finiteCutMasses us j))
            0 xs (Measure.pi fun i => gaussianReal 0 (completedPathClock n b' h' 0 i)) id measurable_id)^2 ≤ 2*C := by
  have hlog : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop 0)
  have hpow : ∀ᶠ n : ℕ in atTop, 2 ≤ (n:ℝ)^δ :=
    ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [eventually_comparison_minimum_raw_ratio_of_finite_margins ℓ Bclock,
    eventually_comparison_regular_band_margins (F:=F) (D:=D) ℓ hm₀ hδ.le hδm hB hcl hcu hAz hBcu hBA hCa hCaB
      hK hKcu hR hR1 hKR hcuR hC hμ hμR hκ₀ hC₀ hCt,hlog,hpow] with n hnraw hnmargin hnlog hnq
  intro E d r₀ u₀ hn hE hd hr₀ hu₀ g
  dsimp only
  intro α hg hgpos hp b h hb hh hbn hhn hmin
  let N := (n:ℝ)
  let U := comparisonSmallMass N E
  let L := comparisonConstraintLength N E d
  have hN : 0 < N := by dsimp only [N]; exact_mod_cast hn
  have hU := comparisonSmallMass_pos hN hE
  have hL := comparisonConstraintLength_pos hN hE hd
  let k := comparisonFloor N δ U
  let M := comparisonCap N δ U L E d
  let c := k 1
  let hr : r₀ ≤ 1 := le_trans hr₀.2 (by norm_num)
  let hu : u₀ ≤ 1 := le_trans hu₀.2 (by norm_num)
  let hc : 0 < c := comparisonFloor_pos hN hU (by norm_num)
  let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
  let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
  let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd.le
  let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd.le (show (0:ℝ) ≤ 1 by norm_num)
  let b' := fun w => (b w-omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) w).toNNReal
  let h' := fun w => (h w+omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
      (hg.continuous.mul continuous_id) α) w).toNNReal
  intro u huobs xs z hxs has hu₀xs hr₀U hz hzxs hdD hupper hlower htest hreg hslow hbare hBclock
  classical
  let cuts := Classical.choice (rawFutureCutFamily_nonempty u hxs hB hμ hμB hu₀xs huobs)
  let Q := constrainedQuantile hr hc hk hkc hm hM α
  let p (v : ℝ) (hv : v ∈ cuts.bands) : Icc u₀ 1 :=
    ⟨(cuts.p v).val,(cuts.cut_order v hv).2.2.1.le,
      (cuts.cut_order v hv).2.2.2.1.le.trans
        ((cuts.cut_order v hv).2.2.2.2.1.le.trans (cuts.cut_order v hv).2.2.2.2.2.1)⟩
  let q (v : ℝ) (hv : v ∈ cuts.bands) : Icc u₀ 1 :=
    ⟨(cuts.q v).val,(cuts.cut_order v hv).2.2.1.le.trans (cuts.cut_order v hv).2.2.2.1.le,
      (cuts.cut_order v hv).2.2.2.2.1.le.trans (cuts.cut_order v hv).2.2.2.2.2.1⟩
  let t (v : ℝ) (hv : v ∈ cuts.bands) : Icc u₀ 1 :=
    ⟨(cuts.t v).val,(cuts.cut_order v hv).2.2.1.le.trans
      ((cuts.cut_order v hv).2.2.2.1.le.trans (cuts.cut_order v hv).2.2.2.2.1.le),
      (cuts.cut_order v hv).2.2.2.2.2.1⟩
  have hcert := fun v (hv : v ∈ cuts.bands) => hnmargin E d xs v r₀ z
    (Q (p v hv)).val (Q (q v hv)).val (Q (t v hv)).val hE hd hdD hxs has
    (cuts.band_bounds v hv).1 (cuts.band_bounds v hv).2 hupper hlower hr₀U hz hzxs
    (Q (p v hv)).property (Q (q v hv)).property (Q (t v hv)).property α.val.val g α.val.property.2
    (by simpa only [p,(cuts.mass_values v hv).1] using constrainedQuantile_spec hr hc hk hkc hm hM α (p v hv))
    (by simpa only [q,(cuts.mass_values v hv).2.1] using constrainedQuantile_spec hr hc hk hkc hm hM α (q v hv))
    (by simpa only [t,(cuts.mass_values v hv).2.2] using constrainedQuantile_spec hr hc hk hkc hm hM α (t v hv))
    hreg hg hgpos hp hslow htest
  choose! η J hcert using hcert
  have hcuts : ∀ v ∈ cuts.bands, cuts.p v ∈ cuts.retained ∧ cuts.q v ∈ cuts.retained ∧
      u₀ < (cuts.p v).val ∧ (cuts.p v).val < (cuts.q v).val ∧ (cuts.q v).val < (cuts.t v).val ∧
      (cuts.t v).val ≤ 1 ∧ 2*v ≤ (cuts.p v).val ∧ 1 ≤ J v := by
    intro v hv
    obtain ⟨hp,hq,hp₀,hpq,hqt,ht₁,h2v⟩ := cuts.cut_order v hv
    exact ⟨hp,hq,hp₀,hpq,hqt,ht₁,h2v,(hcert v hv).1⟩
  refine ⟨cuts.retained,cuts.retained_le_one,cuts.observation_mem,?_⟩
  apply hnraw hN hU hL (min_le_left _ _) hE hd.le hnq hr₀ hu₀ hn g α hg hgpos hp
    b h hb hh hbn hhn hmin cuts.retained cuts.retained_le_one u cuts.observation_mem
    xs C μ cl cu R F (κ₀/Real.log (n:ℝ)) K Ca hxs hC1 hmacro hcl hcu.le hR
    (div_pos hκ₀ hnlog) hK hCa hFmass hFradius hbare hBclock
    cuts.bands cuts.p cuts.q cuts.t η J cuts.cover hcuts
  intro v hv
  dsimp only
  have hpv := (cuts.mass_values v hv).1
  have hqv := (cuts.mass_values v hv).2.1
  have htv := (cuts.mass_values v hv).2.2
  have hdiff : (cuts.q v).val-(cuts.p v).val=B*v := by rw [hpv,hqv]; ring
  have hdiff' : (cuts.t v).val-(cuts.q v).val=B*v := by rw [hqv,htv]; ring
  simpa only [p,q,t,Q,N,hpv,hqv,htv,
    show (2:ℝ)*B*v-B*v=B*v by ring,
    show (3:ℝ)*B*v-2*B*v=B*v by ring] using (hcert v hv).2

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem comparison_minimum_finite_raw_ratio
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
      ∃ us : List PositiveMass, (∀ v ∈ us, v.val ≤ 1) ∧ u ∈ us ∧
        ∀ᶠ j : ℕ in atTop,
          (physicalRawRatio n (ℓ+1) (sampleClockSteps (completedPathClock n b' h') 0 (finiteCutMasses us j))
            0 xs (Measure.pi fun i => gaussianReal 0 (completedPathClock n b' h' 0 i)) id measurable_id)^2 ≤ 2*C := by
  obtain ⟨B,Ca,K,R,C,μ,F,hB,hBcu,hBA,hCa,hCaB,hK,hKcu,hR,hR1,hKR,hcuR,
    hC,hC1,hmacro,hμ,hμR,hμB,hFmass,hFradius⟩ := exists_raw_regular_constants hcl hcu hAz
  exact ⟨C,zero_lt_one.trans_le hC1,
    eventually_comparison_minimum_raw_ratio_regular ℓ Bclock hm₀ hδ hδm
      hB hcl hcu hAz hBcu hBA hCa hCaB hK hKcu hR hR1 hKR hcuR hC hC1 hmacro
      hμ hμR hμB hFmass hFradius hκ₀ hC₀ hCt⟩

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 def physicalCutPairPower (n l : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (c a b d e : ℕ)
    (p : PhysicalPathState P n steps) : ℝ :=
  conditionalPathAverage (uniformWeight n) (finiteFeature n) steps x c
    (fun q => |inner ℝ (physicalCutIncrement n steps x a b p)
      (physicalCutIncrement n steps x d e q)|^(2*l)) p

 theorem physicalCutPairPower_nonneg (n l : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (c a b d e : ℕ)
    (p : PhysicalPathState P n steps) : 0≤physicalCutPairPower n l steps x c a b d e p :=
  conditionalPathAverage_nonneg _ _ _ _ _ (fun _ => pow_nonneg (abs_nonneg _) _) p

 theorem physicalCutPairPower_futurePair (n l : ℕ)
    (common tail mid pre : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (a b : ℕ)
    (p : PhysicalPathState P n (common++(pre++(mid++tail)))) :
    physicalCutPairPower n l (common++(pre++(mid++tail))) x common.length a b
      (common.length+pre.length) (common.length+(pre.length+mid.length)) p =
    conditionalPathAverage (uniformWeight n) (finiteFeature n) (common++(pre++(mid++tail)))
      x common.length (fun q => |∑ i, physicalCutIncrement n (common++(pre++(mid++tail))) x a b p i *
        physicalFuturePairIncrement n common tail mid pre x q i|^(2*l)) p := by
  unfold physicalCutPairPower
  simp_rw [show ∀ q, physicalCutIncrement n (common++(pre++(mid++tail))) x
      (common.length+pre.length) (common.length+(pre.length+mid.length)) q =
      WithLp.toLp 2 (physicalFuturePairIncrement n common tail mid pre x q) from
    fun q => (physicalFuturePairIncrement_eq_spinPath n common tail mid pre x q).symm]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,mul_comm]

 theorem eventually_cut_pair_full_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (common tail mid pre skip : List (GaussianStep (FeatureIndex n)))
      (a c D xs : ℝ), 0 < a → 0 < D → D ≤ B → 0 < xs →
      OrderedSteps a (pre++(mid++tail)) →
      OrderedSteps c (common++((skip++pre)++(mid++tail))) →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (v w : ℕ),
      v ≤ w → w ≤ (common++((skip++pre)++(mid++tail))).length+1 →
      (∀ V : Fin n → ℝ, AlignedFieldClock (fieldProjectionDirection n V) D pre) →
    (∫ p, physicalCutPairPower n (k+1) (common++((skip++pre)++(mid++tail))) x common.length v w
      (common.length+(skip++pre).length)
      (common.length+((skip++pre).length+mid.length)) p
      ∂physicalPathLaw μ n (common++((skip++pre)++(mid++tail))) x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^2 *
        (2*physicalRawRatio n (k+1) (common++((skip++pre)++(mid++tail))) c xs μ x hx)^2 *
        (xs+physicalCutMass c (common++((skip++pre)++(mid++tail))) w) := by
  filter_upwards [eventually_common_cut_projection_moment k B] with n hn
  intro P _ common tail mid pre skip a c D xs ha hD hDB hxs ho hs μ _ x hx v w hvw hw hc
  let steps := common++((skip++pre)++(mid++tail))
  let V := fun p i => physicalCutIncrement n steps x v w p i
  have hV : Measurable V := physicalCutIncrement_coe_measurable n steps hs x hx v w
  have hR : ∀ p, projectionEuclideanNorm n (V p) ≤ 2 := fun p => by
    dsimp only [V]
    rw [projectionEuclideanNorm_coe]
    exact physicalCutIncrement_norm_le n steps hs x v w p
  have hh := hn P common tail mid pre skip a c D ha hD hDB ho hs μ x hx V hV 2 hR (fun p => hc (V p))
  dsimp only [V,steps] at hh
  rw [show 2*k+2=2*(k+1) by omega] at hh
  simp_rw [projectionEuclideanNorm_coe,← physicalCutPairPower_futurePair] at hh
  let A := projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D))
  let Q := physicalRawRatio n (k+1) steps c xs μ x hx
  let S := xs+physicalCutMass c steps w
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (projectionLpConstant_pos k).le (sq_nonneg _))
    (mul_nonneg ha.le (Real.sqrt_nonneg _))
  have hQ : 0 ≤ Q := le_trans zero_le_one (physicalRawRatio_one_le n (k+1) steps c xs μ x hx)
  have hS : 0 ≤ S := add_nonneg hxs.le (physicalCutMass_mem steps hs w).1
  apply root_le_of_even_projection (Nat.succ_pos k)
    (integral_nonneg fun p => physicalCutPairPower_nonneg n (k+1) steps x _ _ _ _ _ p) hA hQ hS
  apply hh.trans
  have hM := mul_le_mul_of_nonneg_left
    (physicalRawRatio_increment_moment n (k+1) (Nat.succ_pos k) steps hs hxs μ x hx hvw hw)
    (pow_nonneg hA (2*k+2))
  simpa only [show 2*(k+1) = 2*k+2 by omega,mul_assoc] using hM

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 theorem physicalCutPairPower_test_measurable (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hc : OrderedSteps c steps)
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (a b d e : ℕ) :
    Measurable (fun z : PhysicalPathState P n steps × PhysicalPathState P n steps =>
      |inner ℝ (physicalCutIncrement n steps x a b z.1)
        (physicalCutIncrement n steps x d e z.2)|^(2*l)) :=
  ((((physicalCutIncrement_measurable n steps hc x hx a b).comp measurable_fst).inner
    ((physicalCutIncrement_measurable n steps hc x hx d e).comp measurable_snd)).abs).pow_const _

 theorem physicalCutPairPower_test_le (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hc : OrderedSteps c steps)
    {P : Type} (x : P → FeatureIndex n → ℝ) (a b d e : ℕ)
    (z : PhysicalPathState P n steps × PhysicalPathState P n steps) :
    |inner ℝ (physicalCutIncrement n steps x a b z.1)
      (physicalCutIncrement n steps x d e z.2)|^(2*l) ≤ 4^(2*l) := by
  apply pow_le_pow_left₀ (abs_nonneg _)
  have hh := norm_inner_le_norm (𝕜 := ℝ)
    (physicalCutIncrement n steps x a b z.1) (physicalCutIncrement n steps x d e z.2)
  rw [Real.norm_eq_abs] at hh
  apply hh.trans
  calc
    _ ≤ 2*2 := mul_le_mul (physicalCutIncrement_norm_le n steps hc x a b z.1)
      (physicalCutIncrement_norm_le n steps hc x d e z.2) (norm_nonneg _) (by norm_num)
    _ = 4 := by norm_num

 theorem physicalCutPairPower_measurable (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hc : OrderedSteps c steps)
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (i a b d e : ℕ) : Measurable (physicalCutPairPower n l steps x i a b d e) :=
  conditionalForkTest_measurable (uniformWeight_pos n) (finiteFeature n) steps hc x hx i
    (physicalCutPairPower_test_measurable n l steps hc x hx a b d e)

 theorem physicalCutPairPower_swap (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hc : OrderedSteps c steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (i a b d e : ℕ) :
    (∫ p, physicalCutPairPower n l steps x i a b d e p ∂physicalPathLaw μ n steps x hx) =
      ∫ p, physicalCutPairPower n l steps x i d e a b p ∂physicalPathLaw μ n steps x hx := by
  have hh := integral_conditionalForkTest_swap (uniformWeight_pos n) (finiteFeature n)
    steps hc μ x hx i (physicalCutPairPower_test_measurable n l steps hc x hx a b d e)
    (fun z => by
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact physicalCutPairPower_test_le n l steps hc x a b d e z)
  simpa only [physicalCutPairPower,physicalPathLaw,conditionalForkTest,Function.comp_apply,Prod.swap,real_inner_comm] using hh

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 def physicalOverlapComponent (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (cs : List (ℝ × ℕ)) (t : ℕ)
    (i : Fin (cs.length+1)) (p : PhysicalPathState P n steps) : EuclideanSpace ℝ (Fin n) :=
  Fin.cases (actualSpinPath n steps x t p)
    (fun j => physicalCutIncrement n steps x (cutPredecessor cs t j) (cs.get j).2 p) i

 theorem sum_physicalOverlapComponent (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (cs : List (ℝ × ℕ)) (t : ℕ)
    (p : PhysicalPathState P n steps) :
    (∑ i, physicalOverlapComponent n steps x cs t i p) =
      actualSpinPath n steps x (lastLayerCut cs t) p := by
  rw [Fin.sum_univ_succ]
  simp only [physicalOverlapComponent,Fin.cases_zero,Fin.cases_succ]
  change actualSpinPath n steps x t p +
    (∑ j, cutIncrement cs (fun k => actualSpinPath n steps x k p) t j) = _
  rw [sum_cutIncrement]
  abel

 theorem physicalOverlapComponent_measurable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hc : OrderedSteps c steps)
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (cs : List (ℝ × ℕ)) (t : ℕ) (i : Fin (cs.length+1)) :
    Measurable (physicalOverlapComponent n steps x cs t i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact actualSpinPath_measurable n steps hc x hx t
  · exact physicalCutIncrement_measurable n steps hc x hx _ _

 theorem physicalOverlapComponent_norm_le (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hc : OrderedSteps c steps)
    {P : Type} (x : P → FeatureIndex n → ℝ) (cs : List (ℝ × ℕ)) (t : ℕ)
    (i : Fin (cs.length+1)) (p : PhysicalPathState P n steps) :
    ‖physicalOverlapComponent n steps x cs t i p‖ ≤ 2 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (actualSpinPath_norm_le n steps hc x t p).trans (by norm_num)
  · exact physicalCutIncrement_norm_le n steps hc x _ _ p

 theorem normalizedSpin_inner_eq_overlap (n : ℕ) (σ τ : Spin n) :
    inner ℝ (WithLp.toLp 2 (normalizedSpin n σ)) (WithLp.toLp 2 (normalizedSpin n τ)) =
      orderedOverlap n σ τ := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,normalizedSpin,orderedOverlap]
  simp_rw [div_mul_div_comm,← pow_two,Real.sq_sqrt (Nat.cast_nonneg n)]
  simp only [Finset.sum_div,mul_comm]

 def physicalOverlapLayerTerm (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (cs : List (ℝ × ℕ)) (t : ℕ)
    (ij : Fin (cs.length+1) × Fin (cs.length+1))
    (z : PhysicalPathState P n steps × PhysicalPathState P n steps) : ℝ :=
  inner ℝ (physicalOverlapComponent n steps x cs t ij.1 z.1)
    (physicalOverlapComponent n steps x cs t ij.2 z.2)

 theorem physicalOverlapLayerTerm_measurable (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hc : OrderedSteps c steps)
    {P : Type} [MeasurableSpace P] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (cs : List (ℝ × ℕ)) (t : ℕ) (ij : Fin (cs.length+1) × Fin (cs.length+1)) :
    Measurable (physicalOverlapLayerTerm n steps x cs t ij) :=
  ((physicalOverlapComponent_measurable n steps hc x hx cs t ij.1).comp measurable_fst).inner
    ((physicalOverlapComponent_measurable n steps hc x hx cs t ij.2).comp measurable_snd)

 theorem physicalOverlapLayerTerm_abs_le (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hc : OrderedSteps c steps)
    {P : Type} (x : P → FeatureIndex n → ℝ) (cs : List (ℝ × ℕ)) (t : ℕ)
    (ij : Fin (cs.length+1) × Fin (cs.length+1))
    (z : PhysicalPathState P n steps × PhysicalPathState P n steps) :
    |physicalOverlapLayerTerm n steps x cs t ij z| ≤ 4 := by
  have hh := norm_inner_le_norm (𝕜 := ℝ)
    (physicalOverlapComponent n steps x cs t ij.1 z.1) (physicalOverlapComponent n steps x cs t ij.2 z.2)
  rw [Real.norm_eq_abs] at hh
  apply hh.trans
  calc
    _ ≤ 2*2 := mul_le_mul (physicalOverlapComponent_norm_le n steps hc x cs t _ _)
      (physicalOverlapComponent_norm_le n steps hc x cs t _ _) (norm_nonneg _) (by norm_num)
    _ = 4 := by norm_num

 theorem sum_physicalOverlapLayerTerm (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (cs : List (ℝ × ℕ)) (t : ℕ)
    (hlast : lastLayerCut cs t = steps.length+1)
    (z : PhysicalPathState P n steps × PhysicalPathState P n steps) :
    (∑ ij, physicalOverlapLayerTerm n steps x cs t ij z) =
      orderedOverlap n (ForwardPath.spin steps.length z.1.2) (ForwardPath.spin steps.length z.2.2) := by
  simp only [physicalOverlapLayerTerm,Fintype.sum_prod_type,← inner_sum,← sum_inner,
    sum_physicalOverlapComponent,hlast,actualSpinPath_terminal]
  exact normalizedSpin_inner_eq_overlap n _ _

 def physicalOverlapResidualPairs (cs : List (ℝ × ℕ)) :
    Finset (Fin (cs.length+1) × Fin (cs.length+1)) := Finset.univ.erase (0,0)

 theorem physicalOverlap_core_add_residual (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (cs : List (ℝ × ℕ)) (t : ℕ)
    (hlast : lastLayerCut cs t = steps.length+1)
    (z : PhysicalPathState P n steps × PhysicalPathState P n steps) :
    orderedOverlap n (ForwardPath.spin steps.length z.1.2) (ForwardPath.spin steps.length z.2.2) =
      inner ℝ (actualSpinPath n steps x t z.1) (actualSpinPath n steps x t z.2) +
        ∑ ij ∈ physicalOverlapResidualPairs cs, physicalOverlapLayerTerm n steps x cs t ij z := by
  rw [← sum_physicalOverlapLayerTerm n steps x cs t hlast z]
  have he := Finset.add_sum_erase Finset.univ (physicalOverlapLayerTerm n steps x cs t · z)
    (Finset.mem_univ (0,0))
  exact he.symm

end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

 theorem conditionalPathAverage_add_bounded {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (x : P → ι → ℝ) (k : ℕ)
    {F G : P × ForwardPath (ι → ℝ) S steps.length → ℝ}
    (hF : Measurable F) (hG : Measurable G) {R T : ℝ}
    (hFR : ∀ p, |F p| ≤ R) (hGR : ∀ p, |G p| ≤ T)
    (p : P × ForwardPath (ι → ℝ) S steps.length) :
    conditionalPathAverage w φ steps x k (fun q => F q+G q) p =
      conditionalPathAverage w φ steps x k F p+conditionalPathAverage w φ steps x k G p := by
  induction steps generalizing P a k with
  | nil =>
    have := hierarchyPathKernel_markov hw φ [] ha
    cases k with
    | zero =>
      exact integral_add (Integrable.of_bound (hF.comp measurable_prodMk_left).aestronglyMeasurable R
        (Eventually.of_forall fun q => hFR (p.1,q)))
        (Integrable.of_bound (hG.comp measurable_prodMk_left).aestronglyMeasurable T
        (Eventually.of_forall fun q => hGR (p.1,q)))
    | succ k => rfl
  | cons st tail ih =>
    have := hierarchyPathKernel_markov hw φ (st::tail) ha
    cases k with
    | zero =>
      exact integral_add (Integrable.of_bound (hF.comp measurable_prodMk_left).aestronglyMeasurable R
        (Eventually.of_forall fun q => hFR (p.1,q)))
        (Integrable.of_bound (hG.comp measurable_prodMk_left).aestronglyMeasurable T
        (Eventually.of_forall fun q => hGR (p.1,q)))
    | succ k =>
      exact ih ha.2.2.2 (fun q : P × (ι → ℝ) => x q.1+q.2) k
        (hF.comp MeasurableEquiv.prodAssoc.measurable) (hG.comp MeasurableEquiv.prodAssoc.measurable)
        (fun q => hFR (q.1.1,(q.1.2,q.2))) (fun q => hGR (q.1.1,(q.1.2,q.2))) ((p.1,p.2.1),p.2.2)

 theorem integral_conditionalForkTest_add {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) (k : ℕ)
    {F G : (P × ForwardPath (ι → ℝ) S steps.length) × (P × ForwardPath (ι → ℝ) S steps.length) → ℝ}
    (hF : Measurable F) (hG : Measurable G) {R T : ℝ}
    (hFR : ∀ z, |F z| ≤ R) (hGR : ∀ z, |G z| ≤ T) :
    (∫ p, conditionalForkTest w φ steps x k (fun z => F z+G z) p
      ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) =
      (∫ p, conditionalForkTest w φ steps x k F p
        ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx)+
      (∫ p, conditionalForkTest w φ steps x k G p
        ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) := by
  have he p := conditionalPathAverage_add_bounded hw φ steps ha x k
    (hF.comp measurable_prodMk_left) (hG.comp measurable_prodMk_left)
    (fun q => hFR (p,q)) (fun q => hGR (p,q)) p
  calc
    _ = ∫ p, (conditionalForkTest w φ steps x k F p+conditionalForkTest w φ steps x k G p)
        ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx :=
      integral_congr_ae (Eventually.of_forall he)
    _ = _ := integral_add (conditionalForkTest_integrable hw φ steps ha μ x hx k hF hFR)
      (conditionalForkTest_integrable hw φ steps ha μ x hx k hG hGR)

 theorem integral_conditionalForkTest_fst {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (x : P → ι → ℝ) (hx : Measurable x) (k : ℕ)
    (F : P × ForwardPath (ι → ℝ) S steps.length → ℝ) :
    (∫ p, conditionalForkTest w φ steps x k (fun z => F z.1) p
      ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) =
      ∫ p, F p ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx := by
  simp only [conditionalForkTest,conditionalPathAverage_const hw φ steps ha]

 theorem integral_conditionalForkTest_snd {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) (k : ℕ)
    {F : P × ForwardPath (ι → ℝ) S steps.length → ℝ} (hF : Measurable F) {R : ℝ}
    (hFR : ∀ p, |F p| ≤ R) :
    (∫ p, conditionalForkTest w φ steps x k (fun z => F z.2) p
      ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) =
      ∫ p, F p ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx := by
  have he := integral_conditionalForkTest_swap hw φ steps ha μ x hx k
    (hF.comp measurable_snd) (fun z => hFR z.2)
  exact he.trans (integral_conditionalForkTest_fst hw φ steps ha μ x hx k F)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 def physicalProjectedOverlapMoment (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (fork t : ℕ) : ℝ :=
  ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork
    (fun z => |inner ℝ (actualSpinPath n steps x t z.1)
      (actualSpinPath n steps x t z.2)|^(2*l)) p ∂physicalPathLaw μ n steps x hx

 theorem physicalProjectedOverlapMoment_le (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) {c xs : ℝ}
    (hc : OrderedSteps c steps) (hxs : 0 < xs) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (fork t : ℕ) (ht : t ≤ steps.length+1) :
    physicalProjectedOverlapMoment n l steps μ x hx fork t ≤
      2*(physicalRawRatio n l steps c xs μ x hx)^(4*l)*(xs+physicalCutMass c steps t)^(2*l) := by
  let Ω := PhysicalPathState P n steps
  let F : Ω × Ω → ℝ := fun z => |inner ℝ (actualSpinPath n steps x t z.1)
    (actualSpinPath n steps x t z.2)|^(2*l)
  let Y : Ω → ℝ := fun p => ‖actualSpinPath n steps x t p‖^(4*l)
  let G : Ω × Ω → ℝ := fun z => Y z.1+Y z.2
  have hX := actualSpinPath_measurable n steps hc x hx t
  have hF : Measurable F := (((hX.comp measurable_fst).inner (hX.comp measurable_snd)).abs).pow_const _
  have hY : Measurable Y := hX.norm.pow_const _
  have hG : Measurable G := (hY.comp measurable_fst).add (hY.comp measurable_snd)
  have hY0 p : 0 ≤ Y p := pow_nonneg (norm_nonneg _) _
  have hY1 p : Y p ≤ 1 := pow_le_one₀ (norm_nonneg _) (actualSpinPath_norm_le n steps hc x t p)
  have hYR p : |Y p| ≤ 1 := by rw [abs_of_nonneg (hY0 p)]; exact hY1 p
  have hG0 z : 0 ≤ G z := add_nonneg (hY0 _) (hY0 _)
  have hGR z : |G z| ≤ 2 := by rw [abs_of_nonneg (hG0 z)]; dsimp only [G]; linarith [hY1 z.1,hY1 z.2]
  have hF0 z : 0 ≤ F z := pow_nonneg (abs_nonneg _) _
  have hFG z : F z ≤ G z := by
    have hI := norm_inner_le_norm (𝕜 := ℝ) (actualSpinPath n steps x t z.1) (actualSpinPath n steps x t z.2)
    rw [Real.norm_eq_abs] at hI
    have hh := pow_le_pow_left₀ (abs_nonneg _) hI (2*l)
    rw [mul_pow] at hh
    have ha : 0 ≤ ‖actualSpinPath n steps x t z.1‖^(2*l) := pow_nonneg (norm_nonneg _) _
    have hb : 0 ≤ ‖actualSpinPath n steps x t z.2‖^(2*l) := pow_nonneg (norm_nonneg _) _
    have he (a : EuclideanSpace ℝ (Fin n)) : (‖a‖^(2*l))^2 = ‖a‖^(4*l) := by rw [← pow_mul]; congr 1; omega
    have hs := sq_nonneg (‖actualSpinPath n steps x t z.1‖^(2*l)-‖actualSpinPath n steps x t z.2‖^(2*l))
    dsimp only [F,G,Y]
    rw [sub_sq,he,he] at hs
    nlinarith [mul_nonneg ha hb]
  have hFR z : |F z| ≤ 2 := by
    rw [abs_of_nonneg (hF0 z)]
    exact (hFG z).trans (by rw [← abs_of_nonneg (hG0 z)]; exact hGR z)
  have hiG := conditionalForkTest_integrable (uniformWeight_pos n) (finiteFeature n) steps hc μ x hx fork hG hGR
  have hle : physicalProjectedOverlapMoment n l steps μ x hx fork t ≤
      ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork G p
        ∂physicalPathLaw μ n steps x hx := by
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun p => conditionalPathAverage_nonneg _ _ _ _ _ (fun q => hF0 (p,q)) p) hiG
    exact Eventually.of_forall fun p => conditionalPathAverage_mono_bounded (uniformWeight_pos n)
      (finiteFeature n) steps hc x fork (hF.comp measurable_prodMk_left) (hG.comp measurable_prodMk_left)
      (fun q => hFR (p,q)) (fun q => hGR (p,q)) (fun q => hFG (p,q)) p
  have he := integral_conditionalForkTest_add (uniformWeight_pos n) (finiteFeature n) steps hc μ x hx fork
    (hY.comp measurable_fst) (hY.comp measurable_snd) (fun z => hYR z.1) (fun z => hYR z.2)
  simp only [Function.comp_def] at he
  rw [integral_conditionalForkTest_fst (uniformWeight_pos n) (finiteFeature n) steps hc μ x hx fork Y,
    integral_conditionalForkTest_snd (uniformWeight_pos n) (finiteFeature n) steps hc μ x hx fork hY hYR] at he
  have hh := physicalRawRatio_moment n l hl steps hc hxs μ x hx ht
  change (∫ p, Y p ∂physicalPathLaw μ n steps x hx) ≤ _ at hh
  change (∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork G p
    ∂physicalPathLaw μ n steps x hx) = _ at he
  rw [he] at hle
  simp only [physicalPathLaw] at hh hle
  nlinarith

end SKFluctuations

end

end OAI
