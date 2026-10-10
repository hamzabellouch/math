import Mathlib
import OAI.Probability.SKFluctuations.ComparisonPolynomialRoom

namespace OAI

/-! Comparison Minimum Regular Raw Moment. -/

noncomputable section


namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem comparisonConstraintLength_pos {N E d : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hd : 0 < d) : 0 < comparisonConstraintLength N E d := by
  unfold comparisonConstraintLength
  exact lt_min (comparisonSmallMass_pos hN hE) (by have ha := comparisonLowerScale_pos hN hE hd; positivity)

 theorem eventually_comparison_minimum_raw_moment_regular
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
      pathPowerMoment (uniformWeight n) (finiteFeature n) (completedPathClock n b' h')
        (orderedOverlap n) (2*(ℓ+1)) u.val ≤ (2*C*(xs+u.val))^(2*(ℓ+1)) := by
  have hlog : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_gt_atTop 0)
  have hpow : ∀ᶠ n : ℕ in atTop, 2 ≤ (n:ℝ)^δ :=
    ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [eventually_comparison_minimum_raw_moment_of_finite_margins ℓ Bclock,
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

 theorem exists_raw_regular_constants {cl cu Az : ℝ}
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) :
    ∃ B Ca K R C μ F : ℝ,
      2 ≤ B ∧ cu ≤ B ∧ 2*cu*Az < B ∧ 0 < Ca ∧ B/cl ≤ Ca ∧
      1 ≤ K ∧ 2*cu/cl ≤ K ∧ 0 < R ∧ R ≤ 1 ∧ 2*K*R ≤ 1 ∧ 2*cu*R ≤ 1 ∧
      3*B/cl+1 < C ∧ 1 ≤ C ∧ 1 ≤ C*μ ∧ 0 < μ ∧ Ca*μ ≤ R ∧ 3*B*μ ≤ 1 ∧
      1+2*cu ≤ F ∧ 1+1/R ≤ F := by
  let B := 2+cu+2*cu*Az
  have hB : 2 ≤ B := by dsimp [B]; nlinarith only [hcu,mul_nonneg hcu.le hAz]
  have hBcu : cu ≤ B := by dsimp [B]; nlinarith only [mul_nonneg hcu.le hAz]
  have hBA : 2*cu*Az < B := by dsimp [B]; linarith only [hcu]
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  let Ca := B/cl
  have hCa : 0 < Ca := div_pos hB0 hcl
  let K := 1+2*cu/cl
  have hK1 : 1 ≤ K := by
    dsimp [K]
    have hh : 0 ≤ 2*cu/cl := by positivity
    linarith only [hh]
  have hKcu : 2*cu/cl ≤ K := by dsimp [K]; linarith
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  let R := 1/(2*(K+cu+1))
  have hden : 0 < 2*(K+cu+1) := by positivity
  have hR : 0 < R := div_pos zero_lt_one hden
  have hR1 : R ≤ 1 := by
    change 1/(2*(K+cu+1)) ≤ 1
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hK1,hcu]
  have hKR : 2*K*R ≤ 1 := by
    change 2*K*(1/(2*(K+cu+1))) ≤ 1
    rw [mul_one_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hcu]
  have hcuR : 2*cu*R ≤ 1 := by
    change 2*cu*(1/(2*(K+cu+1))) ≤ 1
    rw [mul_one_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hK0]
  let μ := R/(Ca+3*B+1)
  have hdμ : 0 < Ca+3*B+1 := by positivity
  have hμ : 0 < μ := div_pos hR hdμ
  have hCaμ : Ca*μ ≤ R := by
    change Ca*(R/(Ca+3*B+1)) ≤ R
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hdμ).mpr
    nlinarith only [mul_nonneg hR.le hB0.le,hR]
  have hBμ : 3*B*μ ≤ 1 := by
    change 3*B*(R/(Ca+3*B+1)) ≤ 1
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hdμ).mpr
    have hh := mul_le_mul_of_nonneg_left hR1 (show 0 ≤ 3*B by positivity)
    nlinarith only [hh,hCa]
  let C := 3*B/cl+2+1/μ
  have hbase : 0 < 3*B/cl := div_pos (by positivity) hcl
  have hC : 3*B/cl+1 < C := by dsimp [C]; have := one_div_pos.mpr hμ; linarith
  have hC1 : 1 ≤ C := by dsimp [C]; have := one_div_pos.mpr hμ; linarith
  have hmacro : 1 ≤ C*μ := by
    have he : (1/μ)*μ=1 := one_div_mul_cancel hμ.ne'
    have hh := mul_pos (show 0 < 3*B/cl+2 by linarith only [hbase]) hμ
    dsimp [C]
    nlinarith only [he,hh]
  let F := 1+2*cu+1/R
  have hF : 1+2*cu ≤ F := by dsimp [F]; have := one_div_pos.mpr hR; linarith
  have hF' : 1+1/R ≤ F := by dsimp [F]; linarith only [hcu]
  exact ⟨B,Ca,K,R,C,μ,F,hB,hBcu,hBA,hCa,le_rfl,hK1,hKcu,hR,hR1,hKR,hcuR,
    hC,hC1,hmacro,hμ,hCaμ,hBμ,hF,hF'⟩

end SKFluctuations

 

 

namespace SKFluctuations
open Filter Set Hierarchy
open scoped Topology

 theorem comparisonStrength_slope_bound {N d lam r c : ℝ} {f : ℝ → ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d) (hnd : 1/N ≤ d)
    (hl : 0 < lam) (hld : lam ≤ d^2) (hr : r ∈ Icc (0:ℝ) 1) (hc : 0 ≤ c)
    (hf : DifferentiableAt ℝ f (lam*r/d^3)) (hfp : f (lam*r/d^3) ≠ 0)
    (hslope : c/(1+Real.log (1+lam*r/d^3)) ≤ 1-comparisonLogSlope f (lam*r/d^3)) :
    (c/3)/Real.log N ≤ 1-comparisonLogSlope (comparisonStrength f d lam) r := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have ht0 : 0 ≤ lam*r/d^3 := div_nonneg (mul_nonneg hl.le hr.1) (pow_nonneg hd.le _)
  have hNd : 1 ≤ d*N := (div_le_iff₀ hN0).mp hnd
  have ht : lam*r/d^3 ≤ N := by
    apply (div_le_iff₀ (pow_pos hd 3)).mpr
    have h₁ := mul_le_mul_of_nonneg_left hr.2 hl.le
    have h₂ := mul_le_mul_of_nonneg_left hNd (sq_nonneg d)
    nlinarith only [h₁,h₂,hld]
  have hden : 0 < 1+Real.log (1+lam*r/d^3) := by
    have hh : 0 ≤ Real.log (1+lam*r/d^3) := Real.log_nonneg (by linarith only [ht0])
    linarith only [hh]
  have hdenup : 1+Real.log (1+lam*r/d^3) ≤ 3*Real.log N := by
    have h₁ := Real.log_le_log (show 0 < 1+lam*r/d^3 by linarith only [ht0])
      (show 1+lam*r/d^3 ≤ 2*N by linarith only [ht,hN])
    have h₂ : Real.log (2:ℝ) ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      norm_num at hh
      exact hh
    rw [Real.log_mul (by norm_num) hN0.ne'] at h₁
    linarith only [h₁,h₂,hlog]
  rw [comparisonLogSlope_strength hd.ne' hl.ne' hf hfp]
  apply le_trans _ hslope
  have hh := div_le_div_of_nonneg_left hc hden hdenup
  simpa only [div_div] using hh

 theorem eventually_comparisonStrength_uniform_slope {C m c : ℝ}
    (hC : 0 < C) (hm : 0 < m) (hc : 0 ≤ c) :
    ∀ᶠ n : ℕ in atTop, ∀ E d lam : ℝ, 0 < E → 0 < d →
      (n:ℝ)^(-(2:ℝ)/3+m)*d ≤ C*E → Real.sqrt (n:ℝ)*E ≤ d^2 →
      0 < lam → lam ≤ d^2 →
    ∀ f : ℝ → ℝ, (∀ t ≥ 0, DifferentiableAt ℝ f t) →
      (∀ t ≥ 0, 0 < f t) →
      (∀ t ≥ 0, c/(1+Real.log (1+t)) ≤ 1-comparisonLogSlope f t) →
      ∀ r ∈ Icc (0:ℝ) 1,
        (c/3)/Real.log (n:ℝ) ≤ 1-comparisonLogSlope (comparisonStrength f d lam) r := by
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_comparisonLowerScale_depth hC hm,hlog,eventually_ge_atTop (1:ℕ)] with n hn hlog hn1
  intro E d lam hE hd hlower hupper hl hld f hf hfp hfs r hr
  have hN : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have had : comparisonLowerScale n E d ≤ d := by
    unfold comparisonLowerScale
    exact (div_le_iff₀ hd).mpr (by nlinarith only [hupper])
  have ht0 : 0 ≤ lam*r/d^3 := div_nonneg (mul_nonneg hl.le hr.1) (pow_nonneg hd.le _)
  exact comparisonStrength_slope_bound hN hlog hd ((hn E d hE hd hlower).trans had)
    hl hld hr hc (hf _ ht0) (hfp _ ht0).ne' (hfs _ ht0)

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem comparison_minimum_retained_raw_moment
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
      pathPowerMoment (uniformWeight n) (finiteFeature n) (completedPathClock n b' h')
        (orderedOverlap n) (2*(ℓ+1)) u.val ≤ (2*C*(xs+u.val))^(2*(ℓ+1)) := by
  obtain ⟨B,Ca,K,R,C,μ,F,hB,hBcu,hBA,hCa,hCaB,hK,hKcu,hR,hR1,hKR,hcuR,
    hC,hC1,hmacro,hμ,hμR,hμB,hFmass,hFradius⟩ := exists_raw_regular_constants hcl hcu hAz
  exact ⟨C,zero_lt_one.trans_le hC1,
    eventually_comparison_minimum_raw_moment_regular ℓ Bclock hm₀ hδ hδm
      hB hcl hcu hAz hBcu hBA hCa hCaB hK hKcu hR hR1 hKR hcuR hC hC1 hmacro
      hμ hμR hμB hFmass hFradius hκ₀ hC₀ hCt⟩

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem eventually_comparison_minimum_raw_ratio_of_finite_margins
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
      ∀ᶠ j : ℕ in atTop,
        (physicalRawRatio n (ℓ+1) (sampleClockSteps (completedPathClock n b' h') 0 (finiteCutMasses us j))
          0 xs (Measure.pi fun i => gaussianReal 0 (completedPathClock n b' h' 0 i)) id measurable_id)^2 ≤ 2*C := by
  filter_upwards [eventually_physical_raw_bootstrap ℓ Bclock] with n hnraw
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
  filter_upwards [hfinalcover] with j hj
  obtain ⟨d,hd,hB,hcover⟩ := hj
  exact hnraw _ (sampleClockSteps_ordered _ _ (finiteCutMasses_ordered us hus j))
    _ xs C hxs hC d hd hB hcover

end SKFluctuations

end

end OAI
