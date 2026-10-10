import OAI.Probability.ProjectionMoments.BallMoments

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sphere_packing_annulus (s : Finset E) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hs : ∀ x ∈ s, ‖x‖ = 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) :
    (s.card : ℝ) * (r/2)^Module.finrank ℝ E ≤
      (1+r/2)^Module.finrank ℝ E - (1-r/2)^Module.finrank ℝ E := by
  classical
  let δ := r/2
  let U : Set E := ⋃ c ∈ s, Metric.ball c δ
  let V : Set E := Metric.ball 0 (1-δ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hinner : 0 < 1-δ := by dsimp [δ]; linarith
  have houter : 0 < 1+δ := by positivity
  have hdis : Set.Pairwise (s : Set E) (fun c d => Disjoint (Metric.ball c δ) (Metric.ball d δ)) := by
    intro c hc d hd hcd
    apply Metric.ball_disjoint_ball
    simpa [δ] using hsep c hc d hd hcd
  have hUV : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro x hx hxV
    obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp hx
    have hxc' : dist x c < δ := hxc
    have hx0 : ‖x‖ < 1-δ := by simpa [V, Metric.mem_ball, dist_zero_right] using hxV
    have hc1 := hs c hc
    have htri := dist_triangle c x (0 : E)
    rw [dist_zero_right, dist_zero_right, dist_comm c x, hc1] at htri
    linarith
  have hsub : U ∪ V ⊆ Metric.ball (0 : E) (1+δ) := by
    rintro x (hx | hx)
    · obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp hx
      apply Metric.mem_ball.mpr
      have htri := dist_triangle x c (0 : E)
      rw [dist_zero_right c, hs c hc] at htri
      exact htri.trans_lt (by have hh : dist x c < δ := hxc; linarith)
    · exact (Metric.ball_subset_ball (by linarith : 1-δ ≤ 1+δ)) hx
  have hU : MeasurableSet U := MeasurableSet.biUnion s.finite_toSet.countable
    (fun c _ => Metric.isOpen_ball.measurableSet)
  have hvol : ((s.card : ℝ≥0∞)*ENNReal.ofReal (δ^Module.finrank ℝ E) +
      ENNReal.ofReal ((1-δ)^Module.finrank ℝ E)) * volume (Metric.ball (0 : E) 1) ≤
      ENNReal.ofReal ((1+δ)^Module.finrank ℝ E)*volume (Metric.ball (0 : E) 1) := by
    calc
      _ = volume (U ∪ V) := by
        rw [measure_union hUV Metric.isOpen_ball.measurableSet,
          show volume U = (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^Module.finrank ℝ E)*
            volume (Metric.ball (0 : E) 1) by
            rw [measure_biUnion_finset hdis (fun _ _ => Metric.isOpen_ball.measurableSet)]
            simp only [Measure.addHaar_ball_of_pos volume _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc],
          Measure.addHaar_ball_of_pos volume 0 hinner, add_mul]
      _ ≤ volume (Metric.ball (0 : E) (1+δ)) := measure_mono hsub
      _ = _ := Measure.addHaar_ball_of_pos volume 0 houter
  have hv0 : volume (Metric.ball (0 : E) 1) ≠ 0 := (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
  have hvt : volume (Metric.ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hh := (ENNReal.mul_le_mul_iff_left hv0 hvt).mp hvol
  have hreal := ENNReal.toReal_le_of_le_ofReal (pow_nonneg houter.le _) hh
  simp only [ENNReal.toReal_add (by finiteness :
    (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^Module.finrank ℝ E) ≠ ∞) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (pow_nonneg hδ.le _),
    ENNReal.toReal_ofReal (pow_nonneg hinner.le _)] at hreal
  dsimp [δ] at hreal
  linarith

lemma sphere_packing_bound (s : Finset E) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hd : 1 ≤ Module.finrank ℝ E) (hs : ∀ x ∈ s, ‖x‖ = 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) :
    (s.card : ℝ)*r^(Module.finrank ℝ E-1) ≤ (8 : ℝ)^Module.finrank ℝ E := by
  let d := Module.finrank ℝ E
  have hi : 0 ≤ 1-r/2 := by linarith
  have ho : 0 ≤ 1+r/2 := by positivity
  have hio : 1-r/2 ≤ 1+r/2 := by linarith
  have h := sphere_packing_annulus s hr hr1 hs hsep
  have hdiff : (1+r/2)^d - (1-r/2)^d ≤ r*d*(1+r/2)^(d-1) := by
    have hh := abs_pow_sub_pow_le (a := (1+r/2)) (b := (1-r/2)) (n := d)
    rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hi hio d)),
      abs_of_nonneg ho, abs_of_nonneg hi, max_eq_left hio,
      show (1+r/2)-(1-r/2) = r by ring, abs_of_pos hr] at hh
    exact hh
  have hpow : (1+r/2)^(d-1) ≤ (2 : ℝ)^d := by
    exact (pow_le_pow_left₀ ho (by linarith : 1+r/2 ≤ 2) _).trans
      (pow_le_pow_right₀ (by norm_num) (Nat.sub_le d 1))
  have hd2 : (d : ℝ) ≤ (2 : ℝ)^d := by
    have hn : ∀ n : ℕ, (n : ℝ) ≤ (2 : ℝ)^n := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        have hp : (1 : ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
        rw [Nat.cast_succ, pow_succ]
        linarith
    exact hn d
  have hupper : r*d*(1+r/2)^(d-1) ≤ r*(4 : ℝ)^d := by
    calc
      _ ≤ r*2^d*2^d := mul_le_mul (mul_le_mul_of_nonneg_left hd2 hr.le) hpow (by positivity) (by positivity)
      _ = _ := by rw [mul_assoc, ← mul_pow]; norm_num
  have hall := h.trans (hdiff.trans hupper)
  have htwo : 0 < (2 : ℝ)^d := by positivity
  rw [div_pow, ← mul_div_assoc, div_le_iff₀ htwo] at hall
  have hp : r^d = r^(d-1)*r := by rw [← pow_succ, Nat.sub_add_cancel hd]
  rw [hp, ← mul_assoc, mul_assoc r, ← mul_pow] at hall
  norm_num only at hall
  nlinarith

lemma sphere_cap_mass_center [Nontrivial E] {c c' : E} (hc : ‖c‖ = 1) (hc' : ‖c'‖ = 1)
    (r : ℝ) :
    NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) =
      NoiselessRegression.ambientSphereLaw (Metric.closedBall c' r) := by
  obtain ⟨O,hO⟩ := rotation_transitive
    (show Orthonormal ℝ (fun _ : Fin 1 => c) by simpa using hc)
    (show Orthonormal ℝ (fun _ : Fin 1 => c') by simpa using hc')
  let e : E ≃ₗᵢ[ℝ] E := Unitary.linearIsometryEquiv O
  have he : e c = c' := hO 0
  have hh := (NoiselessRegression.ambientSphereLaw_isometry e).map_eq
  have hpre : e ⁻¹' Metric.closedBall c' r = Metric.closedBall c r := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_closedBall, ← he, e.dist_map]
  have h := congrArg (fun μ : Measure E => μ (Metric.closedBall c' r)) hh
  rw [Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet, hpre] at h
  exact h

lemma sphere_finite_net {r : ℝ} (hr : 0 < r) :
    ∃ s : Finset E, (∀ c ∈ s, ‖c‖ = 1) ∧
      (∀ c ∈ s, ∀ c' ∈ s, c ≠ c' → r < dist c c') ∧
      ∀ x : E, ‖x‖ = 1 → ∃ c ∈ s, dist x c ≤ r := by
  classical
  let N := ⌈((1+r/2)/(r/2))^Module.finrank ℝ E⌉₊
  obtain ⟨s,hs,hsep,hnet⟩ := NoiselessRegression.exists_net_of_finite_packing_bound
    {x : E | ‖x‖ = 1} hr.le N (by
      intro s hs hsep
      have hh := NoiselessRegression.card_le_volume_ratio s hr (by norm_num : (0:ℝ) ≤ 1)
        (fun c hc => (hs c hc).le) (fun c hc c' hc' hne => (hsep c hc c' hc' hne).le)
      exact_mod_cast hh.trans (Nat.le_ceil _))
  exact ⟨s,hs,hsep,hnet⟩

lemma sphere_cap_lower_one [Nontrivial E] {c : E} (hc : ‖c‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal (r^(Module.finrank ℝ E-1)) ≤
      ENNReal.ofReal ((8:ℝ)^Module.finrank ℝ E) *
        NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) := by
  classical
  let μ : Measure E := NoiselessRegression.ambientSphereLaw
  obtain ⟨s,hs,hsep,hnet⟩ := sphere_finite_net (E := E) hr
  have hcard := sphere_packing_bound s hr hr1
    (Module.finrank_pos (R := ℝ) (M := E)) hs
    (fun x hx y hy hxy => (hsep x hx y hy hxy).le)
  have hcover : μ (⋃ x ∈ s, Metric.closedBall x r) = 1 := by
    rw [← measure_univ (μ := μ)]
    apply measure_congr
    filter_upwards [NoiselessRegression.ambientSphereLaw_ae_norm (E := E)] with x hx
    apply propext
    change (x ∈ ⋃ y ∈ s, Metric.closedBall y r) ↔ x ∈ Set.univ
    simp only [Set.mem_univ, iff_true]
    obtain ⟨y,hy,hxy⟩ := hnet x hx
    exact Set.mem_iUnion₂.mpr ⟨y,hy,hxy⟩
  have hone : (1 : ℝ≥0∞) ≤ (s.card : ℝ≥0∞)*μ (Metric.closedBall c r) := by
    calc
      _ = μ (⋃ x ∈ s, Metric.closedBall x r) := hcover.symm
      _ ≤ ∑ x ∈ s, μ (Metric.closedBall x r) := measure_biUnion_finset_le _ _
      _ = _ := by
        have hm : ∀ x ∈ s, μ (Metric.closedBall x r) = μ (Metric.closedBall c r) :=
          fun x hx => sphere_cap_mass_center (hs x hx) hc r
        simp_rw [Finset.sum_congr rfl hm]
        simp
  calc
    _ = ENNReal.ofReal (r^(Module.finrank ℝ E-1))*1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal (r^(Module.finrank ℝ E-1))*
        ((s.card : ℝ≥0∞)*μ (Metric.closedBall c r)) := mul_le_mul' le_rfl hone
    _ = ENNReal.ofReal ((s.card:ℝ)*r^(Module.finrank ℝ E-1))*
        μ (Metric.closedBall c r) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]; ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hcard) le_rfl

lemma sphere_cap_lower [Nontrivial E] {c : E} (hc : ‖c‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    ENNReal.ofReal (r^(Module.finrank ℝ E-1)) ≤
      ENNReal.ofReal ((16:ℝ)^Module.finrank ℝ E) *
        NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) := by
  by_cases hr1 : r ≤ 1
  · exact (sphere_cap_lower_one hc hr hr1).trans (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8)
        (by norm_num : (8:ℝ) ≤ 16) _)) le_rfl)
  · have h1 := sphere_cap_lower_one hc (by norm_num : (0:ℝ) < 1) le_rfl
    simp only [one_pow, ENNReal.ofReal_one] at h1
    have h2 : r^(Module.finrank ℝ E-1) ≤ (2:ℝ)^Module.finrank ℝ E :=
      (pow_le_pow_left₀ hr.le hr2 _).trans
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
    calc
      _ ≤ ENNReal.ofReal ((2:ℝ)^Module.finrank ℝ E)*1 := by
        simpa using ENNReal.ofReal_le_ofReal h2
      _ ≤ ENNReal.ofReal ((2:ℝ)^Module.finrank ℝ E)*
          (ENNReal.ofReal ((8:ℝ)^Module.finrank ℝ E)*
            NoiselessRegression.ambientSphereLaw (Metric.closedBall c 1)) := mul_le_mul' le_rfl h1
      _ ≤ ENNReal.ofReal ((2:ℝ)^Module.finrank ℝ E)*
          (ENNReal.ofReal ((8:ℝ)^Module.finrank ℝ E)*
            NoiselessRegression.ambientSphereLaw (Metric.closedBall c r)) := by
          gcongr
          exact le_of_not_ge hr1
      _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← mul_pow]; norm_num

end

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma cap_mass_pos [Nontrivial E] {c : E} (hc : ‖c‖ = 1) {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    NoiselessRegression.ambientSphereLaw (Metric.closedBall c r) ≠ 0 := by
  intro h
  have hh := sphere_cap_lower hc hr hr2
  rw [h,mul_zero] at hh
  exact (ENNReal.ofReal_pos.mpr (pow_pos hr _)).not_ge hh

lemma capMeasure_probability [Nontrivial E] {c : E} (hc : ‖c‖ = 1) {r : ℝ}
    (hr : 0 < r) (hr2 : r ≤ 2) : IsProbabilityMeasure (capMeasure c r) := by
  constructor
  simp only [capMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (cap_mass_pos hc hr hr2) (measure_ne_top _ _)

lemma capMeasure_ac (c : E) (r : ℝ) : capMeasure c r ≪ NoiselessRegression.ambientSphereLaw :=
  Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict

lemma capMeasure_support (c : E) (r : ℝ) : (capMeasure c r).support ⊆ Metric.closedBall c r := by
  intro x hx
  have hh := (Measure.support_restrict_subset
    (Measure.smul_absolutelyContinuous.support_mono hx)).1
  simpa only [Metric.isClosed_closedBall.closure_eq] using hh

lemma reciprocal_scale {t : ℝ} (ht : 0 < t) (ht4 : t ≤ 1/4) :
    ∃ j : ℕ, 4*t ≤ 1/((j:ℝ)+1) ∧ 1/((j:ℝ)+1) < 8*t := by
  let n := ⌊1/(4*t)⌋₊
  have hx : 1 ≤ 1/(4*t) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hn : 1 ≤ n := (Nat.one_le_floor_iff _).mpr hx
  have hnle : (n:ℝ) ≤ 1/(4*t) := Nat.floor_le (by positivity)
  have hnlt : 1/(4*t) < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have he : ((n-1:ℕ):ℝ)+1 = n := by exact_mod_cast (Nat.sub_add_cancel hn)
  refine ⟨n-1, ?_, ?_⟩
  · rw [he]
    rw [le_div_iff₀ (by exact_mod_cast (show 0 < n by omega))]
    rw [le_div_iff₀ (by positivity)] at hnle
    nlinarith
  · rw [he, div_lt_iff₀ (by exact_mod_cast (show 0 < n by omega))]
    rw [div_lt_iff₀ (by positivity)] at hnlt
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

lemma exists_capDictionary {c : E} (hc : ‖c‖ = 1) {r α : ℝ}
    (hr : 0 < r) (hα : 1 ≤ α) : Nonempty (CapDictionary c r α) := by
  classical
  let ρ : ℕ → ℝ := fun j => r/((j:ℝ)+1)
  have hρ : ∀ j, 0 < ρ j := fun j => div_pos hr (by positivity)
  choose net hnetnorm hnetsep hnetcover using
    (fun j : ℕ => sphere_finite_net (E := E) (half_pos (hρ j)))
  let I := Option (Σ j : ℕ, {s : E // s ∈ net j})
  let center : I → E := fun i => match i with | none => c | some p => p.2.val
  let radius : I → ℝ := fun i => match i with | none => r | some p => ρ p.1
  have hw (j : ℕ) : (r/ρ j)^α = ((j:ℝ)+1)^α := by
    congr 1
    dsimp [ρ]
    field_simp
  have hproper : ∀ R : ℝ, {i : I | (r/radius i)^α ≤ R}.Finite := by
    intro R
    have hlevel (j : ℕ) : (j:ℝ) ≤ (r/ρ j)^α := by
      rw [hw]
      calc
        _ ≤ (j:ℝ)+1 := by linarith
        _ = ((j:ℝ)+1)^(1:ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith [show (0:ℝ) ≤ j from Nat.cast_nonneg j]) hα
    have hsubset : {i : I | (r/radius i)^α ≤ R} ⊆
        insert none (⋃ j ∈ Finset.range (⌈R⌉₊+1), Option.some ''
          (Sigma.mk j '' (Set.univ : Set {s : E // s ∈ net j}))) := by
      intro i hi
      cases i with
      | none => exact Set.mem_insert _ _
      | some p =>
        right
        have hjR : (p.1:ℝ) ≤ R := (hlevel p.1).trans hi
        have hj : p.1 ∈ Finset.range (⌈R⌉₊+1) := by
          apply Finset.mem_range.mpr
          have hh : p.1 ≤ ⌈R⌉₊ := by exact_mod_cast hjR.trans (Nat.le_ceil R)
          omega
        exact Set.mem_iUnion₂.mpr ⟨p.1,hj,⟨p,⟨p.2,Set.mem_univ _,rfl⟩,rfl⟩⟩
    apply Set.Finite.subset _ hsubset
    apply Set.Finite.insert
    apply Set.Finite.biUnion (Finset.finite_toSet _)
    intro j hj
    exact ((Set.toFinite (Set.univ : Set {s : E // s ∈ net j})).image (Sigma.mk j)).image Option.some
  refine ⟨{
    I := I
    countable := inferInstance
    center := center
    radius := radius
    center_norm := ?_
    radius_pos := ?_
    radius_le := ?_
    parent := none
    parent_center := rfl
    parent_radius := rfl
    proper := hproper
    cover := ?_ }⟩
  · rintro (_|⟨j,s,hs⟩)
    · exact hc
    · exact hnetnorm j s hs
  · rintro (_|⟨j,s⟩)
    · exact hr
    · exact hρ j
  · rintro (_|⟨j,s⟩)
    · exact le_rfl
    · change r/((j:ℝ)+1) ≤ r
      exact div_le_self hr.le (by linarith [show (0:ℝ) ≤ j from Nat.cast_nonneg j])
  · intro s hs t ht ht4
    obtain ⟨j,hj1,hj2⟩ := reciprocal_scale ht ht4
    obtain ⟨s',hs',hss'⟩ := hnetcover j s hs
    refine ⟨some ⟨j,s',hs'⟩,?_,?_,hss'⟩
    · change 4*r*t ≤ r/((j:ℝ)+1)
      have hh := mul_le_mul_of_nonneg_left hj1 hr.le
      rw [mul_one_div] at hh
      nlinarith only [hh]
    · change r/((j:ℝ)+1) < 8*r*t
      have hh := mul_lt_mul_of_pos_left hj2 hr
      rw [mul_one_div] at hh
      nlinarith only [hh]

end ProjectionMoments

end

end OAI
