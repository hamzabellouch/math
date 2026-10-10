import OAI.Analysis.RotationWeights.SamplingBounds

namespace OAI

noncomputable section

namespace CircleSampling

universe uι uX uκ uτ

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology

open Set MeasureTheory
open scoped BigOperators ENNReal Classical
section

lemma product_many_failures_bound {ι : Type uι} {X : ι → Type uX}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (I : Finset ι) (A : ∀ i, Set (X i))
    (hA : ∀ i, MeasurableSet (A i)) (q : ℕ) (p : ℝ≥0∞)
    (hp : ∀ i∈I, μ i (A i) ≤ p) :
    Measure.infinitePi μ {x | q ≤ (I.filter fun i ↦ x i ∈ A i).card} ≤
      (I.card.choose q : ℝ≥0∞) * p^q := by
  classical
  let S := I.powersetCard q
  have hcover : {x | q ≤ (I.filter fun i ↦ x i∈A i).card} ⊆
      ⋃ J∈S, Set.pi (J : Set ι) A := by
    intro x hx
    obtain ⟨J,hJI,hJq⟩ := Finset.exists_subset_card_eq hx
    refine mem_iUnion.mpr ⟨J,mem_iUnion.mpr ⟨?_,?_⟩⟩
    · exact Finset.mem_powersetCard.mpr ⟨hJI.trans (Finset.filter_subset _ _),hJq⟩
    · intro i hi
      exact (Finset.mem_filter.mp (hJI hi)).2
  calc
    Measure.infinitePi μ {x | q ≤ (I.filter fun i ↦ x i ∈ A i).card} ≤
        Measure.infinitePi μ (⋃ J∈S, Set.pi (J : Set ι) A) := measure_mono hcover
    _ ≤ ∑ J∈S, Measure.infinitePi μ (Set.pi (J : Set ι) A) := measure_biUnion_finset_le _ _
    _ = ∑ J∈S, ∏ i∈J, μ i (A i) := by
      apply Finset.sum_congr rfl
      intro J hJ
      exact Measure.infinitePi_pi μ (fun i _ ↦ hA i)
    _ ≤ ∑ _J∈S, p^q := by
      apply Finset.sum_le_sum
      intro J hJ
      obtain ⟨hJI,hJq⟩ := Finset.mem_powersetCard.mp hJ
      calc
        (∏ i∈J, μ i (A i)) ≤ ∏ _i∈J, p := Finset.prod_le_prod fun i hi ↦ hp i (hJI hi)
        _ = p^q := by simp [hJq]
    _ = _ := by simp [S,Finset.card_powersetCard,nsmul_eq_mul]

lemma product_many_failures_exp_bound {ι : Type uι} {X : ι → Type uX}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (I : Finset ι) (A : ∀ i, Set (X i))
    (hA : ∀ i, MeasurableSet (A i)) (q : ℕ) (p : ℝ≥0∞)
    (hp : ∀ i∈I, μ i (A i) ≤ p) :
    Measure.infinitePi μ {x | q ≤ (I.filter fun i ↦ x i ∈ A i).card} ≤
      (2 : ℝ≥0∞)^I.card * p^q := by
  apply (product_many_failures_bound μ I A hA q p hp).trans
  gcongr
  exact_mod_cast Nat.choose_le_two_pow I.card q

end
open Filter Set
open scoped Topology
section

def phaseUnionBound (m : ℕ) : ℝ :=
  3*(2*(10:ℝ)^((9:ℝ)/10)*(m:ℝ)^(-(11:ℝ)/200))^m

lemma phase_failure_count_lower (m : ℕ) : (9:ℝ)/10*m ≤ ((m-m/20:ℕ):ℝ) := by
  have hle : m/20 ≤ m := Nat.div_le_self _ _
  have hd : ((m/20:ℕ):ℝ) ≤ (m:ℝ)/20 := Nat.cast_div_le
  rw [Nat.cast_sub hle]
  nlinarith [show (0:ℝ) ≤ m by positivity]

lemma phase_union_numeric {m : ℕ} (hm : 0 < m)
    (hp : 10*(m:ℝ)^(-(19:ℝ)/20) ≤ 1) :
    3*(m:ℝ)^((4:ℝ)/5*m)*2^m*(10*(m:ℝ)^(-(19:ℝ)/20))^(m-m/20) ≤
      phaseUnionBound m := by
  have hx : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hp0 : 0 < 10*(m:ℝ)^(-(19:ℝ)/20) := by positivity
  have hpow : (10*(m:ℝ)^(-(19:ℝ)/20))^(m-m/20) ≤
      (10*(m:ℝ)^(-(19:ℝ)/20))^((9:ℝ)/10*m) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hp0 hp (phase_failure_count_lower m)
  calc
    _ ≤ 3*(m:ℝ)^((4:ℝ)/5*m)*2^m*(10*(m:ℝ)^(-(19:ℝ)/20))^((9:ℝ)/10*m) := by gcongr
    _ = phaseUnionBound m := by
      unfold phaseUnionBound
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 10) (Real.rpow_nonneg hx.le _)]
      rw [← Real.rpow_mul hx.le, ← Real.rpow_natCast (2:ℝ) m]
      rw [← Real.rpow_natCast (2*(10:ℝ)^((9:ℝ)/10)*(m:ℝ)^(-(11:ℝ)/200)) m]
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 10), ← Real.rpow_mul hx.le]
      have he : (m:ℝ)^((4:ℝ)/5*m)*(m:ℝ)^(-(19:ℝ)/20*((9:ℝ)/10*m)) =
          (m:ℝ)^(-(11:ℝ)/200*m) := by
        rw [← Real.rpow_add hx]
        congr 1
        ring
      calc
        _ = 3*(2:ℝ)^(m:ℝ)*(10:ℝ)^((9:ℝ)/10*m)*
            ((m:ℝ)^((4:ℝ)/5*m)*(m:ℝ)^(-(19:ℝ)/20*((9:ℝ)/10*m))) := by ring
        _ = _ := by rw [he]; ring

lemma tendsto_phaseUnionBound : Tendsto phaseUnionBound atTop (𝓝 0) := by
  have hx : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun m : ℕ => 2*(10:ℝ)^((9:ℝ)/10)*(m:ℝ)^(-(11:ℝ)/200)) atTop (𝓝 0) := by
    simpa only [mul_zero, neg_div, Function.comp_apply] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 11/200)).comp hx |>.const_mul (2*(10:ℝ)^((9:ℝ)/10))
  apply squeeze_zero' (Eventually.of_forall (fun m => by unfold phaseUnionBound; positivity))
    (g := fun m => 3*(1/2:ℝ)^m)
  · filter_upwards [hb.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with m hm
    unfold phaseUnionBound
    gcongr
  · simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).const_mul 3

lemma eventually_phase_failure_small : ∀ᶠ m : ℕ in atTop, 10*(m:ℝ)^(-(19:ℝ)/20) ≤ 1 := by
  have hx : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun m : ℕ => 10*(m:ℝ)^(-(19:ℝ)/20)) atTop (𝓝 0) := by
    simpa only [mul_zero, neg_div, Function.comp_apply] using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 19/20)).comp hx |>.const_mul 10
  filter_upwards [hb.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with m hm
  exact hm.le
open ContinuousCircleWeight.Sampling
open scoped Classical ENNReal

lemma phase_few_successes_subset (m : ℕ) (b c : ℝ) :
    {γ : Fin m → ℝ | (((Finset.univ.filter fun i => γ i ∉ phaseFailure b c).card:ℕ):ℝ) < (m:ℝ)/20} ⊆
      {γ | m-m/20 ≤ (Finset.univ.filter fun i => γ i ∈ phaseFailure b c).card} := by
  intro γ hγ
  have hsum := Finset.card_filter_add_card_filter_not (s:=Finset.univ)
    (fun i : Fin m => γ i ∈ phaseFailure b c)
  simp only [Finset.card_univ,Fintype.card_fin] at hsum
  have hle : (Finset.univ.filter fun i : Fin m => γ i ∉ phaseFailure b c).card ≤ m/20 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 20)).mpr
    have hreal : ((Finset.univ.filter fun i : Fin m => γ i ∉ phaseFailure b c).card:ℝ)*20 ≤ (m:ℝ) := by
      change ((Finset.univ.filter fun i : Fin m => γ i ∉ phaseFailure b c).card:ℝ) < (m:ℝ)/20 at hγ
      linarith
    exact_mod_cast hreal
  change m-m/20 ≤ _
  omega

lemma phase_cover_union_bound {m K : ℕ} (hm : 0 < m) (hK : 0 < K)
    (hp : 10*(m:ℝ)^(-(19:ℝ)/20) ≤ 1) (S : Finset ℤ)
    (hS : (S.card:ℝ) ≤ 3*(m:ℝ)^((4:ℝ)/5*m))
    (hc : ∀ k∈S, ((m:ℝ)*K)/4 ≤ |(k:ℝ)|) :
    Measure.pi (fun _ : Fin m => intervalLaw (1/((m:ℝ)*K)) (2/((m:ℝ)*K)))
      {γ | ∃ k∈S, (((Finset.univ.filter fun i => γ i ∉ phaseFailure ((m:ℝ)^(-(19:ℝ)/20)) k).card:ℕ):ℝ) < (m:ℝ)/20}
      ≤ ENNReal.ofReal (phaseUnionBound m) := by
  let N : ℝ := (m:ℝ)*K
  let b : ℝ := (m:ℝ)^(-(19:ℝ)/20)
  let μ : Measure ℝ := intervalLaw (1/N) (2/N)
  have hN : 0 < N := mul_pos (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hK)
  have hb : 0 ≤ b := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let : IsProbabilityMeasure μ := intervalLaw_probability ((div_lt_div_iff_of_pos_right hN).mpr (by norm_num))
  let A (k : ℤ) : Set (Fin m → ℝ) :=
    {γ | m-m/20 ≤ (Finset.univ.filter fun i => γ i ∈ phaseFailure b k).card}
  have hbound (k : ℤ) (hk : k∈S) : Measure.pi (fun _ : Fin m => μ) (A k) ≤
      (2:ℝ≥0∞)^m*(ENNReal.ofReal (10*b))^(m-m/20) := by
    have he := product_many_failures_exp_bound (fun _ : Fin m => μ) Finset.univ
      (fun _ => phaseFailure b k) (fun _ => measurableSet_phaseFailure _ _) (m-m/20)
      (ENNReal.ofReal (10*b)) (fun _ _ => phase_failure_probability hN hb (hc k hk))
    simpa only [Measure.infinitePi_eq_pi,Finset.card_univ,Fintype.card_fin] using he
  have hcover : {γ : Fin m → ℝ | ∃ k∈S,
      (((Finset.univ.filter fun i => γ i ∉ phaseFailure b k).card:ℕ):ℝ) < (m:ℝ)/20} ⊆ ⋃ k∈S, A k := by
    rintro γ ⟨k,hk,hγ⟩
    exact mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨hk,phase_few_successes_subset m b k hγ⟩⟩
  change Measure.pi (fun _ : Fin m => μ) _ ≤ _
  calc
    _ ≤ Measure.pi (fun _ : Fin m => μ) (⋃ k∈S, A k) := measure_mono hcover
    _ ≤ ∑ k∈S, Measure.pi (fun _ : Fin m => μ) (A k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k∈S, (2:ℝ≥0∞)^m*(ENNReal.ofReal (10*b))^(m-m/20) :=
      Finset.sum_le_sum hbound
    _ = ENNReal.ofReal ((S.card:ℝ)*2^m*(10*b)^(m-m/20)) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      have he : ENNReal.ofReal ((S.card:ℝ)*2^m*(10*b)^(m-m/20)) =
          (S.card:ℝ≥0∞)*2^m*(ENNReal.ofReal (10*b))^(m-m/20) := by
        conv_lhs => rw [ENNReal.ofReal_mul (by positivity)]
        conv_lhs => lhs; rw [ENNReal.ofReal_mul (by positivity)]
        rw [ENNReal.ofReal_natCast,ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2),
          ENNReal.ofReal_ofNat,ENNReal.ofReal_pow (by positivity)]
      rw [he,mul_assoc]
    _ ≤ ENNReal.ofReal (3*(m:ℝ)^((4:ℝ)/5*m)*2^m*(10*b)^(m-m/20)) := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
    _ ≤ ENNReal.ofReal (phaseUnionBound m) := ENNReal.ofReal_le_ofReal (phase_union_numeric hm hp)
end
section
open ContinuousCircleWeight.Sampling
open MeasureTheory Set
lemma intervalLaw_ae_inner (a b : ℝ) : ∀ᵐ x ∂intervalLaw a b, x ∈ Ioo a b := by
  have h : ∀ᵐ x ∂volume.restrict (Ioc a b), x ∈ Ioo a b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne b)] with x hx hxb
    exact ⟨hx.1,hx.2.lt_of_ne hxb⟩
  exact Measure.ae_smul_measure h _
lemma intervalLaw_ae_phase {a b c : ℝ} (hc : c ≠ 0) :
    ∀ᵐ x ∂intervalLaw a b, ((c*x:ℝ):CircleX) ≠ 0 := by
  have h : ∀ᵐ x ∂(volume : Measure ℝ), ∀ k : ℤ, x ≠ (k:ℝ)/c :=
    ae_all_iff.mpr fun k => volume.ae_ne _
  have h' := Measure.ae_smul_measure (ae_restrict_of_ae (s:=Ioc a b) h) (ENNReal.ofReal (b-a))⁻¹
  filter_upwards [h'] with x hx heq
  obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff 1).mp heq
  apply hx k
  apply (eq_div_iff hc).mpr
  simpa [zsmul_eq_mul,mul_comm] using hk.symm
lemma pi_intervalLaw_ae_good {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ]
    {a b : ℝ} (hab : a < b) (c : κ → ℝ) (hc : ∀ n, c n ≠ 0) :
    ∀ᵐ γ : ι → ℝ ∂Measure.pi (fun _ => intervalLaw a b),
      (∀ i, γ i ∈ Ioo a b) ∧ ∀ n i, ((c n*γ i:ℝ):CircleX) ≠ 0 := by
  let := intervalLaw_probability hab
  have h1 : ∀ᵐ γ : ι → ℝ ∂Measure.pi (fun _ => intervalLaw a b), ∀ i, γ i ∈ Ioo a b := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : ι => intervalLaw a b) i).quasiMeasurePreserving.ae
      (intervalLaw_ae_inner a b)
  have h2 : ∀ᵐ γ : ι → ℝ ∂Measure.pi (fun _ => intervalLaw a b), ∀ n i, ((c n*γ i:ℝ):CircleX) ≠ 0 := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : ι => intervalLaw a b) i).quasiMeasurePreserving.ae
      (intervalLaw_ae_phase (hc n))
  exact h1.and h2
end
section
open ContinuousCircleWeight.Sampling MeasureTheory Set
lemma pi_intervalLaw_ae_all_integerPhases {ι : Type uι} [Fintype ι]
    {a b : ℝ} (hab : a < b) :
    ∀ᵐ γ : ι → ℝ ∂Measure.pi (fun _ => intervalLaw a b),
      (∀ i, γ i ∈ Ioo a b) ∧ ∀ k : ℤ, k ≠ 0 → ∀ i, ((k*γ i:ℝ):CircleX) ≠ 0 := by
  let := intervalLaw_probability hab
  have h1 : ∀ᵐ γ : ι → ℝ ∂Measure.pi (fun _ => intervalLaw a b), ∀ i, γ i ∈ Ioo a b := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : ι => intervalLaw a b) i).quasiMeasurePreserving.ae (intervalLaw_ae_inner a b)
  have h2 : ∀ᵐ γ : ι → ℝ ∂Measure.pi (fun _ => intervalLaw a b), ∀ k : ℤ, k ≠ 0 → ∀ i, ((k*γ i:ℝ):CircleX) ≠ 0 := by
    apply ae_all_iff.mpr
    intro k
    by_cases hk : k=0
    · exact Filter.Eventually.of_forall (by simp [hk])
    apply ae_all_iff.mpr
    intro _
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : ι => intervalLaw a b) i).quasiMeasurePreserving.ae
      (intervalLaw_ae_phase (by exact_mod_cast hk))
  exact h1.and h2
end
open Set MeasureTheory
open scoped ENNReal Classical
section
lemma finite_threshold_bound {X : Type uX} {τ : Type uτ} [MeasurableSpace X] [Fintype τ]
    (μ : Measure X) [IsProbabilityMeasure μ] (E : τ → X → ℝ)
    (hE0 : ∀ t x, 0 ≤ E t x) (hEi : ∀ t, Integrable (E t) μ)
    {ε δ : ℝ} (hδ : 0 < δ) (hE : ∀ t, ∫ x, E t x ∂μ ≤ ε) :
    μ {x | ∃ t, δ ≤ E t x} ≤ ENNReal.ofReal ((Fintype.card τ:ℝ)*(ε/δ)) := by
  have hb (t : τ) : μ {x | δ ≤ E t x} ≤ ENNReal.ofReal (ε/δ) := by
    have h := (mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall (hE0 t)) (hEi t) δ).trans (hE t)
    have h' : μ.real {x | δ ≤ E t x} ≤ ε/δ := (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using h)
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h'
  calc
    _ = μ (⋃ t, {x | δ ≤ E t x}) := by congr 1; ext x; simp
    _ ≤ ∑ t, μ {x | δ ≤ E t x} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _t : τ, ENNReal.ofReal (ε/δ) := Finset.sum_le_sum (fun t _ => hb t)
    _ = _ := by simp [ENNReal.ofReal_mul (Nat.cast_nonneg _),nsmul_eq_mul]

lemma exists_good_finite_family {X : Type uX} {τ : Type uτ} [MeasurableSpace X] [Fintype τ]
    (μ : Measure X) [IsProbabilityMeasure μ] (E : τ → X → ℝ)
    (hE0 : ∀ t x, 0 ≤ E t x) (hEi : ∀ t, Integrable (E t) μ)
    {ε δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hE : ∀ t, ∫ x, E t x ∂μ ≤ ε) (bad : Set X) (hbad : μ bad ≤ ENNReal.ofReal B)
    (hbudget : B+(Fintype.card τ:ℝ)*(ε/δ) < 1) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∃ x, P x ∧ x ∉ bad ∧ ∀ t, E t x < δ := by
  have hε : 0 ≤ (Fintype.card τ:ℝ)*(ε/δ) := by
    by_cases hn : Nonempty τ
    · let := hn
      have heps := (integral_nonneg (hE0 (Classical.choice hn))).trans (hE (Classical.choice hn))
      positivity
    · have : IsEmpty τ := not_nonempty_iff.mp hn
      simp
  have hu := finite_threshold_bound μ E hE0 hEi hδ hE
  have hsmall : μ (bad ∪ {x | ∃ t, δ ≤ E t x} ∪ {x | ¬P x}) < 1 := by
    calc
      _ ≤ μ bad + μ {x | ∃ t, δ ≤ E t x} + μ {x | ¬P x} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal B + ENNReal.ofReal ((Fintype.card τ:ℝ)*(ε/δ)) + 0 :=
        add_le_add (add_le_add hbad hu) (le_of_eq (ae_iff.mp hP))
      _ < 1 := by
        rw [add_zero,← ENNReal.ofReal_add hB hε]
        exact (ENNReal.ofReal_lt_one).mpr hbudget
  by_contra! h
  have heq : bad ∪ {x | ∃ t, δ ≤ E t x} ∪ {x | ¬P x} = Set.univ := by
    ext x
    simp only [mem_union,mem_ofPred_eq,mem_univ,iff_true]
    by_cases hp : P x
    · by_cases hb : x∈bad
      · exact Or.inl (Or.inl hb)
      · exact Or.inl (Or.inr (h x hp hb))
    · exact Or.inr hp
  rw [heq,measure_univ] at hsmall
  exact (lt_irrefl _) hsmall
end
open ContinuousCircleWeight.Sampling Filter
open scoped Topology
lemma eventually_trial_budget (T : ℕ) {δ : ℝ} (_hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, phaseUnionBound m+(T:ℝ)*(samplingError m/δ) < 1 := by
  have h := tendsto_phaseUnionBound.add ((tendsto_samplingError.div_const δ).const_mul (T:ℝ))
  norm_num only [zero_div,mul_zero,add_zero] at h
  exact h.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))

lemma exists_ideal_trial {m K : ℕ} (hK : 0 < K) (hn : IdealNumerics K m)
    {τ : Type uτ} [Fintype τ] {κ : τ → Type uκ} [∀ t, Fintype (κ t)] [∀ t, Nonempty (κ t)]
    (positive : τ → Bool) (c : ∀ t, κ t → ℝ)
    (hcard : ∀ t, (m:ℝ)^((69:ℝ)/100*m) ≤ (Fintype.card (κ t):ℝ))
    (hc : ∀ t n, (m:ℝ)^((7:ℝ)/10*m)/2 ≤ c t n)
    (hsep : ∀ t n k, n ≠ k → ∀ v w : ℤ,
      |v| ≤ (m^300:ℕ) → |w| ≤ (m^300:ℕ) → (v ≠ 0 ∨ w ≠ 0) →
      ((m:ℝ)*K)*(m:ℝ)^1000 ≤ |(v:ℝ)*c t n+(w:ℝ)*c t k|)
    (hp : 10*(m:ℝ)^(-(19:ℝ)/20) ≤ 1) (S : Finset ℤ)
    (hS : (S.card:ℝ) ≤ 3*(m:ℝ)^((4:ℝ)/5*m))
    (hcS : ∀ k∈S, ((m:ℝ)*K)/4 ≤ |(k:ℝ)|)
    {δ : ℝ} (hδ : 0 < δ)
    (hbudget : phaseUnionBound m+(Fintype.card τ:ℝ)*(samplingError m/δ) < 1) :
    ∃ γ : Fin m → ℝ,
      (∀ i, γ i ∈ Set.Ioo (1/((m:ℝ)*K)) (2/((m:ℝ)*K))) ∧
      (∀ k : ℤ, k ≠ 0 → ∀ i, ((k*γ i:ℝ):CircleX) ≠ 0) ∧
      (∀ k∈S, (m:ℝ)/20 ≤ (((Finset.univ.filter fun i => γ i ∉ phaseFailure ((m:ℝ)^(-(19:ℝ)/20)) k).card:ℕ):ℝ)) ∧
      ∀ t, idealEnergy (positive t) (scaleEll m) (scaleAlpha m) (c t) γ < δ := by
  have hm : 0 < m := by have := hn.1; omega
  have hN : 0 < (m:ℝ)*K := mul_pos (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hK)
  have hab : 1/((m:ℝ)*K) < 2/((m:ℝ)*K) := (div_lt_div_iff_of_pos_right hN).mpr (by norm_num)
  let μ := Measure.pi (fun _ : Fin m => intervalLaw (1/((m:ℝ)*K)) (2/((m:ℝ)*K)))
  let := intervalLaw_probability hab
  let E (t : τ) : (Fin m → ℝ) → ℝ := idealEnergy (κ:=κ t) (positive t) (scaleEll m) (scaleAlpha m) (c t)
  let bad := {γ : Fin m → ℝ | ∃ k∈S,
    (((Finset.univ.filter fun i => γ i ∉ phaseFailure ((m:ℝ)^(-(19:ℝ)/20)) k).card:ℕ):ℝ) < (m:ℝ)/20}
  have hℓ : 0 < scaleEll m := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hm) _
  have hα := scaleAlpha_pos hm
  obtain ⟨γ,hγ,hgood,hE⟩ := exists_good_finite_family μ E
    (fun t => idealEnergy_nonneg (positive t) _ _ (c t))
    (fun t => idealEnergy_integrable (positive t) hℓ hα (c t) μ)
    hδ (by unfold phaseUnionBound; positivity)
    (fun t => ideal_stage_error hK hn (positive t) (c t) (hcard t) (hc t) (hsep t))
    bad (phase_cover_union_bound hm hK hp S hS hcS) hbudget
    (pi_intervalLaw_ae_all_integerPhases (ι:=Fin m) hab)
  refine ⟨γ,hγ.1,hγ.2,?_,hE⟩
  intro k hk
  exact le_of_not_gt (fun h => hgood ⟨k,hk,h⟩)


end CircleSampling

end

end OAI
