import OAI.Dynamics.SmoothObstruction.Recognition
import OAI.Dynamics.SmoothObstruction.PairLaw

namespace OAI

section

namespace SmoothObstruction.SymbolCores
open MeasureTheory Set
open scoped ENNReal NNReal
variable {M A : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- A finite measurable observation is uniformly stable at nearby points of
one compact core, losing arbitrarily little of the original probability. -/
theorem compact_core (μ : Measure M) [IsFiniteMeasure μ]
    (f : M → A) (hf : Measurable f) {κ : ℝ} (hκ : 0<κ) :
    ∃ (C : Set M) (δ : ℝ≥0), IsCompact C ∧ μ Cᶜ≤ENNReal.ofReal κ ∧
      0<δ ∧ ∀ x∈C,∀ y∈C,edist x y<(δ : ℝ≥0∞) → f x=f y := by
  classical
  let ε := ENNReal.ofReal κ/(Fintype.card A : ℝ≥0∞)
  have he : ε≠0 := by
    dsimp [ε]
    exact ne_of_gt (ENNReal.div_pos (by positivity) (by finiteness))
  have hc : (Fintype.card A : ℝ≥0∞)≠0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hex (a : A) := (hf (measurableSet_singleton a)).exists_isCompact_sdiff_lt
    (measure_ne_top μ _) he
  choose K hK hKc hKm using hex
  let C := ⋃ a,K a
  have hCc : IsCompact C := isCompact_iUnion hKc
  have hmass : μ Cᶜ≤ENNReal.ofReal κ := by
    have hsub : Cᶜ ⊆ ⋃ a, (f ⁻¹' {a}) \ K a := by
      intro x hx
      refine mem_iUnion.mpr ⟨f x,?_,?_⟩
      · rfl
      · intro hk
        exact hx (mem_iUnion.mpr ⟨f x,hk⟩)
    calc
      μ Cᶜ ≤ μ (⋃ a, (f ⁻¹' {a}) \ K a) := measure_mono hsub
      _ ≤ ∑' a,μ ((f ⁻¹' {a}) \ K a) := measure_iUnion_le _
      _ ≤ ∑' _ : A,ε := ENNReal.tsum_le_tsum (fun a => (hKm a).le)
      _ = ENNReal.ofReal κ := by
        rw [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        dsimp [ε]
        rw [ENNReal.mul_div_cancel hc (by finiteness)]
  have hsep (p : A × A) : ∃ r : ℝ≥0, 0<r ∧ ∀ x∈K p.1,∀ y∈K p.2,
      p.1≠p.2 → (r : ℝ≥0∞)<edist x y := by
    by_cases hh : p.1=p.2
    · exact ⟨1,by norm_num,fun _ _ _ _ hn => (hn hh).elim⟩
    have hd : Disjoint (K p.1) (K p.2) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact hh ((hK _ hx).symm.trans (hK _ hy))
    obtain ⟨r,hr,hrr⟩ := Metric.exists_pos_forall_lt_edist (hKc p.1) (hKc p.2).isClosed hd
    exact ⟨r,hr,fun x hx y hy _ => hrr x hx y hy⟩
  choose r hr hrr using hsep
  let δ := Finset.univ.inf' Finset.univ_nonempty r
  refine ⟨C,δ,hCc,hmass,?_,?_⟩
  · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun p _ => hr p)
  · intro x hx y hy hxy
    obtain ⟨a,ha⟩ := mem_iUnion.mp hx
    obtain ⟨b,hb⟩ := mem_iUnion.mp hy
    by_contra hn
    have hab : a≠b := by
      intro h
      exact hn ((hK _ ha).trans (h.trans (hK _ hb).symm))
    have hd : δ≤r (a,b) := Finset.inf'_le _ (Finset.mem_univ _)
    have hd' : (δ : ℝ≥0∞)≤r (a,b) := by exact_mod_cast hd
    exact (not_lt_of_ge hd') (hrr (a,b) x ha y hb hab |>.trans hxy)

end SmoothObstruction.SymbolCores

namespace SmoothObstruction.SymbolMass
open MeasureTheory Set
open scoped ENNReal NNReal
variable {Ω M A : Type*} [MeasurableSpace Ω] [MetricSpace M]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace A]

omit [MeasurableSpace A] in
/-- The per-time mismatch estimate in the original, unnormalized retained
law. Only its actual dominated marginals are used. -/
theorem mismatch_mass (σ : Measure Ω) (μ : Measure M)
    (f : M → A) (C : Set M) (hC : IsClosed C) {δ : ℝ≥0}
    (hcore : ∀ x∈C,∀ y∈C,edist x y<(δ : ℝ≥0∞) → f x=f y)
    (u v : Ω → M) (hu : Measurable u) (hv : Measurable v)
    (a b : ℝ≥0∞) (hU : σ.map u≤a•μ) (hV : σ.map v≤b•μ)
    (hdist : ∀ᵐ ω ∂σ,edist (u ω) (v ω)<(δ : ℝ≥0∞)) :
    σ {ω | f (u ω)≠f (v ω)}≤(a+b)*μ Cᶜ := by
  have hs : (fun ω => ω∈{ω | f (u ω)≠f (v ω)}) ≤ᵐ[σ] (fun ω => ω∈(u ⁻¹' Cᶜ ∪ v ⁻¹' Cᶜ)) := by
    filter_upwards [hdist] with ω hω
    intro hbad
    change u ω∉C ∨ v ω∉C
    by_contra hh
    push Not at hh
    exact hbad (hcore _ hh.1 _ hh.2 hω)
  have hUc := Measure.le_iff.mp hU Cᶜ hC.measurableSet.compl
  have hVc := Measure.le_iff.mp hV Cᶜ hC.measurableSet.compl
  rw [Measure.map_apply hu hC.measurableSet.compl,Measure.smul_apply,smul_eq_mul] at hUc
  rw [Measure.map_apply hv hC.measurableSet.compl,Measure.smul_apply,smul_eq_mul] at hVc
  calc
    σ {ω | f (u ω)≠f (v ω)} ≤ σ (u ⁻¹' Cᶜ ∪ v ⁻¹' Cᶜ) := measure_mono_ae hs
    _ ≤ σ (u ⁻¹' Cᶜ)+σ (v ⁻¹' Cᶜ) := measure_union_le _ _
    _ ≤ a*μ Cᶜ+b*μ Cᶜ := add_le_add hUc hVc
    _ = (a+b)*μ Cᶜ := (add_mul _ _ _).symm

omit [MetricSpace M] [BorelSpace M] in
/-- Invariance transports output domination to every observation time. -/
theorem transported_domination (σ : Measure Ω) (μ : Measure M)
    (z : Ω → M) (hz : Measurable z) (S : M → M)
    (hS : MeasurePreserving S μ μ) (a : ℝ≥0∞) (hzle : σ.map z≤a•μ) :
    σ.map (S ∘ z)≤a•μ := by
  rw [←Measure.map_map hS.measurable hz]
  have hh := Measure.map_mono hzle hS.measurable
  rwa [Measure.map_smul a hS.measurable.aemeasurable,hS.map_eq] at hh

end SmoothObstruction.SymbolMass

namespace SmoothObstruction.SymbolMass
open MeasureTheory Set
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Counted mismatches, before any normalization of the retained law. -/
noncomputable def errors (N : ℕ) (bad : Fin N → Set Ω) (ω : Ω) : ℝ≥0∞ :=
  ∑ t : Fin N, (bad t).indicator (fun _ => (1 : ℝ≥0∞)) ω

lemma measurable_errors (N : ℕ) (bad : Fin N → Set Ω)
    (hb : ∀ t,MeasurableSet (bad t)) : Measurable (errors N bad) := by
  exact Finset.measurable_sum _ (fun t _ => measurable_const.indicator (hb t))

/-- The finite-time Markov bound. The factor N cancels; no mixing in time
and no renormalized law is required. -/
theorem fraction_bad (σ : Measure Ω) (N : ℕ) (hN : 0<N)
    (bad : Fin N → Set Ω) (hb : ∀ t,MeasurableSet (bad t))
    (ε θ : ℝ≥0∞) (hθ : θ≠0) (hθt : θ≠∞)
    (hm : ∀ t,σ (bad t)≤ε) :
    σ {ω | (N:ℝ≥0∞)*θ≤errors N bad ω}≤ε/θ := by
  have hNz : (N:ℝ≥0∞)≠0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hNt : (N:ℝ≥0∞)≠∞ := ENNReal.natCast_ne_top N
  have hi : (∫⁻ ω,errors N bad ω ∂σ)≤(N:ℝ≥0∞)*ε := by
    change (∫⁻ ω,∑ t : Fin N, (bad t).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂σ)≤_
    rw [lintegral_finsetSum _ (fun t _ => measurable_const.indicator (hb t))]
    calc
      ∑ t : Fin N, (∫⁻ ω,(bad t).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂σ)
        ≤ ∑ t : Fin N,σ (bad t) := Finset.sum_le_sum (fun t _ => lintegral_indicator_one_le (bad t))
      _ ≤ ∑ _t : Fin N, ε := Finset.sum_le_sum (fun t _ => hm t)
      _ = _ := by simp [nsmul_eq_mul]
  calc
    _ ≤ (∫⁻ ω,errors N bad ω ∂σ)/((N:ℝ≥0∞)*θ) :=
      meas_ge_le_lintegral_div (measurable_errors N bad hb).aemeasurable
        (mul_ne_zero hNz hθ) (ENNReal.mul_ne_top hNt hθt)
    _ ≤ ((N:ℝ≥0∞)*ε)/((N:ℝ≥0∞)*θ) := by gcongr
    _ = ε/θ := ENNReal.mul_div_mul_left ε θ hNz hNt

/-- Both half-names lose at most twice the one-half Markov bound. -/
theorem two_halves_bad (σ : Measure Ω) (N : ℕ) (hN : 0<N)
    (bad₁ bad₂ : Fin N → Set Ω)
    (hb₁ : ∀ t,MeasurableSet (bad₁ t)) (hb₂ : ∀ t,MeasurableSet (bad₂ t))
    (ε θ : ℝ≥0∞) (hθ : θ≠0) (hθt : θ≠∞)
    (hm₁ : ∀ t,σ (bad₁ t)≤ε) (hm₂ : ∀ t,σ (bad₂ t)≤ε) :
    σ ({ω | (N:ℝ≥0∞)*θ≤errors N bad₁ ω} ∪
      {ω | (N:ℝ≥0∞)*θ≤errors N bad₂ ω})≤2*(ε/θ) := by
  calc
    _ ≤ σ {ω | (N:ℝ≥0∞)*θ≤errors N bad₁ ω}+
        σ {ω | (N:ℝ≥0∞)*θ≤errors N bad₂ ω} := measure_union_le _ _
    _ ≤ ε/θ+ε/θ := add_le_add (fraction_bad σ N hN bad₁ hb₁ ε θ hθ hθt hm₁)
      (fraction_bad σ N hN bad₂ hb₂ ε θ hθ hθt hm₂)
    _ = _ := (two_mul _).symm
end SmoothObstruction.SymbolMass

namespace SmoothObstruction.SymbolMass
open MeasureTheory Set Filter Topology WordConcatenation
open scoped ENNReal
variable {M A : Type} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]

omit [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma errors_eq_mismatches (N : ℕ) (u v : Fin N → M×M → A) (p : M×M) :
    errors N (fun t => {p | u t p≠v t p}) p =
      (mismatches (fun t => u t p) (fun t => v t p):ℝ≥0∞) := by
  classical
  simp only [errors,mismatches_sum,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Nat.cast_one]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : u t p=v t p
  · simp [h]
  · simp [h]

/-- Compact symbol cores give simultaneous full-half-name recovery with
original (not conditionally normalized) mass at least .98. -/
theorem symbol_success (μ : Measure M) [IsProbabilityMeasure μ]
    (S Sinv : M → M) (hS : MeasurePreserving S μ μ) (hSi : MeasurePreserving Sinv μ μ)
    (f : M → A) (hf : Measurable f) :
    ∃ δ : ℝ,0<δ ∧ ∀ (D : SwitchData μ) (n : ℕ),0<n →
      (99/100:ℝ)≤D.law.real D.carrier → D.retained.map D.point≤(2:ℝ≥0∞) • μ →
      (∀ p∈D.carrier,∀ t v : Fin (n+1),
        dist (S^[t.val] (D.point p)) (S^[t.val] p.1)+
        dist (Sinv^[v.val] (D.point p)) (Sinv^[v.val] p.2)<δ) →
      ∃ H : Set (M×M),MeasurableSet H ∧ H⊆D.carrier ∧ (98/100:ℝ)≤D.law.real H ∧
        ∀ p∈H,
          (mismatches (fun t : Fin n => f (S^[t.val] p.1))
            (fun t : Fin n => f (S^[t.val] (D.point p))):ℝ)<(3/400:ℝ)*n ∧
          (mismatches (fun t : Fin n => f (Sinv^[n-t.val] p.2))
            (fun t : Fin n => f (Sinv^[n-t.val] (D.point p))):ℝ)<(3/400:ℝ)*n := by
  classical
  obtain ⟨C,δ,hC,hCm,hδ,hsep⟩ := SymbolCores.compact_core μ f hf (by norm_num : (0:ℝ)<1/1000000)
  refine ⟨δ,hδ,?_⟩
  intro D n hn hmass hdom hshadow
  let : IsProbabilityMeasure D.law := PairLaw.law_probability μ D.label D.label_measurable
  let σ := D.retained
  let : IsFiniteMeasure σ := inferInstanceAs (IsFiniteMeasure (D.law.restrict D.carrier))
  have hσfst : σ.map Prod.fst≤(1:ℝ≥0∞) • μ := by
    rw [one_smul,←PairLaw.first_marginal μ D.label D.label_measurable]
    exact Measure.map_mono Measure.restrict_le_self measurable_fst
  have hσsnd : σ.map Prod.snd≤(1:ℝ≥0∞) • μ := by
    rw [one_smul,←PairLaw.second_marginal μ D.label D.label_measurable]
    exact Measure.map_mono Measure.restrict_le_self measurable_snd
  let b₁ : Fin n → Set (M×M) := fun t => {p | f (S^[t.val] p.1)≠f (S^[t.val] (D.point p))}
  let b₂ : Fin n → Set (M×M) := fun t => {p | f (Sinv^[n-t.val] p.2)≠f (Sinv^[n-t.val] (D.point p))}
  have hb₁ (t : Fin n) : MeasurableSet (b₁ t) :=
    (measurableSet_eq_fun (hf.comp ((hS.iterate _).measurable.comp measurable_fst))
      (hf.comp ((hS.iterate _).measurable.comp D.point_measurable))).compl
  have hb₂ (t : Fin n) : MeasurableSet (b₂ t) :=
    (measurableSet_eq_fun (hf.comp ((hSi.iterate _).measurable.comp measurable_snd))
      (hf.comp ((hSi.iterate _).measurable.comp D.point_measurable))).compl
  have hm₁ (t : Fin n) : σ (b₁ t)≤3*ENNReal.ofReal (1/1000000:ℝ) := by
    have hh := mismatch_mass σ μ f C hC.isClosed hsep
      (fun p => S^[t.val] p.1) (fun p => S^[t.val] (D.point p))
      ((hS.iterate _).measurable.comp measurable_fst)
      ((hS.iterate _).measurable.comp D.point_measurable) 1 2
      (transported_domination σ μ Prod.fst measurable_fst (S^[t.val]) (hS.iterate _) 1 hσfst)
      (transported_domination σ μ D.point D.point_measurable (S^[t.val]) (hS.iterate _) 2 hdom)
      (by
        filter_upwards [ae_restrict_mem D.carrier_measurable] with p hp
        rw [edist_dist,ENNReal.coe_nnreal_eq]
        apply (ENNReal.ofReal_lt_ofReal_iff hδ).mpr
        have hs := hshadow p hp ⟨t.val,by omega⟩ ⟨0,by omega⟩
        rw [dist_comm]
        exact lt_of_le_of_lt (le_add_of_nonneg_right dist_nonneg) hs)
    calc σ (b₁ t) ≤ (1+2)*μ Cᶜ := hh
      _ ≤ 3*ENNReal.ofReal (1/1000000:ℝ) := by norm_num; gcongr
  have hm₂ (t : Fin n) : σ (b₂ t)≤3*ENNReal.ofReal (1/1000000:ℝ) := by
    have hh := mismatch_mass σ μ f C hC.isClosed hsep
      (fun p => Sinv^[n-t.val] p.2) (fun p => Sinv^[n-t.val] (D.point p))
      ((hSi.iterate _).measurable.comp measurable_snd)
      ((hSi.iterate _).measurable.comp D.point_measurable) 1 2
      (transported_domination σ μ Prod.snd measurable_snd (Sinv^[n-t.val]) (hSi.iterate _) 1 hσsnd)
      (transported_domination σ μ D.point D.point_measurable (Sinv^[n-t.val]) (hSi.iterate _) 2 hdom)
      (by
        filter_upwards [ae_restrict_mem D.carrier_measurable] with p hp
        rw [edist_dist,ENNReal.coe_nnreal_eq]
        apply (ENNReal.ofReal_lt_ofReal_iff hδ).mpr
        have hs := hshadow p hp ⟨0,by omega⟩ ⟨n-t.val,by omega⟩
        rw [dist_comm]
        exact lt_of_le_of_lt (le_add_of_nonneg_left dist_nonneg) hs)
    calc σ (b₂ t) ≤ (1+2)*μ Cᶜ := hh
      _ ≤ 3*ENNReal.ofReal (1/1000000:ℝ) := by norm_num; gcongr
  let B := {p | (n:ℝ≥0∞)*ENNReal.ofReal (3/400:ℝ)≤errors n b₁ p} ∪
    {p | (n:ℝ≥0∞)*ENNReal.ofReal (3/400:ℝ)≤errors n b₂ p}
  have hB : MeasurableSet B :=
    (measurableSet_le measurable_const (measurable_errors n b₁ hb₁)).union
      (measurableSet_le measurable_const (measurable_errors n b₂ hb₂))
  have hBm : σ B≤ENNReal.ofReal (1/100:ℝ) := by
    have hh := two_halves_bad σ n hn b₁ b₂ hb₁ hb₂ (3*ENNReal.ofReal (1/1000000:ℝ))
      (ENNReal.ofReal (3/400:ℝ)) (by norm_num) (by finiteness) hm₁ hm₂
    apply hh.trans
    calc
      _ = ENNReal.ofReal (2*(3*(1/1000000)/(3/400):ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
          ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3/400),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)]
        norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by norm_num)
  let H := Bᶜ∩D.carrier
  have hHm : (98/100:ℝ)≤D.law.real H := by
    have he : D.law.real H=σ.real Bᶜ := by
      change (D.law H).toReal=((D.law.restrict D.carrier) Bᶜ).toReal
      rw [Measure.restrict_apply hB.compl]
    rw [he,measureReal_compl hB]
    have hu : σ.real univ=D.law.real D.carrier := by
      simp only [σ,SwitchData.retained,Measure.real,Measure.restrict_apply_univ]
    rw [hu]
    have hBr : σ.real B≤1/100 := (ENNReal.toReal_mono (by finiteness) hBm).trans_eq (by norm_num)
    linarith
  refine ⟨H,hB.compl.inter D.carrier_measurable,inter_subset_right, hHm,?_⟩
  intro p hp
  have hh₁ : errors n b₁ p<(n:ℝ≥0∞)*ENNReal.ofReal (3/400:ℝ) := lt_of_not_ge (fun hh => hp.1 (Or.inl hh))
  have hh₂ : errors n b₂ p<(n:ℝ≥0∞)*ENNReal.ofReal (3/400:ℝ) := lt_of_not_ge (fun hh => hp.1 (Or.inr hh))
  rw [errors_eq_mismatches] at hh₁ hh₂
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
  constructor
  · have hh := ENNReal.toReal_lt_toReal (by finiteness) (by finiteness) |>.mpr hh₁
    norm_num [ENNReal.toReal_mul,b₁] at hh
    simpa only [mul_comm] using hh
  · have hh := ENNReal.toReal_lt_toReal (by finiteness) (by finiteness) |>.mpr hh₂
    norm_num [ENNReal.toReal_mul,b₂] at hh
    simpa only [mul_comm] using hh
end SmoothObstruction.SymbolMass

end

end OAI
