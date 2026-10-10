import Mathlib
import OAI.Probability.Ballisticity.Coupling.SeedOptions

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedOptions_mono {d : ℕ} (f : Direction d) (k : ℕ) (s : ℤ) {g g' : ℝ}
    (hg : g'≤g) (δ : ℝ≥0∞) (ρ : Measure (Lattice d)) :
    SeedOptions f k s g δ ρ → SeedOptions f k s g' δ ρ := by
  rintro ⟨μ,hd,ho⟩
  exact ⟨μ,hd,fun i j hij => seedOrdered_mono f s (ho i j hij) hg⟩

theorem seed_uniform_options {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) (hk : 1≤k) (p : ℝ) (hp : 0<p) :
    ∃ C A R : ℝ, ∃ δ : ℝ≥0∞, 0<C ∧ 0<A ∧ 0<R ∧ 0<δ ∧
    ∀ r : ℝ, R≤r → ∀ H : ℕ,
      (H:ℝ)=C*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r →
      ∃ s : ℤ, (s=1 ∨ s= -1) ∧ ∀ (a : ℤ) (μ : SeedProfile e a),
        environmentLaw ν {ω | ¬SeedOptions f k s (A*r) δ
          (seedEndpointRaw e H (fun _ _ => True) μ.measure ω)} ≤ ENNReal.ofReal p := by
  obtain ⟨b,j,hb,hj,hj1,htests⟩ := seed_block_tests ν hue e f hef htrans
  have hρ : 0≤1-j := by linarith
  have hρ1 : 1-j<1 := by linarith
  have hlim : Tendsto (fun n : ℕ => ((k-1:ℕ):ℝ)*(1-j)^n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1) :
      Tendsto (fun n : ℕ => ((k-1:ℕ):ℝ)*(1-j)^n) atTop (nhds (((k-1:ℕ):ℝ)*0)))
  obtain ⟨N,hN⟩ := (hlim.eventually (gt_mem_nhds (show (0:ℝ)<p/2 by positivity))).exists
  let J := (k-1)*N
  let C : ℝ := 2*(J+1)
  let η : ℝ := b/(4*(2*J+1))
  let ε : ℝ := p/(2*((J+1)*k+1))
  have hC : 0<C := by dsimp [C]; positivity
  have hη : 0<η := by dsimp [η]; positivity
  have hε : 0<ε := by dsimp [ε]; positivity
  have hηeq : (2*(J:ℝ)+1)*η=b/4 := by dsimp [η]; field_simp
  have hεeq : ((J:ℝ)+1)*k*ε≤p/2 := by
    have he : (2*(((J:ℝ)+1)*k+1))*ε=p := by dsimp [ε]; field_simp
    nlinarith [hε.le]
  obtain ⟨c,R,hc,hR,hrest⟩ := htests C η ε hC hη hε
  let δ := (ENNReal.ofReal (min c j)/2)^J*ENNReal.ofReal c
  have hδ : 0<δ := ENNReal.mul_pos_iff.mpr ⟨ENNReal.pow_pos (ENNReal.div_pos
    (ne_of_gt (ENNReal.ofReal_pos.mpr (lt_min hc hj))) (by norm_num)) J, ENNReal.ofReal_pos.mpr hc⟩
  refine ⟨C,b/2,R,δ,hC,by positivity,hR,hδ,fun r hr H hH => ?_⟩
  obtain ⟨hh,θ,s,hs,hclip,hjump⟩ := hrest r hr
  let n := fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
    (commonIncrementProcess (realPosition (step e)) f 0) r
  let h := ⌊n⌋₊
  have hn : 0<n := by exact (Nat.floor_pos.mp hh).trans_lt' (by norm_num)
  have hhn : (h:ℝ)≤n := Nat.floor_le hn.le
  have hJ : (J*h:ℕ)<H := by
    have hreal : ((J*h:ℕ):ℝ)<H := by
      rw [Nat.cast_mul,hH]
      change (J:ℝ)*(h:ℝ)<C*n
      have hle := mul_le_mul_of_nonneg_left hhn (show (0:ℝ)≤J by positivity)
      dsimp [C] at *
      nlinarith
    exact_mod_cast hreal
  let L := H-J*h
  have hL : 0<L := by dsimp [L]; omega
  have hsum : J*h+L=H := by dsimp [L]; omega
  have hz : 0≤η*r := mul_nonneg hη.le (hR.le.trans hr)
  have hgap : b/2*r ≤ b*r-η*r-2*(J:ℝ)*(η*r) := by
    have heq : b*r-η*r-2*(J:ℝ)*(η*r)=(b-(2*(J:ℝ)+1)*η)*r := by ring
    rw [heq,hηeq]
    nlinarith [hR.le.trans hr]
  have hg : 0≤b*r+η*r-2*(J:ℝ)*(η*r) := by
    have hpos : 0≤b/2*r := mul_nonneg (by positivity) (hR.le.trans hr)
    linarith
  refine ⟨s,hs,fun a μ => ?_⟩
  have hc' (t : ℕ) (ht : t∈({h,L}:Finset ℕ)) (μ : ProbabilityMeasure (Lattice d)) :
      environmentLaw ν {ω | (seedEndpointRaw e t (SeedCentral f t θ (η*r)) μ.toMeasure ω Set.univ).toReal<c}≤ENNReal.ofReal ε := by
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε.le).mpr
    apply hclip
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hhn.trans (by change n≤C*n; dsimp [C]; nlinarith)
    · have hlo : L≤H := by dsimp [L]; omega
      exact (Nat.cast_le.mpr hlo).trans_eq hH
  have hj' (a : ℤ) (q : SeedState e a) :
      environmentLaw ν {ω | ¬seedSplitTest e f a s h θ (b*r) j q ω}≤ENNReal.ofReal (1-j) := by
    have hmeas : MeasurableSet {ω | seedSplitTest e f a s h θ (b*r) j q ω} := by
      have hm := (seedSplitTest_joint_rows e f a s hh θ (b*r) j (seedAbove e a)
        (strip_subset_seedAbove e a h )).preimage (f := fun ω => (q,ω)) (measurable_const.prodMk measurable_id)
      exact (rowSigma_le _ _ hm)
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hρ).mpr
    change (environmentLaw ν).real {ω | ¬seedSplitTest e f a s h θ (b*r) j q ω}≤1-j
    rw [show {ω | ¬seedSplitTest e f a s h θ (b*r) j q ω} = {ω | seedSplitTest e f a s h θ (b*r) j q ω}ᶜ by rfl,
      measureReal_compl hmeas]
    simp only [measureReal_def,measure_univ,ENNReal.toReal_one]
    have hh := hjump (seedJumpInput e f a s q).val
    change j≤(environmentLaw ν).real {ω | seedSplitTest e f a s h θ (b*r) j q ω} at hh
    simpa only [measureReal_def] using (sub_le_sub_left hh 1)
  have hbound := seedOptions_failure_bound ν e f a s k N hh hL θ (η*r) (b*r) j c μ hk hj hc hs hz
    (ENNReal.ofReal ε) (ENNReal.ofReal (1-j)) hg hc' hj'
  have hsub : {ω | ¬SeedOptions f k s (b/2*r) δ (seedEndpointRaw e H (fun _ _ => True) μ.measure ω)} ⊆
      {ω | ¬SeedOptions f k s (b*r-η*r-2*(J:ℝ)*(η*r)) δ
        (seedEndpointRaw e (J*h+L) (fun _ _ => True) μ.measure ω)} := by
    intro ω hω ho
    rw [hsum] at ho
    exact hω (seedOptions_mono f k s hgap δ _ ho)
  apply (measure_mono hsub).trans (hbound.trans _)
  have he : (k-1:ℕ)*(ENNReal.ofReal (1-j))^N+(J:ℕ)*(k*ENNReal.ofReal ε)+k*ENNReal.ofReal ε =
      ENNReal.ofReal (((k-1:ℕ):ℝ)*(1-j)^N+((J:ℝ)+1)*k*ε) := by
    have hp₁ : 0≤((k-1:ℕ):ℝ)*(1-j)^N := by positivity
    have hp₂ : 0≤((J:ℝ)+1)*k*ε := by positivity
    rw [ENNReal.ofReal_add hp₁ hp₂, ENNReal.ofReal_mul (by positivity : (0:ℝ)≤(k-1:ℕ)),
      ENNReal.ofReal_natCast,ENNReal.ofReal_pow hρ, ENNReal.ofReal_mul (by positivity : (0:ℝ)≤((J:ℝ)+1)*k),
      ENNReal.ofReal_mul (by positivity : (0:ℝ)≤(J:ℝ)+1),
      ENNReal.ofReal_add (by positivity : (0:ℝ)≤J) (by norm_num),ENNReal.ofReal_one,
      ENNReal.ofReal_natCast,ENNReal.ofReal_natCast]
    ring
  change (k-1:ℕ)*(ENNReal.ofReal (1-j))^N+J*(k*ENNReal.ofReal ε)+k*ENNReal.ofReal ε≤ENNReal.ofReal p
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  linarith

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def seedPoint {d : ℕ} (e : Direction d) (x : Lattice d) : SeedProfile e (signedHeight e x) :=
  ⟨⟨Measure.dirac x,inferInstance⟩, by simp⟩

lemma seedPoint_raw {d : ℕ} (e : Direction d) (H : ℕ) (x : Lattice d) (ω : Environment d) :
    seedEndpointRaw e H (fun _ _ => True) (seedPoint e x).measure ω =
      variableHitKernel (realPosition (step e)) H (ω,x) := by
  simp only [seedEndpointRaw,seedPoint,SeedProfile.measure,ProbabilityMeasure.coe_mk,
    Set.ofPred_true,Measure.restrict_univ]
  exact Measure.dirac_bind (measurable_of_countable _) x

lemma seed_tuple_failure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (k H : ℕ) (s : ℤ) (hs : s=1 ∨ s= -1) (r g : ℝ) (hg : 2*r<g)
    (δ ε : ℝ≥0∞) (hoptions : ∀ x : Lattice d, environmentLaw ν {ω | ¬SeedOptions f k s g δ
      (variableHitKernel (realPosition (step e)) H (ω,x))}≤ε)
    (v : Fin k → Lattice d) :
    environmentLaw ν {ω | rawTupleEndpointLaw (realPosition (step e)) H ω v {y | TupleSeparated f r y}<δ^k}≤k*ε := by
  have hsub : {ω | rawTupleEndpointLaw (realPosition (step e)) H ω v {y | TupleSeparated f r y}<δ^k} ⊆
      ⋃ i : Fin k, {ω | ¬SeedOptions f k s g δ (variableHitKernel (realPosition (step e)) H (ω,v i))} := by
    intro ω hω
    by_contra hn
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq,not_exists,not_not] at hn
    have hh := seedOptions_product_mass f s g r hs hg δ
      (fun i : Fin k => variableHitKernel (realPosition (step e)) H (ω,v i)) le_rfl hn
    exact (not_lt_of_ge hh) hω
  exact (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
    ((Finset.sum_le_sum fun i _ => hoptions (v i)).trans_eq (by simp)))

theorem seed_mass_at_scale {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) (hk : 2≤k) (p : ℝ) (hp : 0<p) :
    ∃ C c₀ g₀ R : ℝ, 0<C ∧ 0<c₀ ∧ 0<g₀ ∧ 0<R ∧
    ∀ r : ℝ, R≤r → ∀ H : ℕ,
      (H:ℝ)=C*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r →
      ∀ π : ProbabilityMeasure (Fin k → Lattice d),
        1-p < (environmentLaw ν).real {ω | ENNReal.ofReal g₀≤
          rawTupleMixture (realPosition (step e)) H π.toMeasure ω {v | TupleSeparated f (c₀*r) v}} := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  let ε := p/(4*k)
  have hε : 0<ε := div_pos hp (by positivity)
  obtain ⟨C,A,R,δ,hC,hA,hR,hδ,hopt⟩ := seed_uniform_options ν hue e f hef htrans k (by omega) ε hε
  let D := (min δ 1)^k
  have hD : 0<D := ENNReal.pow_pos (lt_min hδ (by norm_num)) k
  have hD1 : D≤1 := by exact pow_le_one₀ (show (0:ℝ≥0∞) ≤ min δ 1 from bot_le) (min_le_right _ _)
  have hDt : D≠⊤ := ne_top_of_le_ne_top (by simp) hD1
  have hDr : 0<D.toReal := ENNReal.toReal_pos (ne_of_gt hD) hDt
  refine ⟨C,A/4,D.toReal/2,R,hC,by positivity,by positivity,hR,fun r hr H hH π => ?_⟩
  obtain ⟨s,hs,hsall⟩ := hopt r hr H hH
  have hopt' (x : Lattice d) : environmentLaw ν {ω | ¬SeedOptions f k s (A*r) δ
      (variableHitKernel (realPosition (step e)) H (ω,x))}≤ENNReal.ofReal ε := by
    simpa only [seedPoint_raw] using hsall (signedHeight e x) (seedPoint e x)
  have hgap : 2*(A/4*r)<A*r := by nlinarith [hR.trans_le hr]
  let S := {v : Fin k → Lattice d | TupleSeparated f (A/4*r) v}
  let F : Environment d → (Fin k → Lattice d) → ℝ := fun ω v =>
    (rawTupleEndpointLaw (realPosition (step e)) H ω v S).toReal
  have hF : Measurable (Function.uncurry F) :=
    ((Measure.measurable_coe (Set.to_countable _).measurableSet).comp
      (measurable_rawTupleEndpointLaw _ _)).ennreal_toReal
  have hF0 (ω) (v) : 0≤F ω v := ENNReal.toReal_nonneg
  have hF1 (ω) (v) : F ω v≤1 := by
    apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
    simpa using (measure_mono (Set.subset_univ S) |>.trans (rawTupleEndpointLaw_le_one _ _ ω v))
  have hbad (v : Fin k → Lattice d) : (environmentLaw ν).real {ω | F ω v<2*(D.toReal/2)}≤k*ε := by
    have hsub : {ω | F ω v<2*(D.toReal/2)} ⊆
        {ω | rawTupleEndpointLaw (realPosition (step e)) H ω v S<δ^k} := by
      intro ω hω
      have hd : D≤δ^k := by dsimp [D]; gcongr; exact min_le_left _ _
      by_contra hn
      have hl : D≤rawTupleEndpointLaw (realPosition (step e)) H ω v S := hd.trans (not_lt.mp hn)
      have hh := ENNReal.toReal_mono (measure_ne_top _ _) hl
      change D.toReal≤F ω v at hh
      change F ω v<2*(D.toReal/2) at hω
      linarith
    have hb := seed_tuple_failure ν e f k H s hs (A/4*r) (A*r) hgap δ (ENNReal.ofReal ε) hopt' v
    have hbu : environmentLaw ν {ω | F ω v<2*(D.toReal/2)}≤ENNReal.ofReal ((k:ℝ)*ε) := by
      rw [ENNReal.ofReal_mul hk0.le,ENNReal.ofReal_natCast]
      exact (measure_mono hsub).trans hb
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbu
  have hm := mixture_small_mass_probability (environmentLaw ν) π.toMeasure F hF hF0 hF1
    (show 0<D.toReal/2 by positivity) hbad
  have hint (ω : Environment d) : (∫ v, F ω v ∂π.toMeasure) =
      (rawTupleMixture (realPosition (step e)) H π.toMeasure ω S).toReal := by
    rw [rawTupleMixture_apply]
    exact integral_toReal (measurable_of_countable _).aemeasurable (ae_of_all _ fun v => measure_lt_top _ _)
  have hmf : Measurable (fun ω => (rawTupleMixture (realPosition (step e)) H π.toMeasure ω S).toReal) := by
    have hh : Measurable (fun ω => ∫ v, F ω v ∂π.toMeasure) := hF.stronglyMeasurable.integral_prod_right.measurable
    simpa only [hint] using hh
  have hmass (ω : Environment d) : rawTupleMixture (realPosition (step e)) H π.toMeasure ω S≤1 := by
    rw [rawTupleMixture_apply]
    exact (lintegral_mono fun v => (measure_mono (Set.subset_univ S)).trans (rawTupleEndpointLaw_le_one _ _ ω v)).trans_eq (by simp)
  have he : {ω | ENNReal.ofReal (D.toReal/2)≤rawTupleMixture (realPosition (step e)) H π.toMeasure ω S} =
      {ω | (rawTupleMixture (realPosition (step e)) H π.toMeasure ω S).toReal<D.toReal/2}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_compl_iff,not_lt]
    exact ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top (by simp) (hmass ω))
  rw [he,measureReal_compl (measurableSet_lt hmf measurable_const)]
  simp only [hint] at hm
  have heps : 2*((k:ℝ)*ε)=p/2 := by dsimp [ε]; field_simp; ring
  rw [heps] at hm
  have hu : (environmentLaw ν).real Set.univ=1 := by simp [measureReal_def]
  rw [hu]
  linarith

end DirectionalTransience

end

end OAI
