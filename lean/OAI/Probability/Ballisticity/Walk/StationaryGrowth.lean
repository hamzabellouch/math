import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace DirectionalTransience

noncomputable def orbitAverage {Ω : Type*} (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (n:ℝ)⁻¹ * ∑ i∈Finset.range n, f (T^[i] ω)

lemma orbitAverage_measurable {Ω : Type*} [MeasurableSpace Ω] (T : Ω → Ω) (hT : Measurable T)
    (f : Ω → ℝ) (hf : Measurable f) (n : ℕ) : Measurable (orbitAverage T f n) := by
  unfold orbitAverage
  fun_prop

lemma orbitAverage_bounds {Ω : Type*} (T : Ω → Ω) (f : Ω → ℝ)
    (hf : ∀ ω, f ω∈Set.Icc 0 1) (n : ℕ) (ω : Ω) : orbitAverage T f n ω∈Set.Icc 0 1 := by
  refine ⟨mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (Finset.sum_nonneg fun i _ => (hf _).1),?_⟩
  by_cases hn : n=0
  · simp [orbitAverage,hn]
  calc orbitAverage T f n ω ≤ (n:ℝ)⁻¹*∑ _i∈Finset.range n, (1:ℝ) :=
         mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hf _).2) (by positivity)
       _ = 1 := by simp [hn]

lemma orbitAverage_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ)
    (n : ℕ) (hn : n≠0) : (∫ ω, orbitAverage T f n ω ∂μ)=∫ ω, f ω ∂μ := by
  simp only [orbitAverage]
  rw [integral_const_mul,integral_finsetSum (Finset.range n) (fun i _ => (show Integrable (fun ω => f (T^[i] ω)) μ from (hT.iterate i).integrable_comp_of_integrable hf))]
  have hi (i : ℕ) : (∫ ω, f (T^[i] ω) ∂μ)=∫ ω, f ω ∂μ := by
    have hh := integral_map (hT.iterate i).measurable.aemeasurable
      (show AEStronglyMeasurable f (μ.map (T^[i])) from by rw [(hT.iterate i).map_eq]; exact hf.aestronglyMeasurable)
    rw [(hT.iterate i).map_eq] at hh
    exact hh.symm
  simp only [hi]
  simp [hn]

lemma lp_orbitAverage {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (x : Lp ℝ 2 μ) (n : ℕ) :
    (birkhoffAverage ℝ (Lp.compMeasurePreservingₗᵢ (E:=ℝ) (p:=2) ℝ T hT).toContinuousLinearMap id n x : Lp ℝ 2 μ)
      =ᵐ[μ] orbitAverage T x n := by
  let L := (Lp.compMeasurePreservingₗᵢ (E:=ℝ) (p:=2) ℝ T hT).toContinuousLinearMap
  have hi (i : ℕ) : (L^[i] x : Lp ℝ 2 μ)=ᵐ[μ] (fun ω => x (T^[i] ω)) := by
    change ((Lp.compMeasurePreserving T hT)^[i] x : Lp ℝ 2 μ)=ᵐ[μ] _
    rw [Lp.compMeasurePreserving_iterate]
    exact Lp.coeFn_compMeasurePreserving x (hT.iterate i)
  have hs := Lp.coeFn_fun_finsetSum (Finset.range n) (fun i => L^[i] x)
  have hm := Lp.coeFn_smul ((n:ℝ)⁻¹) (∑ i∈Finset.range n, L^[i] x)
  have hall := ae_all_iff.mpr hi
  filter_upwards [hs,hm,hall] with ω hs hm hh
  change (((n:ℝ)⁻¹ • ∑ i∈Finset.range n, L^[i] x : Lp ℝ 2 μ) : Ω → ℝ) ω=_
  rw [hm]
  change (n:ℝ)⁻¹ * _ = _
  rw [hs]
  simp only [orbitAverage,hh]

lemma stationary_bounded_growth_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (f : Ω → ℝ) (hf : Measurable f) (hb : ∀ ω, f ω∈Set.Icc 0 1) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ᵐ ω ∂μ, g ω∈Set.Icc 0 1) ∧
      (∀ᵐ ω ∂μ, g (T ω)=g ω) ∧ (∫ ω, g ω ∂μ)=∫ ω, f ω ∂μ ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        ∀ᵐ ω ∂μ, Tendsto (fun k => orbitAverage T f (ns k) ω) atTop (𝓝 (g ω)) := by
  let hfLp : MemLp f 2 μ := memLp_of_bounded (Eventually.of_forall hb) hf.aestronglyMeasurable 2
  let x := hfLp.toLp f
  let L := (Lp.compMeasurePreservingₗᵢ (E:=ℝ) (p:=2) ℝ T hT).toContinuousLinearMap
  let y := (L.eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)).orthogonalProjectionOnto x
  have hy : L (y : Lp ℝ 2 μ)=(y : Lp ℝ 2 μ) := y.property
  have hlim := L.tendsto_birkhoffAverage_orthogonalProjection
    (Lp.compMeasurePreservingₗᵢ (E:=ℝ) (p:=2) ℝ T hT).norm_toContinuousLinearMap_le x
  obtain ⟨ns,hns,hnsLim⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  let g := (Lp.aestronglyMeasurable (y : Lp ℝ 2 μ)).mk (y : Lp ℝ 2 μ)
  have hgm : Measurable g := (Lp.aestronglyMeasurable (y : Lp ℝ 2 μ)).measurable_mk
  have hg : (y : Lp ℝ 2 μ)=ᵐ[μ] g := (Lp.aestronglyMeasurable (y : Lp ℝ 2 μ)).ae_eq_mk
  have hall : ∀ᵐ ω ∂μ, ∀ i : ℕ, x (T^[i] ω)=f (T^[i] ω) :=
    ae_all_iff.mpr fun i => (hT.iterate i).quasiMeasurePreserving.ae hfLp.coeFn_toLp
  have hco : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      (birkhoffAverage ℝ L id n x : Lp ℝ 2 μ) ω=orbitAverage T f n ω := by
    have ha := ae_all_iff.mpr (lp_orbitAverage μ hT x)
    filter_upwards [ha,hall] with ω ha hh n
    rw [ha n]
    simp only [orbitAverage,hh]
  have hgLim : ∀ᵐ ω ∂μ, Tendsto (fun k => orbitAverage T f (ns k) ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hnsLim,hco,hg] with ω hh hc hg
    change Tendsto (fun k => (birkhoffAverage ℝ L id (ns k) x : Lp ℝ 2 μ) ω) atTop (𝓝 ((y : Lp ℝ 2 μ) ω)) at hh
    simpa only [hc,hg] using hh
  have hgb : ∀ᵐ ω ∂μ, g ω∈Set.Icc 0 1 := hgLim.mono fun ω hh =>
    isClosed_Icc.mem_of_tendsto hh (Eventually.of_forall fun k => orbitAverage_bounds T f hb _ ω)
  have hinv : ∀ᵐ ω ∂μ, g (T ω)=g ω := by
    have he := Lp.coeFn_compMeasurePreserving (y : Lp ℝ 2 μ) hT
    change ((L (y : Lp ℝ 2 μ) : Lp ℝ 2 μ) : Ω → ℝ)=ᵐ[μ] _ at he
    rw [hy] at he
    filter_upwards [he,hg,hT.quasiMeasurePreserving.ae hg] with ω he hg hgt
    exact hgt.symm.trans (he.symm.trans hg)
  have hfi : Integrable f μ := (memLp_of_bounded (Eventually.of_forall hb) hf.aestronglyMeasurable 1).integrable (by rfl)
  have hint := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1:ℝ))
    (fun k => (orbitAverage_measurable T hT.measurable f hf (ns k)).aestronglyMeasurable)
    (integrable_const 1) (fun k => Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (orbitAverage_bounds T f hb (ns k) ω).1]
      exact (orbitAverage_bounds T f hb (ns k) ω).2) hgLim
  have hevent : ∀ᶠ k in atTop, (∫ ω, orbitAverage T f (ns k) ω ∂μ)=∫ ω, f ω ∂μ := by
    filter_upwards [hns.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk
    exact orbitAverage_integral μ hT hfi _ (by omega)
  refine ⟨g,hgm,hgb,hinv,?_,ns,hns,hgLim⟩
  exact tendsto_nhds_unique hint (tendsto_const_nhds.congr' (hevent.mono fun _ h => h.symm))

lemma growth_limit_respects_symmetry {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {T : Ω → Ω} {f g : Ω → ℝ} (ns : ℕ → ℕ)
    (hg : ∀ᵐ ω ∂μ, Tendsto (fun k => orbitAverage T f (ns k) ω) atTop (𝓝 (g ω)))
    {S : Ω → Ω} (hS : MeasurePreserving S μ μ)
    (hcomm : Function.Commute T S) (hfS : ∀ ω, f (S ω)=f ω) :
    ∀ᵐ ω ∂μ, g (S ω)=g ω := by
  filter_upwards [hg,hS.quasiMeasurePreserving.ae hg] with ω hω hSω
  have he (k : ℕ) : orbitAverage T f (ns k) (S ω)=orbitAverage T f (ns k) ω := by
    simp only [orbitAverage, (hcomm.iterate_left _).eq, hfS]
  exact tendsto_nhds_unique (hSω.congr fun k => he k) hω

lemma stationary_positive_growth {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (c : Ω → ℝ) (hc : Measurable c) (hc0 : ∀ ω, 0≤c ω)
    (hci : Integrable c μ) (hcp : 0<∫ ω, c ω ∂μ) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ᵐ ω ∂μ, g ω∈Set.Icc 0 1) ∧
      (∀ᵐ ω ∂μ, g (T ω)=g ω) ∧ ∃ ζ : ℝ, 0<ζ ∧ 0<μ {ω | ζ<g ω} ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        (∀ᵐ ω ∂μ, Tendsto (fun k => orbitAverage T (fun ω => min (c ω) 1) (ns k) ω) atTop (𝓝 (g ω))) ∧
        ∀ᵐ ω ∂μ, ζ<g ω → ∀ᶠ k in atTop,
          ζ*(ns k:ℝ)<∑ i∈Finset.range (ns k), c (T^[i] ω) := by
  let f := fun ω => min (c ω) 1
  have hfm : Measurable f := hc.min measurable_const
  have hfb : ∀ ω, f ω∈Set.Icc 0 1 := fun ω => ⟨le_min (hc0 ω) (by norm_num),min_le_right _ _⟩
  have hfi : Integrable f μ := (memLp_of_bounded (Eventually.of_forall hfb) hfm.aestronglyMeasurable 1).integrable (by rfl)
  have hfp : 0<∫ ω, f ω ∂μ := by
    by_contra hh
    have hz := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun ω => (hfb ω).1) hfi).mp
      (le_antisymm (le_of_not_gt hh) (integral_nonneg fun ω => (hfb ω).1))
    have hcz : c=ᵐ[μ] 0 := hz.mono fun ω hh => by
      change min (c ω) 1=0 at hh
      change c ω=0
      rcases min_cases (c ω) 1 with h|h
      · rw [h.1] at hh; exact hh
      · rw [h.1] at hh; norm_num at hh
    have hi0 : (∫ ω, c ω ∂μ)=0 :=
      (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hc0) hci).mpr hcz
    linarith
  obtain ⟨g,hgm,hgb,hgT,hgi,ns,hns,hlim⟩ := stationary_bounded_growth_limit μ hT f hfm hfb
  have hgp : 0<∫ ω, g ω ∂μ := by rw [hgi]; exact hfp
  have hex : ∃ ζ : ℝ, 0<ζ ∧ 0<μ {ω | ζ<g ω} := by
    by_contra! hh
    have hz (k : ℕ) : ∀ᵐ ω ∂μ, g ω≤1/(k+1:ℝ) := by
      rw [ae_iff]
      simpa only [not_le] using (le_zero_iff.mp (hh (1/(k+1:ℝ)) (by positivity)))
    have hgz : ∀ᵐ ω ∂μ, g ω≤0 := by
      filter_upwards [ae_all_iff.mpr hz] with ω hω
      exact ge_of_tendsto (tendsto_one_div_add_atTop_nhds_zero_nat) (Eventually.of_forall hω)
    have hgi' : Integrable g μ := (memLp_of_bounded hgb hgm.aestronglyMeasurable 1).integrable (by rfl)
    have hgle := integral_nonpos_of_ae hgz
    linarith
  obtain ⟨ζ,hζ,hE⟩ := hex
  refine ⟨g,hgm,hgb,hgT,ζ,hζ,hE,ns,hns,hlim,?_⟩
  filter_upwards [hlim] with ω hω hgω
  filter_upwards [hω.eventually (lt_mem_nhds hgω),hns.tendsto_atTop.eventually (eventually_ge_atTop 1)] with k hk hn
  have hn0 : (0:ℝ)<ns k := by exact_mod_cast (show 0<ns k by omega)
  have hh : ζ*(ns k:ℝ)<∑ i∈Finset.range (ns k), f (T^[i] ω) := by
    apply (lt_div_iff₀ hn0).mp
    simpa only [orbitAverage,div_eq_mul_inv,mul_comm] using hk
  exact hh.trans_le (Finset.sum_le_sum fun i _ => min_le_left _ _)

end DirectionalTransience

end

end OAI
