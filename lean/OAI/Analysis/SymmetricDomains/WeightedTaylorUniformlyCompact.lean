import Mathlib
import OAI.Analysis.SymmetricDomains.InteriorBallsTotallyReal
import OAI.Analysis.SymmetricDomains.NormalOffsetNoncollapse

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Metric
open scoped Topology

theorem analytic_normal_offset_noncollapse {k : ℕ} {Ω : Set (Fin k → ℂ)}
    (hΩ : IsOpen Ω) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    (hCP : Wiener.DiscContinuityWithin k Ω ε)
    {φ : (Fin k → ℝ) → Fin k → ℝ} (hφ : AnalyticAt ℝ φ 0) (hφ0 : φ 0 = 0)
    (hdφ : HasFDerivAt φ (0 : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ)) 0)
    {G : (Fin k → ℝ) × ℝ → Fin k → ℂ} (hG : AnalyticAt ℝ G 0)
    (hG0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
      G (x,0) = fun i => (x i : ℂ)+Complex.I*(φ x i : ℂ))
    (hGΩ : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), 0 < q.2 → G q ∈ Ω)
    (hbdry : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ),
      (fun i => (x i : ℂ)+Complex.I*(φ x i : ℂ)) ∉ Ω)
    (F : Set (Fin k → ℝ))
    (hexcluded : ∀ (s : ℕ → Fin k → ℝ) (t : ℕ → ℝ) (v : ℕ → Fin k → ℝ) (w : Fin k → ℝ),
      Tendsto s atTop (𝓝 0) → Tendsto t atTop (𝓝 0) → (∀ j, 0 < t j) →
      Tendsto v atTop (𝓝 w) → w ∈ F →
      Tendsto (fun j => infDist (v j)
        (offsetScaled (fun x => {u | ‖u‖ < ρ ∧
          (fun i => (x i : ℂ)+Complex.I*((φ x i+u i) : ℂ)) ∈ Ω}) (s j) (t j))ᶜ)
        atTop (𝓝 0)) : F ≠ univ := by
  obtain ⟨c,C,t₀,hc,hC,ht₀,hballs⟩ :=
    interior_balls_from_totally_real_graphs hΩ hε hCP hφ hφ0 hdφ hG hG0 hGΩ
  exact normal_offset_noncollapse hφ.contDiffAt hφ0 hρ hc hC ht₀ hballs hbdry F hexcluded

end

open Set Filter Metric Asymptotics
open scoped Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def parabolicScale (u : ℝ) (x : E × F) : E × F := (u • x.1,u^2 • x.2)

lemma parabolicScale_norm {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (x : E × F) :
    ‖parabolicScale u x‖ ≤ u*‖x‖ := by
  rw [parabolicScale,Prod.norm_def,max_le_iff]
  constructor
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hu]
    exact mul_le_mul_of_nonneg_left (norm_fst_le x) hu
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg u)]
    calc u^2*‖x.2‖ ≤ u*‖x.2‖ := mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
         _ ≤ u*‖x‖ := mul_le_mul_of_nonneg_left (norm_snd_le x) hu

lemma parabolic_cubic_remainder {R : E × F → G} (hR : R =O[𝓝 0] (fun x => ‖x‖^3))
    {K : Set (E × F)} (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun u x => (u^2)⁻¹ • R (parabolicScale u x))
      (fun _ => 0) (𝓝[>] (0 : ℝ)) K := by
  obtain ⟨C,hC,hbound⟩ := hR.exists_pos
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hbound.bound
  obtain ⟨M,hM,hKM⟩ := hK.exists_pos_norm_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have huid : Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have huM : ∀ᶠ u : ℝ in 𝓝[>] 0, u*M < r := by
    exact (tendsto_order.mp (show Tendsto (fun u : ℝ => u*M) (𝓝[>] 0) (𝓝 0) by
      simpa using huid.mul_const M)).2 r hr
  have huε : ∀ᶠ u : ℝ in 𝓝[>] 0, C*M^3*u < ε := by
    exact (tendsto_order.mp (show Tendsto (fun u : ℝ => C*M^3*u) (𝓝[>] 0) (𝓝 0) by
      simpa using huid.const_mul (C*M^3))).2 ε hε
  filter_upwards [self_mem_nhdsWithin,huM,huε,
    show ∀ᶠ u : ℝ in 𝓝[>] 0, u < 1 from (tendsto_order.mp huid).2 1 zero_lt_one] with u hu hur huε hu1
  intro x hx
  have hn : ‖parabolicScale u x‖ ≤ u*M :=
    (parabolicScale_norm hu.le hu1.le x).trans (mul_le_mul_of_nonneg_left (hKM x hx) hu.le)
  have hb := hrs (mem_ball_zero_iff.mpr (hn.trans_lt hur))
  have hb' : ‖R (parabolicScale u x)‖ ≤ C*(u*M)^3 := by
    apply hb.trans
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) 3)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 3) hC.le
  rw [dist_zero_left,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (sq_pos_of_pos hu))]
  calc (u^2)⁻¹ * ‖R (parabolicScale u x)‖ ≤ (u^2)⁻¹*(C*(u*M)^3) :=
         mul_le_mul_of_nonneg_left hb' (inv_nonneg.mpr (sq_nonneg u))
       _ = C*M^3*u := by field_simp
       _ < ε := huε

lemma multilinear_one_eval (p : FormalMultilinearSeries ℝ (E × F) G) (x : E × F) :
    p 1 (fun _ => x) = (continuousMultilinearCurryFin1 ℝ (E × F) G (p 1)) x := by
  rw [continuousMultilinearCurryFin1_apply]
  congr 1

lemma parabolic_partialSum {f : E × F → G} {p : FormalMultilinearSeries ℝ (E × F) G}
    (hf : HasFPowerSeriesAt f p 0) (hf0 : f 0 = 0)
    (hlin : ∀ z : E, p 1 (fun _ => (z,0)) = 0) {u : ℝ} (hu : u ≠ 0) (x : E × F) :
    (u^2)⁻¹ • p.partialSum 3 (parabolicScale u x) =
      p 1 (fun _ => (0,x.2)) + p 2 (fun _ => (x.1,u • x.2)) := by
  let L := continuousMultilinearCurryFin1 ℝ (E × F) G (p 1)
  have hL : ∀ z : E, L (z,0) = 0 := by
    intro z
    simpa only [L,← multilinear_one_eval] using hlin z
  have hδ : parabolicScale u x = (u • x.1,0)+(u^2) • (0,x.2) := by
    ext <;> simp [parabolicScale]
  have hδ' : parabolicScale u x = u • (x.1,u • x.2) := by
    ext <;> simp [parabolicScale,smul_smul,pow_two]
  have hfirst : p 1 (fun _ => parabolicScale u x) = u^2 • p 1 (fun _ => (0,x.2)) := by
    rw [multilinear_one_eval,hδ,map_add,map_smul]
    change L (u • x.1,0)+(u^2) • L (0,x.2) = _
    rw [hL,zero_add,← multilinear_one_eval]
  have hsecond : p 2 (fun _ => parabolicScale u x) = u^2 • p 2 (fun _ => (x.1,u • x.2)) := by
    simp only [hδ']
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      (p 2).map_smul_univ (fun _ => u) (fun _ => (x.1,u • x.2))
  simp only [FormalMultilinearSeries.partialSum,Finset.sum_range_succ,Finset.sum_range_zero,
    zero_add,hf.coeff_zero,hf0,hfirst,hsecond,smul_add,inv_smul_smul₀ (pow_ne_zero 2 hu)]

theorem parabolic_taylor_uniformly_compact {f : E × F → G}
    {p : FormalMultilinearSeries ℝ (E × F) G} (hf : HasFPowerSeriesAt f p 0)
    (hf0 : f 0 = 0) (hlin : ∀ z : E, p 1 (fun _ => (z,0)) = 0)
    {K : Set (E × F)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun u x => (u^2)⁻¹ • f (parabolicScale u x))
      (fun x => p 1 (fun _ => (0,x.2)) + p 2 (fun _ => (x.1,0)))
      (𝓝[>] (0 : ℝ)) K := by
  have hR : (fun x => f x-p.partialSum 3 x) =O[𝓝 0] (fun x => ‖x‖^3) := by
    simpa only [zero_add] using hf.isBigO_sub_partialSum_pow 3
  have hrem := parabolic_cubic_remainder hR hK.isBounded
  have hpoly : TendstoUniformlyOn
      (fun u (x : E × F) => p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,u • x.2)))
      (fun x => p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,0))) (𝓝[>] (0 : ℝ)) K := by
    have hcont : Continuous (fun q : ℝ × (E × F) =>
        p 1 (fun _ => (0,q.2.2))+p 2 (fun _ => (q.2.1,q.1 • q.2.2))) := by fun_prop
    have hh := continuousOn_uniformly_compact
      (f := fun u (x : E × F) => p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,u • x.2))) hK (univ_mem : (univ : Set ℝ) ∈ 𝓝 (0:ℝ))
      hcont.continuousOn
    have hh' := tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
      (hh.tendstoUniformlyOnFilter.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
    simpa only [zero_smul] using hh'
  have hh : TendstoUniformlyOn
      (fun u x => (u^2)⁻¹ • (f (parabolicScale u x)-p.partialSum 3 (parabolicScale u x)) +
        (p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,u • x.2))))
      (fun x => p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,0))) (𝓝[>] (0 : ℝ)) K := by
    exact (hrem.add hpoly).congr_right (fun x _hx => zero_add _)
  apply hh.congr
  filter_upwards [self_mem_nhdsWithin] with u hu
  intro x _hx
  dsimp only
  rw [← parabolic_partialSum hf hf0 hlin hu.ne' x,← smul_add,sub_add_cancel]

lemma uniform_reindex {I J X Y : Type*} [UniformSpace Y] {l : Filter I} {r : Filter J}
    {A : I → X → Y} {a : X → Y} {K : Set X} (ha : TendstoUniformlyOn A a l K)
    {u : J → I} (hu : Tendsto u r l) : TendstoUniformlyOn (fun j => A (u j)) a r K :=
  fun V hV => hu.eventually (ha V hV)

def weightedScale (t : ℝ) (x : E × F) : E × F :=
  (Real.sqrt t • x.1,t • x.2)

lemma sqrt_tendsto_pos : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact Real.sqrt_pos.mpr ht

theorem weighted_taylor_uniformly_compact {f : E × F → G}
    (hf : AnalyticAt ℝ f 0) (hf0 : f 0 = 0)
    (hlin : ∀ z : E, fderiv ℝ f 0 (z,0) = 0) :
    ∃ q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) G,
      ∀ K : Set (E × F), IsCompact K →
      TendstoUniformlyOn (fun t x => t⁻¹ • f (weightedScale t x))
        (fun x => fderiv ℝ f 0 (0,x.2)+q (fun _ => x.1)) (𝓝[>] (0 : ℝ)) K := by
  obtain ⟨p,hp⟩ := hf
  let q := (p 2).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ E F)
  refine ⟨q,fun K hK => ?_⟩
  have hh := parabolic_taylor_uniformly_compact hp hf0
    (fun z => by simpa only [multilinear_one_eval,← hp.fderiv_eq] using hlin z) hK
  have hu := uniform_reindex hh sqrt_tendsto_pos
  have hce : (fun x : E × F => p 1 (fun _ => (0,x.2))+p 2 (fun _ => (x.1,0))) =
      (fun x => fderiv ℝ f 0 (0,x.2)+q (fun _ => x.1)) := by
    funext x
    simp only [multilinear_one_eval,hp.fderiv_eq,q,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,ContinuousLinearMap.inl_apply]
  rw [hce] at hu
  apply hu.congr
  filter_upwards [self_mem_nhdsWithin] with t ht
  intro x _hx
  simp only [parabolicScale,weightedScale,Real.sq_sqrt ht.le]

end Release061

end

end OAI
