import Mathlib
import OAI.Analysis.PathSelection.ClockComposition
import OAI.Analysis.PathSelection.FilteredExpansions

namespace OAI

/-! Multivariate moving Taylor expansions and finite tuple-clock composition. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Metric
open scoped NNReal ENNReal
namespace DegeneratingTrees.MovingTaylor
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

 

lemma uniform_changeOrigin_coefficients [CompleteSpace F] (p : FormalMultilinearSeries 𝕜 E F)
    {r : ℝ≥0} (hr : (r+r : ℝ≥0∞) < p.radius) :
    ∃ C : ℝ≥0, ∀ x : E, ‖x‖₊ ≤ r → ∀ k : ℕ,
      ‖p.changeOrigin x k‖₊ * r^k ≤ C := by
  have hs := NNReal.summable_sigma.mp (p.changeOriginSeries_summable_aux₁ hr)
  let C : ℝ≥0 := ∑' k : ℕ, ∑' s : Σ l : ℕ,
      {s : Finset (Fin (k+l)) // s.card=l}, ‖p (k+s.1)‖₊ * r^s.1 * r^k
  refine ⟨C,?_⟩
  intro x hx k
  have hr' : (r : ℝ≥0∞) < p.radius := (le_add_of_nonneg_right bot_le).trans_lt hr
  have hx' : (‖x‖₊ : ℝ≥0∞) < p.radius :=
    (ENNReal.coe_le_coe.mpr hx).trans_lt hr'
  calc
    ‖p.changeOrigin x k‖₊ * r^k ≤
        (∑' s : Σ l : ℕ, {s : Finset (Fin (k+l)) // s.card=l},
          ‖p (k+s.1)‖₊ * ‖x‖₊^s.1) * r^k :=
      mul_le_mul' (p.nnnorm_changeOrigin_le k hx') le_rfl
    _ ≤ (∑' s : Σ l : ℕ, {s : Finset (Fin (k+l)) // s.card=l},
          ‖p (k+s.1)‖₊ * r^s.1) * r^k := by
      apply mul_le_mul' ?_ le_rfl
      exact Summable.tsum_le_tsum (fun s => by gcongr)
        (p.changeOriginSeries_summable_aux₂ hx' k)
        (p.changeOriginSeries_summable_aux₂ hr' k)
    _ = ∑' s : Σ l : ℕ, {s : Finset (Fin (k+l)) // s.card=l},
          ‖p (k+s.1)‖₊ * r^s.1 * r^k := (NNReal.tsum_mul_right _ _).symm
    _ ≤ C := hs.2.le_tsum k (fun _ _ => bot_le)

 

theorem analytic_uniform_moving_taylor [CompleteSpace F] {g : E → F} {d : E}
    (hg : AnalyticAt 𝕜 g d) :
    ∃ c : (n : ℕ) → E → (E [×n]→L[𝕜] F),
      (∀ n, AnalyticAt 𝕜 (c n) d) ∧ ∃ r C : ℝ, 0<r ∧ 0≤C ∧
      ∀ a v : E, ‖a-d‖≤r → ‖v‖≤r/2 → ∀ N : ℕ,
        ‖g (a+v)-∑ n ∈ Finset.range N,c n a (fun _ => v)‖ ≤
          C*(‖v‖/r)^N := by
  classical
  obtain ⟨p,R,hp⟩ := hg
  obtain ⟨R₀,hR₀,hR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hR₀' : 0<R₀ := ENNReal.coe_pos.mp hR₀
  let r : ℝ≥0 := R₀/2
  have hr : 0<r := by dsimp [r]; positivity
  have hr' : 0<(r:ℝ) := NNReal.coe_pos.mpr hr
  have hrr : r+r=R₀ := by dsimp [r]; ring
  have hrR : (r+r : ℝ≥0∞)<R := by rw [←ENNReal.coe_add,hrr]; exact hR
  have hrR' : (r : ℝ≥0∞)<R := (le_add_of_nonneg_right bot_le).trans_lt hrR
  obtain ⟨C,hC⟩ := uniform_changeOrigin_coefficients p (hrR.trans_le hp.r_le)
  let c : (n : ℕ) → E → (E [×n]→L[𝕜] F) := fun n a => p.changeOrigin (a-d) n
  refine ⟨c,?_,r,2*(C:ℝ),hr',by positivity,?_⟩
  · intro n
    have h := (p.analyticAt_changeOrigin (hp.r_pos.trans_le hp.r_le) n)
    have hs : AnalyticAt 𝕜 (fun a : E => a-d) d := analyticAt_id.sub analyticAt_const
    have hs' : AnalyticAt 𝕜 (fun x : E => p.changeOrigin x n) (d-d) := by
      simpa only [sub_self] using h
    exact hs'.comp (f := fun a : E => a-d) hs
  intro a v ha hv N
  have hax : ‖a-d‖₊≤r := ha
  have hav : (‖a-d‖₊ : ℝ≥0∞)<R := (ENNReal.coe_le_coe.mpr hax).trans_lt hrR'
  have hv' : ‖v‖₊≤r := by
    change ‖v‖≤(r:ℝ)
    linarith
  have hvR : (‖v‖₊ : ℝ≥0∞)<R-(‖a-d‖₊ : ℝ≥0∞) := by
    apply lt_tsub_iff_right.mpr
    exact (add_le_add (ENNReal.coe_le_coe.mpr hv')
      (ENNReal.coe_le_coe.mpr hax)).trans_lt hrR
  have hvball : v∈Metric.eball (0:E) (R-(‖a-d‖₊ : ℝ≥0∞)) := by
    simpa only [Metric.mem_eball,edist_zero_right,enorm] using hvR
  have hsum := (hp.changeOrigin hav).hasSum hvball
  have hadd : d+(a-d)=a := by abel
  rw [hadd] at hsum
  let q : ℝ := ‖v‖/(r:ℝ)
  have hq0 : 0≤q := div_nonneg (norm_nonneg _) hr'.le
  have hq : q≤1/2 := (div_le_iff₀ hr').mpr (by linarith)
  have hb : ∀ n : ℕ, ‖p.changeOrigin (a-d) n (fun _ => v)‖ ≤ (C:ℝ)*q^n := by
    intro n
    have hn : ‖p.changeOrigin (a-d) n‖*(r:ℝ)^n≤(C:ℝ) := by
      exact_mod_cast hC (a-d) hax n
    calc
      _ ≤ ‖p.changeOrigin (a-d) n‖*∏ _ : Fin n, ‖v‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ = (‖p.changeOrigin (a-d) n‖*(r:ℝ)^n)*q^n := by
        simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,q,div_pow]
        field_simp
      _ ≤ (C:ℝ)*q^n := mul_le_mul_of_nonneg_right hn (pow_nonneg hq0 n)
  have herr := norm_sub_le_of_geometric_bound_of_hasSum (by linarith : q<1) hb hsum N
  rw [norm_sub_rev] at herr
  change ‖g (a+v)-∑ n ∈ Finset.range N,p.changeOrigin (a-d) n (fun _ => v)‖ ≤
    (2*(C:ℝ))*q^N
  apply herr.trans
  apply (div_le_iff₀ (by linarith : 0<1-q)).mpr
  have hpos : 0≤(C:ℝ)*q^N := mul_nonneg C.coe_nonneg (pow_nonneg hq0 N)
  nlinarith

end DegeneratingTrees.MovingTaylor

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma multilinear_tuple_expansion {d n : ℕ}
    (p : (Fin d → ℂ) [×n]→L[ℂ] ℂ) (v : Fin d → ℂ) :
    p (fun _ => v) = ∑ j : Fin n → Fin d,
      (∏ i, v (j i)) * p (fun i => Pi.single (j i) 1) := by
  classical
  have hv : v = ∑ j : Fin d,v j • Pi.single j (1:ℂ) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [p.map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [smul_eq_mul] using p.map_smul_univ (fun i => v (j i))
    (fun i => Pi.single (j i) 1)

lemma BoundedExpansionOver.multilinear {K : Set (ℂ → ℂ)}
    (hK : LowerSectorData K) {d n : ℕ} {δ : ℝ}
    {v : ℂ → Fin d → ℂ} {p : ℂ → ((Fin d → ℂ) [×n]→L[ℂ] ℂ)}
    (hv : ∀ i,BoundedExpansionOver K (-δ) (fun z => v z i))
    (hp : ∀ j : Fin n → Fin d,(fun z => p z (fun i => Pi.single (j i) 1))∈K) :
    BoundedExpansionOver K (-δ*(n:ℝ)) (fun z => p z (fun _ => v z)) := by
  have hterm : ∀ j : Fin n → Fin d,BoundedExpansionOver K (-δ*(n:ℝ))
      (fun z => (∏ i,v z (j i))*p z (fun i => Pi.single (j i) 1)) := by
    intro j
    have hprod := BoundedExpansionOver.prod hK (Finset.univ : Finset (Fin n))
      (fun i _ => hv (j i))
    have h := hprod.mul hK (BoundedExpansionOver.lower hK (hp j))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      add_zero,mul_comm (n:ℝ)] using h
  have h := BoundedExpansionOver.sum hK Finset.univ (fun j _ => hterm j)
  simpa only [←multilinear_tuple_expansion] using h

 

lemma tuple_taylor_expBound {d : ℕ} {g : (Fin d → ℂ) → ℂ} {center : Fin d → ℂ}
    {c : (n : ℕ) → (Fin d → ℂ) → ((Fin d → ℂ) [×n]→L[ℂ] ℂ)}
    {r C : ℝ} (hr : 0<r) (hC : 0≤C)
    (hTaylor : ∀ a v : Fin d → ℂ,‖a-center‖≤r → ‖v‖≤r/2 → ∀ N : ℕ,
      ‖g (a+v)-∑ n∈Finset.range N,c n a (fun _ => v)‖≤C*(‖v‖/r)^N)
    {a v : ℂ → Fin d → ℂ} (ha : Tendsto a sectorInfinity (𝓝 center))
    {δ : ℝ} (hδ : 0<δ) (hv : ∀ i,ExpBound (-δ) (fun z => v z i)) (N : ℕ) :
    ExpBound (-δ*(N:ℝ)) (fun z => g (a z+v z)-
      ∑ n∈Finset.range N,c n (a z) (fun _ => v z)) := by
  have hvO : v =O[sectorInfinity] (fun z => Real.exp (-δ*z.re)) :=
    Asymptotics.isBigO_pi.mpr hv
  obtain ⟨K,hK,hbound⟩ := hvO.exists_pos
  have hv0 : Tendsto v sectorInfinity (𝓝 0) := tendsto_pi_nhds.mpr
    (fun i => (hv i).tendsto_zero (neg_neg_of_pos hδ))
  apply Asymptotics.IsBigO.of_bound (C*(K/r)^N)
  filter_upwards [hbound.bound,ha.eventually (Metric.ball_mem_nhds center hr),
    hv0.eventually (Metric.ball_mem_nhds 0 (by linarith : 0<r/2))] with z hz hza hzv
  have haz : ‖a z-center‖≤r := (by simpa only [Metric.mem_ball,dist_eq_norm] using hza : ‖a z-center‖<r).le
  have hvz : ‖v z‖≤r/2 := (by simpa only [Metric.mem_ball,dist_zero_right] using hzv : ‖v z‖<r/2).le
  have hnorm : ‖v z‖≤K*Real.exp (-δ*z.re) := by simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hz
  calc
    _ ≤ C*(‖v z‖/r)^N := hTaylor (a z) (v z) haz hvz N
    _ ≤ C*((K*Real.exp (-δ*z.re))/r)^N := by gcongr
    _ = (C*(K/r)^N)*‖Real.exp ((-δ*(N:ℝ))*z.re)‖ := by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      have he : Real.exp ((-δ*(N:ℝ))*z.re) = (Real.exp (-δ*z.re))^N := by
        rw [←Real.exp_nat_mul]
        congr 1
        ring
      rw [he]
      rw [mul_div_right_comm,mul_pow]
      ring

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

 

theorem ClockGerm.analytic_comp_tuple_finite {xs : List (ℝ → ℝ)}
    (hvalid : ValidClocks xs) {d : ℕ} {f : Fin d → ℝ → ℂ}
    (hf : ∀ i,ClockGerm xs (f i)) {center : Fin d → ℂ}
    (hlim : ∀ i,Tendsto (f i) atTop (𝓝 (center i)))
    {g : (Fin d → ℂ) → ℂ} (hg : AnalyticAt ℂ g center) :
    ClockGerm xs (fun t => g (fun i => f i t)) := by
  classical
  induction xs generalizing d f center g with
  | nil => exact Puiseux.analytic_comp_tuple_finite hf hlim hg
  | cons X xs ih =>
    obtain ⟨K,hK⟩ := hvalid.sectorData
    choose F hF he using fun i => hK.expansion_iff.mp (hf i)
    have hXt := hvalid.2.2.1
    have hXc := (hvalid.2.1.real_eventually_analytic hvalid.1).mono
      (fun _ h => h.continuousAt)
    have hreal : ∀ i,Tendsto (fun t : ℝ => F i (t:ℂ)) atTop (𝓝 (center i)) :=
      fun i => tendsto_of_comp_clock hXt hXc ((hlim i).congr' (he i))
    choose a v δ hδ ham ha hv hdec hva heq using
      fun i => hK.finite_decomposition hvalid (hF i) (hreal i)
    obtain ⟨ε,hε,hεδ⟩ := finite_common_positive hδ
    have hvs : ∀ i,BoundedExpansionOver K (-ε) (v i) :=
      fun i => (hv i).mono (neg_le_neg (hεδ i))
    have hvb : ∀ i,ExpBound (-(ε/2)) (v i) := fun i =>
      (hdec i).mono (by linarith [hεδ i])
    let A : ℂ → Fin d → ℂ := fun z i => a i z
    let V : ℂ → Fin d → ℂ := fun z i => v i z
    have hAt : Tendsto A sectorInfinity (𝓝 center) := tendsto_pi_nhds.mpr ha
    have hVt : Tendsto V sectorInfinity (𝓝 0) := tendsto_pi_nhds.mpr
      (fun i => (hvb i).tendsto_zero (by linarith : -(ε/2)<0))
    have hAa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ A z := by
      filter_upwards [eventually_all.mpr (fun i => hK.lower.analytic (ham i))] with z hz
      exact analyticAt_pi_iff.mpr hz
    have hVa : ∀ᶠ z in sectorInfinity,AnalyticAt ℂ V z := by
      filter_upwards [eventually_all.mpr hva] with z hz
      exact analyticAt_pi_iff.mpr hz
    have hAVt : Tendsto (fun z => A z+V z) sectorInfinity (𝓝 center) := by
      simpa only [add_zero] using hAt.add hVt
    obtain ⟨c,hc,r,C,hr,hC,hTaylor⟩ := MovingTaylor.analytic_uniform_moving_taylor hg
    let q : (n : ℕ) → (Fin n → Fin d) → (Fin d → ℂ) → ℂ :=
      fun n j x => c n x (fun i => Pi.single (j i) 1)
    have hq : ∀ n j,AnalyticAt ℂ (q n j) center := by
      intro n j
      exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => Fin d → ℂ) ℂ
        (fun i => Pi.single (j i) 1)).analyticAt _).comp (hc n)
    have hqm : ∀ n j,(fun z => q n j (A z))∈K := by
      intro n j
      apply (hK.membership _).mpr
      constructor
      · exact ih hvalid.1 (fun i => ((hK.membership _).mp (ham i)).1)
          (fun i => (ha i).comp (tendsto_real_sectorInfinity.comp hXt)) (hq n j)
      · filter_upwards [hAa,hAt.eventually (hq n j).eventually_analyticAt] with z haz hqz
        exact hqz.comp (f := A) haz
    let term : ℕ → ℂ → ℂ := fun n z => c n (A z) (fun _ => V z)
    have hterm : ∀ n : ℕ,BoundedExpansionOver K (-ε*(n:ℝ)) (term n) := by
      intro n
      exact BoundedExpansionOver.multilinear hK.lower hvs (hqm n)
    have hcomp : ExpansionOver K (fun z => g (A z+V z)) := by
      apply BoundedExpansionOver.negative_series hK.lower hε hterm
      · filter_upwards [hAa,hVa,hAVt.eventually hg.eventually_analyticAt] with z haz hvz hgz
        exact hgz.comp (f := fun z => A z+V z) (haz.add hvz)
      · intro B
        obtain ⟨N,hN⟩ := exists_nat_gt (-2*B/ε)
        filter_upwards [eventually_ge_atTop N] with M hM
        refine ⟨-(ε/2)*(M:ℝ),?_,?_⟩
        · have hh := (div_lt_iff₀ hε).mp hN
          have hNM : (N:ℝ)≤M := Nat.cast_le.mpr hM
          nlinarith
        · exact tuple_taylor_expBound hr hC hTaylor hAt (by linarith : 0<ε/2) hvb M
    apply hK.expansion_iff.mpr
    refine ⟨fun z => g (A z+V z),hcomp,?_⟩
    filter_upwards [eventually_all.mpr he] with t ht
    apply congrArg g
    ext i
    exact (ht i).trans (heq i (X t:ℂ))

end DegeneratingTrees.Clock
end

end OAI
