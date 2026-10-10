import OAI.MeasureTheory.Falconer.Estimates.Availability
import OAI.MeasureTheory.Falconer.Angular.ProjectedDirections
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-!
# Transport of cap bounds from auxiliary projections

The fixed factor in the cap radius can be absorbed in an arbitrarily small
power of the resolution. The center of an original cap need not be in the
domain where normalized projection is Lipschitz; we choose an actual
source direction in a nonempty cap, and double its radius before projecting.
This is the lifting step of `prep:integer-caps`.
-/

namespace Falconer
open Set MeasureTheory Filter NormedSpace
open scoped ENNReal Topology

private theorem radial_ne_diagonal {d k : ℕ} (P : Space d →L[ℝ] Space k)
    {x y : Space d} {c : ℝ} (hc : 0 < c) (h : c ≤ ‖P (radialDirection x y)‖) :
    y ≠ x := by
  intro heq
  subst y
  simp [radialDirection] at h
  linarith

private theorem projected_radial_identity {d k : ℕ} (P : Space d →L[ℝ] Space k)
    {x y : Space d} {c : ℝ} (hc : 0 < c) (h : c ≤ ‖P (radialDirection x y)‖) :
    NormedSpace.normalize (P (radialDirection x y)) = radialDirection (P x) (P y) := by
  simpa only [radialDirection, NormedSpace.normalize] using
    normalize_map_radial P (radial_ne_diagonal P hc h)

private theorem projected_radial_norm {d k : ℕ} (P : Space d →L[ℝ] Space k)
    {x y : Space d} {c : ℝ} (hc : 0 < c) (h : c ≤ ‖P (radialDirection x y)‖) :
    ‖radialDirection (P x) (P y)‖ = 1 := by
  rw [← projected_radial_identity P hc h]
  exact norm_normalize (norm_pos_iff.mp (hc.trans_le h))

/-- Every actual direction in an original radius-`u` cap maps into a radius
`max 1 (4/c) * u` cap about any chosen actual direction in the first cap. -/
theorem projected_radial_cap {d k : ℕ} (P : Space d →L[ℝ] Space k)
    {x y y₀ w : Space d} {c u : ℝ} (hc : 0 < c) (hP : ‖P‖ ≤ 1)
    (hy : c ≤ ‖P (radialDirection x y)‖)
    (hy₀ : c ≤ ‖P (radialDirection x y₀)‖)
    (hcap : dist (radialDirection x y) w < u)
    (hcap₀ : dist (radialDirection x y₀) w < u) :
    dist (radialDirection (P x) (P y)) (radialDirection (P x) (P y₀)) <
      max 1 (4 / c) * u := by
  have hu : 0 < u := dist_nonneg.trans_lt hcap
  have hL : 0 < 2 / c := div_pos (by norm_num) hc
  have hdist : dist (radialDirection x y) (radialDirection x y₀) < 2 * u := by
    have ht := dist_triangle (radialDirection x y) w (radialDirection x y₀)
    rw [dist_comm w (radialDirection x y₀)] at ht
    linarith
  calc
    dist (radialDirection (P x) (P y)) (radialDirection (P x) (P y₀)) =
        dist (NormedSpace.normalize (P (radialDirection x y))) (NormedSpace.normalize (P (radialDirection x y₀))) := by
      rw [projected_radial_identity P hc hy, projected_radial_identity P hc hy₀]
    _ ≤ (2 / c) * dist (radialDirection x y) (radialDirection x y₀) :=
      normalized_projection_dist_le P hc hP hy hy₀
    _ < (2 / c) * (2 * u) := mul_lt_mul_of_pos_left hdist hL
    _ = (4 / c) * u := by ring
    _ ≤ max 1 (4 / c) * u := mul_le_mul_of_nonneg_right (le_max_right _ _) hu.le

/-- A fixed radius enlargement is absorbed into the permitted scale loss. -/
theorem eventually_radius_factor_absorbed {K q a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, K ^ q ≤ ((2 : ℝ) ^ N) ^ a := by
  have ht : Tendsto (fun N : ℕ => ((2 : ℝ) ^ N) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  exact ht.eventually (eventually_ge_atTop (K ^ q))

private theorem enlarged_cap_scalar {R K u e a q : ℝ}
    (hR : 1 ≤ R) (hK : 0 ≤ K) (hu : 0 ≤ u) (hconstant : K ^ q ≤ R ^ a) :
    R ^ e * (K * u) ^ q ≤ R ^ (e + a) * u ^ q := by
  rw [Real.mul_rpow hK hu, Real.rpow_add (zero_lt_one.trans_le hR)]
  calc
    R ^ e * (K ^ q * u ^ q) = (R ^ e * u ^ q) * K ^ q := by ring
    _ ≤ (R ^ e * u ^ q) * R ^ a := mul_le_mul_of_nonneg_left hconstant
      (mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans_le hR).le e) (Real.rpow_nonneg hu q))
    _ = R ^ e * R ^ a * u ^ q := by ring

/-- A cap estimate for the projected source law bounds a fiber of the
original law. Source labels remain distinct even when their images coincide. -/
theorem projected_fiber_cap_bound {d k : ℕ} (P : Space d →L[ℝ] Space k)
    (ν : ProbabilityMeasure (Space d)) (H : Set (Space d)) (J : Set (Space k))
    (x : Space d) {R c e a q : ℝ}
    (hR : 1 ≤ R) (hc : 0 < c) (hP : ‖P‖ ≤ 1) (he : 0 ≤ e) (hq : 0 ≤ q)
    (hconstant : (max 1 (4 / c)) ^ q ≤ R ^ a)
    (himage : ∀ y ∈ H, P y ∈ J)
    (hlower : ∀ y ∈ H, c ≤ ‖P (radialDirection x y)‖)
    (hcap : ∀ w : Space k, ‖w‖ = 1 → ∀ u : ℝ, R⁻¹ ≤ u → u ≤ 1 →
      ((ν.map P : ProbabilityMeasure (Space k)) : Measure (Space k))
        {y | y ∈ J ∧ dist (radialDirection (P x) y) w < u} ≤
          ENNReal.ofReal (R ^ e * u ^ q)) :
    ∀ w : Space d, ‖w‖ = 1 → ∀ u : ℝ, R⁻¹ ≤ u → u ≤ 1 →
      (ν : Measure (Space d)) {y | y ∈ H ∧ dist (radialDirection x y) w < u} ≤
        ENNReal.ofReal (R ^ (e + a) * u ^ q) := by
  intro w _ u hu _
  have hupos : 0 < u := (inv_pos.mpr (zero_lt_one.trans_le hR)).trans_le hu
  let K : ℝ := max 1 (4 / c)
  have hK : 1 ≤ K := le_max_left _ _
  have hscalar := enlarged_cap_scalar (e := e) hR (zero_le_one.trans hK) hupos.le hconstant
  by_cases hsmall : K * u ≤ 1
  · by_cases hex : Set.Nonempty {y | y ∈ H ∧ dist (radialDirection x y) w < u}
    · obtain ⟨y₀, hy₀, hcap₀⟩ := hex
      have hset : {y | y ∈ H ∧ dist (radialDirection x y) w < u} ⊆
          P ⁻¹' {y | y ∈ J ∧ dist (radialDirection (P x) y)
            (radialDirection (P x) (P y₀)) < K * u} := by
        rintro y ⟨hy, hycap⟩
        exact ⟨himage y hy, projected_radial_cap P hc hP (hlower y hy)
          (hlower y₀ hy₀) hycap hcap₀⟩
      have hpre := (measure_mono (μ := (ν : Measure (Space d))) hset).trans
        (Measure.le_map_apply P.continuous.measurable.aemeasurable _)
      have hrad : R⁻¹ ≤ K * u := hu.trans (le_mul_of_one_le_left hupos.le hK)
      exact hpre.trans ((hcap _ (projected_radial_norm P hc (hlower y₀ hy₀))
        _ hrad hsmall).trans (ENNReal.ofReal_le_ofReal hscalar))
    · simp only [Set.not_nonempty_iff_eq_empty.mp hex, measure_empty]
      exact bot_le
  · have hmass : (ν : Measure (Space d)) {y | y ∈ H ∧ dist (radialDirection x y) w < u} ≤ 1 := by
      exact (measure_mono (subset_univ _)).trans_eq (measure_univ : (ν : Measure (Space d)) univ = 1)
    have hpow : 1 ≤ (K * u) ^ q := Real.one_le_rpow (le_of_not_ge hsmall) hq
    have hepow : 1 ≤ R ^ e := Real.one_le_rpow hR he
    have hone : 1 ≤ R ^ (e + a) * u ^ q := by
      have : 1 ≤ R ^ e * (K * u) ^ q := by nlinarith
      exact this.trans hscalar
    exact hmass.trans (by simpa using (ENNReal.ofReal_le_ofReal hone))

private theorem map_mem_support {d k : ℕ} (P : Space d →L[ℝ] Space k)
    (μ : ProbabilityMeasure (Space d)) {x : Space d}
    (hx : x ∈ (μ : Measure (Space d)).support) :
    P x ∈ ((μ.map P : ProbabilityMeasure (Space k)) : Measure (Space k)).support := by
  apply (Measure.mem_support_iff_forall _).mpr
  intro U hU
  have hpre : P ⁻¹' U ∈ 𝓝 x := P.continuous.continuousAt.preimage_mem_nhds hU
  exact ((Measure.mem_support_iff_forall _).mp hx _ hpre).trans_le
    (Measure.le_map_apply P.continuous.measurable.aemeasurable U)

/-- Pull back both cap estimates through a fixed auxiliary projection. -/
theorem RadialCapBound.pullback {d k N : ℕ} (P : Space d →L[ℝ] Space k)
    (μ ν : ProbabilityMeasure (Space d))
    {G : Set (Space d × Space d)} {G' : Set (Space k × Space k)} {c e a q : ℝ}
    (hc : 0 < c) (hP : ‖P‖ ≤ 1) (he : 0 ≤ e) (hq : 0 ≤ q)
    (hconstant : (max 1 (4 / c)) ^ q ≤ ((2 : ℝ) ^ N) ^ a)
    (hG : G ⊆ Prod.map P P ⁻¹' G')
    (hlower : ∀ z ∈ G, c ≤ ‖P (radialDirection z.1 z.2)‖ ∧
      c ≤ ‖P (radialDirection z.2 z.1)‖)
    (hcap : RadialCapBound (μ.map P) (ν.map P) G' N e q) :
    RadialCapBound μ ν G N (e + a) q := by
  have hR : 1 ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
  constructor
  · intro x hx
    exact projected_fiber_cap_bound P ν {y | (x, y) ∈ G} {y | (P x, y) ∈ G'} x
      hR hc hP he hq hconstant
      (fun y hy => hG hy) (fun y hy => (hlower (x, y) hy).1)
      (hcap.1 (P x) (map_mem_support P μ hx))
  · intro y hy
    exact projected_fiber_cap_bound P μ {x | (x, y) ∈ G} {x | (x, P y) ∈ G'} y
      hR hc hP he hq hconstant
      (fun x hx => hG hx) (fun x hx => (hlower (x, y) hx).2)
      (hcap.2 (P y) (map_mem_support P ν hy))

/-- Auxiliary projected cap estimates lift to the original pair law.
The deletion is the preimage of the projected bad set intersected with the
original pair filter; its mass is bounded by the projected product mass. -/
theorem CapAvailable.pullback {d k : ℕ} (P : Space d →L[ℝ] Space k)
    (μ ν : ProbabilityMeasure (Space d))
    {Γ : ℕ → Set (Space d × Space d)} {Γ' : ℕ → Set (Space k × Space k)} {c q : ℝ}
    (hc : 0 < c) (hP : ‖P‖ ≤ 1) (hq : 0 ≤ q)
    (hΓ : ∀ N, MeasurableSet (Γ N))
    (hΓsub : ∀ N, Γ N ⊆ Prod.map P P ⁻¹' Γ' N)
    (hlower : ∀ N, ∀ z ∈ Γ N, c ≤ ‖P (radialDirection z.1 z.2)‖ ∧
      c ≤ ‖P (radialDirection z.2 z.1)‖)
    (hcap : CapAvailable (μ.map P) (ν.map P) Γ' q) :
    CapAvailable μ ν Γ q := by
  intro e he
  obtain ⟨c₀, C, hc₀, hC, N₀, hN₀⟩ := hcap (e / 2) (by linarith)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (eventually_radius_factor_absorbed (K := max 1 (4 / c)) (q := q)
      (by linarith : (0 : ℝ) < e / 2))
  refine ⟨c₀, C, hc₀, hC, max N₀ N₁, ?_⟩
  intro N hN
  obtain ⟨B', hB', hB'sub, hmass, hgood⟩ := hN₀ N ((le_max_left _ _).trans hN)
  let B := Γ N ∩ Prod.map P P ⁻¹' B'
  have hPmeas : Measurable (P : Space d → Space k) := P.continuous.measurable
  have hB : MeasurableSet B := (hΓ N).inter (hB'.preimage (hPmeas.prodMap hPmeas))
  have hpre := Measure.le_map_apply
    (μ := (μ : Measure (Space d)).prod (ν : Measure (Space d)))
    (hPmeas.prodMap hPmeas).aemeasurable B'
  rw [← Measure.map_prod_map _ _ hPmeas hPmeas] at hpre
  have hmassB : ((μ : Measure (Space d)).prod (ν : Measure (Space d))) B ≤
      ENNReal.ofReal (C * ((2 : ℝ) ^ N) ^ (-c₀)) :=
    (measure_mono inter_subset_right).trans (hpre.trans hmass)
  refine ⟨B, hB, inter_subset_left, hmassB, ?_⟩
  have hgoodsub : Γ N \ B ⊆ Prod.map P P ⁻¹' (Γ' N \ B') := by
    intro z hz
    exact ⟨hΓsub N hz.1, fun hb => hz.2 ⟨hz.1, hb⟩⟩
  have hbound := hgood.pullback P μ ν hc hP (by linarith) hq
    (hN₁ N ((le_max_right _ _).trans hN)) hgoodsub
    (fun z hz => hlower N z hz.1)
  convert hbound using 1
  ring

end Falconer

end OAI
