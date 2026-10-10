import OAI.Analysis.Brenier.ConvexOptimality

namespace OAI

noncomputable section

open Set Filter
open scoped Topology NNReal BoundedContinuousFunction

namespace Problem358

/-- Arzelà--Ascoli in the form needed for a sequence of transport potentials. -/
theorem exists_uniformly_convergent_subseq_of_lipschitz
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    (u : ℕ → X → ℝ) (L : ℝ≥0) (M : ℝ)
    (hLip : ∀ n, LipschitzWith L (u n))
    (hbound : ∀ n x, |u n x| ≤ M) :
    ∃ (v : X → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      TendstoUniformly (fun n => u (φ n)) v atTop ∧ LipschitzWith L v := by
  let F : ℕ → X →ᵇ ℝ := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨u n, (hLip n).continuous⟩
  have hEqui : Equicontinuous (fun g : Set.range F => (g.1 : X → ℝ)) := by
    apply (LipschitzWith.uniformEquicontinuous _ L ?_).equicontinuous
    rintro ⟨g, n, rfl⟩
    exact hLip n
  have hcompact : IsCompact (closure (Set.range F)) := by
    apply BoundedContinuousFunction.arzela_ascoli (Set.Icc (-M) M) isCompact_Icc
    · intro g x hg
      obtain ⟨n, rfl⟩ := hg
      exact abs_le.mp (hbound n x)
    · exact hEqui
  obtain ⟨v, hv, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  have hunif : TendstoUniformly (fun n => u (φ n)) (fun x => v x) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  refine ⟨v, φ, hφ, hunif, ?_⟩
  apply (isClosed_setOfPred_lipschitzWith L).mem_of_tendsto
    (tendsto_pi_nhds.mpr hunif.tendsto_at)
  exact Filter.Eventually.of_forall (fun n => hLip (φ n))

/-- Convexity on a fixed set is preserved by pointwise limits on that set. -/
theorem convexOn_of_pointwise_limit
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    {K : Set V} {u : ℕ → V → ℝ} {v : V → ℝ}
    (hconv : ∀ n, ConvexOn ℝ K (u n))
    (hlim : ∀ x ∈ K, Tendsto (fun n => u n x) atTop (𝓝 (v x))) :
    ConvexOn ℝ K v := by
  refine ⟨(hconv 0).1, ?_⟩
  intro x hx y hy a b ha hb hab
  apply le_of_tendsto_of_tendsto
    (hlim (a • x + b • y) ((hconv 0).1 hx hy ha hb hab))
    (((hlim x hx).const_mul a).add ((hlim y hy).const_mul b))
  exact Filter.Eventually.of_forall (fun n => (hconv n).2 hx hy ha hb hab)

/-- Normalized convex potentials with a uniform Lipschitz constant on a compact convex
body admit a uniformly convergent subsequence, and the limit has the same properties. -/
theorem exists_normalized_convex_potential_subseq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set V} (hK : IsCompact K)
    (x₀ : V) (hx₀ : x₀ ∈ K) (u : ℕ → V → ℝ) (L : ℝ≥0)
    (hLip : ∀ n, LipschitzOnWith L (u n) K)
    (hconv : ∀ n, ConvexOn ℝ K (u n))
    (hnormal : ∀ n, u n x₀ = 0) :
    ∃ (v : V → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      TendstoUniformlyOn (fun n => u (φ n)) v atTop K ∧
      LipschitzOnWith L v K ∧ ConvexOn ℝ K v ∧ v x₀ = 0 := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hbound : ∀ n (x : K), |u n x| ≤ (L : ℝ) * (R + ‖x₀‖) := by
    intro n x
    calc
      |u n x| = dist (u n x) (u n x₀) := by rw [hnormal n, dist_zero_right, Real.norm_eq_abs]
      _ ≤ (L : ℝ) * dist (x : V) x₀ := (hLip n).dist_le_mul x x.property x₀ hx₀
      _ ≤ (L : ℝ) * (R + ‖x₀‖) := by
        apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
        rw [dist_eq_norm]
        exact (norm_sub_le _ _).trans (add_le_add (hR x x.property) le_rfl)
  obtain ⟨w, φ, hφ, hwlim, hwLip⟩ := exists_uniformly_convergent_subseq_of_lipschitz
    (fun n (x : K) => u n x) L ((L : ℝ) * (R + ‖x₀‖))
    (fun n => (hLip n).to_restrict) hbound
  let v : V → ℝ := fun x => if hx : x ∈ K then w ⟨x, hx⟩ else 0
  have hv : ∀ x : K, v x = w x := by intro x; simp [v, x.property]
  have hvlim : TendstoUniformlyOn (fun n => u (φ n)) v atTop K := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa only [Function.comp_def, hv] using hwlim
  have hvLip : LipschitzOnWith L v K := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [← hv, Subtype.dist_eq] using hwLip.dist_le_mul ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨v, φ, hφ, hvlim, hvLip, ?_, ?_⟩
  · exact convexOn_of_pointwise_limit (fun n => hconv (φ n))
      (fun x hx => hvlim.tendsto_at hx)
  · have hzero : Tendsto (fun n => u (φ n) x₀) atTop (𝓝 (0 : ℝ)) := by
      simpa only [hnormal] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique (hvlim.tendsto_at hx₀) hzero

/-- Supporting inequalities survive simultaneous convergence of potentials and slopes.
The conclusion holds for every comparison point in `K`, without a countability restriction. -/
theorem supporting_inequality_of_pointwise_limit
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {K : Set V} {u : ℕ → V → ℝ} {v : V → ℝ} {p : ℕ → V} {q x : V}
    (hx : x ∈ K)
    (hu : ∀ z ∈ K, Tendsto (fun n => u n z) atTop (𝓝 (v z)))
    (hp : Tendsto p atTop (𝓝 q))
    (hsupport : ∀ n z, z ∈ K → u n x + inner ℝ (p n) (z - x) ≤ u n z) :
    ∀ z ∈ K, v x + inner ℝ q (z - x) ≤ v z := by
  intro z hz
  exact le_of_tendsto_of_tendsto
    ((hu x hx).add (hp.inner tendsto_const_nhds)) (hu z hz)
    (Filter.Eventually.of_forall (fun n => hsupport n z hz))

/-- Almost-everywhere version of the limiting supporting inequality. Countably many
full-measure support conditions are intersected before taking the limit, so the
comparison point remains universally quantified in the conclusion. -/
theorem ae_supporting_inequality_of_pointwise_limit
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    (μ : MeasureTheory.Measure V)
    {K : Set V} {u : ℕ → V → ℝ} {v : V → ℝ}
    {T : ℕ → V → V} {S : V → V}
    (hK : ∀ᵐ x ∂μ, x ∈ K)
    (hu : ∀ z ∈ K, Tendsto (fun n => u n z) atTop (𝓝 (v z)))
    (hT : ∀ᵐ x ∂μ, Tendsto (fun n => T n x) atTop (𝓝 (S x)))
    (hsupport : ∀ n, ∀ᵐ x ∂μ,
      ∀ z ∈ K, u n x + inner ℝ (T n x) (z - x) ≤ u n z) :
    ∀ᵐ x ∂μ, ∀ z ∈ K, v x + inner ℝ (S x) (z - x) ≤ v z := by
  have hall : ∀ᵐ x ∂μ, ∀ n, ∀ z ∈ K,
      u n x + inner ℝ (T n x) (z - x) ≤ u n z :=
    MeasureTheory.ae_all_iff.mpr hsupport
  filter_upwards [hK, hT, hall] with x hx hTx hsx
  exact supporting_inequality_of_pointwise_limit hx hu hTx hsx

end Problem358

end

section

open Filter MeasureTheory
open scoped Topology

namespace Problem358

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {u : V → ℝ} {x p : V} {u' : V →L[ℝ] ℝ} {K : Set V}

/-- A linear functional supporting a differentiable function locally is its derivative.
Convexity is not needed once the supporting inequality has been established. -/
theorem hasFDerivAt_eq_of_eventually_support
    (hu : HasFDerivAt u u' x)
    (hp : ∀ᶠ z in 𝓝 x, u x + inner ℝ p (z - x) ≤ u z) :
    u' = innerSL ℝ p := by
  have hmin : IsLocalMin (fun z => u z - inner ℝ p z) x := by
    filter_upwards [hp] with z hz
    simp only [inner_sub_right] at hz
    linarith
  have hz := hmin.hasFDerivAt_eq_zero
    (hu.sub (innerSL ℝ p).hasFDerivAt)
  exact sub_eq_zero.mp hz

/-- Supporting maps coincide almost everywhere if the potential is differentiable
almost everywhere and the source gives full mass to the interior. -/
theorem supporting_maps_ae_eq [MeasurableSpace V] (ρ : Measure V)
    {T S : V → V}
    (hu : ∀ᵐ x ∂ρ, DifferentiableAt ℝ u x)
    (hK : ∀ᵐ x ∂ρ, x ∈ interior K)
    (hT : ∀ᵐ x ∂ρ, ∀ z ∈ K, u x + inner ℝ (T x) (z - x) ≤ u z)
    (hS : ∀ᵐ x ∂ρ, ∀ z ∈ K, u x + inner ℝ (S x) (z - x) ≤ u z) :
    T =ᵐ[ρ] S := by
  filter_upwards [hu, hK, hT, hS] with x hux hx hTx hSx
  exact supporting_slope_unique hux hx hTx hSx

/-- Supporting inequalities are closed under pointwise convergence of potentials
and convergence of the supporting slope. -/
theorem supporting_inequality_of_tendsto
    {ι : Type*} {l : Filter ι} [NeBot l]
    {uₙ : ι → V → ℝ} {pₙ : ι → V}
    (hx : x ∈ K)
    (hu : ∀ z ∈ K, Tendsto (fun n => uₙ n z) l (𝓝 (u z)))
    (hp : Tendsto pₙ l (𝓝 p))
    (hs : ∀ᶠ n in l, ∀ z ∈ K,
      uₙ n x + inner ℝ (pₙ n) (z - x) ≤ uₙ n z) :
    ∀ z ∈ K, u x + inner ℝ p (z - x) ≤ u z := by
  intro z hz
  exact le_of_tendsto_of_tendsto
    ((hu x hx).add (hp.inner tendsto_const_nhds))
    (hu z hz) (hs.mono fun n hn => hn z hz)

/-- Countably many almost-everywhere supporting inequalities pass to an
almost-everywhere converging sequence of slopes.  The potential convergence
is assumed on the whole body, so the resulting inequality is simultaneous
for every comparison point, not merely almost every comparison point. -/
theorem supporting_maps_of_ae_tendsto [MeasurableSpace V]
    (ρ : Measure V) {uₙ : ℕ → V → ℝ} {Tₙ : ℕ → V → V} {T : V → V}
    (hK : ∀ᵐ x ∂ρ, x ∈ K)
    (hu : ∀ z ∈ K, Tendsto (fun n => uₙ n z) atTop (𝓝 (u z)))
    (hT : ∀ᵐ x ∂ρ, Tendsto (fun n => Tₙ n x) atTop (𝓝 (T x)))
    (hs : ∀ n, ∀ᵐ x ∂ρ, ∀ z ∈ K,
      uₙ n x + inner ℝ (Tₙ n x) (z - x) ≤ uₙ n z) :
    ∀ᵐ x ∂ρ, ∀ z ∈ K, u x + inner ℝ (T x) (z - x) ≤ u z := by
  filter_upwards [hK, hT, ae_all_iff.mpr hs] with x hx hTx hsx
  exact supporting_inequality_of_tendsto hx hu hTx
    (Filter.Eventually.of_forall hsx)

/-- Compactly constrained supporting slopes converge wherever the limiting
potential is differentiable.  This is valid for arbitrary filters and requires
only pointwise convergence of potentials, not convergence of their derivatives. -/
theorem supporting_slopes_tendsto_of_isCompact
    {ι : Type*} {l : Filter ι} {uₙ : ι → V → ℝ} {pₙ : ι → V} {Y : Set V}
    (hY : IsCompact Y) (hx : x ∈ interior K)
    (hderiv : HasFDerivAt u (innerSL ℝ p) x)
    (hu : ∀ z ∈ K, Tendsto (fun n => uₙ n z) l (𝓝 (u z)))
    (hmem : ∀ᶠ n in l, pₙ n ∈ Y)
    (hs : ∀ᶠ n in l, ∀ z ∈ K,
      uₙ n x + inner ℝ (pₙ n) (z - x) ≤ uₙ n z) :
    Tendsto pₙ l (𝓝 p) := by
  apply hY.tendsto_nhds_of_unique_mapClusterPt hmem
  intro q _ hq
  obtain ⟨U, hUl, hUq⟩ := mapClusterPt_iff_ultrafilter.mp hq
  have hsupport : ∀ z ∈ K, u x + inner ℝ q (z - x) ≤ u z :=
    supporting_inequality_of_tendsto (interior_subset hx)
      (fun z hz => (hu z hz).mono_left hUl) hUq (hUl hs)
  exact ((innerSL_inj (𝕜 := ℝ)).mp
    (hasFDerivAt_eq_innerSL_of_supporting hderiv hx hsupport)).symm

/-- A differentiable pointwise limit of potentials admits a supporting slope
in the same compact target set, and the full slope family converges to it. -/
theorem exists_supporting_slope_limit_of_isCompact
    {ι : Type*} {l : Filter ι} [NeBot l]
    {uₙ : ι → V → ℝ} {pₙ : ι → V} {Y : Set V}
    (hY : IsCompact Y) (hx : x ∈ interior K)
    (hderiv : DifferentiableAt ℝ u x)
    (hu : ∀ z ∈ K, Tendsto (fun n => uₙ n z) l (𝓝 (u z)))
    (hmem : ∀ᶠ n in l, pₙ n ∈ Y)
    (hs : ∀ᶠ n in l, ∀ z ∈ K,
      uₙ n x + inner ℝ (pₙ n) (z - x) ≤ uₙ n z) :
    ∃ p ∈ Y, Tendsto pₙ l (𝓝 p) ∧
      ∀ z ∈ K, u x + inner ℝ p (z - x) ≤ u z := by
  obtain ⟨p, hpY, hp⟩ := hY.exists_mapClusterPt_of_frequently hmem.frequently
  obtain ⟨U, hUl, hUp⟩ := mapClusterPt_iff_ultrafilter.mp hp
  have hsupport : ∀ z ∈ K, u x + inner ℝ p (z - x) ≤ u z :=
    supporting_inequality_of_tendsto (interior_subset hx)
      (fun z hz => (hu z hz).mono_left hUl) hUp (hUl hs)
  have hdiff : HasFDerivAt u (innerSL ℝ p) x := by
    rw [← hasFDerivAt_eq_innerSL_of_supporting hderiv.hasFDerivAt hx hsupport]
    exact hderiv.hasFDerivAt
  exact ⟨p, hpY, supporting_slopes_tendsto_of_isCompact hY hx hdiff hu hmem hs,
    hsupport⟩

/-- The compact-slope limit construction holds almost everywhere simultaneously
for an entire sequence of supporting maps. -/
theorem ae_exists_supporting_map_limit [MeasurableSpace V]
    (ρ : Measure V) {uₙ : ℕ → V → ℝ} {Tₙ : ℕ → V → V} {Y : Set V}
    (hY : IsCompact Y)
    (hK : ∀ᵐ x ∂ρ, x ∈ interior K)
    (hderiv : ∀ᵐ x ∂ρ, DifferentiableAt ℝ u x)
    (hu : ∀ z ∈ K, Tendsto (fun n => uₙ n z) atTop (𝓝 (u z)))
    (hmem : ∀ n, ∀ᵐ x ∂ρ, Tₙ n x ∈ Y)
    (hs : ∀ n, ∀ᵐ x ∂ρ, ∀ z ∈ K,
      uₙ n x + inner ℝ (Tₙ n x) (z - x) ≤ uₙ n z) :
    ∀ᵐ x ∂ρ, ∃ p ∈ Y, Tendsto (fun n => Tₙ n x) atTop (𝓝 p) ∧
      ∀ z ∈ K, u x + inner ℝ p (z - x) ≤ u z := by
  filter_upwards [hK, hderiv, ae_all_iff.mpr hmem, ae_all_iff.mpr hs]
    with x hx hdx hmx hsx
  exact exists_supporting_slope_limit_of_isCompact hY hx hdx hu
    (Filter.Eventually.of_forall hmx) (Filter.Eventually.of_forall hsx)

end Problem358

end

noncomputable section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Problem358

/-- Compactly constrained supporting maps have a measurable limiting representative
when their potentials converge to an almost-everywhere differentiable potential. -/
theorem exists_measurable_supporting_map_limit
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (ρ : Measure V) {K Y : Set V} {uₙ : ℕ → V → ℝ} {u : V → ℝ}
    {Tₙ : ℕ → V → V}
    (hY : IsCompact Y)
    (hK : ∀ᵐ x ∂ρ, x ∈ interior K)
    (hderiv : ∀ᵐ x ∂ρ, DifferentiableAt ℝ u x)
    (hu : ∀ z ∈ K, Tendsto (fun n => uₙ n z) atTop (𝓝 (u z)))
    (hmeas : ∀ n, Measurable (Tₙ n))
    (hmem : ∀ n, ∀ᵐ x ∂ρ, Tₙ n x ∈ Y)
    (hs : ∀ n, ∀ᵐ x ∂ρ, ∀ z ∈ K,
      uₙ n x + inner ℝ (Tₙ n x) (z - x) ≤ uₙ n z) :
    ∃ T : V → V, Measurable T ∧
      (∀ᵐ x ∂ρ, Tendsto (fun n => Tₙ n x) atTop (𝓝 (T x))) ∧
      (∀ᵐ x ∂ρ, T x ∈ Y) ∧
      (∀ᵐ x ∂ρ, ∀ z ∈ K, u x + inner ℝ (T x) (z - x) ≤ u z) := by
  have hlim := ae_exists_supporting_map_limit ρ hY hK hderiv hu hmem hs
  obtain ⟨T, hT, hTlim⟩ := measurable_limit_of_tendsto_metrizable_ae
    (fun n => (hmeas n).aemeasurable) (hlim.mono (fun x hx => by
      obtain ⟨p, hpY, hplim, hps⟩ := hx
      exact ⟨p, hplim⟩))
  refine ⟨T, hT, hTlim, ?_, ?_⟩
  · filter_upwards [hlim, hTlim] with x hx hTx
    obtain ⟨p, hpY, hplim, hps⟩ := hx
    exact tendsto_nhds_unique hTx hplim ▸ hpY
  · exact supporting_maps_of_ae_tendsto ρ (hK.mono (fun x hx => interior_subset hx))
      hu hTlim hs

/-- Joint subsequential compactness of normalized convex potentials and their
compactly constrained supporting maps on a uniform convex source. -/
theorem exists_potential_and_map_limit
    {d : ℕ} {K Y : Set (E d)}
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hY : IsCompact Y)
    (x₀ : E d) (hx₀ : x₀ ∈ K)
    (uₙ : ℕ → E d → ℝ) (Tₙ : ℕ → E d → E d) (L : ℝ≥0)
    (hLip : ∀ n, LipschitzOnWith L (uₙ n) K)
    (hconv : ∀ n, ConvexOn ℝ K (uₙ n))
    (hnormal : ∀ n, uₙ n x₀ = 0)
    (hmeas : ∀ n, Measurable (Tₙ n))
    (hmem : ∀ n, ∀ᵐ x ∂uniformMeasure K, Tₙ n x ∈ Y)
    (hs : ∀ n, ∀ᵐ x ∂uniformMeasure K, ∀ z ∈ K,
      uₙ n x + inner ℝ (Tₙ n x) (z - x) ≤ uₙ n z) :
    ∃ (u : E d → ℝ) (T : E d → E d) (φ : ℕ → ℕ),
      StrictMono φ ∧ TendstoUniformlyOn (fun n => uₙ (φ n)) u atTop K ∧
      LipschitzOnWith L u K ∧ ConvexOn ℝ K u ∧ u x₀ = 0 ∧
      Measurable T ∧
      (∀ᵐ x ∂uniformMeasure K, Tendsto (fun n => Tₙ (φ n) x) atTop (𝓝 (T x))) ∧
      (∀ᵐ x ∂uniformMeasure K, T x ∈ Y) ∧
      (∀ᵐ x ∂uniformMeasure K, ∀ z ∈ K,
        u x + inner ℝ (T x) (z - x) ≤ u z) := by
  obtain ⟨u, φ, hφ, hulim, huLip, huconv, hunormal⟩ :=
    exists_normalized_convex_potential_subseq hK x₀ hx₀ uₙ L hLip hconv hnormal
  have hudiff := ae_differentiableAt_uniformMeasure hKconv hK.measurableSet huLip
  obtain ⟨T, hTmeas, hTlim, hTmem, hTs⟩ := exists_measurable_supporting_map_limit
    (uniformMeasure K) hY (hudiff.mono (fun x hx => hx.1))
    (hudiff.mono (fun x hx => hx.2)) (fun z hz => hulim.tendsto_at hz)
    (fun n => hmeas (φ n)) (fun n => hmem (φ n)) (fun n => hs (φ n))
  exact ⟨u, T, φ, hφ, hulim, huLip, huconv, hunormal, hTmeas, hTlim, hTmem, hTs⟩

end Problem358

namespace Problem358

/-- The approximation step for Brenier-map existence. Finite supporting potentials
and quantized target laws suffice; quantitative stability is not an assumption. -/
theorem exists_uniqueOptimalMap_of_quantized_supporting_potentials
    {d : ℕ} {K Y : Set (E d)} {μ : Measure (E d)}
    [IsFiniteMeasure (uniformMeasure K)] [IsFiniteMeasure μ]
    (hK : IsCompact K) (hKconv : Convex ℝ K) (hY : IsCompact Y)
    (hμ : IsSupported μ Y) (x₀ : E d) (hx₀ : x₀ ∈ K)
    (uₙ : ℕ → E d → ℝ) (Tₙ Qₙ : ℕ → E d → E d) (L : ℝ≥0)
    (hLip : ∀ n, LipschitzOnWith L (uₙ n) K)
    (hconv : ∀ n, ConvexOn ℝ K (uₙ n))
    (hnormal : ∀ n, uₙ n x₀ = 0)
    (hTmeas : ∀ n, Measurable (Tₙ n))
    (hQmeas : ∀ n, Measurable (Qₙ n))
    (hQmem : ∀ n, ∀ᵐ y ∂μ, Qₙ n y ∈ Y)
    (hQlim : ∀ᵐ y ∂μ, Tendsto (fun n => Qₙ n y) atTop (𝓝 y))
    (hpush : ∀ n, Measure.map (Tₙ n) (uniformMeasure K) = Measure.map (Qₙ n) μ)
    (hs : ∀ n, ∀ᵐ x ∂uniformMeasure K, ∀ z ∈ K,
      uₙ n x + inner ℝ (Tₙ n x) (z - x) ≤ uₙ n z) :
    ∃ (T : E d → E d) (φ : ℕ → ℕ), StrictMono φ ∧
      IsUniqueQuadraticOptimalMap (uniformMeasure K) μ T ∧
      (∀ᵐ x ∂uniformMeasure K, T x ∈ Y) ∧
      (∀ᵐ x ∂uniformMeasure K, Tendsto (fun n => Tₙ (φ n) x) atTop (𝓝 (T x))) ∧
      Tendsto (fun n => mapL2Dist (uniformMeasure K) (Tₙ (φ n)) T) atTop (𝓝 0) := by
  have hTmem : ∀ n, ∀ᵐ x ∂uniformMeasure K, Tₙ n x ∈ Y := by
    intro n
    apply ae_of_ae_map (hTmeas n).aemeasurable
    rw [hpush n]
    exact (ae_map_iff (hQmeas n).aemeasurable hY.measurableSet).mpr (hQmem n)
  obtain ⟨u, T, φ, hφ, hulim, huLip, huconv, hunormal, hT, hTlim, hTY, hTs⟩ :=
    exists_potential_and_map_limit hK hKconv hY x₀ hx₀ uₙ Tₙ L
      hLip hconv hnormal hTmeas hTmem hs
  have hlimitlaw : Measure.map T (uniformMeasure K) = μ :=
    CompactIntegrability.map_eq_of_ae_tendsto_of_map_eq_quantizers
      (fun n => hTmeas (φ n)) hT (fun n => hQmeas (φ n)) hY
      (fun n => hTmem (φ n)) (fun n => hQmem (φ n)) hTlim
      (hQlim.mono (fun y hy => hy.comp hφ.tendsto_atTop)) (fun n => hpush (φ n))
  have hopt : IsUniqueQuadraticOptimalMap (uniformMeasure K) μ T := by
    apply isUniqueQuadraticOptimalMap_uniform_of_supporting_potential
      hK ⟨x₀, hx₀⟩ hKconv hY hμ huLip hT hlimitlaw
    filter_upwards [hTs] with x hx
    intro z hz
    simpa only [real_inner_comm (z - x) (T x)] using hx z hz
  exact ⟨T, φ, hφ, hopt, hTY, hTlim,
    CompactIntegrability.tendsto_mapL2Dist_of_ae_tendsto
      (fun n => hTmeas (φ n)) hT hY (fun n => hTmem (φ n)) hTlim⟩

end Problem358

end

end OAI
