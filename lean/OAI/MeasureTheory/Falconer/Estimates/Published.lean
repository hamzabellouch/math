import OAI.MeasureTheory.Falconer.Measures.RootSimilarityMeasures

namespace OAI

/-!
# Published radial input for the planar Falconer application

The only input isolated here is the planar specialization of Orponen,
*On the dimension and smoothness of radial projections*, Analysis & PDE
12 (2019), 1273–1294, proof of Theorem 1.13, equations (3.5)–(3.6).
The parameters used by the application are
`s = 1 + δ / 2`, `t = 1 - δ / 4`, and `p = 1 + δ / 8`.
They satisfy the strict inequalities in (3.5).  Orponen uses a distance
weighted source measure; on disjoint compact supports that weight and its
inverse are bounded, so finiteness of the moment is unchanged.

Prepared root measures follow from this radial moment estimate.
-/

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

/-- The precise finite-energy consequence of the published radial theorem used
in the planar application.  The source and pin laws may be interchanged. -/
def PublishedPlanarRadialMoment : Prop :=
  ∀ (α β : ProbabilityMeasure Plane) (δ : ℝ), 0 < δ → δ < 1 →
    IsCompact (α : Measure Plane).support →
    IsCompact (β : Measure Plane).support →
    Disjoint (α : Measure Plane).support (β : Measure Plane).support →
    rieszEnergy α (1 + δ / 2) < ∞ →
    rieszEnergy β (1 - δ / 4) < ∞ →
    (∫⁻ x, (sourceDensityNorm (1 + δ / 8)
      ((α : Measure Plane).map (sourceRadialUnit x))) ^ (1 + δ / 8) ∂β) < ∞

theorem compact_neighborhood_probability_for_published_radial (E : Set Plane) (hE : IsCompact E)
    (ζ : ProbabilityMeasure Plane) (hζ : (ζ : Measure Plane) Eᶜ = 0)
    {u C : ℝ} (hC : 0 < C) (hball : BallBound ζ u C)
    (x : Plane) (hx : x ∈ (ζ : Measure Plane).support) {r : ℝ} (hr : 0 < r) :
    ∃ μ : ProbabilityMeasure Plane, (μ : Measure Plane) (E ∩ closedBall x r)ᶜ = 0 ∧
      ∃ D : ℝ, 0 < D ∧ BallBound μ u D := by
  have hpos : 0 < (ζ : Measure Plane) (E ∩ closedBall x r) := by
    have hp := ((ζ : Measure Plane).mem_support_iff_forall x).mp hx (ball x r) (ball_mem_nhds x hr)
    have hsub : ball x r ⊆ (E ∩ closedBall x r) ∪ Eᶜ := by
      intro z hz
      by_cases he : z ∈ E
      · exact Or.inl ⟨he,ball_subset_closedBall hz⟩
      · exact Or.inr he
    have hb := (measure_mono hsub).trans (measure_union_le _ _ (μ := (ζ : Measure Plane)))
    rw [hζ,add_zero] at hb
    exact hp.trans_le hb
  obtain ⟨μ,hμ,D,hD,hb,_⟩ := normalized_restriction_ball_bound ζ hball hC
    (E ∩ closedBall x r) (hE.measurableSet.inter measurableSet_closedBall) hpos
  exact ⟨μ,hμ,D,hD,hb⟩

/-- Compact simultaneous restrictions turn the integrated published radial
estimate into uniform control at every retained pin. -/
theorem source_uniform_radial_restrictions_of_published_radial
    (hOrponen : PublishedPlanarRadialMoment) (μ₀ ν₀ : ProbabilityMeasure Plane)
    (hμK : IsCompact (μ₀ : Measure Plane).support)
    (hνK : IsCompact (ν₀ : Measure Plane).support)
    (hsep : Disjoint (μ₀ : Measure Plane).support (ν₀ : Measure Plane).support)
    {δ C : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hC : 0 < C)
    (hμball : BallBound μ₀ (1+δ) C) (hνball : BallBound ν₀ (1+δ) C) :
    ∃ μ ν : ProbabilityMeasure Plane,
      IsCompact (μ : Measure Plane).support ∧ IsCompact (ν : Measure Plane).support ∧
      (μ : Measure Plane).support ⊆ (μ₀ : Measure Plane).support ∧
      (ν : Measure Plane).support ⊆ (ν₀ : Measure Plane).support ∧
      ∃ D : ℝ, 0 < D ∧ BallBound μ (1+δ) D ∧ BallBound ν (1+δ) D ∧
      ∃ K : ℝ≥0∞, K ≠ ∞ ∧
        (∀ x ∈ (μ : Measure Plane).support,
          sourceDensityNorm (1+δ/8) ((ν : Measure Plane).map (sourceRadialUnit x)) ≤ K) ∧
        (∀ y ∈ (ν : Measure Plane).support,
          sourceDensityNorm (1+δ/8) ((μ : Measure Plane).map (sourceRadialUnit y)) ≤ K) := by
  obtain ⟨hs1, _, hp1, _, ht0, _, _, hsδ, htδ⟩ := radial_parameters hδ hδ1
  have hpq : (1+δ/8).HolderConjugate ((1+δ/8)/((1+δ/8)-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp1).mpr rfl
  have hIμ := hOrponen ν₀ μ₀ δ hδ hδ1 hνK hμK hsep.symm
    (rieszEnergy_lt_top_of_ball_bound ν₀ (zero_lt_one.trans hs1) hsδ hνball)
    (rieszEnergy_lt_top_of_ball_bound μ₀ ht0 htδ hμball)
  have hIν := hOrponen μ₀ ν₀ δ hδ hδ1 hμK hνK hsep
    (rieszEnergy_lt_top_of_ball_bound μ₀ (zero_lt_one.trans hs1) hsδ hμball)
    (rieszEnergy_lt_top_of_ball_bound ν₀ ht0 htδ hνball)
  exact uniform_restrictions_of_finite_radial_moments μ₀ ν₀ hμK hνK
    (add_pos zero_lt_one hδ) hC hμball hνball hpq hIμ hIν

theorem exists_normalized_root_setup_of_published_radial
    (hOrponen : PublishedPlanarRadialMoment) (E : Set Plane) (hE : IsCompact E) (hd : 1 < dimH E) :
    ∃ δ s : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < s ∧
      ∃ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) ∧
        dist (Q 0).center (Q 1).center = 250 ∧
      ∃ μ ν : ProbabilityMeasure Plane,
        IsCompact (μ : Measure Plane).support ∧ IsCompact (ν : Measure Plane).support ∧
        (μ : Measure Plane).support ⊆ (fun x : Plane => s • x) '' E ∧
        (ν : Measure Plane).support ⊆ (fun x : Plane => s • x) '' E ∧
        (μ : Measure Plane).support ⊆ (Q 0).carrier ∧
        (ν : Measure Plane).support ⊆ (Q 1).carrier ∧
        (μ : Measure Plane) (Q 0).carrierᶜ = 0 ∧ (ν : Measure Plane) (Q 1).carrierᶜ = 0 ∧
      ∃ C : ℝ, 0 < C ∧ BallBound μ (1+δ) C ∧ BallBound ν (1+δ) C ∧
      ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
        (∀ x ∈ (μ : Measure Plane).support,
          sourceDensityNorm (1+δ/8) ((ν : Measure Plane).map (sourceRadialUnit x)) ≤ K) ∧
        (∀ y ∈ (ν : Measure Plane).support,
          sourceDensityNorm (1+δ/8) ((μ : Measure Plane).map (sourceRadialUnit y)) ≤ K) := by
  obtain ⟨δ,hδ,hδ1,ζ,hζ,hna,C,hC,hball,_⟩ := exists_frostman_above_one E hE hd
  let := hna
  obtain ⟨x,hx,y,hy,hxy⟩ := exists_distinct_support_points ζ
  let r := dist x y/1000
  let s := 250/dist x y
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  have hr : 0 < r := by dsimp only [r]; positivity
  have hs : 0 < s := by dsimp only [s]; positivity
  obtain ⟨μ₀,hμ₀,Cμ,hCμ,hbμ⟩ := compact_neighborhood_probability_for_published_radial E hE ζ hζ hC hball x hx hr
  obtain ⟨ν₀,hν₀,Cν,hCν,hbν⟩ := compact_neighborhood_probability_for_published_radial E hE ζ hζ hC hball y hy hr
  let f : Plane → Plane := fun z => s • z
  have hfc : Continuous f := by dsimp only [f]; fun_prop
  let μ₁ := μ₀.map f
  let ν₁ := ν₀.map f
  let Q : Fin 2 → DyadicSquare := ![(rootPatchEnvelope x r).dilate s,(rootPatchEnvelope y r).dilate s]
  have hgeo := normalized_root_patch_geometry x y hxy
  have hQ (l : Fin 2) : (Q l).side = 1 := by
    fin_cases l
    · exact hgeo.2.1
    · exact hgeo.2.2.1
  have hcent : dist (Q 0).center (Q 1).center = 250 := hgeo.2.2.2.1
  have hAK : IsCompact (f '' (E ∩ closedBall x r)) := (hE.inter_right isClosed_closedBall).image hfc
  have hBK : IsCompact (f '' (E ∩ closedBall y r)) := (hE.inter_right isClosed_closedBall).image hfc
  have hμA : (μ₁ : Measure Plane).support ⊆ f '' (E ∩ closedBall x r) :=
    support_subset_carrier μ₁ hAK.isClosed (dilate_carried_compact μ₀ _
      (hE.inter_right isClosed_closedBall) hμ₀ s)
  have hνB : (ν₁ : Measure Plane).support ⊆ f '' (E ∩ closedBall y r) :=
    support_subset_carrier ν₁ hBK.isClosed (dilate_carried_compact ν₀ _
      (hE.inter_right isClosed_closedBall) hν₀ s)
  have hμK := hAK.of_isClosed_subset Measure.isClosed_support hμA
  have hνK := hBK.of_isClosed_subset Measure.isClosed_support hνB
  have hμQ : (μ₁ : Measure Plane).support ⊆ (Q 0).carrier :=
    hμA.trans ((image_mono inter_subset_right).trans hgeo.2.2.2.2.1)
  have hνQ : (ν₁ : Measure Plane).support ⊆ (Q 1).carrier :=
    hνB.trans ((image_mono inter_subset_right).trans hgeo.2.2.2.2.2)
  have hsep : Disjoint (μ₁ : Measure Plane).support (ν₁ : Measure Plane).support := by
    apply disjoint_left.mpr
    intro z hz hz'
    have hx := (Q 0).dist_center_le_three_quarters (by rw [hQ 0]; norm_num) (hμQ hz)
    have hy := (Q 1).dist_center_le_three_quarters (by rw [hQ 1]; norm_num) (hνQ hz')
    have ht := dist_triangle (Q 0).center z (Q 1).center
    rw [hQ 0] at hx
    rw [hQ 1] at hy
    rw [hcent, dist_comm (Q 0).center z] at ht
    linarith
  let D := max (Cμ/s^(1+δ)) (Cν/s^(1+δ))
  have hD : 0 < D := (by positivity : 0 < Cμ/s^(1+δ)).trans_le (le_max_left _ _)
  have hbμ₁ : BallBound μ₁ (1+δ) D := by
    intro z a ha
    exact ((hbμ.dilate hs) z a ha).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hbν₁ : BallBound ν₁ (1+δ) D := by
    intro z a ha
    exact ((hbν.dilate hs) z a ha).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
  obtain ⟨μ,ν,hμK',hνK',hμsub,hνsub,D',hD',hbμ',hbν',K,hK,hU,hV⟩ :=
    source_uniform_radial_restrictions_of_published_radial hOrponen μ₁ ν₁ hμK hνK hsep hδ hδ1 hD hbμ₁ hbν₁
  have hμQ' := hμsub.trans hμQ
  have hνQ' := hνsub.trans hνQ
  refine ⟨δ,s,hδ,hδ1,hs,Q,hQ,hcent,μ,ν,hμK',hνK',
    hμsub.trans (hμA.trans (image_mono inter_subset_left)),
    hνsub.trans (hνB.trans (image_mono inter_subset_left)),hμQ',hνQ',?_,?_,
    D',hD',hbμ',hbν',K,hK,hU,hV⟩
  · exact measure_mono_null (compl_subset_compl.mpr hμQ') (μ : Measure Plane).support_mem_ae
  · exact measure_mono_null (compl_subset_compl.mpr hνQ') (ν : Measure Plane).support_mem_ae


end PlanarFalconer

end OAI
