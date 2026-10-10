import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineFromHorizontalLabels

namespace OAI

/-! # The deterministic affinity criterion from the two segment inequalities -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory Module
open scoped NNReal ContDiff Topology

theorem affine_profile_of_segment_inequalities
    {H V W I B K J N L : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H] [Fintype N]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    [Fintype I] [Fintype B] [Nonempty B]
    [Fintype L] [Nonempty L] [MeasurableSpace L] [MeasurableSingletonClass L]
    {c : ℕ} (a : DynkinCoefficients c 2) (br : V →L[ℝ] V →L[ℝ] V)
    (hbr : IsLieBracket br) (hg : PolynomialGroupLaws (dynkinProduct a br))
    (hc : ExponentialConjugationLaw (dynkinProduct a br) br)
    (D : H →L[ℝ] V) (bH : Basis N ℝ H)
    (X : K → H) (b₀ : Basis J ℝ V) (w₀ : J → FreeMagma K)
    (hw₀ : ∀ j, evalBilinearWord br (fun k => D (X k)) (w₀ j) = b₀ j)
    (μ : Measure (PolynomialCoordinateGroup (dynkinProduct a br) hg))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (Ω : Set (PolynomialCoordinateGroup (dynkinProduct a br) hg)) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hne : Ω.Nonempty)
    (f : V → W) (hf : Continuous f)
    (π : PolynomialCoordinateGroup (dynkinProduct a br) hg →* Multiplicative W)
    (p : V →L[ℝ] W) (hp : Function.Surjective (p.comp D))
    (hπExp : ∀ v, (π (PolynomialCoordinateGroup.exp _ hg v)).toAdd = p v)
    (P : SupportDatum W I B) (hweights : ∀ i, P.weight i ≠ 0)
    (σ : I → Bool) (hσ : (weightChamber (fun i => (P.weight i).toContinuousLinearMap) σ).Nonempty)
    (A : L → templateSymmetryGroup P) (C : H → ℝ≥0)
    (hlip : ∀ v g, LipschitzOnWith (C v)
      (fun t : ℝ => f (dynkinProduct a br g (t • D v)))
      {t | dynkinProduct a br g (t • D v) ∈ Ω})
    (hsegments : ∀ v (T : ℝ), 0 < T →
      ∀ g ∈ flowLineBase Ω (PolynomialCoordinateGroup.exp _ hg) (D v) T,
        T⁻¹ • (f (dynkinProduct a br g (T • D v)) - f g) ∈
            convexHull ℝ (range fun l => (A l).val (p (D v))) ∧
        T * P.segmentSupport (p (D v)) ≤ P.templateSupport
          ((fun t : ℝ => f (dynkinProduct a br g (t • D v))) '' Icc 0 T)) :
    ∃ l b, ∀ g ∈ Ω, f g = (A l).val ((π g).toAdd) + b := by
  classical
  let G := PolynomialCoordinateGroup (dynkinProduct a br) hg
  let e : V ≃ₜ G := PolynomialCoordinateGroup.expHomeomorph _ hg
  let : T2Space G := inferInstanceAs (T2Space V)
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace V)
  let : SecondCountableTopology G := inferInstanceAs (SecondCountableTopology V)
  let : IsTopologicalGroup G := PolynomialCoordinateGroup.isTopologicalGroup _ hg
    (continuous_dynkinProduct a (fun _ => br) Prod.fst Prod.snd
      continuous_const continuous_fst continuous_snd)
  have hm : ContDiff ℝ ∞ (fun z : V × V => dynkinProduct a br z.1 z.2) :=
    contDiff_dynkinProduct a (fun _ => br) Prod.fst Prod.snd
      contDiff_const contDiff_fst contDiff_snd
  have hlocal (g : V) (v : H) : ∃ T : ℝ, 0 < T ∧
      (g ∈ Ω → g ∈ flowLineBase Ω (PolynomialCoordinateGroup.exp _ hg) (D v) T) := by
    by_cases hgΩ : g ∈ Ω
    · have hevent : ∀ᶠ t : ℝ in 𝓝 0, dynkinProduct a br g (t • D v) ∈ Ω := by
        have hcont : Continuous (fun t : ℝ => dynkinProduct a br g (t • D v)) :=
          hm.continuous.comp (continuous_const.prodMk (continuous_id.smul continuous_const))
        have h0 : dynkinProduct a br g ((0 : ℝ) • D v) ∈ Ω := by
          simpa only [zero_smul, hg.2.2.1] using hgΩ
        exact hcont.continuousAt (hΩ.mem_nhds h0)
      obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hevent
      refine ⟨ε / 2, half_pos hε, fun _ t ht => he ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact ht.2.trans_lt (half_lt_self hε)
    · exact ⟨1, zero_lt_one, fun h => (hgΩ h).elim⟩
  choose T hT hstay using hlocal
  obtain ⟨label, hlabel, hbase⟩ := exists_measurable_horizontal_profile_label
    (dynkinProduct a br) hg hm μ f hf Ω hΩ D bH C hlip P (p.comp D) hp A T
    (fun g _ v => hT g v)
    (fun g hgΩ v t ht htT =>
      (hsegments v t ht g (fun s hs => hstay g v hgΩ s ⟨hs.1, hs.2.trans htT.le⟩)).1)
    (fun g hgΩ v t ht htT =>
      (hsegments v t ht g (fun s hs => hstay g v hgΩ s ⟨hs.1, hs.2.trans htT.le⟩)).2)
  apply affine_of_horizontal_labels a br hbr hg hc D X b₀ w₀ hw₀ μ Ω hΩ hconn hne f hf
    π p hp hπExp P hweights σ hσ label hlabel A hbase C hlip
  intro v t ht g hgt
  exact (hsegments v t ht g hgt).2

end PolycyclicRecognition

end

end OAI
