import OAI.Geometry.SurfaceImmersion.Correction.SmoothingAtlas

namespace OAI

/-! Smoothing atlases whose actual centers index prescribed neighborhoods. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

/-- The finite atlas retains the point indexing of prescribed neighborhoods.
Its outer cutoffs equal one on a neighborhood of every weight-support point. -/
theorem exists_smoothingAtlas_subordinate_locally_one (V : M → Set M)
    (hV : ∀ p, IsOpen (V p)) (hpV : ∀ p, p ∈ V p) :
    ∃ A : SmoothingAtlas M,
      (∀ i : A.centers, tsupport (A.weight i) ⊆ V (i : M)) ∧
      ∀ (i : A.centers) (x : M), x ∈ tsupport (A.weight i) →
        A.outer i =ᶠ[𝓝 x] (fun _ => 1) := by
  classical
  obtain ⟨t,ψ,hψ,hsupp,_,_,hsum⟩ :=
    PhaseGeometry.exists_finite_smooth_square_partition (E := Plane)
      (fun p : M => V p ∩ (chart p).source)
      (fun p => (hV p).inter (chart p).open_source)
      (fun p => ⟨hpV p,by rw [chart_source]; exact mem_chart_source Plane p⟩)
  have hchart (i : t) : tsupport (ψ i) ⊆ (chart (i : M)).source :=
    fun x hx => (hsupp i hx).2
  have hout : ∀ i : t, ∃ χ : M → ℝ,
      ContMDiff planeModel 𝓘(ℝ) ∞ χ ∧
      tsupport χ ⊆ (chart (i : M)).source ∧
      ∀ x ∈ tsupport (ψ i), χ =ᶠ[𝓝 x] (fun _ => 1) := by
    intro i
    have hc : IsCompact (tsupport (ψ i)) := (isClosed_tsupport _).isCompact
    obtain ⟨B,hB,hKB,hBc⟩ := hc.exists_isOpen_closure_subset
      (((hV (i : M)).inter (chart (i : M)).open_source).mem_nhdsSet.mpr (hsupp i))
    obtain ⟨O,hO,hKO,hOc⟩ := hc.exists_isOpen_closure_subset (hB.mem_nhdsSet.mpr hKB)
    obtain ⟨χ,hχ,_,hχs,hχone⟩ :=
      exists_contMDiff_support_eq_eq_one_iff (I := planeModel) (n := (⊤ : ℕ∞))
        hB isClosed_closure hOc
    refine ⟨χ,hχ,?_,?_⟩
    · change closure (Function.support χ) ⊆ _
      rw [hχs]
      exact fun x hx => (hBc hx).2
    · intro x hx
      filter_upwards [hO.mem_nhds (hKO hx)] with y hy
      exact (hχone y).mp (subset_closure hy)
  choose χ hχ hχs hχone using hout
  let A : SmoothingAtlas M :=
    ⟨t,ψ,χ,hψ,hchart,hχ,hχs,fun i x hx => (hχone i x hx).eq_of_nhds,hsum⟩
  exact ⟨A,(fun i x hx => (hsupp i hx).1),hχone⟩

/-- The finite atlas weights are subordinate to their actual centers'
prescribed open neighborhoods. -/
theorem exists_smoothingAtlas_subordinate (V : M → Set M)
    (hV : ∀ p, IsOpen (V p)) (hpV : ∀ p, p ∈ V p) :
    ∃ A : SmoothingAtlas M, ∀ i : A.centers, tsupport (A.weight i) ⊆ V (i : M) := by
  obtain ⟨A,hA,_⟩ := exists_smoothingAtlas_subordinate_locally_one V hV hpV
  exact ⟨A,hA⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
