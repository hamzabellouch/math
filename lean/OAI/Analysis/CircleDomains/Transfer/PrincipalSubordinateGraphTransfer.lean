import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Rigidity.PrincipalAbsentMaskedTransfer
import OAI.Analysis.CircleDomains.Rigidity.SubordinateMaskedBranches
import OAI.Analysis.CircleDomains.Rigidity.ActualMaskedTransfer
import OAI.Analysis.CircleDomains.Uniformization.FiniteModelCoordinates
import OAI.Analysis.CircleDomains.Transfer.CompletedChart
import OAI.Analysis.CircleDomains.Rigidity.MaskBranchCollars

namespace OAI

/-! Construct the finite masked model directly from subordinate branch
neighborhoods and the physical contour graph avoidance. The active label,
real collars and absent-coordinate replacements are all derived here. -/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem principal_subordinate_graph_transfer
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {J : Type*} [Finite J] (T : J → ℂ ≃ₜ ℂ)
    (hTdisj : Pairwise (Disjoint on fun j => closure (jordanInterior (T j))))
    {I : Type*} [Fintype I] {n : ℕ} (hn : 0 < n)
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on fun i => closure (D i)))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    {G K : Set (ℝ × ℝ)} (hG : IsOpen G)
    (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ)) (hKG : K ⊆ G)
    (hKQ : sphericalCore K ⊆ openCompletedRegion T)
    (hcover : realChartDomain (completedRegion T) ⊆ G ∪ ⋃ i, D i)
    (hKD : ∀ x ∈ K, ∀ i, x ∉ D i)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ l, SmoothCircleOn (f l) (G ∩ interior (M l)))
    (hf2 : ∀ l, MemLp (circleGradient (f l)) 2 (volume.restrict (G ∩ M l)))
    (χ : (ℝ × ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχzero : ∀ᶠ x in 𝓝ˢ K, χ x = 0)
    (L : Fin n → Type*) (P : ∀ l, L l → Set (ℝ × ℝ))
    (v : ∀ l, L l → (ℝ × ℝ) → ℝ)
    (hv : ∀ l a, ContDiffOn ℝ ∞ (v l a) (G ∩ P l a))
    (hproj : ∀ l a x, x ∈ G ∩ P l a → (v l a x : UnitAddCircle) = f l x)
    (Nbh : I → Set (ℝ × ℝ)) (hNbh : ∀ i, IsOpen (Nbh i))
    (hBN : ∀ i, frontier (D i) ⊆ Nbh i)
    (hbranch : ∀ i l, Disjoint (Nbh i) (M l) ∨
      ∃ a, Nbh i ⊆ interior (M l) ∩ P l a)
    (hBG : ∀ i, frontier (D i) ⊆ G)
    (hBK : ∀ i, Disjoint (frontier (D i)) K)
    (hBχ : ∀ i, frontier (D i) ⊆ interior {x | χ x = 1})
    (R : Fin n → Set (Sphere × UnitAddCircle)) (q : (ℝ × ℝ) → Sphere)
    (hgraph : ∀ l x, x ∈ G ∩ interior (M l) → (q x, f l x) ∈ R l)
    (N : ℕ) (θ : Fin n → ℝ)
    (hgrid : ∀ i, ∃ k : ℕ, ∀ l : Fin n, l.val ≠ k →
      Disjoint (frontier (D i)) (q ⁻¹' (⋃ j, reciprocalGraphLevel (R l) (θ l) N j)))
    (hvi : ∀ k, IntegrableOn (maskedCircleWedges M (circleCutoffFamily f χ N
      (staircaseWidth (reciprocalGridStep N) k) θ)) (G \ K))
    {ε : ℝ} (hgood : ∃ᶠ k in atTop, (∫ z in G \ K, maskedCircleWedges M
      (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) z) < ε / 2)
    (k₀ : ℕ) :
    ∃ f₀ : Fin n → (ℝ × ℝ) → UnitAddCircle,
      (∀ l, f₀ l =ᶠ[𝓝ˢ (M l)] f l) ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ l, f₀ l z = f l z) ∧
    ∃ (k : ℕ) (F : Fin n → (ℝ × ℝ) → UnitAddCircle)
      (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric)
      (V : Set Sphere) (φ φi : Sphere → Sphere),
      k₀ ≤ k ∧ IsMaskedFilledCircleFamily D (G ∪ ⋃ i, D i) M
        (circleCutoffFamily f₀ χ N (staircaseWidth (reciprocalGridStep N) k) θ) F ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ i, F i z = f i z) ∧
      0 < R ∧ ContDiff ℝ ∞ g ∧ (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (realChartDomain (completedRegion T) \ K) ∩ M i,
        fieldEnergy (circleGradient (F i)) g z) < ε ∧
      (∀ i : Fin n, ∀ E : Set (ℝ × ℝ), MeasurableSet E → E ⊆ K →
        (∫ z in (realChartDomain (completedRegion T) \ E) ∩ M i,
          fieldEnergy (circleGradient (F i)) g z) <
        (∫ z in (G \ E) ∩ M i, fieldEnergy (circleGradient (f i))
          (fun z => sphericalMetricFactor z • 1) z) + ε) ∧
      IsCircleDomain V ∧ IsSmoothSphereEquivalence φ φi (openCompletedRegion T) V ∧
      IsConformalOn φ (sphericalCore K) ∧ IsPrincipalNormalized φ ∧
      (∀ l, IsOpen (sphereRealMap φ '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
        SmoothCircleOn (F l ∘ sphereRealMap φi)
          (sphereRealMap φ '' (realChartDomain (openCompletedRegion T) ∩ interior (M l))) ∧
        (∀ x ∈ realChartDomain (openCompletedRegion T) ∩ interior (M l),
          ((F l ∘ sphereRealMap φi) ∘ sphereRealMap φ) =ᶠ[𝓝 x] F l)) ∧
      (∀ l (s : Set (ℝ × ℝ)), MeasurableSet s →
        s ⊆ realChartDomain (openCompletedRegion T) ∩ interior (M l) →
        (∫ y in sphereRealMap φ '' s,
          fieldEnergy (circleGradient (F l ∘ sphereRealMap φi)) (fun _ => 1) y) =
        ∫ x in s, fieldEnergy (circleGradient (F l)) g x) := by
  classical
  obtain ⟨O, present, u, hO, habsent, hu, hproj', hOM⟩ :=
    exists_subordinate_masked_branches L G K hG hK M f P v hv hproj
      (fun i => frontier (D i)) Nbh hNbh hBN hbranch χ hBG hBK hBχ
  have hex (i : I) : ∃ a : Fin n, ∀ l, l ≠ a →
      (present i l → Disjoint (u i l '' frontier (D i))
        (shiftedLattice (reciprocalGridStep N) (θ l))) := by
    apply exists_active_coordinate_of_single_exception hn
    obtain ⟨k, hk⟩ := hgrid i
    refine ⟨k, fun l hl hp => ?_⟩
    apply Set.disjoint_left.mpr
    rintro r ⟨x, hx, rfl⟩ hr
    obtain ⟨j, hj⟩ := exists_reciprocal_level_of_mem_lattice hr
    apply Set.disjoint_left.mp (hk l hl) hx
    refine mem_iUnion.mpr ⟨j, ?_⟩
    change (q x, ((θ l + (j.val : ℝ) * reciprocalGridStep N : ℝ) : UnitAddCircle)) ∈ R l
    rw [← hj, hproj' i l hp x ((hO i).2.1 hx)]
    exact hgraph l x ⟨hBG i hx, hOM i l hp ((hO i).2.1 hx)⟩
  choose active hactive using hex
  exact principal_absent_masked_transfer hcompact hfinite T hTdisj
    D hD hdisj hfrontc hfrontconn hG hK hKc hKG hKQ hcover hKD
    M hM hboundary f hf hf2 χ hχ hχzero O (fun i => (hO i).1)
    (fun i => (hO i).2.1) (fun i => (hO i).2.2.2.2)
    (fun i => (hO i).2.2.2.1) present habsent u hu hproj' N active θ
    (fun i l hp hl => hactive i l hl hp) hvi hgood k₀

end CircleDomainRigidity.FiniteTransfer

end

end OAI
