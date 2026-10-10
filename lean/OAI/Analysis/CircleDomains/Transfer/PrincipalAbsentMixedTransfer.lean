import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Transfer.PrincipalMixedTransfer
import OAI.Analysis.CircleDomains.Rigidity.MaskBranchCollars

namespace OAI

/-! Exterior replacements preserve every full-mask real coordinate,
including its exact real collar branch and its transported real filling. -/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem principal_absent_mixed_transfer
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {J : Type*} [Finite J] (T : J → ℂ ≃ₜ ℂ)
    (hTdisj : Pairwise (Disjoint on fun j => closure (jordanInterior (T j))))
    {I : Type*} [Fintype I] {n : ℕ}
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
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hDO : ∀ i, frontier (D i) ⊆ O i)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (hOK : ∀ i, Disjoint (O i) K)
    (present : I → Fin n → Prop)
    (habsent : ∀ i l, ¬present i l → Disjoint (O i) (M l))
    (u : I → Fin n → (ℝ × ℝ) → ℝ) (hu : ∀ i l, present i l → ContDiffOn ℝ ∞ (u i l) (O i))
    (hproj : ∀ i l, present i l → ∀ x, x ∈ O i → (u i l x : UnitAddCircle) = f l x)
    (N : ℕ) (active : I → Fin n) (θ : Fin n → ℝ)
    (havoid : ∀ i l, present i l → l ≠ active i →
      Disjoint (u i l '' frontier (D i)) (shiftedLattice (reciprocalGridStep N) (θ l)))
    {A : Type*} [Fintype A] (ι : A → Fin n) (hι : Injective ι)
    (r : A → (ℝ × ℝ) → ℝ) (hr : ∀ j, ContDiffOn ℝ ∞ (r j) G)
    (hRM : ∀ j, M (ι j) = univ)
    (hrproj : ∀ j x, (r j x : UnitAddCircle) = f (ι j) x)
    (hreal : ∀ i j, EqOn (u i (ι j)) (r j) (O i))
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
        ∫ x in s, fieldEnergy (circleGradient (F l)) g x) ∧
      ∃ W : A → (ℝ × ℝ) → ℝ,
        IsFilledCoordinateFamily D (G ∪ ⋃ i, D i)
          (fun j => cutoffStaircase (r j) χ (shiftedStaircase (reciprocalGridStep N)
            (staircaseWidth (reciprocalGridStep N) k) (θ (ι j)))) W ∧
        (∀ j x, (W j x : UnitAddCircle) = F (ι j) x) ∧
        (∀ᶠ x in 𝓝ˢ K, ∀ j, W j x = r j x) ∧
        (∀ j, ContDiffOn ℝ ∞ (W j ∘ sphereRealMap φi) (realChartDomain V) ∧
          ∀ x ∈ realChartDomain (openCompletedRegion T),
            ((W j ∘ sphereRealMap φi) ∘ sphereRealMap φ) =ᶠ[𝓝 x] W j) ∧
        (∀ j (s : Set (ℝ × ℝ)), MeasurableSet s → s ⊆ realChartDomain (openCompletedRegion T) →
          (∫ y in sphereRealMap φ '' s, gradientEnergy (W j ∘ sphereRealMap φi) (fun _ => 1) y) =
            ∫ x in s, gradientEnergy (W j) g x) ∧
        (∀ p ∈ openCompletedRegion T, IsMetricConformalAt g φ p) := by
  classical
  have hBd : Pairwise (Disjoint on fun i => frontier (D i)) :=
    fun i j hij => (hdisj hij).mono frontier_subset_closure frontier_subset_closure
  obtain ⟨V, W, v, hV, hW, hv, hvproj, hvavoid, hvreal⟩ := exists_mask_branch_collars
    (fun i => frontier (D i)) hfrontc hBd O hO hDO hOK M f present habsent u hu hproj
      (reciprocalGridStep_pos N) θ active havoid
  let f₀ : Fin n → (ℝ × ℝ) → UnitAddCircle := fun l =>
    exteriorMaskReplacement (W l) ((θ l + reciprocalGridStep N / 2 : ℝ) : UnitAddCircle) (f l)
  have heqM (l : Fin n) : f₀ l =ᶠ[𝓝ˢ (M l)] f l :=
    exteriorMaskReplacement_eventuallyEq (hW l).1 (hW l).2.1 _ _
  have heqK : ∀ᶠ z in 𝓝ˢ K, ∀ l, f₀ l z = f l z :=
    eventually_all.mpr fun l =>
      exteriorMaskReplacement_eventuallyEq (hW l).1 (hW l).2.2 _ _
  have hgrad (l : Fin n) (z : ℝ × ℝ) (hz : z ∈ M l) :
      circleGradient (f₀ l) z = circleGradient (f l) z :=
    exteriorMaskReplacement_gradient (hW l).1 (hW l).2.1 _ _ hz
  have hcost (k : ℕ) : maskedCircleWedges M
      (circleCutoffFamily f₀ χ N (staircaseWidth (reciprocalGridStep N) k) θ) =
      maskedCircleWedges M (circleCutoffFamily f χ N
        (staircaseWidth (reciprocalGridStep N) k) θ) :=
    exteriorMaskReplacement_masked_wedges W M (fun l => (hW l).1)
      (fun l => (hW l).2.1) _ f χ N _ θ
  have hpres (i : I) (j : A) : present i (ι j) := by
    by_contra hp
    obtain ⟨x, hx⟩ := (hfrontconn i).nonempty
    exact Set.disjoint_left.mp (habsent i (ι j) hp) (hDO i hx) (by rw [hRM]; trivial)
  have hrproj₀ (j : A) (x : ℝ × ℝ) : (r j x : UnitAddCircle) = f₀ (ι j) x := by
    exact (hrproj j x).trans ((heqM (ι j)).self_of_nhdsSet (by rw [hRM]; trivial)).symm
  obtain ⟨k, F, R, g, V₀, φ, φi, hlate, hfill, hretain, hR, hg, hPD, hcore, hfar,
      htail, hlocal, hV₀, heq, hconf, hnorm, hcoordinates, henergy,
      Wreal, hWreal, hWproj, hWretain, hWcoords, hWenergy, hmetric⟩ :=
    principal_actual_mixed_transfer hcompact hfinite T hTdisj D hD hdisj hfrontc hfrontconn
      hG hK hKc hKG hKQ hcover hKD M hM hboundary f₀
      (fun l => exteriorMaskReplacement_smooth (hW l).1 (hW l).2.1 _ _ (hf l))
      (fun l => exteriorMaskReplacement_memLp (hW l).1 (hW l).2.1
        hG.measurableSet (hM l).measurableSet _ _ (hf2 l))
      χ hχ hχzero V (fun i => (hV i).1) (fun i => (hV i).2.1)
      (fun i z hz => hχone i z ((hV i).2.2 hz)) v hv hvproj N active θ hvavoid
      ι hι r hr hrproj₀
      (fun i j x hx => (hvreal i (ι j) (hpres i j) hx).trans
        (hreal i j ((hV i).2.2 hx)))
      (fun k => by rw [hcost k]; exact hvi k)
      (hgood.mono fun k hk => by rw [hcost k]; exact hk) k₀
  refine ⟨f₀, heqM, heqK, k, F, R, g, V₀, φ, φi, hlate, hfill, ?_, hR, hg, hPD,
    hcore, hfar, htail, ?_, hV₀, heq, hconf, hnorm, hcoordinates, henergy,
    Wreal, hWreal, hWproj, hWretain, hWcoords, hWenergy, hmetric⟩
  · filter_upwards [hretain, heqK] with z hz he l
    exact (hz l).trans (he l)
  · intro l E hE hEK
    have hi := hlocal l E hE hEK
    have he : (∫ z in (G \ E) ∩ M l, fieldEnergy (circleGradient (f₀ l))
        (fun z => sphericalMetricFactor z • 1) z) =
        ∫ z in (G \ E) ∩ M l, fieldEnergy (circleGradient (f l))
          (fun z => sphericalMetricFactor z • 1) z := by
      apply setIntegral_congr_fun ((hG.measurableSet.diff hE).inter (hM l).measurableSet)
      intro z hz
      simp only [fieldEnergy, hgrad l z hz.2]
    rwa [he] at hi

end CircleDomainRigidity.FiniteTransfer

end

end OAI
