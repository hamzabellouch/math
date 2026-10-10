import OAI.Analysis.CircleDomains.Topology.MixedCircleFillings
import OAI.Analysis.CircleDomains.Rigidity.MaskedTransferWithData

namespace OAI

/-! Transfer real barriers and masked period coordinates using one width
and one metric, retaining the exact real barriers near the chosen core. -/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem transfer_actual_mixed_cutoff
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    (hdisj : Pairwise (Disjoint on fun i => closure (D i)))
    (hfrontc : ∀ i, IsCompact (frontier (D i)))
    (hfrontconn : ∀ i, IsConnected (frontier (D i)))
    {G Q K : Set (ℝ × ℝ)} (hG : IsOpen G) (hQ : IsClosed Q)
    (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ)) (hKG : K ⊆ G)
    (hcover : Q ⊆ G ∪ ⋃ i, D i) (hKD : ∀ x ∈ K, ∀ i, x ∉ D i)
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
    (u : I → Fin n → (ℝ × ℝ) → ℝ) (hu : ∀ i l, ContDiffOn ℝ ∞ (u i l) (O i))
    (hproj : ∀ i l x, x ∈ O i → (u i l x : UnitAddCircle) = f l x)
    (N : ℕ) (active : I → Fin n) (θ : Fin n → ℝ)
    (havoid : ∀ i l, l ≠ active i →
      Disjoint (u i l '' frontier (D i)) (shiftedLattice (reciprocalGridStep N) (θ l)))
    {J : Type*} [Fintype J] (ι : J → Fin n) (hι : Injective ι)
    (r : J → (ℝ × ℝ) → ℝ) (hr : ∀ j, ContDiffOn ℝ ∞ (r j) G)
    (hrproj : ∀ j x, (r j x : UnitAddCircle) = f (ι j) x)
    (hreal : ∀ i j, EqOn (u i (ι j)) (r j) (O i))
    (hvi : ∀ k, IntegrableOn (maskedCircleWedges M (circleCutoffFamily f χ N
      (staircaseWidth (reciprocalGridStep N) k) θ)) (G \ K))
    {ε : ℝ} (hgood : ∃ᶠ k in atTop, (∫ z in G \ K, maskedCircleWedges M
      (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) z) < ε / 2)
    (k₀ : ℕ) :
    ∃ (k : ℕ) (F : Fin n → (ℝ × ℝ) → UnitAddCircle)
      (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric),
      k₀ ≤ k ∧ IsMaskedFilledCircleFamily D (G ∪ ⋃ i, D i) M
        (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) F ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ i, F i z = f i z) ∧
      0 < R ∧ ContDiff ℝ ∞ g ∧ (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (Q \ K) ∩ M i, fieldEnergy (circleGradient (F i)) g z) < ε ∧
      (∀ i : Fin n, ∀ E : Set (ℝ × ℝ), MeasurableSet E → E ⊆ K →
        (∫ z in (Q \ E) ∩ M i, fieldEnergy (circleGradient (F i)) g z) <
          (∫ z in (G \ E) ∩ M i, fieldEnergy (circleGradient (f i))
            (fun z => sphericalMetricFactor z • 1) z) + ε) ∧
      ∃ W : J → (ℝ × ℝ) → ℝ,
        IsFilledCoordinateFamily D (G ∪ ⋃ i, D i)
          (fun j => cutoffStaircase (r j) χ (shiftedStaircase (reciprocalGridStep N)
            (staircaseWidth (reciprocalGridStep N) k) (θ (ι j)))) W ∧
        (∀ j x, (W j x : UnitAddCircle) = F (ι j) x) ∧
        (∀ᶠ x in 𝓝ˢ K, ∀ j, W j x = r j x) := by
  have hfill := eventually_fill_actual_mixed_cutoff D hD hdisj hfrontc hfrontconn
    hG M f hf χ hχ O hO hDO hχone u hu hproj N active θ havoid ι hι r hr hrproj hreal
  have hretain (δ : ℝ) : ∀ᶠ x in 𝓝ˢ K, ∀ i, circleCutoffFamily f χ N δ θ i x = f i x := by
    filter_upwards [hχzero] with x hx i
    exact circleCutoff_eq_of_zero (f i) χ (shiftedStaircase (reciprocalGridStep N) δ (θ i)) hx
  have hcost : ∃ᶠ k in atTop, (∫ z in G \ K, 2 * maskedCircleWedges M
      (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) z) < ε := by
    apply hgood.mono
    intro k hk
    rw [integral_const_mul]
    linarith
  obtain ⟨k, F, R, g, hlate, hF, hcore, hR, hg, hPD, hmetric, hfar, hsum, hlocal,
      W, hW, hWproj⟩ := exists_masked_circle_transfer_with_data D hD
    (hG.union (isOpen_iUnion hD)) hQ hG.measurableSet hK hKc
    (fun z hz => hcover hz.1) hKG hcover hKD M hM hboundary
    (fun δ => circleCutoffFamily f χ N δ θ) f hf2 hretain (reciprocalGridStep_pos N)
    (fun δ F => ∃ W : J → (ℝ × ℝ) → ℝ,
      IsFilledCoordinateFamily D (G ∪ ⋃ i, D i)
        (fun j => cutoffStaircase (r j) χ
          (shiftedStaircase (reciprocalGridStep N) δ (θ (ι j)))) W ∧
      ∀ j x, (W j x : UnitAddCircle) = F (ι j) x)
    hfill (fun k => (hvi k).const_mul 2) hcost k₀
  refine ⟨k, F, R, g, hlate, hF, hcore, hR, hg, hPD, hmetric, hfar, hsum,
    hlocal, W, hW, hWproj, ?_⟩
  apply eventually_nhdsSet_iff_forall.mpr
  intro x hx
  apply eventually_all.mpr
  intro j
  filter_upwards [hW.eventuallyEq_outside hD (hKD x hx) j,
    hχzero.filter_mono (nhds_le_nhdsSet hx)] with y hy hyχ
  exact hy.trans (cutoffStaircase_of_zero hyχ)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
