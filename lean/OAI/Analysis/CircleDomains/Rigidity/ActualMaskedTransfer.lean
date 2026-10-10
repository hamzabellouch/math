import OAI.Analysis.CircleDomains.Rigidity.MaskedFiniteTransfer

namespace OAI

/-!
# Transfer of the selected actual masked cutoff

The collar construction and the common-width energy selection are
applied to the actual reciprocal-grid cutoff family. Only the original
masked L² norms are used on the retained core.
-/

open Set Filter Function MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem transfer_actual_masked_circle_cutoff
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
      ∀ i : Fin n, ∀ E : Set (ℝ × ℝ), MeasurableSet E → E ⊆ K →
        (∫ z in (Q \ E) ∩ M i, fieldEnergy (circleGradient (F i)) g z) <
          (∫ z in (G \ E) ∩ M i, fieldEnergy (circleGradient (f i))
            (fun z => sphericalMetricFactor z • 1) z) + ε := by
  have hfill := eventually_fill_actual_masked_circle_cutoff D hD hdisj hfrontc hfrontconn
    M f hf χ hχ O hO hDO hχone u hu hproj N active θ havoid
  have hretain (δ : ℝ) : ∀ᶠ x in 𝓝ˢ K, ∀ i, circleCutoffFamily f χ N δ θ i x = f i x := by
    filter_upwards [hχzero] with x hx i
    exact circleCutoff_eq_of_zero (f i) χ (shiftedStaircase (reciprocalGridStep N) δ (θ i)) hx
  have hcost : ∃ᶠ k in atTop, (∫ z in G \ K, 2 * maskedCircleWedges M
      (circleCutoffFamily f χ N (staircaseWidth (reciprocalGridStep N) k) θ) z) < ε := by
    apply hgood.mono
    intro k hk
    rw [integral_const_mul]
    linarith
  exact exists_masked_circle_transfer_at_good_width D hD
    (hG.union (isOpen_iUnion hD)) hQ hG.measurableSet hK hKc
    (fun z hz => hcover hz.1) hKG hcover hKD M hM hboundary
    (fun δ => circleCutoffFamily f χ N δ θ) f hf2 hretain (reciprocalGridStep_pos N)
    hfill (fun k => (hvi k).const_mul 2) hcost k₀

end CircleDomainRigidity.FiniteTransfer

end

end OAI
