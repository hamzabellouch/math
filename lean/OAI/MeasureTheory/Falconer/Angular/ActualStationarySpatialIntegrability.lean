import OAI.MeasureTheory.Falconer.Angular.ActualStationaryProductKernel

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_far_stationary_integrable {Ψ : ℝ → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hsΨ : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {sig : ℝ} (hsig : 0 < sig) (K o : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ)
    (lam : Fin 2 → ℝ) (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ v h L₀ : ℝ, v-h = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    ∀ (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ],
    ∀ Z : Set (Fin 4 → Plane),
    (∀ᵐ x ∂μ.restrict Z, 4*(2:ℝ)^(-h) ≤ ‖x 0-x 1‖ ∧ 4*(2:ℝ)^(-h) ≤ ‖x 2-x 3‖) →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N (lam l) sig (J l) (i l) (hsp l)
    IntegrableOn (angularStationarySpatialKernel (β 0) (β 1) o v Ψ) Z μ := by
  obtain ⟨H,hH,N₀,h₀⟩ := uniform_actual_stationary_product_kernel hΨ hsΨ hsig K o
  refine ⟨N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hL Q hQ ρ m lam J i hsp hm hb v h L₀ hv hLL hL₀ μ instμ Z hgeom
  let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
    N (lam l) sig (J l) (i l) (hsp l)
  have hβ (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol _ _ _ _ _ _ _ _ _ _ _ _ (hm l)
  have hG := angularStationarySpatialKernel_measurable (β 0) (β 1) (hβ 0) (hβ 1)
    (inheritedCircleSymbol_contDiff _ _ _ _ (hQ 0) _ _ _ _ _ _ _ _)
    (inheritedCircleSymbol_contDiff _ _ _ _ (hQ 1) _ _ _ _ _ _ _ _) o v hΨ.continuous.measurable
  apply (integrable_const (H*(2:ℝ)^(-(v-h)))).mono' hG.aestronglyMeasurable
  filter_upwards [hgeom] with x hx
  have hpos : 0 < (2:ℝ)^(-h) := by positivity
  have hdist : ∀ l : Fin 2, (2:ℝ)^(-h) ≤ ‖(![x 0,x 2] : Fin 2 → Plane) l-(![x 1,x 3] : Fin 2 → Plane) l‖ := by
    intro l
    fin_cases l
    · change (2:ℝ)^(-h) ≤ ‖x 0-x 1‖; linarith [hx.1]
    · change (2:ℝ)^(-h) ≤ ‖x 2-x 3‖; linarith [hx.2]
  have hD : ∀ l : Fin 2, sourceSymbolScale N sig L^2 ≤
      (2:ℝ)^v*‖(![x 0,x 2] : Fin 2 → Plane) l-(![x 1,x 3] : Fin 2 → Plane) l‖ := by
    intro l
    apply sourceSymbolScale_far_frequency_le hsig.le N L hv hLL hL₀
    fin_cases l
    · exact hx.1
    · exact hx.2
  have he := h₀ N hN S b k hcard hK L hL Q hQ ρ m lam J i hsp ![x 0,x 2] ![x 1,x 3]
    (fun l => hb l _) (fun l => hb l _) v h hdist hD
  have hxvec : (![x 0,x 1,x 2,x 3] : Fin 4 → Plane) = x := by ext j; fin_cases j <;> rfl
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,hxvec] at he
  apply he.trans
  apply div_le_self (by positivity)
  apply one_le_pow₀
  have : 0 ≤ (2:ℝ)^v*|‖x 0-x 1‖-‖x 2-x 3‖| := by positivity
  linarith

end PlanarFalconer

end OAI
