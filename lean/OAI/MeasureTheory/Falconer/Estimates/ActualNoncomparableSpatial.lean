import OAI.MeasureTheory.Falconer.Radial.NoncomparableRadialSymmetry

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_noncomparable_spatial {sig T : ℝ} (hsig : 0 < sig) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (b : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, ∑ t ∈ S l, k l t ≤ K) →
    ∀ L ≤ N, (∀ l t, t ∈ S l → descriptorLength (b l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ)
    (lam : Fin 2 → ℝ) (J i : Fin 2 → ℕ) (hsp : Fin 2 → Plane → ℂ),
    (∀ l, Measurable (hsp l)) → (∀ l x, ‖hsp l x‖ ≤ 1) →
    ∀ v h L₀ : ℝ, v-h = 2*L₀ → (L:ℝ) ≤ L₀ → 10*sig*(N:ℝ) ≤ L₀ →
    ∀ (μ : Measure (Fin 4 → Plane)) [IsFiniteMeasure μ],
    ∀ Z : Set (Fin 4 → Plane), MeasurableSet Z →
    (∀ᵐ x ∂μ.restrict Z,
      (4*(2:ℝ)^(-h) ≤ ‖x 0-x 1‖ ∧ 2*‖x 2-x 3‖ ≤ ‖x 0-x 1‖) ∨
      (4*(2:ℝ)^(-h) ≤ ‖x 2-x 3‖ ∧ 2*‖x 0-x 1‖ ≤ ‖x 2-x 3‖)) →
    let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
      N (lam l) sig (J l) (i l) (hsp l)
    IntegrableOn (angularOriginalSpatialKernel (β 0) (β 1) v Ψ) Z μ ∧
    ‖∫ x in Z, angularOriginalSpatialKernel (β 0) (β 1) v Ψ x ∂μ‖ ≤
      ((2:ℝ)^N)^(-T)*μ.real Z := by
  obtain ⟨N₀,h₀⟩ := uniform_actual_noncomparable_radial_either (T := T) hsig K hΨ hpos hs hW hw
  refine ⟨N₀,?_⟩
  intro N hN ι inst S b k hcard hK L hLN hL Q hQ ρ m lam J i hsp hm hb
    v h L₀ hv hLL hL₀ μ instμ Z hZ hgeom
  let β := fun l => inheritedCircleSymbol (S l) (b l) (k l) (Q l) (ρ l) (m l)
    N (lam l) sig (J l) (i l) (hsp l)
  have hβ (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol _ _ _ _ _ _ _ _ _ _ _ _ (hm l)
  have hbd (l : Fin 2) (x : Plane) := inheritedCircleSymbol_norm_le
    (S l) (b l) (k l) (Q l) (hQ l) (ρ l) (m l) N (lam l) sig (J l) (i l) (hsp l) K (hK l) x (hb l x)
  have hD : 0 ≤ symbolDerivativeConstant K^K := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  have hF := angularOriginalSpatialKernel_integrable μ (β 0) (β 1) (hβ 0) (hβ 1)
    hD hD (hbd 0) (hbd 1) v hΨ.continuous.measurable hs hW
    (fun t => by rw [abs_of_nonneg (hpos t)]; exact hw t)
  refine ⟨hF.integrableOn,?_⟩
  have he : ∀ᵐ z ∂μ.restrict Z, ‖angularOriginalSpatialKernel (β 0) (β 1) v Ψ z‖ ≤ ((2:ℝ)^N)^(-T) := by
    filter_upwards [hgeom] with z hz
    have hh := h₀ N hN S b k hcard hK L hLN hL Q hQ ρ m lam J i hsp hm
      ![z 0,z 2] ![z 1,z 3] (fun l => hb l _) (fun l => hb l _)
      v h L₀ hv hLL hL₀ hz
    have hzeta : (![z 0,z 1,z 2,z 3] : Fin 4 → Plane) = z := by
      funext l; fin_cases l <;> rfl
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons,hzeta] using hh
  simpa only [Measure.real,Measure.restrict_apply_univ] using norm_integral_le_of_norm_le_const he

end PlanarFalconer

end OAI
