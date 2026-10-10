import OAI.MeasureTheory.Falconer.Estimates.ActualProductEquation13

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

theorem finiteEnergyMaximum_empty {ι : Type*} (E : ι → ℝ≥0∞) :
    finiteEnergyMaximum ∅ E = 0 := by simp [finiteEnergyMaximum]

theorem finiteEnergyMaximum_attained {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (E : ι → ℝ≥0∞) : ∃ i ∈ S, finiteEnergyMaximum S E = (E i).toReal := by
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup S hS (fun i => (E i).toNNReal)
  refine ⟨i,hi,?_⟩
  exact congrArg (fun x : ℝ≥0 => (x:ℝ)) he

theorem inherited_product_energy_finite
    {ι : Fin 2 → Type} (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor)
    (k : ∀ l, ι l → ℕ) (K : ℕ) (hK : ∀ l, (∑ t ∈ S l, k l t) ≤ K)
    (Q : Fin 2 → DyadicSquare) (hQ : ∀ l, 0 < (Q l).side)
    (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)]
    (mass : Fin 2 → ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (X Y : Set Plane) (p v : ℝ) {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    sourceAngularH p v Ψ
      (fun z => sourceAngularTransform (ρ 0) X M₁ (β 0) z.1 z.2)
      (fun z => sourceAngularTransform (ρ 1) Y M₂ (β 1) z.1 z.2) ≠ ⊤ := by
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  have hm (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l) (hh l)
  have hb : ∀ (l : Fin 2) (x : Plane) (dir : UnitCircle), ‖β l x dir‖ ≤ symbolDerivativeConstant K^K := by
    intro l x dir
    exact inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQ l) (ρ l) (mass l) N lam sig J i (h l)
      K (hK l) x (hhb l x) dir
  obtain ⟨W,hW,hw⟩ := continuous_supported_bump_bound hΨ.continuous hs
  exact (sourceAngularH_original_four_transform p v hΨ.continuous.measurable hpos hs hW
    (fun t => (le_abs_self _).trans (hw t)) (ρ 0) (ρ 1) X Y hM₁ hM₂ (β 0) (β 1) (hm 0) (hm 1)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K) (hb 0) (hb 1)).1

end PlanarFalconer

end OAI
