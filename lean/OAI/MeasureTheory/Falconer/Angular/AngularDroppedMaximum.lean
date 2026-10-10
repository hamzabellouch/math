import OAI.MeasureTheory.Falconer.Graphs.ActualProductEnergyFinite
import OAI.MeasureTheory.Falconer.Angular.ActualAngularDropping

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal ContDiff

theorem finiteEnergyMaximum_le_mul {ι : Type*} (S : Finset ι) (E F : ι → ℝ≥0∞)
    {c : ℝ} (hc : 0 ≤ c) (hb : ∀ i ∈ S, (E i).toReal ≤ c*(F i).toReal) :
    finiteEnergyMaximum S E ≤ c*finiteEnergyMaximum S F := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨i,hi,he⟩ := finiteEnergyMaximum_attained S hs E
    rw [he]
    exact (hb i hi).trans (mul_le_mul_of_nonneg_left (le_finiteEnergyMaximum S F hi) hc)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he,finiteEnergyMaximum_empty]

noncomputable def remainingAngularEnergy
    {ι : Fin 2 → Type} (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor)
    (k : ∀ l, ι l → ℕ) (Q : Fin 2 → DyadicSquare) (ρ : Fin 2 → Measure Plane)
    (mass : Fin 2 → ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Fin 2 → Plane → ℂ)
    (M₁ M₂ p v : ℝ) (Ψ : ℝ → ℝ) (row : CellPath × CellPath) : ℝ≥0∞ :=
  sourceAngularH p v Ψ
    (fun z => sourceAngularTransform (ρ 0) ((Q 0).descendant row.1).carrier M₁
      (inheritedCircleSymbol ((S 0).filter (fun c => row.1.length < descriptorAnchor (d 0 c)))
        (d 0) (k 0) (Q 0) (ρ 0) (mass 0) N lam sig J i (h 0)) z.1 z.2)
    (fun z => sourceAngularTransform (ρ 1) ((Q 1).descendant row.2).carrier M₂
      (inheritedCircleSymbol ((S 1).filter (fun c => row.2.length < descriptorAnchor (d 1 c)))
        (d 1) (k 1) (Q 1) (ρ 1) (mass 1) N lam sig J i (h 1)) z.1 z.2)

theorem inherited_product_energy_drop_real
    {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)]
    (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor)
    (k : ∀ l, ι l → ℕ) (K : ℕ) (hK : ∀ l, (∑ t ∈ S l, k l t) ≤ K)
    (Q : Fin 2 → DyadicSquare) (hQ : ∀ l, 0 < (Q l).side)
    (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)]
    (mass : Fin 2 → ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (row : CellPath × CellPath) (p v : ℝ) {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let E := sourceAngularH p v Ψ
      (fun z => sourceAngularTransform (ρ 0) ((Q 0).descendant row.1).carrier M₁ (β 0) z.1 z.2)
      (fun z => sourceAngularTransform (ρ 1) ((Q 1).descendant row.2).carrier M₂ (β 1) z.1 z.2)
    let F := remainingAngularEnergy S d k Q ρ mass N lam sig J i h M₁ M₂ p v Ψ row
    F ≠ ⊤ ∧ E.toReal ≤ (symbolDerivativeConstant K^K)^4*F.toReal := by
  classical
  let P : Fin 2 → CellPath := ![row.1,row.2]
  let S' := fun l => (S l).filter (fun c => (P l).length < descriptorAnchor (d l c))
  have hb (l : Fin 2) : (∑ t ∈ S' l, k l t) ≤ K :=
    remaining_symbol_budget (S l) (d l) (k l) (P l).length K (hK l)
  have hf := inherited_product_energy_finite S' d k K hb Q hQ ρ mass N lam sig J i h hh hhb
    ((Q 0).descendant row.1).carrier ((Q 1).descendant row.2).carrier p v hM₁ hM₂ hΨ hpos hs
  have hdrop := actual_inherited_H_drop (S 0) (S 1) (d 0) (d 1) (k 0) (k 1) (Q 0) (Q 1)
    (hQ 0) (hQ 1) (ρ 0) (ρ 1) (mass 0) (mass 1) N lam sig J i row.1 row.2 (h 0) (h 1)
    K K (hK 0) (hK 1)
    (((Q 0).descendant row.1).center_mem ((Q 0).descendant_side_pos (hQ 0) row.1))
    (((Q 1).descendant row.2).center_mem ((Q 1).descendant_side_pos (hQ 1) row.2)) M₁ M₂ p v Ψ
  dsimp only
  have hf' : remainingAngularEnergy S d k Q ρ mass N lam sig J i h M₁ M₂ p v Ψ row ≠ ⊤ := hf
  refine ⟨hf',?_⟩
  have hn : 0 ≤ symbolDerivativeConstant K^K := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) hf') hdrop
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofReal hn] at ht
  convert ht using 1
  ring

end PlanarFalconer

end OAI
