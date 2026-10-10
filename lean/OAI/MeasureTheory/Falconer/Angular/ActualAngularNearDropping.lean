import OAI.MeasureTheory.Falconer.Angular.ActualAngularNear
import OAI.MeasureTheory.Falconer.Angular.AngularDroppedMaximum

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem actual_angular_near_dropped
    {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)] (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor)
    (k : ∀ l, ι l → ℕ) (K : ℕ) (hK : ∀ l, (∑ t ∈ S l, k l t) ≤ K)
    (Q : Fin 2 → DyadicSquare) (hQ : ∀ l, (Q l).side = 1)
    (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (N B₀ : ℕ) (hN : 0 < N)
    (δ lam sig : ℝ) (hd : ∀ l, RegularizedProfileData (Q l) (ρ l) N B₀ δ lam (mass l))
    (J i : ℕ) (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (A B : CellPath) (a n : ℕ) (hA : A.length = a) (hB : B.length = a) (hp : a+n ≤ N)
    (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    let R := (2:ℝ)^N
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l (p : ℝ) => R^(-mass l p)
    let U := angularCellTransform (Q 0) (ρ 0) (M 0 a) (β 0) A
    let V := angularCellTransform (Q 1) (ρ 1) (M 1 a) (β 1) B
    let E := fun row : CellPath × CellPath => sourceAngularH (a+n) v Ψ
      (angularCellTransform (Q 0) (ρ 0) (M 0 (a+n)) (β 0) row.1)
      (angularCellTransform (Q 1) (ρ 1) (M 1 (a+n)) (β 1) row.2)
    let F := remainingAngularEnergy S d k Q ρ mass N lam sig J i h
      (M 0 (a+n)) (M 1 (a+n)) (a+n) v Ψ
    let near := angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B n a v Ψ
      (M 0 a) (M 1 a) (M 0 (a+n)) (M 1 (a+n)) (β 0) (β 1) (angularNear (Q 0) (Q 1) (a+n))
    let far := angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B n a v Ψ
      (M 0 a) (M 1 a) (M 0 (a+n)) (M 1 (a+n)) (β 0) (β 1)
      (fun row col => ¬ angularNear (Q 0) (Q 1) (a+n) row col)
    sourceAngularH a v Ψ U V ≠ ⊤ ∧ (∀ row, E row ≠ ⊤) ∧ (∀ row, F row ≠ ⊤) ∧
      ((sourceAngularH a v Ψ U V).toReal : ℂ) = near+far ∧
      ‖near‖ ≤ 15352201216*(symbolDerivativeConstant K^K)^4*R^(
        -(mass 0 (a+n)-((a:ℝ)+n)/N-(mass 0 a-(a:ℝ)/N))
        -(mass 1 (a+n)-((a:ℝ)+n)/N-(mass 1 a-(a:ℝ)/N))+12*lam)*
        finiteEnergyMaximum (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n) F := by
  classical
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  have hQpos (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; norm_num
  have hk := actual_angular_near_fixed S d k K hK Q hQ ρ mass N B₀ hN δ lam sig hd
    J i h hh hhb A B a n hA hB hp v hΨ hpos hs
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  let M := fun l (p : ℝ) => ((2:ℝ)^N)^(-mass l p)
  let E := fun row : CellPath × CellPath => sourceAngularH (a+n) v Ψ
    (angularCellTransform (Q 0) (ρ 0) (M 0 (a+n)) (β 0) row.1)
    (angularCellTransform (Q 1) (ρ 1) (M 1 (a+n)) (β 1) row.2)
  let F := remainingAngularEnergy S d k Q ρ mass N lam sig J i h
    (M 0 (a+n)) (M 1 (a+n)) (a+n) v Ψ
  have hdrop (row : CellPath × CellPath) : F row ≠ ⊤ ∧
      (E row).toReal ≤ (symbolDerivativeConstant K^K)^4*(F row).toReal :=
    inherited_product_energy_drop_real S d k K hK Q hQpos ρ mass N lam sig J i h hh hhb row
      (a+n) v (by dsimp [M]; positivity) (by dsimp [M]; positivity) hΨ hpos hs
  have hmax := finiteEnergyMaximum_le_mul (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n)
    E F (by positivity : 0 ≤ (symbolDerivativeConstant K^K)^4) (fun row _ => (hdrop row).2)
  dsimp only at hk ⊢
  refine ⟨hk.1,hk.2.1,(fun row => (hdrop row).1),hk.2.2.1,hk.2.2.2.trans ?_⟩
  apply (mul_le_mul_of_nonneg_left hmax (by positivity)).trans_eq
  ring

end PlanarFalconer

end OAI
