import OAI.MeasureTheory.Falconer.Angular.RegularizedAngularNear
import OAI.MeasureTheory.Falconer.Angular.AngularParentNearFar
import OAI.MeasureTheory.Falconer.Graphs.ActualProductEnergyFinite

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem actual_angular_near_fixed
    {ι : Fin 2 → Type} (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor)
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
    let near := angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B n a v Ψ
      (M 0 a) (M 1 a) (M 0 (a+n)) (M 1 (a+n)) (β 0) (β 1) (angularNear (Q 0) (Q 1) (a+n))
    let far := angularCellContribution (Q 0) (Q 1) (ρ 0) (ρ 1) A B n a v Ψ
      (M 0 a) (M 1 a) (M 0 (a+n)) (M 1 (a+n)) (β 0) (β 1)
      (fun row col => ¬ angularNear (Q 0) (Q 1) (a+n) row col)
    sourceAngularH a v Ψ U V ≠ ⊤ ∧ (∀ row, E row ≠ ⊤) ∧
      ((sourceAngularH a v Ψ U V).toReal : ℂ) = near+far ∧
      ‖near‖ ≤ 15352201216*R^(
        -(mass 0 (a+n)-((a:ℝ)+n)/N-(mass 0 a-(a:ℝ)/N))
        -(mass 1 (a+n)-((a:ℝ)+n)/N-(mass 1 a-(a:ℝ)/N))+12*lam)*
        finiteEnergyMaximum (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n) E := by
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  have hQpos (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; norm_num
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  have hm (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l) (hh l)
  let D := symbolDerivativeConstant K^K
  have hD : 0 ≤ D := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  have hb (l : Fin 2) (x : Plane) (u : UnitCircle) : ‖β l x u‖ ≤ D :=
    inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQpos l) (ρ l) (mass l) N lam sig J i (h l)
      K (hK l) x (hhb l x) u
  obtain ⟨W,hW,hw⟩ := continuous_supported_bump_bound hΨ.continuous hs
  have hw' := fun t => (le_abs_self (Ψ t)).trans (hw t)
  have hparent := angular_parent_near_far (Q 0) (Q 1) (hQpos 0) (hQpos 1) A B (ρ 0) (ρ 1)
    n a v hΨ.continuous.measurable hpos hs hW hw'
    (Ma₁ := ((2:ℝ)^N)^(-mass 0 a)) (Ma₂ := ((2:ℝ)^N)^(-mass 1 a))
    (Mp₁ := ((2:ℝ)^N)^(-mass 0 (a+n))) (Mp₂ := ((2:ℝ)^N)^(-mass 1 (a+n)))
    (by positivity) (by positivity) (by positivity) (by positivity)
    (β 0) (β 1) (hm 0) (hm 1) hD hD (hb 0) (hb 1) (angularNear (Q 0) (Q 1) (a+n))
  have hnear := regularized_angular_near_bound (Q 0) (Q 1) (hQ 0) (hQ 1) (ρ 0) (ρ 1)
    N B₀ hN δ lam (mass 0) (mass 1) (hd 0) (hd 1) A B a n hA hB hp
    (β 0) (β 1) (hm 0) (hm 1) hD hD (hb 0) (hb 1) v hΨ.continuous.measurable hpos hs hW hw'
  dsimp only
  refine ⟨hparent.1,?_,hparent.2,hnear⟩
  intro row
  exact inherited_product_energy_finite S d k K hK Q hQpos ρ mass N lam sig J i h hh hhb
    ((Q 0).descendant row.1).carrier ((Q 1).descendant row.2).carrier (a+n) v
    (by positivity) (by positivity) hΨ hpos hs

end PlanarFalconer

end OAI
