import OAI.MeasureTheory.Falconer.Angular.ActualAngularNearDropping

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_angular_near_equation23 (K : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀     {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor)
    (k : ∀ l, ι l → ℕ) (_hK : ∀ l, (∑ t ∈ S l, k l t) ≤ K)
    (Q : Fin 2 → DyadicSquare) (_hQ : ∀ l, (Q l).side = 1)
    (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (B₀ : ℕ)
    (δ lam sig : ℝ) (_hd : ∀ l, RegularizedProfileData (Q l) (ρ l) N B₀ δ lam (mass l))
    (J i : ℕ) (h : Fin 2 → Plane → ℂ) (_hh : ∀ l, Measurable (h l)) (_hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (A B : CellPath) (a n : ℕ) (_hA : A.length = a) (_hB : B.length = a) (_hp : a+n ≤ N)
    (v : ℝ) {Ψ : ℝ → ℝ} (_hΨ : ContDiff ℝ ∞ Ψ) (_hpos : ∀ t, 0 ≤ Ψ t)
    (_hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4),
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
      ‖near‖ ≤ R^(
        -(mass 0 (a+n)-((a:ℝ)+n)/N-(mass 0 a-(a:ℝ)/N))
        -(mass 1 (a+n)-((a:ℝ)+n)/N-(mass 1 a-(a:ℝ)/N))+12*lam+η)*
        finiteEnergyMaximum (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n) F := by
  obtain ⟨N₁,habs⟩ := fixed_constant_absorbed hη (15352201216*(symbolDerivativeConstant K^K)^4)
  refine ⟨max 1 N₁,?_⟩
  intro N hN ι inst S d k hK Q hQ ρ mass B₀ δ lam sig hd J i h hh hhb A B a n hA hB hp v Ψ hΨ hpos hs
  have hNpos : 0 < N := lt_of_lt_of_le (by omega : 0 < max 1 N₁) hN
  have hk := actual_angular_near_dropped S d k K hK Q hQ ρ mass N B₀ hNpos δ lam sig hd
    J i h hh hhb A B a n hA hB hp v hΨ hpos hs
  have hc := habs N ((le_max_right _ _).trans hN)
  dsimp only at hk ⊢
  refine ⟨hk.1,hk.2.1,hk.2.2.1,hk.2.2.2.1,hk.2.2.2.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (finiteEnergyMaximum_nonneg _ _)
  apply (mul_le_mul_of_nonneg_right hc (by positivity)).trans_eq
  rw [← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
  congr 1
  ring

end PlanarFalconer

end OAI
