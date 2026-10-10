import OAI.MeasureTheory.Falconer.Angular.AngularTerminalBound

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem actual_inherited_angular_terminal
    {ι : Fin 2 → Type} (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor)
    (k : ∀ l, ι l → ℕ) (K : ℕ) (hK : ∀ l, (∑ t ∈ S l, k l t) ≤ K)
    (Q : Fin 2 → DyadicSquare) (hQ : ∀ l, 0 < (Q l).side)
    (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (N B : ℕ) (δ lam sig : ℝ)
    (hd : ∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l))
    (J i : ℕ) (h : Fin 2 → Plane → ℂ) (hh : ∀ l, Measurable (h l)) (hhb : ∀ l x, ‖h l x‖ ≤ 1)
    (a q : ℕ) (ha : a ≤ N) (A : Fin 2 → CellPath) (hA : ∀ l, (A l).length = a)
    (v : ℝ) (hv : v-a ≤ 100*q) (Ψ : ℝ → ℝ)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) (hs : ∀ t, 4 < t → Ψ t = 0) :
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let U := fun l => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ l) ((Q l).descendant (A l)).carrier (((2:ℝ)^N)^(-mass l a)) (β l) z.1 z.2
    sourceAngularH a v Ψ (U 0) (U 1) ≠ ⊤ ∧
    (sourceAngularH a v Ψ (U 0) (U 1)).toReal ≤
      (4*W*(symbolDerivativeConstant K^K)^4*(sourceArcLength.real univ)^2) *
        (2:ℝ)^(200*(q:ℝ)) * ((2:ℝ)^N)^(12*lam) := by
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  let U := fun l => fun z : ℝ × UnitCircle =>
    sourceAngularTransform (ρ l) ((Q l).descendant (A l)).carrier (((2:ℝ)^N)^(-mass l a)) (β l) z.1 z.2
  let C := symbolDerivativeConstant K^K
  have hC : 0 ≤ C := pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K
  have hm (l : Fin 2) : Measurable (U l) := measurable_sourceAngularTransform _ _ _ _
    (measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l) (hh l))
  have hb (l : Fin 2) (z : ℝ × UnitCircle) : ‖U l z‖ ≤ C*((2:ℝ)^N)^(3*lam) := by
    have ht := sourceAngularTransform_norm_le (ρ l) ((Q l).descendant (A l)).carrier
      (((2:ℝ)^N)^(-mass l a)) (by positivity) (β l) C
      (fun x _ dir => inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQ l) (ρ l)
        (mass l) N lam sig J i (h l) K (hK l) x (hhb l x) dir) z.1 z.2
    apply ht.trans
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((hd l).normalized_cell_mass_le ha (hA l)) hC
  have he := sourceAngularH_uniform_bound a v Ψ hW hw hs (U 0) (U 1) (hm 0) (hm 1)
    (by positivity) (by positivity) (hb 0) (hb 1)
  have hp : (((2:ℝ)^N)^(3*lam))^4 = ((2:ℝ)^N)^(12*lam) := by
    rw [← Real.rpow_natCast _ 4,← Real.rpow_mul (by positivity : (0:ℝ) ≤ (2:ℝ)^N)]
    congr 1
    norm_num
    ring
  have houter : (2:ℝ)^(2*(v-a)) ≤ (2:ℝ)^(200*(q:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  refine ⟨he.1,he.2.trans ?_⟩
  calc
    _ = (4*W*C^4*(sourceArcLength.real univ)^2) * (2:ℝ)^(2*(v-a)) * (((2:ℝ)^N)^(3*lam))^4 := by ring
    _ ≤ (4*W*C^4*(sourceArcLength.real univ)^2) * (2:ℝ)^(200*(q:ℝ)) * (((2:ℝ)^N)^(3*lam))^4 := by
      gcongr
    _ = _ := by rw [hp]

end PlanarFalconer

end OAI
