import OAI.Probability.InvariantIsing.Fields.SpinPriorDiagonalStatistics
import OAI.Probability.InvariantIsing.Pressure.PressureCoordinateMinimum

namespace OAI

/-! The spectral self-overlap estimate at a actual quenched constrained-cascade pressure minimum. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

theorem spinPriorDiagonal_energy_at_minimum {N m k n : ℕ} (hN : 0<N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ]
    (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ)
    (eig c : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ)
    (amplitude : Fin k → ℝ) (r : Fin k → ℕ) (h : ℕ → ℝ)
    (hh : Monotone h) (h0 : 0≤h 0) (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w s K B : ℝ)
    (hw : w∈Set.Icc (1 : ℝ) 2) (he : perturbationScale N≤1/32)
    (hs : 0<s) (hs' : s≤1/4) (hK : 0<K)
    (hF : ∀ q : ℝ, |q|≤2 →
      MemLp (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h) 2 ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates))
    (hv : ∀ q : ℝ, |q|≤2 →
      variance (spinPriorNamespacedLog (n := n) π (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h) ((μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates)≤B)
    (hmin :
      let M := fun q => (N : ℝ)⁻¹ * ∫ p, spinPriorNamespacedLog (n := n) π
        (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
        c I degree amplitude r h p ∂(μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
      ∀ q∈Set.Icc (1 : ℝ) 2, -M w+(w-3/2)^2≤-M q+(q-3/2)^2) :
    let A := N*perturbationScale N
    let c₀ := N/A^2
    let P := (μ.prod (labeledCascadeLaw n b : Measure (LabeledTree n))).prod gaussianCoordinates
    let ν := spinPriorNamespacedReference (n := n) π
      (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude
      r h
    let Y := fun p : (TensorFlatDisorder N n) × (Spin N × LabeledLeaf n) =>
      projectedOverlap (specialRotation p.1.1.1) (I a) p.2.1 p.2.1
    let E := fun p : TensorFlatDisorder N n => ∫ x, |Y (p,x)-2*c₀*(A*w-A*(3/2))|
      ∂(ν p).tilted (fun x => A*w*Y (p,x))
    Integrable E P ∧ (∫ p, E p ∂P)≤
      (2*c₀+K^2)/(2*K)+c₀*(A*s)+4*(2*Real.sqrt B)/(A*s) := by
  intro A c₀ P ν Y E
  let Q := P
  let M := fun q => (N : ℝ)⁻¹ * ∫ p, spinPriorNamespacedLog (n := n) π
    (diagonalPerturbedEigenvalues eig I (Function.update v a q) t)
    c I degree amplitude r h p ∂P
  let L := fun z => ∫ p, spinPriorDiagonalCGF π eig c I degree amplitude n r h v t a z p ∂Q
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hA : 0 < A := mul_pos hn (Real.rpow_pos_of_pos hn _)
  have hY : Measurable Y := by
    apply measurable_from_prod_countable_left
    intro x
    exact (measurable_projectedOverlap (I a) x.1 x.1).comp measurable_fst.fst
  have hYb (p : TensorFlatDisorder N n) (x : Spin N × LabeledLeaf n) :
      Y (p, x) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨projectedOverlap_self_nonneg _ _ _, projectedOverlap_self_le_one _ _ _⟩
  have hstat (q : ℝ) (hq : |q| ≤ 2) :=
    spinPriorDiagonalCGF_statistics hN μ π b eig c I degree amplitude r h hh h0 v t a q B
      (fun z hz => by
        rcases hz with hz | hz
        · rw [hz]
          exact hF q hq
        · rw [hz]
          exact hF 0 (by norm_num))
      (fun z hz => by
        rcases hz with hz | hz
        · rw [hz]
          exact hv q hq
        · rw [hz]
          exact hv 0 (by norm_num))
  have hmean (q : ℝ) (hq : |q| ≤ 2) : L (A * q) = N * (M q - M 0) := by
    dsimp only [L,A,Q,P,M]
    rw [(hstat q hq).2.1]
    have hn0 := hn.ne'
    field_simp
  have hcost (q : ℝ) (hq : q ∈ Set.Icc (1 : ℝ) 2) :
      0 ≤ M q - M 0 ∧ M q - M 0 ≤ 2 * perturbationScale N := by
    have hqa : |q| ≤ 2 := abs_le.mpr ⟨by linarith [hq.1], hq.2⟩
    have hqb : ∀ p, 0 ≤ spinPriorDiagonalCGF π eig c I degree amplitude n r h v t a (A * q) p ∧
        spinPriorDiagonalCGF π eig c I degree amplitude n r h v t a (A * q) p ≤ A * q := by
      intro p
      exact bounded_nonnegative_cgf_bounds (ν p) (fun x => Y (p, x))
        (measurable_of_countable _) (hYb p) (mul_nonneg hA.le (by linarith [hq.1]))
    have hlo : 0 ≤ L (A * q) := integral_nonneg (fun p => (hqb p).1)
    have hhi : L (A * q) ≤ A * q := by
      calc
        _ ≤ ∫ _ : TensorFlatDisorder N n, A * q ∂Q :=
          integral_mono ((hstat q hqa).1.integrable (by norm_num)) (integrable_const _) (fun p => (hqb p).2)
        _ = _ := by simp [Q,P]
    rw [hmean q hqa] at hlo hhi
    have hbound := mul_le_mul_of_nonneg_left hq.2 hA.le
    refine ⟨(mul_nonneg_iff_of_pos_left hn).mp hlo, ?_⟩
    dsimp only [A] at hbound hhi
    nlinarith
  have hpen := diagonalCoordinate_minimum_penalty
    ⟨(hcost (3 / 2) (by constructor <;> norm_num)).1, (hcost w hw).2⟩
    (hmin (3 / 2) (by constructor <;> norm_num))
  obtain ⟨hlo, hhi⟩ := diagonalCoordinate_minimum_interior hpen he hs'
  have hlocal := pressureCoordinate_minimum_rescale (Nat.cast_nonneg N) hA hw hlo hhi
    (fun q hq => hmean q (abs_le.mpr ⟨by linarith [hq.1], hq.2⟩))
    (show ∀ q ∈ Set.Icc (1 : ℝ) 2, -M w + 1 * (w - 3 / 2) ^ 2 ≤
      -M q + 1 * (q - 3 / 2) ^ 2 by simpa only [one_mul] using hmin)
  have hconc (z : ℝ) (hz : z ∈ ({A * w - A * s, A * w, A * w + A * s} : Set ℝ)) :
      (∫ p, |spinPriorDiagonalCGF π eig c I degree amplitude n r h v t a z p - L z| ∂Q) ≤
        2 * Real.sqrt B := by
    have hzi : z ∈ Set.Icc (A * w - A * s) (A * w + A * s) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl <;> constructor <;> nlinarith [mul_pos hA hs]
    have hzq : z / A ∈ Set.Icc (1 : ℝ) 2 := by
      constructor
      · apply (le_div_iff₀ hA).mpr
        nlinarith [hzi.1]
      · apply (div_le_iff₀ hA).mpr
        nlinarith [hzi.2]
    have hza : |z / A| ≤ 2 := abs_le.mpr ⟨by linarith [hzq.1], hzq.2⟩
    have hc := (hstat (z / A) hza).2.2
    simpa only [A, mul_div_cancel₀ _ hA.ne'] using hc
  simpa only [mul_one] using boundedObservable_energy_at_minimum Q ν
    (measurable_spinPriorNamespacedReference (n := n) π
      (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) c I degree amplitude r h)
    Y hY 1 (fun p x => projectedOverlap_abs_le_one _ _ _ _)
    (mul_pos hA hs) hK hlocal hconc

end InvariantIsing

end

end OAI
