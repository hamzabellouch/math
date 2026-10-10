import OAI.Combinatorics.Progressions.Estimates.NativeAnchoredSquarePartition
import OAI.Combinatorics.Progressions.Nilpotent.NativeSquareNiltest

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

def NativeAnchoredSquareNiltestsSpec (s a C : ℕ) : Prop :=
    ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      (T : D.Niltest (fun _ : Unit => 1)) (c : ℤ) (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → T.ComplexityLE p → (q : ℝ) ≤ Real.exp p →
      0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ (dQ : ℕ) (Q : RationalFilteredNilmanifold (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) s dQ) (weight : Fin dQ → ℕ),
        (∀ j, Q.filtration.layer j = Submodule.span ℚ (Q.basis '' {i | j ≤ weight i})) ∧
        Q.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ 1 / δ ≤ Real.exp ((p + C) ^ C) ∧
        ∃ n k : ℕ, 0 < n ∧ 0 < k ∧
          (Fintype.card ((Fin n × ZMod q) × Fin k) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : ((Fin n × ZMod q) × Fin k) → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} (s + 1) N ((p + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            (∀ j x, 0 < A j x → (x.val : ZMod q) = j.1.2) ∧
            (∀ j x y, 0 < A j x → 0 < A j y →
              dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ δ) ∧
            (∀ h : ZMod N, ((cyclicWrapExceptional h δ).card : ℝ) / N ≤ 6 * δ + 3 / N) ∧
            letI := Q.metricSpace
            ∀ χ : D.RealGroup → CircleFourier.Circle,
              (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
                T.observable (z • x) = CircleFourier.character (χ z) * T.observable x) →
              ∀ (h : ZMod N) (branch : Fin 2), ∃ S : Q.Niltest (fun _ : Unit => 1),
                S.normBound = T.normBound ^ 2 ∧ S.ComplexityLE ((p + C) ^ C) ∧
                (∀ z : Unit → ℤ, S.eval z =
                  T.eval (z + fun _ => (h.val : ℤ) - (branch.val : ℤ) * N) *
                    star (T.eval (z + fun _ => c))) ∧
                ∀ i j x y,
                  x ∉ cyclicWrapExceptional h δ → y ∉ cyclicWrapExceptional h δ →
                  0 < A i x * A j (x + h) → 0 < A i y * A j (y + h) →
                  dist (Q.cyclicOrbitPoint S.orbit N (fun _ : Unit => x))
                    (Q.cyclicOrbitPoint S.orbit N (fun _ : Unit => y)) ≤ ε

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

theorem exists_native_anchored_square_niltests (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeAnchoredSquareNiltestsSpec s a C := by
  obtain ⟨B, _, hpartition⟩ := exists_native_anchored_square_partition s a
  let R : ℕ := Classical.choose (exists_specified_square_niltest.{0, 0} s)
  have hconstruct := @(Classical.choose_spec (exists_specified_square_niltest.{0, 0} s)).2
  let X : Polynomial ℕ := Polynomial.X
  let U := X + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + (U + Polynomial.C R) ^ R)
  refine ⟨C, hC, ?_⟩
  dsimp only [NativeAnchoredSquareNiltestsSpec]
  intro L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ T c q N _ _ p ε hp hT hq hε hε1 hεinv
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨b, v, hF, M, hM, hin, hout, hb, hV, hQ, δ, hδ, hδε, hδinv,
      n, k, hn, hk, hcount, A, hA, hsum, hres, hcircle, hexception, hblocks⟩ :=
    hpartition D T.orbit c q N hp hT.1 hq hε hε1 hεinv
  let bs := D.filtration.squareFinBasis b v (hF 2)
  let vs := squareFinWeight v
  let hls := D.filtration.squareFinBasis_layers b v hF
  let V := D.filtration.squareFiltration.ofAdaptedBasis bs vs hls
    (D.filtration.squareLattice D.lattice) M hM hin hout
  let Q := D.filtration.squareFiltration.topQuotientModel bs vs hls
    (D.filtration.squareLattice D.lattice) M hM hin hout
  let r := p + (p + B) ^ B
  have hpr : p ≤ r := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hBr : (p + B) ^ B ≤ r := le_add_of_nonneg_left hp0
  have hr : 0 ≤ r := hp0.trans hpr
  have htotal : r + (r + R) ^ R ≤ (p + C) ^ C := by
    simpa [X, U, r, Polynomial.eval₂_pow] using hbudget p hp0
  have hrC : r ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans htotal
  have hBC : (p + B) ^ B ≤ (p + C) ^ C := hBr.trans hrC
  have hRC : (r + R) ^ R ≤ (p + C) ^ C := (le_add_of_nonneg_left hr).trans htotal
  refine ⟨_, Q, quotientFinWeight vs {i | s + 1 ≤ vs i}, ?_, hQ.mono Q hBC,
    δ, hδ, hδε, hδinv.trans (Real.exp_le_exp.mpr hBC), n, k, hn, hk,
    hcount.trans (Real.exp_le_exp.mpr hBC), A,
    fun j => (hA j).mono le_rfl hBC, hsum, hres, hcircle, hexception, ?_⟩
  · exact D.filtration.squareFiltration.quotientFinBasis_layers bs vs hls
      (D.filtration.squareFiltration.layerIdeal (s + 1)) le_rfl
      {i | s + 1 ≤ vs i} (hls (s + 1))
  let := Q.metricSpace
  intro χ hvert h branch
  obtain ⟨η, γ, rSq, hγ, hη, hnorm, hcell⟩ := hblocks h branch
  obtain ⟨S, horbit, _, hSNorm, hSComplexity, hSval⟩ :=
    hconstruct D b v hF M hM hin hout T hr (hT.mono hpr) (hV.mono V hBr)
      (fun i j => (hb i j).trans hBr) η
      (fun i => (hη i).trans (Real.exp_le_exp.mpr hBr)) rSq χ hvert
  refine ⟨S, hSNorm, hSComplexity.mono hRC, ?_, ?_⟩
  · intro z
    exact (hSval z).trans (D.filtration.realSquareObservable_recovers_product D.lattice η γ
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (z + fun _ => (h.val : ℤ) - (branch.val : ℤ) * N) T.orbit)
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (z + fun _ => c) T.orbit) hγ T.observable
      (D.filtration.squareFiltration.realification.polynomialOrbitEval
        (fun _ : Unit => 1) z rSq) (hnorm z).1 (hnorm z).2)
  · intro i j x y hx hy hxy hyy
    have hpoint (z : ZMod N) : Q.cyclicOrbitPoint S.orbit N (fun _ : Unit => z) =
        Q.cyclicOrbitPoint
          (D.filtration.squareFiltration.realQuotientPolynomialOrbit
            (D.filtration.squareFiltration.layerIdeal (s + 1)) le_rfl rSq) N
          (fun _ : Unit => z) :=
      congrArg (fun g => Q.cyclicOrbitPoint g N (fun _ : Unit => z)) horbit
    exact (congrArg₂ (fun u v : Q.Space => dist u v) (hpoint x) (hpoint y)).trans_le
      (hcell i j x y hx hy hxy hyy)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
