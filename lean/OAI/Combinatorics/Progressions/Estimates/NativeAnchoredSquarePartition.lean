import OAI.Combinatorics.Progressions.Dynamics.NativeSquarePathRecovery
import OAI.Combinatorics.Progressions.Estimates.RecoveryPrecision
import OAI.Combinatorics.Progressions.Geometry.NativeTopQuotientMetric
import OAI.Combinatorics.Progressions.Sampling.AnchoredObservationPartition

namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

def NativeReducedSquareRecoverySpec (s C : ℕ) : Prop :=
    ∀ {L : Type u} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
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
        D.filtration.squareFiltration.layerIdeal (s + 1)))] {p : ℝ},
      2 ≤ p → D.GeometryComplexityLE p →
      ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
        (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
        (m : ℕ) (hm : 0 < m)
        (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates
          (D.filtration.squareFinBasis b w (hF 2)) (D.filtration.squareLattice D.lattice))
        (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b w (hF 2))
          (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid m),
        let V := D.filtration.squareFiltration.ofAdaptedBasis
          (D.filtration.squareFinBasis b w (hF 2)) (NilpotentLieFiltration.squareFinWeight w)
          (D.filtration.squareFinBasis_layers b w hF)
          (D.filtration.squareLattice D.lattice) m hm hin hout
        let Q := D.filtration.squareFiltration.topQuotientModel
          (D.filtration.squareFinBasis b w (hF 2)) (NilpotentLieFiltration.squareFinWeight w)
          (D.filtration.squareFinBasis_layers b w hF)
          (D.filtration.squareLattice D.lattice) m hm hin hout
        (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        V.GeometryComplexityLE ((p + C) ^ C) ∧ Q.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ (Δ : Bool → Subgroup D.filtration.Group) (l : Bool → ℕ)
          (hl : ∀ i, 0 < l i)
          (hlin : ∀ i, scaledIntegerGrid (l i) ⊆ bchSubgroupCoordinates D.basis (Δ i))
          (hlout : ∀ i, bchSubgroupCoordinates D.basis (Δ i) ⊆ denominatorGrid (l i)),
          let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
          (∀ i, Δ i ≤ D.lattice ∧ ((Δ i).subgroupOf D.lattice).Characteristic ∧
            ((Δ i).subgroupOf D.lattice).Normal ∧ ((Δ i).subgroupOf D.lattice).FiniteIndex ∧
            ((Δ i).relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
          letI : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
          letI := Q.metricSpace
          ∀ {σ : Type v} (ω : σ → ℕ), (∀ i, 0 < ω i) →
            ∀ (g : D.filtration.realification.PolynomialOrbit ω) (a b : σ → ℤ),
            ∃ (ε γ : D.RealGroup) (q : D.filtration.squareFiltration.realification.PolynomialOrbit ω),
              γ ∈ D.realLattice ∧
              (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (∀ x : σ → ℤ,
                D.filtration.realSquareFstHom
                  (D.filtration.squareFiltration.realification.polynomialOrbitEval ω x q) =
                    ε⁻¹ * D.filtration.realification.polynomialOrbitEval ω (x + a) g * γ⁻¹ ∧
                D.filtration.realSquareSndHom
                  (D.filtration.squareFiltration.realification.polynomialOrbitEval ω x q) =
                    D.filtration.realification.polynomialOrbitEval ω (x + b) g) ∧
              ∀ (x y : σ → ℤ) (ρ : ℝ), 0 ≤ ρ → ρ ≤ Real.exp (-((p + C) ^ C)) →
                dist (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval ω (x + a) g) :
                  (E true).Space)
                  (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval ω (y + a) g)) ≤ ρ →
                dist (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval ω (x + b) g) :
                  (E false).Space)
                  (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval ω (y + b) g)) ≤ ρ →
                dist (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitEval ω x
                    (D.filtration.squareFiltration.realQuotientPolynomialOrbit
                      (D.filtration.squareFiltration.layerIdeal (s + 1)) le_rfl q)) : Q.Space)
                  (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitEval ω y
                    (D.filtration.squareFiltration.realQuotientPolynomialOrbit
                      (D.filtration.squareFiltration.layerIdeal (s + 1)) le_rfl q))) ≤
                    Real.exp ((p + C) ^ C) * ρ

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

theorem exists_native_reduced_square_recovery (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeReducedSquareRecoverySpec.{u, v} s C := by
  let B : ℕ := Classical.choose (exists_native_square_path_recovery.{u, v} (s + 1))
  have hrec := @(Classical.choose_spec (exists_native_square_path_recovery.{u, v} (s + 1))).2
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + 2) ^ 2)
  refine ⟨C, hC, ?_⟩
  dsimp only [NativeReducedSquareRecoverySpec]
  intro L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp hD
  obtain ⟨b, w, hF, m, hm, hin, hout, hb, hV, Δ, l, hl, hlin, hlout, hindex, hE, hpaths⟩ :=
    hrec D hp hD
  let V := D.filtration.squareFiltration.ofAdaptedBasis
    (D.filtration.squareFinBasis b w (hF 2)) (NilpotentLieFiltration.squareFinWeight w)
    (D.filtration.squareFinBasis_layers b w hF)
    (D.filtration.squareLattice D.lattice) m hm hin hout
  let Q := D.filtration.squareFiltration.topQuotientModel
    (D.filtration.squareFinBasis b w (hF 2)) (NilpotentLieFiltration.squareFinWeight w)
    (D.filtration.squareFinBasis_layers b w hF)
    (D.filtration.squareLattice D.lattice) m hm hin hout
  let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
  let r := (p + B) ^ B
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : r + (r + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p (by linarith)
  have hrC : r ≤ (p + C) ^ C := (le_add_of_nonneg_right (sq_nonneg _)).trans htotal
  have hQ := D.filtration.squareFiltration.topQuotientModel_geometry
    (D.filtration.squareFinBasis b w (hF 2)) (NilpotentLieFiltration.squareFinWeight w)
    (D.filtration.squareFinBasis_layers b w hF)
    (D.filtration.squareLattice D.lattice) m hm hin hout hr hV
  refine ⟨b, w, hF, m, hm, hin, hout, fun i j => (hb i j).trans hrC,
    hV.mono V hrC, hQ.mono Q hrC,
    Δ, l, hl, hlin, hlout, ?_, fun i => (hE i).mono (E i) hrC, ?_⟩
  · intro i
    rcases hindex i with ⟨hle, hchar, hnormal, hfinite, hi⟩
    exact ⟨hle, hchar, hnormal, hfinite, hi.trans (Real.exp_le_exp.mpr hrC)⟩
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  let := V.metricSpace
  let := Q.metricSpace
  intro σ ω hω g shiftA shiftB
  obtain ⟨ε, γ, q, hγ, hε, hq, hpath⟩ := hpaths ω hω g shiftA shiftB
  refine ⟨ε, γ, q, hγ, fun i => (hε i).trans (Real.exp_le_exp.mpr hrC), hq, ?_⟩
  intro x y ρ hρ hsmall hfirst hsecond
  have hsquare := hpath x y ρ hρ
    (hsmall.trans (Real.exp_le_exp.mpr (neg_le_neg hrC))) hfirst hsecond
  have hquot := D.filtration.squareFiltration.topQuotientModel_orbit_dist_le
    (D.filtration.squareFinBasis b w (hF 2)) (NilpotentLieFiltration.squareFinWeight w)
    (D.filtration.squareFinBasis_layers b w hF)
    (D.filtration.squareLattice D.lattice) m hm hin hout hr hV q x y
  apply hquot.trans
  calc
    _ ≤ Real.exp ((r + 2) ^ 2) * (Real.exp r * ρ) :=
      mul_le_mul_of_nonneg_left hsquare (Real.exp_pos _).le
    _ = Real.exp (r + (r + 2) ^ 2) * ρ := by
      rw [← mul_assoc, ← Real.exp_add, add_comm ((r + 2) ^ 2) r]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr htotal) hρ

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

def NativeAnchoredSquarePartitionSpec (s a C : ℕ) : Prop :=
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
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (c : ℤ) (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → D.GeometryComplexityLE p → (q : ℝ) ≤ Real.exp p →
      0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
        (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
        (m : ℕ) (hm : 0 < m)
        (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates
          (D.filtration.squareFinBasis b w (hF 2)) (D.filtration.squareLattice D.lattice))
        (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b w (hF 2))
          (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid m),
        let V := D.filtration.squareFiltration.ofAdaptedBasis
          (D.filtration.squareFinBasis b w (hF 2)) (NilpotentLieFiltration.squareFinWeight w)
          (D.filtration.squareFinBasis_layers b w hF)
          (D.filtration.squareLattice D.lattice) m hm hin hout
        let Q := D.filtration.squareFiltration.topQuotientModel
          (D.filtration.squareFinBasis b w (hF 2)) (NilpotentLieFiltration.squareFinWeight w)
          (D.filtration.squareFinBasis_layers b w hF)
          (D.filtration.squareLattice D.lattice) m hm hin hout
        (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        V.GeometryComplexityLE ((p + C) ^ C) ∧ Q.GeometryComplexityLE ((p + C) ^ C) ∧
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
            ∀ (h : ZMod N) (branch : Fin 2),
              ∃ (η γ : D.RealGroup)
                (r : D.filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1)),
                γ ∈ D.realLattice ∧
                (∀ i, |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
                (∀ z : Unit → ℤ,
                  D.filtration.realSquareFstHom
                    (D.filtration.squareFiltration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) z r) =
                    η⁻¹ * D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                      (z + fun _ => (h.val : ℤ) - (branch.val : ℤ) * N) g * γ⁻¹ ∧
                  D.filtration.realSquareSndHom
                    (D.filtration.squareFiltration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) z r) =
                    D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                      (z + fun _ => c) g) ∧
                ∀ i j x y,
                  x ∉ cyclicWrapExceptional h δ → y ∉ cyclicWrapExceptional h δ →
                  0 < A i x * A j (x + h) → 0 < A i y * A j (y + h) →
                  dist (Q.cyclicOrbitPoint
                    (D.filtration.squareFiltration.realQuotientPolynomialOrbit
                      (D.filtration.squareFiltration.layerIdeal (s + 1)) le_rfl r) N
                      (fun _ : Unit => x))
                    (Q.cyclicOrbitPoint
                      (D.filtration.squareFiltration.realQuotientPolynomialOrbit
                        (D.filtration.squareFiltration.layerIdeal (s + 1)) le_rfl r) N
                        (fun _ : Unit => y)) ≤ ε

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

theorem exists_native_anchored_square_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeAnchoredSquarePartitionSpec s a C := by
  obtain ⟨R, _, hrec⟩ := exists_native_reduced_square_recovery.{0, 0} s
  let B : ℕ := Classical.choose (exists_anchored_observation_partition (s + 1) 1)
  have hpartition := @(Classical.choose_spec (exists_anchored_observation_partition (s + 1) 1)).2
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C R) ^ R
  let T := X + U + (X + 2) ^ a + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  dsimp only [NativeAnchoredSquarePartitionSpec]
  intro L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ g c q N _ _ p ε hp hD hq hε hε1 hεinv
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨b, w, hF, M, hM, hin, hout, hb, hV, hQ, Δ, l, hl, hlin, hlout, _, hE, hpaths⟩ :=
    hrec D hp hD
  let V := D.filtration.squareFiltration.ofAdaptedBasis
    (D.filtration.squareFinBasis b w (hF 2)) (NilpotentLieFiltration.squareFinWeight w)
    (D.filtration.squareFinBasis_layers b w hF)
    (D.filtration.squareLattice D.lattice) M hM hin hout
  let Q := D.filtration.squareFiltration.topQuotientModel
    (D.filtration.squareFinBasis b w (hF 2)) (NilpotentLieFiltration.squareFinWeight w)
    (D.filtration.squareFinBasis_layers b w hF)
    (D.filtration.squareLattice D.lattice) M hM hin hout
  let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
  let r := (p + R) ^ R
  let K := (p + 2) ^ a
  let t := p + r + K + 2
  let δ := ε * Real.exp (-r)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hrt : r ≤ t := by dsimp [t]; linarith
  have hkr : K + r ≤ t := by dsimp [t]; linarith
  have ht : 0 ≤ t := hp0.trans hpt
  obtain ⟨hδ, hδε, hδsmall, hδerror, hδinv⟩ := recovery_precision_bounds hr hε hε1 hεinv
  have htotal : t + (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, U, T, r, K, t, Polynomial.eval₂_pow] using hbudget p hp0
  have hcost : (t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans htotal
  have htC : t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans htotal
  have hrC : r ≤ (p + C) ^ C := hrt.trans htC
  let E' : Unit → Bool → RationalFilteredNilmanifold L (s + 1) d := fun _ => E
  let g' : ∀ i b, (E' i b).filtration.realification.PolynomialOrbit (fun _ : Unit => 1) :=
    fun _ _ => g
  have hδinverse : 1 / δ ≤ Real.exp ((t + 2) ^ 1) := by
    apply hδinv.trans (Real.exp_le_exp.mpr _)
    rw [pow_one]
    linarith
  obtain ⟨n, k, hn, hk, hcount, A, hA, hsum, hres, hcircle, hexception, hanchor, hmove⟩ :=
    hpartition E' g' (fun _ => c) q N (Nat.succ_le_succ (Nat.zero_le s)) ht
      (by simpa only [Fintype.card_unit, Nat.cast_one] using
        ((by linarith : 1 ≤ p).trans hpt))
      (fun _ b => (hE b).mono (E b) hrt)
      (hq.trans (Real.exp_le_exp.mpr hpt)) hδ hδinverse
  refine ⟨b, w, hF, M, hM, hin, hout, fun i j => (hb i j).trans hrC,
    hV.mono V hrC, hQ.mono Q hrC,
    δ, hδ, hδε, hδinv.trans (Real.exp_le_exp.mpr (hkr.trans htC)),
    n, k, hn, hk, hcount.trans (Real.exp_le_exp.mpr hcost), A,
    fun j => (hA j).mono le_rfl hcost, hsum, hres, hcircle, hexception, ?_⟩
  let : ∀ b, MetricSpace (E b).Space := fun b => (E b).metricSpace
  let := Q.metricSpace
  intro h branch
  obtain ⟨η, γ, rSq, hγ, hη, hnorm, hrecover⟩ := hpaths (fun _ : Unit => 1)
    (fun _ => Nat.zero_lt_one) g (fun _ => (h.val : ℤ) - (branch.val : ℤ) * N) (fun _ => c)
  refine ⟨η, γ, rSq, hγ, fun i => (hη i).trans (Real.exp_le_exp.mpr hrC), hnorm, ?_⟩
  intro i j x y hx hy hxy hyy
  have hpositive (z : ZMod N) (hz : 0 < A i z * A j (z + h)) : 0 < A i z := by
    rcases mul_pos_iff.mp hz with hz | hz
    · exact hz.1
    · linarith [((hA i).unit_interval z).1]
  have hfirst := hmove h branch i j x y hx hy hxy hyy ()
  change dist ((E true).integerOrbitPoint g ((x.val : ℤ) + h.val - (branch.val : ℤ) * N))
    ((E true).integerOrbitPoint g ((y.val : ℤ) + h.val - (branch.val : ℤ) * N)) ≤ δ at hfirst
  have hsecond := hanchor i x y (hpositive x hxy) (hpositive y hyy) ()
  change dist ((E false).integerOrbitPoint g ((x.val : ℤ) + c))
    ((E false).integerOrbitPoint g ((y.val : ℤ) + c)) ≤ δ at hsecond
  have hbound := hrecover (fun _ => (x.val : ℤ)) (fun _ => (y.val : ℤ)) δ hδ.le hδsmall
    (by
      change dist ((E true).integerOrbitPoint g ((x.val : ℤ) + ((h.val : ℤ) - (branch.val : ℤ) * N)))
        ((E true).integerOrbitPoint g ((y.val : ℤ) + ((h.val : ℤ) - (branch.val : ℤ) * N))) ≤ δ
      simpa only [add_sub_assoc] using hfirst)
    hsecond
  change dist (Q.cyclicOrbitPoint
    (D.filtration.squareFiltration.realQuotientPolynomialOrbit
      (D.filtration.squareFiltration.layerIdeal (s + 1)) le_rfl rSq) N (fun _ : Unit => x))
    (Q.cyclicOrbitPoint
      (D.filtration.squareFiltration.realQuotientPolynomialOrbit
        (D.filtration.squareFiltration.layerIdeal (s + 1)) le_rfl rSq) N (fun _ : Unit => y)) ≤
      Real.exp r * δ at hbound
  exact hδerror ▸ hbound

end Erdos3.RationalFilteredNilmanifold

end

end OAI
