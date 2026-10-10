import OAI.Combinatorics.Progressions.Nilpotent.NativeAnchoredSquareNiltests

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

def NativeAnchoredSquareFamilySpec (s a C : ℕ) : Prop :=
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      (T : ∀ i, (D i).Niltest (fun _ : Unit => 1)) (c : ι → ℤ)
      (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (∀ i, (T i).ComplexityLE p) →
      (q : ℝ) ≤ Real.exp p → 0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ (dQ : ι → ℕ)
        (Q : ∀ i, RationalFilteredNilmanifold ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1)) s (dQ i))
        (weight : ∀ i, Fin (dQ i) → ℕ),
        (∀ i j, (Q i).filtration.layer j =
          Submodule.span ℚ ((Q i).basis '' {k | j ≤ weight i k})) ∧
        (∀ i, (Q i).GeometryComplexityLE ((p + C) ^ C)) ∧
        ∃ n k : ι → ℕ, (∀ i, 0 < n i ∧ 0 < k i) ∧
        ∃ m : ℕ, 0 < m ∧
          (Fintype.card (((∀ i, (Fin (n i) × ZMod q) × Fin (k i)) × ZMod q) × Fin m) : ℝ)
            ≤ Real.exp ((p + C) ^ C) ∧
          ∃ U : (((∀ i, (Fin (n i) × ZMod q) × Fin (k i)) × ZMod q) × Fin m) → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} (s + 1) N ((p + C) ^ C) (U j)) ∧
            (∀ x, ∑ j, U j x = 1) ∧
            (∀ j x, 0 < U j x → (x.val : ZMod q) = j.1.2) ∧
            (∀ j x y, 0 < U j x → 0 < U j y →
              dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ε) ∧
            (∀ h : ZMod N, ((cyclicWrapExceptional h ε).card : ℝ) / N ≤ 6 * ε + 3 / N) ∧
            letI : ∀ i, MetricSpace (Q i).Space := fun i => (Q i).metricSpace
            ∀ χ : ∀ i, (D i).RealGroup → CircleFourier.Circle,
              (∀ i, ∀ z ∈ (D i).filtration.realification.subgroup (s + 1), ∀ x,
                (T i).observable (z • x) = CircleFourier.character (χ i z) * (T i).observable x) →
              ∀ (h : ZMod N) (branch : ι → Fin 2),
                ∃ S : ∀ i, (Q i).Niltest (fun _ : Unit => 1),
                  (∀ i, (S i).normBound = (T i).normBound ^ 2) ∧
                  (∀ i, (S i).ComplexityLE ((p + C) ^ C)) ∧
                  (∀ i (z : Unit → ℤ), (S i).eval z =
                    (T i).eval (z + fun _ => (h.val : ℤ) - ((branch i).val : ℤ) * N) *
                      star ((T i).eval (z + fun _ => c i))) ∧
                  ∀ i j l x y,
                    x ∉ cyclicWrapExceptional h ε → y ∉ cyclicWrapExceptional h ε →
                    0 < U j x * U l (x + h) → 0 < U j y * U l (y + h) →
                    dist ((Q i).cyclicOrbitPoint (S i).orbit N (fun _ : Unit => x))
                      ((Q i).cyclicOrbitPoint (S i).orbit N (fun _ : Unit => y)) ≤ ε

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_native_anchored_square_family (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeAnchoredSquareFamilySpec s a C := by
  obtain ⟨B, _, hsingle⟩ := exists_native_anchored_square_niltests s a
  obtain ⟨R, _, hcommon⟩ := exists_common_positive_partition_refinement a
  let X : Polynomial ℕ := Polynomial.X
  let V := X + (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (V + (V + Polynomial.C R) ^ R)
  refine ⟨C, hC, ?_⟩
  dsimp only [NativeAnchoredSquareFamilySpec]
  intro ι _ _ L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ T c q N _ _ p ε hp hι hT hq hε hε1 hεinv
  have hp0 : 0 ≤ p := by linarith
  let r := p + (p + B) ^ B
  have hpr : p ≤ r := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hr : 0 ≤ r := hp0.trans hpr
  have hBr : (p + B) ^ B ≤ r := le_add_of_nonneg_left hp0
  have htotal : r + (r + R) ^ R ≤ (p + C) ^ C := by
    simpa [X, V, r, Polynomial.eval₂_pow] using hbudget p hp0
  have hrC : r ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans htotal
  have hBC : (p + B) ^ B ≤ (p + C) ^ C := hBr.trans hrC
  have hRC : (r + R) ^ R ≤ (p + C) ^ C := (le_add_of_nonneg_left hr).trans htotal
  choose dQ Q weight hadapt hQ δ _hδ hδε _hδinv n k hn hk hcount A hA hsum
      _hres _hcircle _hexception hblocks using
    fun i => hsingle (D i) (T i) (c i) q N hp (hT i) hq hε hε1 hεinv
  obtain ⟨m, hm, hUcount, U, hU, hUsum, hUres, hUcircle, hUexception, _, hsupport⟩ :=
    hcommon (q := q) A (by omega) hr (hι.trans hpr)
      (fun i => (hcount i).trans (Real.exp_le_exp.mpr hBr))
      (fun i j => (hA i j).mono le_rfl hBr) hsum
      (hq.trans (Real.exp_le_exp.mpr hpr)) hε
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2)
          (by linarith : p + 2 ≤ r + 2) a)))
  refine ⟨dQ, Q, weight, hadapt, fun i => (hQ i).mono (Q i) hBC,
    n, k, fun i => ⟨hn i, hk i⟩, m, hm, hUcount.trans (Real.exp_le_exp.mpr hRC), U,
    fun j => (hU j).mono le_rfl hRC, hUsum, hUres, hUcircle, hUexception, ?_⟩
  let : ∀ i, MetricSpace (Q i).Space := fun i => (Q i).metricSpace
  intro χ hvert h branch
  choose S hSnorm hScomplexity hSeval hScell using
    fun i => hblocks i (χ i) (hvert i) h (branch i)
  refine ⟨S, hSnorm, fun i => (hScomplexity i).mono hBC, hSeval, ?_⟩
  intro i j l x y hx hy hUx hUy
  exact hScell i (j.1.1 i) (l.1.1 i) x y
    (fun hbad => hx (cyclicWrapExceptional_mono h (hδε i) hbad))
    (fun hbad => hy (cyclicWrapExceptional_mono h (hδε i) hbad))
    (hsupport h j l x hUx i) (hsupport h j l y hUy i)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

def NativeAnchoredInputPartitionSpec (s a C : ℕ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      (E : ∀ j, RationalFilteredNilmanifold (K j) s (e j))
      (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
      (T : ∀ i, (D i).Niltest (fun _ : Unit => 1)) (c : ι → ℤ)
      (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (T i).ComplexityLE p) → (∀ j, (E j).GeometryComplexityLE p) →
      (q : ℝ) ≤ Real.exp p → 0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ (dQ : ι → ℕ)
        (Q : ∀ i, RationalFilteredNilmanifold ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1)) s (dQ i))
        (weight : ∀ i, Fin (dQ i) → ℕ),
        (∀ i j, (Q i).filtration.layer j =
          Submodule.span ℚ ((Q i).basis '' {k | j ≤ weight i k})) ∧
        (∀ i, (Q i).GeometryComplexityLE ((p + C) ^ C)) ∧
        ∃ n k : ι → ℕ, (∀ i, 0 < n i ∧ 0 < k i) ∧
        ∃ m l : ℕ, 0 < m ∧ 0 < l ∧
          (Fintype.card ((((∀ i, (Fin (n i) × ZMod q) × Fin (k i)) × ZMod q) × Fin m) × Fin l) : ℝ)
            ≤ Real.exp ((p + C) ^ C) ∧
          ∃ U : ((((∀ i, (Fin (n i) × ZMod q) × Fin (k i)) × ZMod q) × Fin m) × Fin l) → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} (s + 1) N ((p + C) ^ C) (U j)) ∧
            (∀ x, ∑ j, U j x = 1) ∧
            (∀ j x, 0 < U j x → (x.val : ZMod q) = j.1.1.2) ∧
            (∀ j x y, 0 < U j x → 0 < U j y →
              dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ε) ∧
            (∀ h : ZMod N, ((cyclicWrapExceptional h ε).card : ℝ) / N ≤ 6 * ε + 3 / N) ∧
            (pi (sumFactors E Q)).GeometryComplexityLE ((p + C) ^ C) ∧
            letI : ∀ i, MetricSpace (Q i).Space := fun i => (Q i).metricSpace
            letI : ∀ j, MetricSpace (E j).Space := fun j => (E j).metricSpace
            (∀ j x y, 0 < U j x → 0 < U j y → ∀ b,
              dist ((E b).cyclicOrbitPoint (g b) N (fun _ : Unit => x))
                ((E b).cyclicOrbitPoint (g b) N (fun _ : Unit => y)) ≤ ε) ∧
            ∀ χ : ∀ i, (D i).RealGroup → CircleFourier.Circle,
              (∀ i, ∀ z ∈ (D i).filtration.realification.subgroup (s + 1), ∀ x,
                (T i).observable (z • x) = CircleFourier.character (χ i z) * (T i).observable x) →
              ∀ (h : ZMod N) (branch : ι → Fin 2),
                ∃ S : ∀ i, (Q i).Niltest (fun _ : Unit => 1),
                  (∀ i, (S i).normBound = (T i).normBound ^ 2) ∧
                  (∀ i, (S i).ComplexityLE ((p + C) ^ C)) ∧
                  (∀ i (z : Unit → ℤ), (S i).eval z =
                    (T i).eval (z + fun _ => (h.val : ℤ) - ((branch i).val : ℤ) * N) *
                      star ((T i).eval (z + fun _ => c i))) ∧
                  (∀ i j b x y,
                    x ∉ cyclicWrapExceptional h ε → y ∉ cyclicWrapExceptional h ε →
                    0 < U j x * U b (x + h) → 0 < U j y * U b (y + h) →
                    dist ((Q i).cyclicOrbitPoint (S i).orbit N (fun _ : Unit => x))
                      ((Q i).cyclicOrbitPoint (S i).orbit N (fun _ : Unit => y)) ≤ ε) ∧
                  let Z := sumFactors E Q
                  letI : FiniteDimensional ℚ (∀ i, sumLieSpace K
                    (fun j => (D j).filtration.squareLieSubalgebra ⧸
                      (D j).filtration.squareFiltration.layerIdeal (s + 1)) i) :=
                    (productFinBasis Z).finiteDimensional_of_finite
                  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, sumLieSpace K
                    (fun j => (D j).filtration.squareLieSubalgebra ⧸
                      (D j).filtration.squareFiltration.layerIdeal (s + 1)) i))
                  letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, sumLieSpace K
                    (fun j => (D j).filtration.squareLieSubalgebra ⧸
                      (D j).filtration.squareFiltration.layerIdeal (s + 1)) i)) :=
                    IsModuleTopology.isTopologicalAddGroup ℝ _
                  letI : T2Space (ℝ ⊗[ℚ] (∀ i, sumLieSpace K
                    (fun j => (D j).filtration.squareLieSubalgebra ⧸
                      (D j).filtration.squareFiltration.layerIdeal (s + 1)) i)) :=
                    realification_moduleTopology_t2 (productFinBasis Z)
                  letI := (pi Z).metricSpace
                  let G := NilpotentLieFiltration.piRealOrbit (fun i => (Z i).filtration)
                    (sumOrbits E Q g (fun i => (S i).orbit))
                  ∀ j b x y,
                    x ∉ cyclicWrapExceptional h ε → y ∉ cyclicWrapExceptional h ε →
                    0 < U j x * U b (x + h) → 0 < U j y * U b (y + h) →
                    dist ((pi Z).cyclicOrbitPoint G N (fun _ : Unit => x))
                      ((pi Z).cyclicOrbitPoint G N (fun _ : Unit => y)) ≤
                        Real.exp ((p + C) ^ C) * ε

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_native_anchored_input_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeAnchoredInputPartitionSpec s a C := by
  obtain ⟨B, _, hfamily⟩ := exists_native_anchored_square_family s a
  obtain ⟨R, _, hrefine⟩ := exists_fixed_observation_refinement s a
  let X : Polynomial ℕ := Polynomial.X
  let V := 2 * X + (X + Polynomial.C B) ^ B + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (V + (V + Polynomial.C R) ^ R + (V + 2) ^ 2 + (V + 4) ^ 4)
  refine ⟨C, hC, ?_⟩
  dsimp only [NativeAnchoredInputPartitionSpec]
  intro ι κ _ _ _ _ L _ _ d _ _ _ _ K _ _ e _ _ _ _ D _ _ _ _ _ _ _ _
    E g T c q N _ _ p ε hp hι hκ hT hE hq hε hε1 hεinv
  have hp0 : 0 ≤ p := by linarith
  let r := 2 * p + (p + B) ^ B + 2
  have hB0 : 0 ≤ (p + B) ^ B := by positivity
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp0.trans hpr
  have hBr : (p + B) ^ B ≤ r := by dsimp [r]; linarith
  have htotal : r + (r + R) ^ R + (r + 2) ^ 2 + (r + 4) ^ 4 ≤ (p + C) ^ C := by
    simpa [X, V, r, Polynomial.eval₂_pow] using hbudget p hp0
  have hR0 : 0 ≤ (r + R) ^ R := by positivity
  have hG0 : 0 ≤ (r + 2) ^ 2 := sq_nonneg _
  have hM0 : 0 ≤ (r + 4) ^ 4 := by positivity
  have hrC : r ≤ (p + C) ^ C := by linarith
  have hBC : (p + B) ^ B ≤ (p + C) ^ C := hBr.trans hrC
  have hRC : (r + R) ^ R ≤ (p + C) ^ C := by linarith
  have hGC : (r + 2) ^ 2 ≤ (p + C) ^ C := by linarith
  have hMC : (r + 4) ^ 4 ≤ (p + C) ^ C := by linarith
  obtain ⟨dQ, Q, weight, hadapt, hQ, n, k, hnk, m, hm, hcount, A, hA, hsum,
      hres, hcircle, hbad, hblocks⟩ :=
    hfamily D T c q N hp hι hT hq hε hε1 hεinv
  obtain ⟨l, hl, hUcount, U, hU, hUsum, hsupport, hpairs, hobs⟩ :=
    hrefine E g A (by omega) hr (hκ.trans hpr)
      (fun j => (hE j).mono (E j) hpr) (hcount.trans (Real.exp_le_exp.mpr hBr))
      (fun j => (hA j).mono le_rfl hBr) hsum hε
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2)
          (by linarith : p + 2 ≤ r + 2) a)))
  let Z := sumFactors E Q
  have hcardZ : (Fintype.card (κ ⊕ ι) : ℝ) ≤ r := by
    simp only [Fintype.card_sum, Nat.cast_add]
    dsimp [r]
    linarith
  have hZ : ∀ i, (Z i).GeometryComplexityLE r := by
    intro i
    cases i with
    | inl j => exact (hE j).mono (E j) hpr
    | inr j => exact (hQ j).mono (Q j) hBr
  refine ⟨dQ, Q, weight, hadapt, fun i => (hQ i).mono (Q i) hBC,
    n, k, hnk, m, l, hm, hl, hUcount.trans (Real.exp_le_exp.mpr hRC), U,
    fun j => (hU j).mono le_rfl hRC, hUsum,
    fun j x hx => hres j.1 x (hsupport j x hx),
    fun j x y hx hy => hcircle j.1 x y (hsupport j x hx) (hsupport j y hy),
    hbad, (pi_geometry Z hr hcardZ hZ).mono (pi Z) hGC, ?_⟩
  let : ∀ i, MetricSpace (Q i).Space := fun i => (Q i).metricSpace
  let : ∀ j, MetricSpace (E j).Space := fun j => (E j).metricSpace
  refine ⟨hobs, ?_⟩
  intro χ hvert h branch
  obtain ⟨S, hSnorm, hScomplexity, hSeval, hScell⟩ := hblocks χ hvert h branch
  have hcell i j b x y (hx : x ∉ cyclicWrapExceptional h ε) (hy : y ∉ cyclicWrapExceptional h ε)
      (hUx : 0 < U j x * U b (x + h)) (hUy : 0 < U j y * U b (y + h)) :
      dist ((Q i).cyclicOrbitPoint (S i).orbit N (fun _ : Unit => x))
        ((Q i).cyclicOrbitPoint (S i).orbit N (fun _ : Unit => y)) ≤ ε :=
    hScell i j.1 b.1 x y hx hy (hpairs h j b x hUx) (hpairs h j b y hUy)
  refine ⟨S, hSnorm, fun i => (hScomplexity i).mono hBC, hSeval, hcell, ?_⟩
  let KL := sumLieSpace K (fun j => (D j).filtration.squareLieSubalgebra ⧸
    (D j).filtration.squareFiltration.layerIdeal (s + 1))
  let : FiniteDimensional ℚ (∀ i, KL i) := (productFinBasis Z).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, KL i)) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, KL i)) := realification_moduleTopology_t2 (productFinBasis Z)
  let := (pi Z).metricSpace
  let : ∀ i, MetricSpace (Z i).Space := fun i => (Z i).metricSpace
  intro j b x y hx hy hUx hUy
  have hpositive j b x (hh : 0 < U j x * U b (x + h)) : 0 < U j x := by
    rcases mul_pos_iff.mp hh with hh | hh
    · exact hh.1
    · linarith [((hU j).unit_interval x).1]
  have hinputs : ∀ i,
      dist ((Z i).cyclicOrbitPoint (sumOrbits E Q g (fun j => (S j).orbit) i) N (fun _ : Unit => x))
        ((Z i).cyclicOrbitPoint (sumOrbits E Q g (fun j => (S j).orbit) i) N (fun _ : Unit => y)) ≤ ε := by
    intro i
    cases i with
    | inl i => exact hobs j x y (hpositive j b x hUx) (hpositive j b y hUy) i
    | inr i => exact hcell i j b x y hx hy hUx hUy
  exact (pi_cyclicOrbitPoint_dist_le_exp Z (sumOrbits E Q g (fun i => (S i).orbit)) N
    (fun _ : Unit => x) (fun _ : Unit => y) hr hcardZ (fun i => (hZ i).1) hε.le hinputs).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hMC) hε.le)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
