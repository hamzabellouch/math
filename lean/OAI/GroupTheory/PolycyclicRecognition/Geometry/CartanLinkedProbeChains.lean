import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTranslatedProbeChains

namespace OAI

/-! # Consecutive actual chains with one vanishing prefix bound -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- All three logarithmic chains in the original neighboring-sheet coordinates.
The first starts at the allowed suffix, the second at its neighbor, and the third starts at the second's actual
last vertex. Their coefficients retain their original template bounds. -/
structure LinkedProbeChains
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (γ : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (E k) γ t scale (probe k))
    (origin base : ∀ n, Y n → cartanRootIdeal H) (ε : ℕ → ℝ) where
  vertex : ∀ k n, Y n → Fin ((P k).length + 1) → cartanRootIdeal H
  measurable : ∀ k n j, Measurable (fun y => b₀.equivFun (vertex k n y j))
  first_start : ∀ n y, vertex 0 n y 0 = origin n y
  first_exp : ∀ n y j, F.ExpN (F.N.equiv (vertex 0 n y j)) =
    F.ExpN (F.N.equiv (origin n y)) * F.ExpN (F.N.equiv ((P 0).vertex n y j))
  second_start : ∀ n y, vertex 1 n y 0 = base n y
  third_start : ∀ n y, vertex 2 n y 0 = vertex 1 n y (Fin.last (P 1).length)
  second_exp : ∀ n y j, F.ExpN (F.N.equiv (vertex 1 n y j)) =
    F.ExpN (F.N.equiv (base n y)) * F.ExpN (F.N.equiv ((P 1).vertex n y j))
  third_exp : ∀ n y j, F.ExpN (F.N.equiv (vertex 2 n y j)) =
    F.ExpN (F.N.equiv (vertex 1 n y (Fin.last (P 1).length))) *
      F.ExpN (F.N.equiv ((P 2).vertex n y j))
  bound : ∀ k n y j,
    ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
      (fun i => bracketWordExponent t (γ.val i)) (scale n)).equivFun (vertex k n y j)‖ ≤
        Real.exp (scale n * ε n)
  step : ∀ k n y j, F.ExpN (F.N.equiv (vertex k n y j.succ)) =
    F.ExpN (F.N.equiv (vertex k n y j.castSucc)) *
      F.ExpN (F.N.equiv ((P k).coefficient n y j • M.letter ((P k).mode n j)))

omit [SimplyConnectedSpace G] [FiniteDimensional ℝ W] [Nonempty (Fin M.letterCount)] in
/-- Translate the two noninitial chains consecutively and keep one vanishing
prefix envelope. In particular, the third initial profile is exactly the second
terminal profile, rather than merely asymptotic to it. -/
theorem exists_linked_probe_chains
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (γ : M.Bases) (t : Fin M.letterCount → ℝ)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent t w) γ.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (E k) γ t scale (probe k))
    (origin base : ∀ n, Y n → cartanRootIdeal H)
    (horiginMeas : ∀ n, Measurable (fun y => b₀.equivFun (origin n y)))
    (hmeas : ∀ n, Measurable (fun y => b₀.equivFun (base n y)))
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 ≤ ε n) (hε : Tendsto ε atTop (𝓝 0))
    (horigin : ∀ n y,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
        (fun i => bracketWordExponent t (γ.val i)) (scale n)).equivFun (origin n y)‖ ≤
          Real.exp (scale n * ε n))
    (hbase : ∀ n y,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList γ)
        (fun i => bracketWordExponent t (γ.val i)) (scale n)).equivFun (base n y)‖ ≤
          Real.exp (scale n * ε n)) :
    ∃ η : ℕ → ℝ, (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
      Nonempty (M.LinkedProbeChains T F hunimod eW b₀ E γ t scale probe P origin base η) := by
  obtain ⟨η₀, v₀, hη₀0, hη₀, hm₀, hz₀, _, hp₀, hb₀, hs₀⟩ :=
    BoxProbeChains.exists_translated T M F hunimod eW haarN dynkinN b₀ (E 0) γ t hγ
      scale hscale hscale1 (probe 0) (P 0) origin horiginMeas ε hε0 hε horigin
  obtain ⟨η₁, v₁, hη₁0, hη₁, hm₁, hz₁, _, hp₁, hb₁, hs₁⟩ :=
    BoxProbeChains.exists_translated T M F hunimod eW haarN dynkinN b₀ (E 1) γ t hγ
      scale hscale hscale1 (probe 1) (P 1) base hmeas ε hε0 hε hbase
  obtain ⟨η₂, v₂, hη₂0, hη₂, hm₂, hz₂, _, hp₂, hb₂, hs₂⟩ :=
    BoxProbeChains.exists_translated T M F hunimod eW haarN dynkinN b₀ (E 2) γ t hγ
      scale hscale hscale1 (probe 2) (P 2)
      (fun n y => v₁ n y (Fin.last (P 1).length))
      (fun n => hm₁ n _) η₁ hη₁0 hη₁ (fun n y => hb₁ n y _)
  let η := fun n => η₀ n + η₁ n + η₂ n
  have hη : Tendsto η atTop (𝓝 0) := by
    simpa only [add_zero] using (hη₀.add hη₁).add hη₂
  let v : ∀ k n, Y n → Fin ((P k).length + 1) → cartanRootIdeal H :=
    Fin.cases v₀ (Fin.cases v₁ (Fin.cases v₂ (fun i => i.elim0)))
  refine ⟨η, fun n => add_nonneg (add_nonneg (hη₀0 n) (hη₁0 n)) (hη₂0 n), hη, ⟨{
    vertex := v
    measurable := ?_
    first_start := hz₀
    first_exp := hp₀
    second_start := hz₁
    third_start := hz₂
    second_exp := hp₁
    third_exp := hp₂
    bound := ?_
    step := ?_ }⟩⟩
  · intro k n j
    fin_cases k
    · exact hm₀ n j
    · exact hm₁ n j
    · exact hm₂ n j
  · intro k n y j
    have hs : 0 ≤ scale n := le_trans zero_le_one (hscale1 n)
    fin_cases k
    · exact (hb₀ n y j).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (by dsimp [η]; linarith [hη₁0 n, hη₂0 n]) hs))
    · exact (hb₁ n y j).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (by dsimp [η]; linarith [hη₀0 n, hη₂0 n]) hs))
    · exact (hb₂ n y j).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (by dsimp [η]; linarith [hη₀0 n, hη₁0 n]) hs))
  · intro k n y j
    fin_cases k
    · exact hs₀ n y j
    · exact hs₁ n y j
    · exact hs₂ n y j

omit [SimplyConnectedSpace G] [FiniteDimensional ℝ W] [Nonempty (Fin M.letterCount)] in
/-- Each linked chain is the original chain left-translated by its actual
initial vertex; this identity keeps the common profile centering unchanged. -/
theorem LinkedProbeChains.exp_eq_start_mul
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (γ : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (E k) γ t scale (probe k))
    (origin base : ∀ n, Y n → cartanRootIdeal H) (ε : ℕ → ℝ)
    (Q : M.LinkedProbeChains T F hunimod eW b₀ E γ t scale probe P origin base ε)
    (k : Fin 3) (n : ℕ) (y : Y n) (j : Fin ((P k).length + 1)) :
    F.ExpN (F.N.equiv (Q.vertex k n y j)) =
      F.ExpN (F.N.equiv (Q.vertex k n y 0)) *
        F.ExpN (F.N.equiv ((P k).vertex n y j)) := by
  fin_cases k
  · change F.ExpN (F.N.equiv (Q.vertex 0 n y j)) =
      F.ExpN (F.N.equiv (Q.vertex 0 n y 0)) * F.ExpN (F.N.equiv ((P 0).vertex n y j))
    rw [Q.first_exp, Q.first_start]
  · change F.ExpN (F.N.equiv (Q.vertex 1 n y j)) =
      F.ExpN (F.N.equiv (Q.vertex 1 n y 0)) * F.ExpN (F.N.equiv ((P 1).vertex n y j))
    rw [Q.second_exp, Q.second_start]
  · change F.ExpN (F.N.equiv (Q.vertex 2 n y j)) =
      F.ExpN (F.N.equiv (Q.vertex 2 n y 0)) * F.ExpN (F.N.equiv ((P 2).vertex n y j))
    rw [Q.third_exp, Q.third_start]

omit [SimplyConnectedSpace G] [FiniteDimensional ℝ W] [Nonempty (Fin M.letterCount)] in
/-- The three last vertices are the actual three endpoints used in packing. -/
theorem LinkedProbeChains.endpoint
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (γ : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (probe : Fin 3 → ∀ n, Y n → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (E k) γ t scale (probe k))
    (origin base : ∀ n, Y n → cartanRootIdeal H) (ε : ℕ → ℝ)
    (Q : M.LinkedProbeChains T F hunimod eW b₀ E γ t scale probe P origin base ε)
    (n : ℕ) (y : Y n) :
    F.ExpN (F.N.equiv (Q.vertex 0 n y (Fin.last (P 0).length))) =
      F.ExpN (F.N.equiv (origin n y)) * probe 0 n y ∧
    F.ExpN (F.N.equiv (Q.vertex 1 n y (Fin.last (P 1).length))) =
      F.ExpN (F.N.equiv (base n y)) * probe 1 n y ∧
    F.ExpN (F.N.equiv (Q.vertex 2 n y (Fin.last (P 2).length))) =
      F.ExpN (F.N.equiv (base n y)) * probe 1 n y * probe 2 n y := by
  rw [Q.first_exp, (P 0).vertex_last, Q.third_exp, Q.second_exp,
    (P 1).vertex_last, (P 2).vertex_last]
  exact ⟨rfl, rfl, rfl⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
