import Mathlib
import OAI.Computability.MaxCut.Games.LabelBound
import OAI.Computability.MaxCut.Games.MatrixChartKMSNeighbors

namespace OAI

/-! The concrete interface consumed by the shortcode assembly: an arbitrary
KMS interval becomes a `Shortcode.Slice`, with exact equation counts.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Matrix

theorem exists_shortcode_slice {ell m : Nat}
    (A B : Submodule (ZMod 2) (KMS.Ambient (ell + m))) :
    ∃ S : Shortcode.Slice ell m,
      S.rows = Module.finrank (ZMod 2) A ∧
      S.columns = (ell + m) - Module.finrank (ZMod 2) B ∧
      ∀ M : Shortcode.Mat ell m,
        S.Contains M ↔ A ≤ (matrixVertex M).val ∧ (matrixVertex M).val ≤ B := by
  classical
  let e := coordinateJoin (ZMod 2) ell m
  let A' := A.comap e.toLinearMap
  let B' := B.comap e.toLinearMap
  have hA : Module.finrank (ZMod 2) A' = Module.finrank (ZMod 2) A := by
    rw [show A' = A.map e.symm.toLinearMap from
      Submodule.comap_equiv_eq_map_symm e A]
    exact e.symm.finrank_map_eq A
  have hB : Module.finrank (ZMod 2) B' = Module.finrank (ZMod 2) B := by
    rw [show B' = B.map e.symm.toLinearMap from
      Submodule.comap_equiv_eq_map_symm e B]
    exact e.symm.finrank_map_eq B
  obtain ⟨nr, nc, d, s, t, q, hnr, hnc, h⟩ := exists_matrix_interval_slice A' B'
  have hE : Module.finrank (ZMod 2)
      ((Fin ell → ZMod 2) × (Fin m → ZMod 2)) = ell + m := by simp
  have hnc' : nc = (ell + m) - Module.finrank (ZMod 2) B := by
    simpa only [Submodule.finrank_quotient, hE, hB] using hnc
  let S : Shortcode.Slice ell m := ⟨nr, nc, d, s, q, t⟩
  refine ⟨S, hnr.trans hA, hnc', ?_⟩
  intro M
  have hcontains : S.Contains M ↔
      (∀ i, d i ᵥ* M = s i) ∧ (∀ j, M *ᵥ q j = t j) := by
    constructor
    · rintro ⟨hr, hc⟩
      exact ⟨fun i => funext (hr i), hc⟩
    · rintro ⟨hr, hc⟩
      exact ⟨fun i j => congrFun (hr i) j, hc⟩
  rw [hcontains, ← h M]
  have hlow : A' ≤ matrixGraph M ↔ A ≤ (matrixVertex M).val := by
    change A.comap e.toLinearMap ≤ matrixGraph M ↔
      A ≤ (matrixGraph M).map e.toLinearMap
    have hh := Submodule.comap_le_comap_iff_of_surjective
      (f := e.toLinearMap) e.surjective (p := A)
      (q := (matrixGraph M).map e.toLinearMap)
    simpa only [Submodule.comap_map_eq_of_injective e.injective] using hh
  have hupp : matrixGraph M ≤ B' ↔ (matrixVertex M).val ≤ B :=
    Submodule.map_le_iff_le_comap.symm
  exact and_congr hlow hupp

end MaxCutGames.Inverse.MatrixChart

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped Classical
open Shortcode MatrixChart

/-- The exact self-loop mass when independent uniform binary factors include
zero. The overlap of the two zero events is subtracted once. -/
def zeroFactorMass (ell m : ℕ) : ℝ :=
  ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ - ((2 : ℝ) ^ (ell + m))⁻¹

/-- A common lower bound on both dimensions makes the zero-factor probability
as small as required. This threshold depends only on the acceptance parameter.
-/
theorem exists_zeroFactorMass_threshold {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ ell m : ℕ, N ≤ ell → N ≤ m → zeroFactorMass ell m ≤ η / 2 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < η / 4 by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨N, ?_⟩
  intro ell m hell hm
  have hpow (n : ℕ) (hn : N ≤ n) : ((2 : ℝ) ^ n)⁻¹ ≤ η / 4 := by
    have hmon : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    simpa only [one_div, inv_pow] using hmon.trans hN.le
  have hell' := hpow ell hell
  have hm' := hpow m hm
  have hnonneg : 0 ≤ ((2 : ℝ) ^ (ell + m))⁻¹ := by positivity
  unfold zeroFactorMass
  linarith

/-- Finite sampling bridge, stated on the actual equality test, actual
lifted output fibers, and actual Grassmann retention. The positive dimensions
exclude the degenerate empty-neighbor cases. No KMS or inverse principle is
part of this proposition. -/
def ChartFiberRetention : Prop :=
  ∀ {ell m : ℕ}, 1 ≤ ell → 1 ≤ m →
    ∀ η : ℝ, 0 < η → η < 1 → zeroFactorMass ell m ≤ η / 2 →
      ∀ f : Mat ell m → Vector ell, η ≤ equalityAcceptance f →
        ∃ y : Vector ell, (liftedFiber f y).Nonempty ∧
          η / 4 ≤ KMS.retention (liftedFiber f y)

theorem inversePrinciple_of_expansion_and_chart
    (hKMS : KMS.ExpansionPrinciple) (hChart : ChartFiberRetention) :
    InversePrinciple := by
  intro η hη hη1
  obtain ⟨α, hαpos, hαone, r, hr, ellKMS, hKMSell⟩ :=
    hKMS (η / 4) (by positivity) (by linarith)
  obtain ⟨N, hN⟩ := exists_zeroFactorMass_threshold hη
  refine ⟨α, hαpos, hαone, r, hr, max ellKMS (max 1 N), ?_⟩
  intro ell hell
  have hellKMS : ellKMS ≤ ell := (le_max_left _ _).trans hell
  have hellone : 1 ≤ ell := (le_max_left 1 N).trans ((le_max_right _ _).trans hell)
  have hellN : N ≤ ell := (le_max_right 1 N).trans ((le_max_right _ _).trans hell)
  obtain ⟨nKMS, hKMSn⟩ := hKMSell ell hellKMS
  refine ⟨max nKMS (max 1 N), ?_⟩
  intro m hm f haccept
  have hmKMS : nKMS ≤ m := (le_max_left _ _).trans hm
  have hmone : 1 ≤ m := (le_max_left 1 N).trans ((le_max_right _ _).trans hm)
  have hmN : N ≤ m := (le_max_right 1 N).trans ((le_max_right _ _).trans hm)
  obtain ⟨y, hnonempty, hretention⟩ :=
    hChart hellone hmone η hη hη1 (hN ell m hellN hmN) f haccept
  obtain ⟨A, B, _hAB, hbudget, hintersection, hdense⟩ :=
    hKMSn (ell + m) (by omega) (liftedFiber f y) hnonempty hretention
  change Module.finrank (ZMod 2) A +
    ((ell + m) - Module.finrank (ZMod 2) B) ≤ r at hbudget
  obtain ⟨S, hrows, hcolumns, hcontains⟩ := exists_shortcode_slice A B
  apply hasAffineSlice_of_dense_interval f y (KMS.interval A B) S
  · intro M
    simpa only [KMS.interval, Finset.mem_filter, Finset.mem_univ, true_and]
      using hcontains M
  · omega
  · omega
  · exact hintersection
  · exact hdense

end
end MaxCutGames.Inverse.ShortcodeFromGrassmann

/-!
The exact sampling bridge from the vector factors in the shortcode test
to actual KMS Grassmann vertices. Every nonzero vector pair is sent to the
matrix `M + rankOne a l`, and this is a bijection onto the chart neighbors.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Matrix
open Shortcode (Vector Mat rankOne)

variable {ell m : ℕ}

@[simp] theorem dotFunctional_zero_binary :
    dotFunctional (0 : Vector ell) = 0 := by
  apply LinearMap.ext
  intro x
  change (0 : Vector ell) ⬝ᵥ x = 0
  simp

theorem dotFunctional_ne_zero {a : Vector ell} (ha : a ≠ 0) :
    dotFunctional a ≠ 0 := by
  intro h
  exact ha (dotFunctional_injective (h.trans dotFunctional_zero_binary.symm))

/-- The shortcode outer product is precisely the rank-one chart map. -/
theorem vecMulLinear_rankOne (a : Vector ell) (l : Vector m) :
    (rankOne a l).vecMulLinear = (dotFunctional a).smulRight l := by
  apply LinearMap.ext
  intro x
  change x ᵥ* Matrix.vecMulVec a l = (a ⬝ᵥ x) • l
  rw [Matrix.vecMul_vecMulVec, dotProduct_comm x a]

/-- This is the exact perturbation, including its functional/vector order. -/
theorem vecMulLinear_add_rankOne (M : Mat ell m) (a : Vector ell) (l : Vector m) :
    (M + rankOne a l).vecMulLinear = M.vecMulLinear + (dotFunctional a).smulRight l := by
  apply LinearMap.ext
  intro x
  change x ᵥ* (M + rankOne a l) = M.vecMulLinear x +
    ((dotFunctional a).smulRight l) x
  rw [Matrix.vecMul_add]
  exact congrArg (fun y => M.vecMulLinear x + y)
    (LinearMap.congr_fun (vecMulLinear_rankOne a l) x)

theorem adjacent_matrixVertex_add_rankOne (M : Mat ell m)
    (a : Vector ell) (l : Vector m) (ha : a ≠ 0) (hl : l ≠ 0) :
    KMS.Adjacent (matrixVertex M) (matrixVertex (M + rankOne a l)) := by
  apply (adjacent_matrixVertex_iff M (M + rankOne a l)).mpr
  apply (adjacent_iff_rank_one M.vecMulLinear (M + rankOne a l).vecMulLinear).mp
  rw [vecMulLinear_add_rankOne]
  exact adjacent_rank_one_step M.vecMulLinear (dotFunctional a) l
    (dotFunctional_ne_zero ha) hl

abbrev NonzeroVectorFactors (ell m : ℕ) :=
  {a : Vector ell // a ≠ 0} × {l : Vector m // l ≠ 0}

/-- Actual Grassmann vertices adjacent to `matrixVertex M` and remaining
inside the finite matrix chart. -/
abbrev MatrixVertexChartNeighbors (M : Mat ell m) :=
  {L : KMS.Vertex (ell + m) ell //
    KMS.Adjacent (matrixVertex M) L ∧ L ∈ matrixChart ell m}

def vectorFactorMatrixNeighbor (M : Mat ell m) (p : NonzeroVectorFactors ell m) :
    MatrixVertexChartNeighbors M :=
  ⟨matrixVertex (M + rankOne p.1.val p.2.val),
    adjacent_matrixVertex_add_rankOne M p.1.val p.2.val p.1.property p.2.property,
    (mem_matrixChart _).mpr ⟨M + rankOne p.1.val p.2.val, rfl⟩⟩

theorem vectorFactorMatrixNeighbor_injective (M : Mat ell m) :
    Function.Injective (vectorFactorMatrixNeighbor M) := by
  intro p q h
  have hM : M + rankOne p.1.val p.2.val = M + rankOne q.1.val q.2.val :=
    matrixVertex_injective (congrArg Subtype.val h)
  have hrank := congrArg Matrix.vecMulLinear (add_left_cancel hM)
  rw [vecMulLinear_rankOne, vecMulLinear_rankOne] at hrank
  obtain ⟨ha, hl⟩ := binary_smulRight_unique (dotFunctional_ne_zero p.1.property)
    p.2.property hrank
  exact Prod.ext (Subtype.ext (dotFunctional_injective ha)) (Subtype.ext hl)

theorem vectorFactorMatrixNeighbor_surjective (M : Mat ell m) :
    Function.Surjective (vectorFactorMatrixNeighbor M) := by
  intro L
  obtain ⟨N, hN⟩ := (mem_matrixChart L.val).mp L.property.2
  have hMN : KMS.Adjacent (matrixVertex M) (matrixVertex N) := by
    rw [hN]
    exact L.property.1
  have hNM : KMS.Adjacent (matrixVertex N) (matrixVertex M) :=
    ⟨hMN.1.symm, by rw [inf_comm]; exact hMN.2⟩
  obtain ⟨a, l, ha, hl, hfactor⟩ := exists_smulRight_of_rank_one
    (N.vecMulLinear - M.vecMulLinear) ((adjacent_matrixVertex_iff N M).mp hNM)
  obtain ⟨v, hv⟩ := dotFunctional_surjective a
  have hv0 : v ≠ 0 := by
    intro h
    apply ha
    rw [← hv, h, dotFunctional_zero_binary]
  have hmatrix : M + rankOne v l = N := by
    apply (LinearMap.toMatrixRight' (R := ZMod 2)).symm.injective
    change (M + rankOne v l).vecMulLinear = N.vecMulLinear
    rw [vecMulLinear_add_rankOne, hv]
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hfactor).symm
  refine ⟨(⟨v, hv0⟩, ⟨l, hl⟩), ?_⟩
  apply Subtype.ext
  change matrixVertex (M + rankOne v l) = L.val
  rw [hmatrix]
  exact hN

/-- Uniform independent nonzero vector factors induce exactly uniform
neighbors of the actual Grassmann vertex within the matrix chart. -/
noncomputable def vectorFactorsEquivMatrixVertexChartNeighbors (M : Mat ell m) :
    NonzeroVectorFactors ell m ≃ MatrixVertexChartNeighbors M :=
  Equiv.ofBijective (vectorFactorMatrixNeighbor M)
    ⟨vectorFactorMatrixNeighbor_injective M, vectorFactorMatrixNeighbor_surjective M⟩

@[simp] theorem vectorFactorsEquivMatrixVertexChartNeighbors_apply (M : Mat ell m)
    (p : NonzeroVectorFactors ell m) :
    (vectorFactorsEquivMatrixVertexChartNeighbors M p).val =
      matrixVertex (M + rankOne p.1.val p.2.val) := rfl

/-- The chart degree in the actual KMS vertex type. -/
theorem card_matrixVertexChartNeighbors (M : Mat ell m) :
    Nat.card (MatrixVertexChartNeighbors M) = (2 ^ ell - 1) * (2 ^ m - 1) := by
  classical
  rw [← Nat.card_congr (vectorFactorsEquivMatrixVertexChartNeighbors M)]
  simp only [NonzeroVectorFactors, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    Shortcode.Vector, Fintype.card_fun, ZMod.card, Fintype.card_fin]

end MaxCutGames.Inverse.MatrixChart

/-!
The exact finite sampling conversion in the shortcode proof. Independent
nonzero binary vector factors parametrize chart neighbors bijectively; the full
Grassmann degree is twice the chart degree. These identities imply the exact
factor one half, including its averaging over a nonempty output fiber.
-/

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped BigOperators Classical
open Shortcode MatrixChart

/-- Relative density is uniform expectation on the predicate subtype. -/
theorem relativeDensity_filter_eq_expect {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : Finset Ω) (P : Ω → Prop) [DecidablePred P] :
    KMS.relativeDensity S (Finset.univ.filter P) =
      𝔼 x : {x : Ω // P x}, if x.val ∈ S then (1 : ℝ) else 0 := by
  unfold KMS.relativeDensity
  rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp)
    (fun x => if x ∈ S then (1 : ℝ) else 0)]
  rw [Finset.sum_boole, Fintype.card_subtype]
  have hsets : S ∩ Finset.univ.filter P =
      (Finset.univ.filter P).filter (fun x => x ∈ S) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hsets]

/-- Lifting a finite set along an injection preserves its uniform starting
law. No regularity or nonempty-neighbor hypothesis is needed for this step. -/
theorem retention_image {X : Type*} [DecidableEq X] {n ell : ℕ}
    (S : Finset X) (e : X → KMS.Vertex n ell) (he : Function.Injective e) :
    KMS.retention (S.image e) =
      S.expect fun x => KMS.relativeDensity (S.image e) (KMS.neighbors (e x)) := by
  have h : KMS.retention (S.image e) =
      (S.image e).expect fun L => KMS.relativeDensity (S.image e) (KMS.neighbors L) := by
    rw [Finset.expect_eq_sum_div_card]
    rfl
  rw [h]
  exact Finset.expect_image he.injOn

/-- At every starting matrix the full-neighbor retention is half the uniform
nonzero-factor retention. This follows from exact finite bijections and degree
counts; the zero-factor law is handled separately before this theorem. -/
theorem relativeDensity_neighbors_eq_nonzero_average_half {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) (M : Mat ell m) :
    KMS.relativeDensity (liftedFiber f y) (KMS.neighbors (matrixVertex M)) =
      (𝔼 p : NonzeroVectorFactors ell m,
        if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) / 2 := by
  let C := KMS.neighbors (matrixVertex M) ∩ matrixChart ell m
  have hC : C = Finset.univ.filter (fun L : KMS.Vertex (ell + m) ell =>
      KMS.Adjacent (matrixVertex M) L ∧ L ∈ matrixChart ell m) := by
    ext L
    simp [C, KMS.neighbors]
  have hcardC : C.card = (2 ^ ell - 1) * (2 ^ m - 1) := by
    rw [hC]
    have h := card_matrixVertexChartNeighbors M
    simpa only [MatrixVertexChartNeighbors, Nat.card_eq_fintype_card,
      Fintype.card_subtype] using h
  have hcard : (KMS.neighbors (matrixVertex M)).card = 2 * C.card := by
    rw [hcardC]
    exact card_full_neighbors_twice M
  have hnumerator : liftedFiber f y ∩ C =
      liftedFiber f y ∩ KMS.neighbors (matrixVertex M) :=
    KMS.inter_chart_eq _ _ _ (liftedFiber_subset_chart f y)
  have hhalf : KMS.relativeDensity (liftedFiber f y)
      (KMS.neighbors (matrixVertex M)) =
        KMS.relativeDensity (liftedFiber f y) C / 2 := by
    unfold KMS.relativeDensity
    rw [hcard, ← hnumerator, Nat.cast_mul, Nat.cast_ofNat,
      mul_comm (2 : ℝ), div_mul_eq_div_div]
  rw [hhalf]
  congr 1
  rw [hC]
  trans (𝔼 L : MatrixVertexChartNeighbors M,
    if L.val ∈ liftedFiber f y then (1 : ℝ) else 0)
  · exact relativeDensity_filter_eq_expect (liftedFiber f y)
      (fun L => KMS.Adjacent (matrixVertex M) L ∧ L ∈ matrixChart ell m)
  symm
  apply Fintype.expect_equiv (vectorFactorsEquivMatrixVertexChartNeighbors M)
  intro p
  simp only [vectorFactorsEquivMatrixVertexChartNeighbors_apply,
    matrixVertex_mem_liftedFiber]

/-- The exact Grassmann retention of an output fiber is half its retention
under independent uniform nonzero vector factors. Empty fibers and degenerate
dimensions also satisfy this identity with zero-expectation conventions. -/
theorem liftedFiber_retention_eq_half {ell m : ℕ}
    (f : Mat ell m → Vector ell) (y : Vector ell) :
    KMS.retention (liftedFiber f y) =
      (𝔼 M ∈ matrixFiber f y, 𝔼 p : NonzeroVectorFactors ell m,
        if f (M + rankOne p.1.val p.2.val) = y then (1 : ℝ) else 0) / 2 := by
  unfold liftedFiber
  rw [retention_image _ _ matrixVertex_injective]
  change (𝔼 M ∈ matrixFiber f y,
    KMS.relativeDensity (liftedFiber f y) (KMS.neighbors (matrixVertex M))) = _
  simp_rw [relativeDensity_neighbors_eq_nonzero_average_half]
  exact (Finset.expect_div _ _ _).symm

end
end MaxCutGames.Inverse.ShortcodeFromGrassmann

/-!
Finite equality-fiber extraction for the Grassmann-to-matrix route.

These elementary results do not assume a shortcode inverse theorem.  They
separate the equality test, the retention of a nonempty output fiber, and the
subsequent removal of zero perturbation factors.  The dimension-uniform
Grassmann expansion theorem remains a separate mathematical obligation.
-/

namespace MaxCutGames.Inverse.EqualityFiber

noncomputable section

open scoped BigOperators Classical
open MaxCutGames.Foundations.Information

variable {X Y : Type*} [Fintype X] [Fintype Y]

def fiberMass (p : X → ℝ) (f : X → Y) (y : Y) : ℝ := by
  classical
  exact ∑ x, if f x = y then p x else 0

def fiberFlow (p : X → ℝ) (k : X → X → ℝ) (f : X → Y) (y : Y) : ℝ := by
  classical
  exact ∑ x, p x * ∑ x', k x x' * if f x = y ∧ f x' = y then 1 else 0

def equalityAcceptance (p : X → ℝ) (k : X → X → ℝ) (f : X → Y) : ℝ := by
  classical
  exact ∑ x, p x * ∑ x', k x x' * if f x = f x' then 1 else 0

theorem sum_fiberMass (p : X → ℝ) (f : X → Y) :
    ∑ y, fiberMass p f y = ∑ x, p x := by
  classical
  unfold fiberMass
  rw [Finset.sum_comm]
  simp

omit [Fintype Y] in
theorem fiberMass_nonneg (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (f : X → Y) (y : Y) : 0 ≤ fiberMass p f y := by
  classical
  apply Finset.sum_nonneg
  intro x _
  split
  · exact hp x
  · exact le_rfl

omit [Fintype Y] in
theorem fiberFlow_nonneg (p : X → ℝ) (k : X → X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hk : ∀ x x', 0 ≤ k x x')
    (f : X → Y) (y : Y) : 0 ≤ fiberFlow p k f y := by
  classical
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (hp x)
  apply Finset.sum_nonneg
  intro x' _
  apply mul_nonneg (hk x x')
  split <;> norm_num

omit [Fintype Y] in
theorem fiberFlow_le_mass (p : X → ℝ) (k : X → X → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hk : ∀ x, IsProbability (k x))
    (f : X → Y) (y : Y) : fiberFlow p k f y ≤ fiberMass p f y := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases h : f x = y
  · simp only [h, true_and, ite_true]
    have hinner : (∑ x', k x x' * if f x' = y then 1 else 0) ≤ 1 := by
      calc
        _ ≤ ∑ x', k x x' := by
          apply Finset.sum_le_sum
          intro x' _
          split <;> simp [(hk x).1 x']
        _ = 1 := (hk x).2
    simpa using mul_le_mul_of_nonneg_left hinner (hp x)
  · simp [h]

private theorem sum_sameFiber_indicator_inline_EqualityFiber (a b : Y) :
    (∑ y, if a = y ∧ b = y then (1 : ℝ) else 0) =
      if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro y _
    have h' : ¬ (a = y ∧ b = y) := fun hy => h (hy.1.trans hy.2.symm)
    simp [h']

theorem sum_fiberFlow (p : X → ℝ) (k : X → X → ℝ) (f : X → Y) :
    ∑ y, fiberFlow p k f y = equalityAcceptance p k f := by
  classical
  unfold fiberFlow equalityAcceptance
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x' _
  rw [← Finset.mul_sum, sum_sameFiber_indicator_inline_EqualityFiber]

/-- A probability-weighted average at least `η` contains a positive-weight
fiber whose unnormalized flow is at least `η` times its mass. -/
theorem exists_positive_mass_le_flow (mass flow : Y → ℝ)
    (hmass : IsProbability mass) (_hflow : ∀ y, 0 ≤ flow y)
    (hzero : ∀ y, mass y = 0 → flow y = 0)
    {η : ℝ} (haccept : η ≤ ∑ y, flow y) :
    ∃ y, 0 < mass y ∧ η * mass y ≤ flow y := by
  classical
  by_contra hnone
  have hless (y : Y) (hy : 0 < mass y) : flow y < η * mass y := by
    apply lt_of_not_ge
    intro h
    exact hnone ⟨y, hy, h⟩
  have hle (y : Y) : flow y ≤ η * mass y := by
    rcases eq_or_lt_of_le (hmass.1 y) with hz | hz
    · simp [← hz, hzero y hz.symm]
    · exact (hless y hz).le
  have hex : ∃ y, 0 < mass y := by
    by_contra hn
    have hall (y : Y) : mass y = 0 := le_antisymm (le_of_not_gt (fun hy => hn ⟨y, hy⟩))
      (hmass.1 y)
    have := hmass.2
    simp [hall] at this
  obtain ⟨y, hy⟩ := hex
  have hstrict : (∑ y, flow y) < ∑ y, η * mass y := by
    exact Finset.sum_lt_sum (fun y _ => hle y) ⟨y, Finset.mem_univ y, hless y hy⟩
  rw [← Finset.mul_sum, hmass.2, mul_one] at hstrict
  exact (not_lt_of_ge haccept) hstrict

/-- Equality acceptance supplies a nonempty output fiber with the claimed
retention.  The kernel is the actual sampling kernel; no conditioned sampling
law is silently substituted. -/
theorem exists_fiber_retention (p : X → ℝ) (k : X → X → ℝ)
    (hp : IsProbability p) (hk : ∀ x, IsProbability (k x))
    (f : X → Y) {η : ℝ} (haccept : η ≤ equalityAcceptance p k f) :
    ∃ y, 0 < fiberMass p f y ∧ η ≤ fiberFlow p k f y / fiberMass p f y := by
  have hmass : IsProbability (fiberMass p f) :=
    ⟨fiberMass_nonneg p hp.1 f, (sum_fiberMass p f).trans hp.2⟩
  have hflow := fiberFlow_nonneg p k hp.1 (fun x => (hk x).1) f
  have hzero (y : Y) (hy : fiberMass p f y = 0) : fiberFlow p k f y = 0 := by
    apply le_antisymm _ (hflow y)
    simpa [hy] using fiberFlow_le_mass p k hp.1 hk f y
  obtain ⟨y, hy, hret⟩ := exists_positive_mass_le_flow (fiberMass p f)
    (fiberFlow p k f) hmass hflow hzero (by simpa [sum_fiberFlow] using haccept)
  exact ⟨y, hy, (le_div_iff₀ hy).2 hret⟩

/-- Removing a self-loop mass `p₀ ≤ η/2` leaves retention at least `η/2`.
This is the precise algebra needed when one or both rank-one factors may be
zero in the unconditioned test. -/
theorem nonzero_retention_ge_half {η p₀ R : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hp₀ : 0 ≤ p₀) (hp₀η : p₀ ≤ η / 2)
    (haccept : η ≤ p₀ + (1 - p₀) * R) : η / 2 ≤ R := by
  have hp₀1 : p₀ < 1 := by linarith
  have hden : 0 < 1 - p₀ := by linarith
  have hprod : η / 2 * (1 - p₀) ≤ (1 - p₀) * R := by nlinarith
  nlinarith

theorem chart_retention_ge_quarter {η R : ℝ} (h : η / 2 ≤ R) : η / 4 ≤ R / 2 := by
  linarith

end
end MaxCutGames.Inverse.EqualityFiber

/-! The actual uniform matrix test supplies a positive-mass output fiber with
large retention. The transition kernel averages independent full vectors,
including zero, exactly as in the shortcode theorem. -/

namespace MaxCutGames.Inverse.Shortcode

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Foundations.Information

def matrixWeight {ell m : ℕ} (_ : Mat ell m) : ℝ :=
  (Fintype.card (Mat ell m) : ℝ)⁻¹

theorem matrixWeight_probability (ell m : ℕ) :
    IsProbability (matrixWeight (ell := ell) (m := m)) := by
  constructor
  · intro M
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · have hcard : (Fintype.card (Mat ell m) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp [matrixWeight, hcard]

def matrixKernel {ell m : ℕ} (M N : Mat ell m) : ℝ :=
  𝔼 a : Vector ell, 𝔼 l : Vector m,
    if N = M + rankOne a l then 1 else 0

theorem matrixKernel_nonneg {ell m : ℕ} (M N : Mat ell m) :
    0 ≤ matrixKernel M N := by
  apply Finset.expect_nonneg
  intro a _
  apply Finset.expect_nonneg
  intro l _
  split <;> norm_num

theorem matrixKernel_probability {ell m : ℕ} (M : Mat ell m) :
    IsProbability (matrixKernel M) := by
  refine ⟨matrixKernel_nonneg M, ?_⟩
  unfold matrixKernel
  rw [← Finset.expect_sum_comm]
  have hpoint (a : Vector ell) :
      (∑ N : Mat ell m, 𝔼 l : Vector m,
        if N = M + rankOne a l then (1 : ℝ) else 0) = 1 := by
    rw [← Finset.expect_sum_comm]
    simp
  simp only [hpoint]
  simp

theorem matrixKernel_equality {ell m : ℕ} (f : Mat ell m → Vector ell)
    (M : Mat ell m) :
    (∑ N, matrixKernel M N * if f M = f N then (1 : ℝ) else 0) =
      𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then 1 else 0 := by
  simp only [matrixKernel, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro a _
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro l _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem equalityAcceptance_eq_kernel {ell m : ℕ} (f : Mat ell m → Vector ell) :
    equalityAcceptance f = EqualityFiber.equalityAcceptance matrixWeight matrixKernel f := by
  calc
    equalityAcceptance f = ∑ M, matrixWeight M *
        (𝔼 a, 𝔼 l, if f M = f (M + rankOne a l) then (1 : ℝ) else 0) := by
      unfold equalityAcceptance matrixWeight
      rw [Fintype.expect_eq_sum_div_card]
      simp only [div_eq_mul_inv, ← Finset.mul_sum, mul_comm]
    _ = EqualityFiber.equalityAcceptance matrixWeight matrixKernel f := by
      unfold EqualityFiber.equalityAcceptance
      apply Finset.sum_congr rfl
      intro M _
      congr 1
      convert (matrixKernel_equality f M).symm using 1
      apply Finset.sum_congr rfl
      intro N _
      by_cases h : f M = f N <;> simp [h]

/-- Positive-mass fibers, with their actual transition flow, are obtained from
the full uniform factor law. This is the first step before conditioning both
factors to be nonzero and passing to Grassmann neighbors. -/
theorem exists_output_fiber {ell m : ℕ} (f : Mat ell m → Vector ell)
    {η : ℝ} (haccept : η ≤ equalityAcceptance f) :
    ∃ y : Vector ell, 0 < EqualityFiber.fiberMass matrixWeight f y ∧
      η ≤ EqualityFiber.fiberFlow matrixWeight matrixKernel f y /
        EqualityFiber.fiberMass matrixWeight f y := by
  apply EqualityFiber.exists_fiber_retention matrixWeight matrixKernel
    (matrixWeight_probability ell m) matrixKernel_probability f
  rwa [← equalityAcceptance_eq_kernel]

end
end MaxCutGames.Inverse.Shortcode

namespace MaxCutGames.Inverse.FactorSampling

noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Foundations.Information

variable {A B : Type*} [Fintype A] [Fintype B] [Zero A] [Zero B]

def fullAverage (p : A → ℝ) (q : B → ℝ) (h : A → B → ℝ) : ℝ :=
  ∑ a, ∑ b, p a * q b * h a b

def nonzeroFlow (p : A → ℝ) (q : B → ℝ) (h : A → B → ℝ) : ℝ :=
  ∑ a, ∑ b, p a * q b * if a ≠ 0 ∧ b ≠ 0 then h a b else 0

def zeroMass (p : A → ℝ) (q : B → ℝ) : ℝ :=
  p 0 + q 0 - p 0 * q 0

omit [Fintype A] [Fintype B] in
private theorem boundary_indicator_inline_FactorSampling (a : A) (b : B) :
    (if a = 0 ∨ b = 0 then (1 : ℝ) else 0) =
      (if a = 0 then 1 else 0) + (if b = 0 then 1 else 0) -
        (if a = 0 then 1 else 0) * (if b = 0 then 1 else 0) := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb]

/-- The overlap of the two zero-factor events is subtracted exactly once. -/
theorem boundary_mass (p : A → ℝ) (q : B → ℝ)
    (hp : IsProbability p) (hq : IsProbability q) :
    fullAverage p q (fun a b => if a = 0 ∨ b = 0 then 1 else 0) = zeroMass p q := by
  unfold fullAverage zeroMass
  simp_rw [boundary_indicator_inline_FactorSampling, mul_sub, mul_add]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h₁ : (∑ a, ∑ b, p a * q b * if a = 0 then 1 else 0) = p 0 := by
    calc
      _ = ∑ a, p a * (∑ b, q b) * if a = 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = p 0 := by simp [hq.2, mul_ite]
  have h₂ : (∑ a, ∑ b, p a * q b * if b = 0 then 1 else 0) = q 0 := by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.sum_mul, hp.2, one_mul]
  have h₃ : (∑ a, ∑ b, p a * q b *
      ((if a = 0 then 1 else 0) * (if b = 0 then 1 else 0))) = p 0 * q 0 := by
    simp [mul_ite]
  rw [h₁, h₂, h₃]

/-- A self-loop occurs whenever either perturbation factor is zero. -/
theorem fullAverage_eq_zeroMass_add_nonzeroFlow (p : A → ℝ) (q : B → ℝ)
    (hp : IsProbability p) (hq : IsProbability q) (h : A → B → ℝ)
    (hleft : ∀ b, h 0 b = 1) (hright : ∀ a, h a 0 = 1) :
    fullAverage p q h = zeroMass p q + nonzeroFlow p q h := by
  have hpoint (a : A) (b : B) : h a b =
      (if a = 0 ∨ b = 0 then 1 else 0) +
        (if a ≠ 0 ∧ b ≠ 0 then h a b else 0) := by
    by_cases ha : a = 0
    · subst a
      simp [hleft]
    · by_cases hb : b = 0
      · subst b
        simp [hright]
      · simp [ha, hb]
  calc
    fullAverage p q h =
        fullAverage p q (fun a b => if a = 0 ∨ b = 0 then 1 else 0) +
          nonzeroFlow p q h := by
      unfold fullAverage nonzeroFlow
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simpa only [mul_add] using congrArg (fun z : ℝ => p a * q b * z) (hpoint a b)
    _ = _ := by rw [boundary_mass p q hp hq]

def conditionedRetention (p : A → ℝ) (q : B → ℝ) (h : A → B → ℝ) : ℝ :=
  nonzeroFlow p q h / (1 - zeroMass p q)

theorem fullAverage_eq_mixture (p : A → ℝ) (q : B → ℝ)
    (hp : IsProbability p) (hq : IsProbability q) (h : A → B → ℝ)
    (hleft : ∀ b, h 0 b = 1) (hright : ∀ a, h a 0 = 1)
    (hzero : zeroMass p q < 1) :
    fullAverage p q h = zeroMass p q +
      (1 - zeroMass p q) * conditionedRetention p q h := by
  rw [fullAverage_eq_zeroMass_add_nonzeroFlow p q hp hq h hleft hright]
  unfold conditionedRetention
  have hne : 1 - zeroMass p q ≠ 0 := by linarith
  field_simp

/-- This is the full sampling-law implication, rather than only the scalar
inequality under an assumed mixture identity. -/
theorem conditionedRetention_ge_half (p : A → ℝ) (q : B → ℝ)
    (hp : IsProbability p) (hq : IsProbability q) (h : A → B → ℝ)
    (hleft : ∀ b, h 0 b = 1) (hright : ∀ a, h a 0 = 1)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hzero : 0 ≤ zeroMass p q) (hzeroη : zeroMass p q ≤ η / 2)
    (haccept : η ≤ fullAverage p q h) : η / 2 ≤ conditionedRetention p q h := by
  apply EqualityFiber.nonzero_retention_ge_half hη hη1 hzero hzeroη
  rw [← fullAverage_eq_mixture p q hp hq h hleft hright (by linarith)]
  exact haccept

omit [Fintype A] [Fintype B] in
/-- Specialization of the excluded zero-factor mass to uniform binary vector
spaces. The powers are supplied by the cardinalities, so the formula also
keeps track of the overlap when both factors are zero. -/
theorem zeroMass_binary_uniform (p : A → ℝ) (q : B → ℝ) (ell m : ℕ)
    (hp0 : p 0 = ((2 : ℝ) ^ ell)⁻¹) (hq0 : q 0 = ((2 : ℝ) ^ m)⁻¹) :
    zeroMass p q = ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ - ((2 : ℝ) ^ (ell + m))⁻¹ := by
  unfold zeroMass
  rw [hp0, hq0, pow_add, mul_inv]

end
end MaxCutGames.Inverse.FactorSampling

end OAI
