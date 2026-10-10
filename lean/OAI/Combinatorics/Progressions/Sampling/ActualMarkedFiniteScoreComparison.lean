import OAI.Combinatorics.Progressions.Lattices.UniformExternalMarkedAffineSliceFreezingDictionary

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

variable {σ κ L T : Type*} [Fintype σ] [DecidableEq σ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
  {F : NilpotentLieFiltration T t} {w : σ → ℕ}
  {S : T →ₗ[ℚ] L} {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}

structure MarkedFiniteScoreFreezing
    (E R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (EF RF : (F.realification.adaptedPolynomialFiltration w).Group)
    (Tbox : σ → ℝ) (ε B : ℝ) where
  N : ℕ
  Q : ℕ
  M : ℕ
  n : ℕ
  Q_pos : 0 < Q
  Q_le : (Q : ℝ) ≤ max 1 B
  M_pos : 0 < M
  M_le : (M : ℝ) ≤ B
  pair_card_le : (Fintype.card ((Fin d → Fin (N + 1)) × Fin n) : ℝ) ≤ B ^ 2
  cell_card_le : (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B
  left : (Fin d → Fin (N + 1)) → D.RealGroup
  right : Fin n → D.RealGroup
  leftLabel : (σ → Fin (Q + 1)) → (Fin d → Fin (N + 1))
  rightLabel : (σ → ZMod M) → Fin n
  error : ∀ (test : D.Niltest w)
    (g P : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
    E * P * R = g → ∀ cell (x : σ → ℤ),
    (∀ i, |(x i : ℝ)| ≤ Tbox i) →
    (∀ i, |(x i : ℝ) - normalizedRealBoxGrid Tbox Q cell i| ≤ Tbox i * (2 / Q)) →
    ‖test.observable (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
        (fun i => (x i : ℝ)) g)) -
      test.markedFrozenValue F w S hS EF RF P (left (leftLabel cell))
        (right (rightLabel (fun i => (x i : ZMod M)))) x‖ ≤ (test.lipBound : ℝ) * ε

variable {E R : (D.filtration.realification.adaptedPolynomialFiltration w).Group}
  {EF RF : (F.realification.adaptedPolynomialFiltration w).Group}
  {Tbox : σ → ℝ} {ε B : ℝ}

theorem BoundedCellMarkedPolynomialFreezing.exists_finite_score_freezing
    {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {l : ℕ} {A : ℝ}
    (hfreeze : D.BoundedCellMarkedPolynomialFreezing F c φ hφ w S hS l Tbox A ε B)
    (hE : D.filtration.PolynomialSlowBound D.basis w Tbox A E)
    (hEF : F.PolynomialSlowBound c w Tbox A EF)
    (hR : D.filtration.PolynomialRationalGrid D.basis w l R)
    (hRF : F.PolynomialRationalGrid c w l RF)
    (hEproj : D.filtration.realPolynomialGroupMap F φ hφ w E = EF)
    (hRproj : D.filtration.realPolynomialGroupMap F φ hφ w R = RF) :
    Nonempty (MarkedFiniteScoreFreezing (S := S) (hS := hS) E R EF RF Tbox ε B) := by
  obtain ⟨N, Q, M, m, n, _, hQ, hQb, hM, _, _, _, hQc, hMb, _, _, hpair,
    left, right, _, _, hfreeze⟩ := hfreeze
  obtain ⟨leftLabel, rightLabel, _, herror⟩ :=
    hfreeze E EF R RF hE hEF hR hRF hEproj hRproj
  exact ⟨{
    N := N
    Q := Q
    M := M
    n := n
    Q_pos := hQ
    Q_le := hQb
    M_pos := hM
    M_le := hMb
    pair_card_le := hpair
    cell_card_le := hQc
    left := left
    right := right
    leftLabel := leftLabel
    rightLabel := rightLabel
    error := herror }⟩

namespace MarkedFiniteScoreFreezing

variable (A : MarkedFiniteScoreFreezing (S := S) (hS := hS) E R EF RF Tbox ε B)

noncomputable def value (test : D.Niltest w)
    (P : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (cell : σ → Fin (A.Q + 1)) (x : σ → ℤ) : ℂ :=
  test.markedFrozenValue F w S hS EF RF P (A.left (A.leftLabel cell))
    (A.right (A.rightLabel (fun i => (x i : ZMod A.M)))) x

theorem norm_score_sub_le {J X : Type*} [Fintype J]
    (tests : X → D.Niltest w) (localLaw : FiniteProbabilityWeights J)
    (physical : J → X) (point : J → σ → ℤ) (cell : J → σ → Fin (A.Q + 1))
    (weight : J → ℂ)
    (g P : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (hfactor : E * P * R = g) {Bweight Lip : ℝ}
    (hε : 0 ≤ ε) (hBweight : 0 ≤ Bweight)
    (hweight : ∀ j, ‖weight j‖ ≤ Bweight)
    (hlip : ∀ j, ((tests (physical j)).lipBound : ℝ) ≤ Lip)
    (hpoint : ∀ j i, |(point j i : ℝ)| ≤ Tbox i)
    (hcell : ∀ j i, |(point j i : ℝ) - normalizedRealBoxGrid Tbox A.Q (cell j) i| ≤
      Tbox i * (2 / A.Q)) :
    ‖localLaw.complexMean (fun j => weight j *
        (tests (physical j)).observable (QuotientGroup.mk
          (D.filtration.adaptedPolynomialRealValueHom w
            (fun i => (point j i : ℝ)) g))) -
      localLaw.complexMean (fun j => weight j * A.value (tests (physical j)) P
        (cell j) (point j))‖ ≤ Bweight * (Lip * ε) := by
  apply localLaw.norm_complexMean_weighted_sub_le weight _ _ hBweight hweight
  intro j
  exact (A.error (tests (physical j)) g P hfactor (cell j) (point j)
    (hpoint j) (hcell j)).trans (mul_le_mul_of_nonneg_right (hlip j) hε)

theorem exists_external_restored_scores {Ω J X : Type*} [Fintype Ω] [Fintype J]
    (tests : X → D.Niltest w) (htests : ∀ x, (tests x).UnitIntervalValued)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → J → σ → ℤ)
    (cell : Ω → J → σ → Fin (A.Q + 1)) (weight : Ω → J → ℂ)
    (g P : Ω → (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (hfactor : ∀ a ∈ H, E * P a * R = g a) {Bweight Lip δ : ℝ}
    (hε : 0 ≤ ε) (hBweight : 0 < Bweight)
    (hmargin : 0 < δ - Bweight * (Lip * ε))
    (hweight : ∀ a ∈ H, ∀ j, ‖weight a j‖ ≤ Bweight)
    (hlip : ∀ a ∈ H, ∀ j, ((tests (physical a j)).lipBound : ℝ) ≤ Lip)
    (hpoint : ∀ a ∈ H, ∀ j i, |(point a j i : ℝ)| ≤ Tbox i)
    (hcell : ∀ a ∈ H, ∀ j i,
      |(point a j i : ℝ) - normalizedRealBoxGrid Tbox A.Q (cell a j) i| ≤
        Tbox i * (2 / A.Q))
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun j => weight a j * A.value ((tests (physical a j)).kernelProjection K hK)
        (P a) (cell a j) (point a j))).re) :
    ∃ z : D.RealGroup, z.coord ∈ K.baseChange ℝ ∧
      (∀ y : ℝ ⊗[ℚ] L, ⁅z.coord, y⁆ = 0) ∧
      ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
        (δ - Bweight * (Lip * ε)) / (2 * Bweight) * outer.mass H ≤ outer.mass H' ∧
        ∀ a ∈ H', (δ - Bweight * (Lip * ε)) / 2 ≤
          ((localLaw a).complexMean (fun j => weight a j *
            (tests (physical a j)).observable (z • QuotientGroup.mk
              (D.filtration.adaptedPolynomialRealValueHom w
                (fun i => (point a j i : ℝ)) (g a))))).re := by
  apply Niltest.exists_external_kernelProjection_common_translation tests htests K hK
    outer H hH localLaw physical
    (fun a j => QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
      (fun i => (point a j i : ℝ)) (g a))) weight hBweight hmargin hweight
  intro a ha
  have herr := A.norm_score_sub_le (fun x => (tests x).kernelProjection K hK)
    (localLaw a) (physical a) (point a) (cell a) (weight a) (g a) (P a) (hfactor a ha)
    hε hBweight.le (hweight a ha) (hlip a ha) (hpoint a ha) (hcell a ha)
  have hre := (Complex.abs_re_le_norm _).trans herr
  rw [Complex.sub_re] at hre
  have hs := hscore a ha
  have hlo := (abs_le.mp hre).1
  linarith

end MarkedFiniteScoreFreezing

theorem exists_external_marked_frozen_restored_scores
    {Ω J X : Type*} [Fintype Ω] [Fintype J]
    (Es Rs : Ω → (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (EFs RFs : Ω → (F.realification.adaptedPolynomialFiltration w).Group)
    (boxes : Ω → σ → ℝ)
    (data : ∀ a, MarkedFiniteScoreFreezing (S := S) (hS := hS)
      (Es a) (Rs a) (EFs a) (RFs a) (boxes a) ε B)
    (tests : X → D.Niltest w) (htests : ∀ x, (tests x).UnitIntervalValued)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → J → σ → ℤ)
    (cell : ∀ a, J → σ → Fin ((data a).Q + 1)) (weight : Ω → J → ℂ)
    (g P : Ω → (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (hfactor : ∀ a ∈ H, Es a * P a * Rs a = g a) {Bweight Lip δ : ℝ}
    (hε : 0 ≤ ε) (hBweight : 0 < Bweight)
    (hmargin : 0 < δ - Bweight * (Lip * ε))
    (hweight : ∀ a ∈ H, ∀ j, ‖weight a j‖ ≤ Bweight)
    (hlip : ∀ a ∈ H, ∀ j, ((tests (physical a j)).lipBound : ℝ) ≤ Lip)
    (hpoint : ∀ a ∈ H, ∀ j i, |(point a j i : ℝ)| ≤ boxes a i)
    (hcell : ∀ a ∈ H, ∀ j i,
      |(point a j i : ℝ) - normalizedRealBoxGrid (boxes a) (data a).Q (cell a j) i| ≤
        boxes a i * (2 / (data a).Q))
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun j => weight a j * (data a).value ((tests (physical a j)).kernelProjection K hK)
        (P a) (cell a j) (point a j))).re) :
    ∃ z : D.RealGroup, z.coord ∈ K.baseChange ℝ ∧
      (∀ y : ℝ ⊗[ℚ] L, ⁅z.coord, y⁆ = 0) ∧
      ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
        (δ - Bweight * (Lip * ε)) / (2 * Bweight) * outer.mass H ≤ outer.mass H' ∧
        ∀ a ∈ H', (δ - Bweight * (Lip * ε)) / 2 ≤
          ((localLaw a).complexMean (fun j => weight a j *
            (tests (physical a j)).observable (z • QuotientGroup.mk
              (D.filtration.adaptedPolynomialRealValueHom w
                (fun i => (point a j i : ℝ)) (g a))))).re := by
  apply Niltest.exists_external_kernelProjection_common_translation tests htests K hK
    outer H hH localLaw physical
    (fun a j => QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
      (fun i => (point a j i : ℝ)) (g a))) weight hBweight hmargin hweight
  intro a ha
  have herr := (data a).norm_score_sub_le (fun x => (tests x).kernelProjection K hK)
    (localLaw a) (physical a) (point a) (cell a) (weight a) (g a) (P a) (hfactor a ha)
    hε hBweight.le (hweight a ha) (hlip a ha) (hpoint a ha) (hcell a ha)
  have hre := (Complex.abs_re_le_norm _).trans herr
  rw [Complex.sub_re] at hre
  have hs := hscore a ha
  have hlo := (abs_le.mp hre).1
  linarith

end Erdos3.RationalFilteredNilmanifold

end

end OAI
