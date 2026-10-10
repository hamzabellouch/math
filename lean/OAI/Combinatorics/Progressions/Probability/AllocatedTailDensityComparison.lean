import OAI.Combinatorics.Progressions.Estimates.AllocatedProxyL1Averaging

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "sets" => (fun a : {a // ¬grid a} => rows (Sigma.fst (Subtype.val a)))

include hR hσ hrows hcard in
theorem exists_allocated_tail_density_comparison
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B) (O := fun a => O a.1) (α := α) degree
        (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
        A T (ε / 2) ∧
      let t := booleanMassPerturbationScale (B := B) (O := fun a => O a.1) (α := α)
        ((G × Option α) ⊕ (Σ a, SamplerCoefficientSlot G B degree a)) degree
        (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧ ((∀ j, σ j ≤ t) →
      ∀ block : ∀ a : {a // ¬grid a}, O a.val.1 → B a.val,
      (∀ a, Function.Injective (block a)) →
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∫ v, |diagonalImageDensity (fun o : realOutput => R o.1.val.1)
          (activeAveragedProfileIdeal (G := G) (B := B) (G × Option α) degree grid sets δ) v -
        allocatedContinuousLongJetProxy B U basis S x u rows s hA v|) ≤ ε) := by
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcomp⟩ :=
    exists_allocated_proxy_l1_comparison (G := G) (α := α) (O := O)
      B ψ hψ hrange hzero hone A T hLip hTransition hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro hsmall block hblock s hA
  have hL1 := (hcomp U basis hR hσ hsmall S x u rows hrows hcard
    (fun a => ⟨block a, hblock a⟩) s hA).1
  rw [diagonalImageDensity_eq_pullback (fun o : realOutput => R o.1.val.1)
    (fun o => (hR o.1.val.1).ne')]
  exact hL1

end Erdos3.VectorPolynomial

end

end OAI
