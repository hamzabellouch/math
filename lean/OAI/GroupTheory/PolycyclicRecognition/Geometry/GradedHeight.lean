import OAI.GroupTheory.PolycyclicRecognition.Algebra.GradedHorizontalStructure
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoordinateChartSampling
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateTopology

namespace OAI

/-! # The original height is a homomorphism on the graded group -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter
open scoped Topology

variable {L G W I : Type*} [LieRing L] [LieAlgebra ℝ L]
  [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [Fintype I] [DecidableEq I]

/-- Exact height additivity survives in every rescaled word chart. -/
theorem rescaledWordChartProduct_height
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    (Exp : L → G) (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = h x)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (r : ℝ) (x y : Fin (finrank ℝ L) → ℝ) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    h (b.equivFun.symm (dynkinProduct a
      (basisBracket (exponentialRescaleBasis b cost r)) x y)) =
        h (b.equivFun.symm x) + h (b.equivFun.symm y) := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let br := exponentialRescaleBasis b cost r
  have hp (z : Fin (finrank ℝ L) → ℝ) :
      h (br.equivFun.symm z) = Real.exp r • h (b.equivFun.symm z) := by
    simpa only [br, cost, bracketWordExponent_one, Real.log_exp] using
      word_length_chart_height X S β h hh (Real.exp_pos r) z
  have he := congrArg (fun g : G => (π g).toAdd)
    (exp_basis_dynkinProduct br Exp a hm x y)
  simp only [map_mul, toAdd_mul, hπ, hp, ← smul_add] at he
  exact (smul_right_injective W (ne_of_gt (Real.exp_pos r))) he

/-- The rescaled coordinates of a scaled pivot retain exactly its height. -/
theorem word_length_chart_pivot_height
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (height : L →ₗ[ℝ] W) (hkill : ∀ x y : L, height ⁅x, y⁆ = 0)
    {r : ℝ} (hr : 0 < r) (pivot : L) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    let br := exponentialRescaleBasis b cost (Real.log r)
    height (b.equivFun.symm (br.equivFun (r • pivot))) = height pivot := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let br := exponentialRescaleBasis b
    (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (Real.log r)
  have he : height (br.equivFun.symm (br.equivFun (r • pivot))) =
      r • height (b.equivFun.symm (br.equivFun (r • pivot))) := by
    simpa only [b, br, bracketWordExponent_one] using
      word_length_chart_height X S β height hkill hr (br.equivFun (r • pivot))
  rw [LinearEquiv.symm_apply_apply, map_smul] at he
  exact ((smul_right_injective W hr.ne') he).symm

/-- Passing the finite-scale identity to the limiting polynomial product
gives the actual height homomorphism, without a new input on the limit. -/
theorem gradedWordChartProduct_height
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    (Exp : L → G) (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = h x)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (hweight : ∀ i j k,
      (WordBasisSelections.basis X S β).repr
        ⁅(WordBasisSelections.basis X S β) i, (WordBasisSelections.basis X S β) j⁆ k ≠ 0 →
      bracketWordExponent (fun _ : I => 1) (β.val i) +
        bracketWordExponent (fun _ : I => 1) (β.val j) ≤
          bracketWordExponent (fun _ : I => 1) (β.val k))
    (x y : Fin (finrank ℝ L) → ℝ) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    h (b.equivFun.symm (dynkinProduct a (gradedCoordinateBracket b cost) x y)) =
      h (b.equivFun.symm x) + h (b.equivFun.symm y) := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let p := h.comp b.equivFun.symm.toLinearMap
  have hprod := ((continuous_dynkinProduct a id (fun _ => x) (fun _ => y)
    continuous_id continuous_const continuous_const).tendsto
      (gradedCoordinateBracket b cost)).comp
        (basisBracket_rescale_tendsto b cost hweight)
  have hp := p.continuous_of_finiteDimensional.tendsto _ |>.comp hprod
  have he : (fun r : ℝ => p (dynkinProduct a
      (basisBracket (exponentialRescaleBasis b cost r)) x y)) =
      (fun _ => h (b.equivFun.symm x) + h (b.equivFun.symm y)) := by
    funext r
    exact rescaledWordChartProduct_height X S β h hh Exp π hπ a hm r x y
  dsimp only [Function.comp_def, id_eq] at hp
  rw [he] at hp
  exact tendsto_nhds_unique hp tendsto_const_nhds

/-- Regard an additive coordinate height as a homomorphism on the
polynomial group. Its additivity is supplied by the preceding limit proof. -/
def polynomialCoordinateHeightHom
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : V → V → V) (hg : PolynomialGroupLaws m) (p : V →L[ℝ] W)
    (hp : ∀ x y, p (m x y) = p x + p y) :
    PolynomialCoordinateGroup m hg →* Multiplicative W where
  toFun x := Multiplicative.ofAdd (p x)
  map_one' := by change Multiplicative.ofAdd (p 0) = 1; rw [map_zero]; rfl
  map_mul' x y := congrArg Multiplicative.ofAdd (hp x y)

/-- Surjectivity of the original height persists on the horizontal layer. -/
theorem surjective_word_height_on_horizontal
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
    [FiniteDimensional ℝ L]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (h : L →ₗ[ℝ] W) (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    (hsurj : Function.Surjective h) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    let p := (h.comp b.equivFun.symm.toLinearMap).toContinuousLinearMap
    Function.Surjective (p.comp (gradedGeneratorMap b cost 1)) := by
  dsimp only
  intro w
  obtain ⟨v, hv⟩ := hsurj w
  refine ⟨v, ?_⟩
  exact (gradedGenerator_word_height X S β h hh v).trans hv

end PolycyclicRecognition

end

end OAI
