import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartPivot
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoordinateFlowProfileIdentity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.GradedFlowLimit

namespace OAI

/-! # The exact height of a word-chart horizontal flow and its graded limit -/

noncomputable section
namespace PolycyclicRecognition

open Module Filter Set
open scoped Topology

variable {L G W I : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]

omit [FiniteDimensional ℝ L] in
/-- Exact height is retained at every finite physical scale. -/
theorem wordChartFlow_height (X : I → L) (S : Finset (FreeMagma I))
    (β : WordBasisSelections X S) (h : L →ₗ[ℝ] W)
    (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    (Exp : L → G) (π : G →* Multiplicative W) (hπ : ∀ x, (π (Exp x)).toAdd = h x)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    {r : ℝ} (hr : 1 ≤ r) (v : L) (z : Fin (finrank ℝ L) → ℝ) (t : ℝ) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    let br := exponentialRescaleBasis b cost (max (Real.log r) 0)
    h (b.equivFun.symm (dynkinFlowMap a (basisBracket br) (br.equivFun (r • v)) (z, t))) =
      h (b.equivFun.symm z) + t • h v := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let br := exponentialRescaleBasis b cost (max (Real.log r) 0)
  let flow := dynkinFlowMap a (basisBracket br) (br.equivFun (r • v))
  have he := congrArg (fun g : G => (π g).toAdd) (exp_basis_horizontal_flow Exp br a hm r t v z)
  simp only [hπ, map_mul, toAdd_mul, map_smul] at he
  have hp (w : Fin (finrank ℝ L) → ℝ) : h (br.equivFun.symm w) = r • h (b.equivFun.symm w) :=
    wordChartPivot_height X S β h hh hr w
  rw [hp, hp] at he
  have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr)
  have he' := congrArg (fun w : W => r⁻¹ • w) he
  simpa only [b, cost, br, map_smul, smul_add, smul_smul, inv_mul_cancel₀ hr0, one_smul,
    ← mul_assoc, inv_mul_cancel₀ hr0, one_mul] using he'

omit [FiniteDimensional ℝ L] in
/-- The limiting horizontal flow projects to the original affine segment.
This follows from convergence and the finite-scale identity, without an
extra homomorphism premise on the limiting polynomial group. -/
theorem gradedWordChartFlow_height (X : I → L) (S : Finset (FreeMagma I))
    (β : WordBasisSelections X S) (h : L →ₗ[ℝ] W)
    (hh : ∀ x y : L, h ⁅x, y⁆ = 0)
    (Exp : L → G) (π : G →* Multiplicative W) (hπ : ∀ x, (π (Exp x)).toAdd = h x)
    {c : ℕ} (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (v : L) (z : Fin (finrank ℝ L) → ℝ) (t : ℝ)
    (hweight : ∀ i j k,
      (WordBasisSelections.basis X S β).repr
          ⁅(WordBasisSelections.basis X S β) i, (WordBasisSelections.basis X S β) j⁆ k ≠ 0 →
        bracketWordExponent (fun _ : I => 1) (β.val i) +
            bracketWordExponent (fun _ : I => 1) (β.val j) ≤
          bracketWordExponent (fun _ : I => 1) (β.val k)) :
    let b := WordBasisSelections.basis X S β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    h (b.equivFun.symm
      (dynkinFlowMap a (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v) (z, t))) =
        h (b.equivFun.symm z) + t • h v := by
  dsimp only
  let b := WordBasisSelections.basis X S β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  let p := h.comp b.equivFun.symm.toLinearMap
  have hv : ∀ j, b.repr v j ≠ 0 → (1 : ℝ) ≤ cost j := by
    intro j _
    have hlen (w : FreeMagma I) : 1 ≤ bracketWordLength w := by
      induction w using FreeMagma.rec with
      | of i => simp [bracketWordLength]
      | mul u w hu hw => simp only [bracketWordLength]; omega
    dsimp only [cost]
    rw [bracketWordExponent_one]
    exact_mod_cast hlen (β.val j)
  have hf := rescaled_horizontal_flow_tendstoUniformlyOn a b cost hweight v hv
    (isCompact_singleton (x := (z, t)))
  have heval := hf.tendsto_at (mem_singleton (z, t))
  have hp := p.continuous_of_finiteDimensional.tendsto _ |>.comp heval
  have hconst : ∀ᶠ s : ℝ in atTop,
      p (dynkinProduct a (basisBracket (exponentialRescaleBasis b cost s)) z
        (t • (exponentialRescaleBasis b cost s).equivFun (Real.exp s • v))) =
        h (b.equivFun.symm z) + t • h v := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    change h (b.equivFun.symm (dynkinProduct a
      (basisBracket (exponentialRescaleBasis b cost s)) z
      (t • (exponentialRescaleBasis b cost s).equivFun (Real.exp s • v)))) = _
    have he := wordChartFlow_height X S β h hh Exp π hπ a hm
      (Real.one_le_exp_iff.mpr hs) v z t
    simpa only [p, b, cost, LinearMap.comp_apply, dynkinFlowMap, ContinuousMap.coe_mk,
      Real.log_exp, max_eq_left hs] using he
  exact tendsto_nhds_unique hp (tendsto_const_nhds.congr' (hconst.mono fun _ he => he.symm))

end PolycyclicRecognition

end

end OAI
