import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanChartAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniformInteriorSlack

namespace OAI

/-! # Interior slack for actual scaled Cartan chart positions -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter
open scoped BigOperators Topology

variable {L W Z I G A : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The conjugation parameter for a fixed normal-factor move tends to zero
uniformly over the bounded interior chart samples, even after the enlarged
deterministic suffix. The chart action and both word expansions are derived
from the actual Lie algebra. -/
theorem chart_suffix_conjugation_tendstoUniformly
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi)
    (ht : 0 ≤ 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (X : I → H) (S : Finset (FreeMagma I)) (βD : WordBasisSelections X S)
    (z : Z → Fin (finrank ℝ H) → ℝ) {R : ℝ} (hR : 0 ≤ R) (hz : ∀ u, ‖z u‖ ≤ R)
    (hdomain : ∀ u, eW (heightProjection T.character
      ((WordBasisSelections.basis X S βD).equivFun.symm (z u) : L)) ∈
        (fun x => (1 - c * δ) • x) '' E)
    (Exp : cartanRootIdeal H → G) (hinj : Function.Injective Exp)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    {c₀ : ℕ} (a : DynkinCoefficients c₀ 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : cartanRootIdeal H →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (ε : ℝ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℝ → cartanRootIdeal H)
    (hk : ∀ᶠ r : ℝ in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) r).equivFun (k r)‖ ≤
          Real.exp (r * ε r))
    (v : cartanRootIdeal H) :
    let bN := fun r => M.boxBasis T hunimod eW E β r
    let bD := fun r => exponentialRescaleBasis (WordBasisSelections.basis X S βD)
      (fun i => (bracketWordLength (βD.val i : FreeMagma I) : ℝ)) (Real.log r)
    TendstoUniformly (fun r u => dynkinProduct a (basisBracket (bN r))
      (dynkinProduct a (basisBracket (bN r)) ((bN r).equivFun (k r))
        ((bN r).equivFun (cartanIdealAdjointAutomorphism T H
          ((bD r).equivFun.symm (z u)) v))) (-((bN r).equivFun (k r))))
      (fun _ => 0) atTop := by
  classical
  obtain ⟨εu, au, hεupos, hεu, hau⟩ := M.exists_chart_adjoint_word_envelope T hunimod eW
    b₀ hE hne ht β γ hβ X S βD z hR hz hdomain v
  let bk := fun r => exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
    (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) r
  have hex (r : ℝ) := exists_word_expansion_of_rescaled_norm_le M.letter M.wordList β
    (fun w => (1 + δ) * M.boxCost T hunimod eW E w) r
    (norm_nonneg ((bk r).equivFun (k r))) (k r) le_rfl
  choose ak hak hkeq using hex
  have hkcoeff : ∀ᶠ r : ℝ in atTop, ∀ w,
      |ak r w| ≤ (finrank ℝ (cartanRootIdeal H) : ℝ) *
        Real.exp (r * ((1 + δ) * M.boxCost T hunimod eW E w + (ε r + εu r))) := by
    filter_upwards [hk, eventually_ge_atTop (0 : ℝ)] with r hr hr0 w
    apply (hak r w).trans
    calc
      _ ≤ (finrank ℝ (cartanRootIdeal H) : ℝ) * Real.exp (r * ε r) *
          Real.exp (r * ((1 + δ) * M.boxCost T hunimod eW E w)) := by gcongr
      _ = (finrank ℝ (cartanRootIdeal H) : ℝ) *
          Real.exp (r * ((1 + δ) * M.boxCost T hunimod eW E w + ε r)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_right (hεupos r)
  have hucoeff : ∀ᶠ r : ℝ in atTop, ∀ u w,
      |au r u w| ≤ (1 : ℝ) *
        Real.exp (r * ((1 - c * δ) * M.boxCost T hunimod eW E w + (ε r + εu r))) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr u w
    apply ((hau r hr u).1 w).trans
    rw [one_mul]
    apply Real.exp_le_exp.mpr
    have hp := hεpos r
    nlinarith
  have hnil : lowerCentralSeries ℝ (cartanRootIdeal H) (cartanRootIdeal H) (M.bound + 1) = ⊥ := by
    rw [lowerCentralSeries_succ, M.bound_zero]
    simp
  have hlim : Tendsto (fun r => ε r + εu r) atTop (𝓝 0) := by
    simpa only [add_zero] using hε.add hεu
  have hu := rescaled_word_conjugation_tendstoUniformly M.letter M.bound_zero hnil b₀
    ((M.supportIn T hunimod eW).weightSupport E) (fun _ => β) (fun _ => hβ)
    Exp hinj hneg a hm j ρ hρ hmatch hδ hc hhi (Nat.cast_nonneg _) zero_le_one
    hcost hgap (fun r => ε r + εu r) hlim ak au hkcoeff hucoeff
  apply (tendstoUniformly_congr ?_).mp hu
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  funext u
  simp only [hkeq, (hau r hr u).2]
  rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
