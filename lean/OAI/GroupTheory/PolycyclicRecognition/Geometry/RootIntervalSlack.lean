import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniformInteriorSlack
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BoxWordExpansion
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoordinateChartSampling
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBoxes

namespace OAI

/-! # Interior slack for the actual bounded root intervals -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter Set
open scoped Topology BigOperators

variable {I L G A : Type*} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Every bounded interval in an interior root direction remains in the
unit normalized box after conjugation by the enlarged suffix. The actual
finite-word envelope is constructed from the root and suffix coordinates. -/
theorem root_interval_conjugation_mem_box
    [Nonempty (Fin (finrank ℝ L))]
    (X : I → L) {k₀ c₀ : ℕ} (hk : lowerCentralSeries ℝ L L k₀ = ⊥)
    (hletters : ∀ i, FreeMagma.of i ∈ boundedBracketWords (I := I) k₀)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (s q : I → ℝ)
    (β : WordBasisSelections X (boundedBracketWords k₀))
    (hβ : IsMaximizingColumnBasis
      (wordListCoordinates X (boundedBracketWords k₀) b₀)
      (fun w => bracketWordExponent s w) β.val)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (a : DynkinCoefficients c₀ 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    {δ c lo hi R : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hR : 0 ≤ R)
    (hcost : ∀ w : boundedBracketWords (I := I) k₀,
      lo ≤ bracketWordExponent s w ∧ bracketWordExponent s w ≤ hi)
    (hgap : (k₀ : ℝ) * hi < c * lo)
    (hq : ∀ i, q i ≤ (1 - c * δ) * s i)
    (ε : ℝ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℝ → L)
    (hkbox : ∀ᶠ r in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k₀) β)
        (fun i => (1 + δ) * bracketWordExponent s (β.val i)) r).equivFun (k r)‖ ≤
          Real.exp (r * ε r)) :
    ∀ᶠ r in atTop, ∀ i t, |t| ≤ R →
      Exp (k r) * Exp ((t * Real.exp (r * q i)) • X i) * (Exp (k r))⁻¹ ∈
        exponentialCoordinateBox Exp
          (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k₀) β)
            (fun i => bracketWordExponent s (β.val i)) r) 1 := by
  classical
  let S := boundedBracketWords (I := I) k₀
  let cost : S → ℝ := fun w => bracketWordExponent s w
  let b := fun r => exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun i => cost (β.val i)) r
  let bk := fun r => exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun i => (1 + δ) * cost (β.val i)) r
  have hex (r : ℝ) := exists_word_expansion_of_rescaled_norm_le X S β
    (fun w => (1 + δ) * cost w) r (norm_nonneg ((bk r).equivFun (k r))) (k r) le_rfl
  choose ak hak hkeq using hex
  have hak' : ∀ᶠ r in atTop, ∀ w,
      |ak r w| ≤ (finrank ℝ L : ℝ) * Real.exp (r * ((1 + δ) * cost w + ε r)) := by
    filter_upwards [hkbox] with r hr w
    apply (hak r w).trans
    calc
      _ ≤ (finrank ℝ L : ℝ) * Real.exp (r * ε r) *
          Real.exp (r * ((1 + δ) * cost w)) := by gcongr
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  let Z := {z : I × ℝ // |z.2| ≤ R}
  let letter (i : I) : S := ⟨FreeMagma.of i, hletters i⟩
  let au (r : ℝ) (z : Z) (w : S) :=
    if w = letter z.val.1 then z.val.2 * Real.exp (r * q z.val.1) else 0
  have hau : ∀ᶠ r in atTop, ∀ z w,
      |au r z w| ≤ R * Real.exp (r * ((1 - c * δ) * cost w + ε r)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr z w
    by_cases hw : w = letter z.val.1
    · subst w
      simp only [au, ite_eq_left rfl, abs_mul, abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul z.property _ (Real.exp_pos _).le hR
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hr
      have he : cost (letter z.val.1) = s z.val.1 := by
        simp only [cost, letter, bracketWordExponent_of]
      rw [he]
      exact (hq _).trans (le_add_of_nonneg_right (hεpos r))
    · simp only [au, ite_eq_right hw, abs_zero]
      positivity
  have hueq (r : ℝ) (z : Z) :
      ∑ w, au r z w • evalBracketWord X w =
        (z.val.2 * Real.exp (r * q z.val.1)) • X z.val.1 := by
    simp [au, letter]
  have hnil : lowerCentralSeries ℝ L L (k₀ + 1) = ⊥ := by
    rw [lowerCentralSeries_succ, hk]
    simp
  have hu := rescaled_word_conjugation_tendstoUniformly X hk hnil b₀ s
    (fun _ => β) (fun _ => hβ) Exp hinj hneg a hm j ρ hρ hmatch hδ hc hhi
    (Nat.cast_nonneg _) hR hcost hgap ε hε ak au hak' hau
  have hsmall := (Metric.tendstoUniformly_iff.mp hu) 1 zero_lt_one
  filter_upwards [hsmall] with r hr i t ht
  let z : Z := ⟨(i, t), ht⟩
  let v := dynkinProduct a (basisBracket (b r))
    (dynkinProduct a (basisBracket (b r)) ((b r).equivFun (k r))
      ((b r).equivFun ((t * Real.exp (r * q i)) • X i))) (-((b r).equivFun (k r)))
  refine ⟨(b r).equivFun.symm v, ?_, ?_⟩
  · simp only [v, exp_basis_dynkinProduct (b r) Exp a hm,
      LinearEquiv.symm_apply_apply, map_neg, hneg]
  · rw [LinearEquiv.apply_symm_apply]
    have hh := hr z
    change dist 0 (dynkinProduct a (basisBracket (b r))
      (dynkinProduct a (basisBracket (b r))
        ((b r).equivFun (∑ w, ak r w • evalBracketWord X w))
        ((b r).equivFun (∑ w, au r z w • evalBracketWord X w)))
      (-((b r).equivFun (∑ w, ak r w • evalBracketWord X w)))) < 1 at hh
    rw [hkeq, hueq] at hh
    simpa only [v, z, dist_zero_left] using hh.le

end PolycyclicRecognition

end

end OAI
