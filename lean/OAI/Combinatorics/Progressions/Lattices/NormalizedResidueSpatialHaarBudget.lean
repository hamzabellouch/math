import OAI.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover
import OAI.Combinatorics.Progressions.Lattices.OriginalKernelResidueRetained

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

private theorem variableLengthZeroCube_pi_residue_disintegration
    {G : Type*} [Fintype G] [DecidableEq G]
    (L : G → ℕ) (q : ℕ) [NeZero q] (hL : ∀ g, 0 < L g) (hq : 0 < q) (hqL : ∀ g, q ≤ L g)
    (test : (G → ZMod q) → (∀ g, IntegerScalarCubeBox Empty (L g)) → ℂ) :
    (FiniteProbabilityWeights.pi (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))).complexMean
      (fun x => test (fun g => ((x g none : ℤ) : ZMod q)) x) =
    (FiniteProbabilityWeights.pi (fun g : G =>
      (integerScalarCubeWeights Empty (L g) (hL g)).fiberLaw
        (fun x => ((x none : ℤ) : ZMod q)))).complexMean (fun r =>
      (FiniteProbabilityWeights.pi (fun g : G => scalarCubeResidueWeights Empty (L g) q (hL g)
        (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl)
          (by simpa using hqL g))).complexMean (test r)) := by
  rw [FiniteProbabilityWeights.pi_complexMean_disintegrate
    (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))
    (fun _ x => ((x none : ℤ) : ZMod q))
    (fun g r => integerScalarCubeWeights_empty_residue_mass_pos (L g) q (hL g) hq (hqL g) r) test]
  apply congrArg (FiniteProbabilityWeights.pi (fun g : G =>
    (integerScalarCubeWeights Empty (L g) (hL g)).fiberLaw
      (fun x => ((x none : ℤ) : ZMod q)))).complexMean
  funext r
  apply congrArg (fun p : FiniteProbabilityWeights (∀ g, IntegerScalarCubeBox Empty (L g)) =>
    p.complexMean (test r))
  apply congrArg FiniteProbabilityWeights.pi
  funext g
  exact integerScalarCubeWeights_empty_residue_condition (L g) q (hL g) hq (hqL g) (r g)

theorem variableLengthZeroCube_pi_uniform_residue_error
    {G : Type*} [Fintype G] [DecidableEq G]
    (L : G → ℕ) (q : ℕ) [NeZero q] (hL : ∀ g, 0 < L g) (hq : 0 < q) (hqL : ∀ g, q ≤ L g)
    (test : (G → ZMod q) → (∀ g, IntegerScalarCubeBox Empty (L g)) → ℂ)
    (hbound : ∀ r x, ‖test r x‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))).complexMean
      (fun x => test (fun g => ((x g none : ℤ) : ZMod q)) x) -
      𝔼 r : G → ZMod q,
        (FiniteProbabilityWeights.pi (fun g : G => scalarCubeResidueWeights Empty (L g) q (hL g)
          (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl)
            (by simpa using hqL g))).complexMean (test r)‖ ≤
      ∑ g, (q : ℝ) / L g := by
  let μ := fun g => (integerScalarCubeWeights Empty (L g) (hL g)).fiberLaw
    (fun x => ((x none : ℤ) : ZMod q))
  let ν := FiniteProbabilityWeights.uniform (ZMod q)
  let F (r : G → ZMod q) :=
    (FiniteProbabilityWeights.pi (fun g : G => scalarCubeResidueWeights Empty (L g) q (hL g)
      (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl)
        (by simpa using hqL g))).complexMean (test r)
  have hF (r : G → ZMod q) : ‖F r‖ ≤ 1 := by
    apply (FiniteProbabilityWeights.norm_complexMean_le_mean_norm _ _).trans
    exact (FiniteProbabilityWeights.mean_mono _ (hbound r)).trans_eq
      (FiniteProbabilityWeights.mean_const _ 1)
  rw [variableLengthZeroCube_pi_residue_disintegration L q hL hq hqL test,
    ← FiniteProbabilityWeights.pi_uniform_complexMean]
  exact (FiniteProbabilityWeights.norm_complexMean_sub_le_weight_l1
    (FiniteProbabilityWeights.pi (fun g : G => μ g))
    (FiniteProbabilityWeights.pi (fun _ : G => ν)) F hF).trans
      ((FiniteProbabilityWeights.pi_weight_l1_le_sum (fun g : G => μ g) (fun _ : G => ν)).trans
        (Finset.sum_le_sum (fun g _ => integerScalarCubeWeights_empty_residue_l1 (L g) q (hL g))))

theorem variableLengthZeroCube_residue_slow_quadrature
    {G : Type*} [Fintype G] [DecidableEq G]
    (L : G → ℕ) (q : ℕ) [NeZero q]
    (hL : ∀ g, 0 < L g) (hq : 0 < q) (hqL : ∀ g, q ≤ L g)
    (hsmall : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / L g) <
      volume.real (scalarCubeDomain Empty))
    (F : (G → ZMod q) → (G → Option Empty → ℝ) → ℂ)
    {K : ℝ≥0} (hF : ∀ r, LipschitzWith K (F r))
    (hbound : ∀ r x, ‖F r x‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))).complexMean
        (fun z => F (fun g => ((z g none : ℤ) : ZMod q))
          (fun g i => (z g i : ℝ) / L g)) -
      𝔼 r : G → ZMod q, ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty /
        volume.real (scalarCubeDomain Empty) + K)) *
          (∑ g, (q : ℝ) / L g) := by
  let test := fun (r : G → ZMod q) (z : ∀ g, IntegerScalarCubeBox Empty (L g)) =>
    F r (fun g i => (z g i : ℝ) / L g)
  let law := fun (r : G → ZMod q) => FiniteProbabilityWeights.pi
    (fun g : G => scalarCubeResidueWeights Empty (L g) q (hL g)
      (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl) (by simpa using hqL g))
  let e : ℝ := 2 * (2 * scalarCubeGridBoundaryConstant Empty /
    volume.real (scalarCubeDomain Empty) + K) * (∑ g, (q : ℝ) / L g)
  have hcond (r : G → ZMod q) :
      ‖(law r).complexMean (test r) - ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ ≤ e := by
    simpa only [law, test, e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
      scalarCubeResidueWeights_pi_complex_riemann L (fun _ => q) hL
        (fun (_ : G) (_ : Option Empty) => q) (fun g _ => r g) (fun _ _ => hq)
        (fun _ _ => le_rfl) (fun g => by simpa using hqL g)
        hsmall (F r) (hF r) zero_le_one (hbound r)
  have hmix := variableLengthZeroCube_pi_uniform_residue_error L q hL hq hqL
    test (fun r _ => hbound r _)
  have havg : ‖(𝔼 r : G → ZMod q, (law r).complexMean (test r)) -
      𝔼 r : G → ZMod q, ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ ≤ e := by
    rw [← Finset.expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    exact (Finset.expect_le_expect (fun r _ => hcond r)).trans_eq (by simp)
  calc
    _ ≤ ‖(FiniteProbabilityWeights.pi (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))).complexMean
        (fun z => test (fun g => ((z g none : ℤ) : ZMod q)) z) -
          𝔼 r : G → ZMod q, (law r).complexMean (test r)‖ +
        ‖(𝔼 r : G → ZMod q, (law r).complexMean (test r)) -
          𝔼 r : G → ZMod q, ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (∑ g, (q : ℝ) / L g) + e := add_le_add hmix havg
    _ = _ := by dsimp only [e]; ring

theorem integerBox_residue_spatial_riemann
    {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (q : ℕ) [NeZero q]
    (hN : ∀ i, 0 < N i) (hqN : ∀ i, q ≤ N i)
    (hsmall : ∀ i, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / N i) < 1)
    (H : (X → ZMod q) → (X → ℝ) → ℂ) {L : ℝ≥0}
    (hH : ∀ r, LipschitzWith L (H r)) (hbound : ∀ r x, ‖H r x‖ ≤ 1) :
    ‖(𝔼 u ∈ integerBox N, H (fun i => (u i : ZMod q))
        (fun i => (u i : ℝ) / N i)) -
      𝔼 r : X → ZMod q, ∫ x, H r x ∂unitBoxMeasure X‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + L)) *
        ∑ i, (q : ℝ) / N i := by
  let F := fun (r : X → ZMod q) (x : X → Option Empty → ℝ) => H r (fun i => x i none)
  have hproject : LipschitzWith 1
      (fun x : X → Option Empty → ℝ => fun i => x i none) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    exact (dist_le_pi_dist (x i) (y i) none).trans (dist_le_pi_dist x y i)
  have hF (r) : LipschitzWith L (F r) := by
    simpa only [mul_one, Function.comp_def, F] using (hH r).comp hproject
  have he := variableLengthZeroCube_residue_slow_quadrature N q hN (NeZero.pos q) hqN
    (fun i => by simpa only [Measure.real, scalarCubeDomain_empty_volume,
      ENNReal.toReal_one] using hsmall i) F hF (fun r _ => hbound r _)
  have hid (r : X → ZMod q) :
      (∫ x, F r x ∂scalarCubeProductMeasure X Empty) = ∫ x, H r x ∂unitBoxMeasure X := by
    rw [← scalarCubeProductMeasure_empty_map X]
    exact (integral_map
      (by fun_prop : Measurable (fun x : X → Option Empty → ℝ => fun i => x i none)).aemeasurable
      (hH r).continuous.measurable.aestronglyMeasurable).symm
  simp_rw [hid] at he
  have hmean := integerScalarCubeWeights_zero_product_complexMean N hN
    (fun u => H (fun i => (u i : ZMod q)) (fun i => (u i : ℝ) / N i))
  simpa only [F, hmean, Measure.real, scalarCubeDomain_empty_volume,
    ENNReal.toReal_one, div_one] using he

namespace VectorPolynomial.NormalizedPolynomialTwist

theorem integerBox_frozenSingleSiteHaarReference_riemann
    {X : Type*} [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) [NeZero W.modulus]
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (hqN : ∀ i, W.modulus ≤ N i)
    (hsmall : ∀ i, scalarCubeGridBoundaryConstant Empty * ((W.modulus : ℝ) / N i) < 1) :
    ‖(𝔼 u ∈ integerBox N, W.frozenSingleSiteHaarReference U ν
        (fun i => (u i : ZMod W.modulus)) (fun i => (u i : ℝ) / N i)) -
      𝔼 r : X → ZMod W.modulus, ∫ x, W.frozenSingleSiteHaarReference U ν r x
        ∂unitBoxMeasure X‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + L)) *
        ∑ i, (W.modulus : ℝ) / N i := by
  exact integerBox_residue_spatial_riemann N W.modulus hN hqN hsmall
    (W.frozenSingleSiteHaarReference U ν)
    (W.frozenSingleSiteHaarReference_lipschitz U ν)
    (W.norm_frozenSingleSiteHaarReference_le U ν)

end VectorPolynomial.NormalizedPolynomialTwist
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem normalizedResidueSpatial_budget
    {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) (q : ℕ) (K : ℝ≥0) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hdim : (Fintype.card X : ℝ) ≤ P)
    (hq : (q : ℝ) ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp P)
    (hN : ∀ i, Real.exp (3 * P + E + 20) ≤ (N i : ℝ)) :
    (∀ i, 0 < N i) ∧ (∀ i, q ≤ N i) ∧
      (∀ i, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / N i) < 1) ∧
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + (K : ℝ))) *
        (∑ i, (q : ℝ) / N i) ≤ Real.exp (-E) := by
  have hNp (i : X) : (0 : ℝ) < N i := (Real.exp_pos _).trans_le (hN i)
  have hqN (i : X) : (q : ℝ) ≤ N i :=
    hq.trans ((Real.exp_le_exp.mpr (by linarith)).trans (hN i))
  have hmesh (i : X) : (q : ℝ) / N i ≤ Real.exp (-2 * P - E - 20) := by
    calc
      _ ≤ Real.exp P / Real.exp (3 * P + E + 20) :=
        div_le_div₀ (Real.exp_nonneg _) hq (Real.exp_pos _) (hN i)
      _ = _ := by rw [← Real.exp_sub]; congr 1; ring
  have hC : scalarCubeGridBoundaryConstant Empty = 4 := by
    norm_num [scalarCubeGridBoundaryConstant]
  have hexpP : 1 ≤ Real.exp P := (Real.add_one_le_exp P).trans' (by linarith)
  have hpref : 1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + (K : ℝ)) ≤
      19 * Real.exp P := by rw [hC]; linarith
  have hdimexp : (Fintype.card X : ℝ) ≤ Real.exp P :=
    hdim.trans (by linarith only [Real.add_one_le_exp P])
  have hsum : (∑ i, (q : ℝ) / N i) ≤
      Real.exp P * Real.exp (-2 * P - E - 20) := by
    calc
      _ ≤ ∑ _i : X, Real.exp (-2 * P - E - 20) := Finset.sum_le_sum (fun i _ => hmesh i)
      _ = (Fintype.card X : ℝ) * Real.exp (-2 * P - E - 20) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hdimexp (Real.exp_nonneg _)
  refine ⟨fun i => by exact_mod_cast hNp i, fun i => by exact_mod_cast hqN i, ?_, ?_⟩
  · intro i
    rw [hC]
    calc
      4 * ((q : ℝ) / N i) ≤ 4 * Real.exp (-2 * P - E - 20) := by gcongr; exact hmesh i
      _ ≤ 4 * Real.exp (-20) := by gcongr; linarith
      _ < 1 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
        linarith only [Real.add_one_le_exp 20]
  · calc
      _ ≤ (19 * Real.exp P) * (Real.exp P * Real.exp (-2 * P - E - 20)) :=
        mul_le_mul hpref hsum (Finset.sum_nonneg (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
          (by positivity)
      _ = 19 * Real.exp (-E - 20) := by
        rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-E) := by
        rw [Real.exp_sub, ← mul_div_assoc, div_le_iff₀ (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (by linarith only [Real.add_one_le_exp 20])
          (Real.exp_nonneg (-E)) |>.trans_eq (mul_comm _ _)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem integerBox_frozenSingleSiteHaarReference_riemann_budget
    {X : Type*} [Fintype X] [DecidableEq X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j))
        (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) [NeZero W.modulus]
    {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hX : (Fintype.card X : ℝ) ≤ P)
    (hL : (L : ℝ) ≤ Real.exp P) (hmod : (W.modulus : ℝ) ≤ Real.exp P)
    (N : X → ℕ) (hsize : ∀ i, Real.exp (3 * P + E + 20) ≤ (N i : ℝ)) :
    ‖(𝔼 u ∈ integerBox N, W.frozenSingleSiteHaarReference U ν
        (fun i => (u i : ZMod W.modulus)) (fun i => (u i : ℝ) / N i)) -
      𝔼 r : X → ZMod W.modulus, ∫ x, W.frozenSingleSiteHaarReference U ν r x
        ∂unitBoxMeasure X‖ ≤ Real.exp (-E) := by
  obtain ⟨hN, hqN, hsmall, herror⟩ :=
    normalizedResidueSpatial_budget N W.modulus L hP hE hX hmod hL hsize
  exact (W.integerBox_frozenSingleSiteHaarReference_riemann U ν N hN hqN hsmall).trans herror

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI
