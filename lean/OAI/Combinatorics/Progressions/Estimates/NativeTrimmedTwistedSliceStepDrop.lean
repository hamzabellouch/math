import OAI.Combinatorics.Progressions.Dynamics.NativeTwistedSliceBudget
import OAI.Combinatorics.Progressions.Lattices.NativePairAffineCellStepDrop

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold BooleanCubeKernel
open VectorPolynomial
open scoped TensorProduct BigOperators NNReal

theorem exists_native_twisted_slice_step_drop.{universeLevel} (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {A K X : Type*} [Fintype A]
      [Fintype K] [DecidableEq K] [Nonempty K] [Fintype X]
      {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)] [IsEmpty (Σ j, J j)]
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (twists : A → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (_hq : 0 < q)
      (hlen : ∀ k, 0 < S.length k) {p : ℝ} (_hp : 0 ≤ p)
      (_hS : ∀ k, Real.exp (-p) * (P k : ℝ) ≤ S.length k)
      (_hP : ∀ k, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (P k : ℝ))
      (_hperiod : ((∏ a, (twists a).modulus : ℕ) : ℝ) ≤ Real.exp p)
      (_hLip : (Lip : ℝ) ≤ Real.exp p)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (frame : A → Option K × X → ℤ) (B : A → K → ℝ)
      (_hB : ∀ a k, 0 ≤ B a k) (_hsum : ∀ a, ∑ k, B a k ≤ 1)
      (_hslope : ∀ a k x, |(frame a (some k, x) : ℝ) / N x| * P k ≤ B a k)
      {LG MG : Type universeLevel} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
      (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
      (V : D.Niltest (fun _ : K => 1)) (W : E.Niltest (fun _ : K => 1))
      (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p) (_hWnorm : W.normBound ≤ 1)
      (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
      (_hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
      (_hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
      (_hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        V.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x)
      (_hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
        W.observable (z • x) = CircleFourier.character
          ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x)
      (_hK : (Fintype.card K : ℝ) ≤ p) (a : A)
      (_hbias : Real.exp (-p) ≤ ‖(S.fullSliceLaw hlen).complexMean (fun t =>
        star ((twists a).eval N poly (integerPhysicalSite t.val (frame a))) *
          (V.eval t.val * W.eval t.val))‖),
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra LG MG))) ℚ (PairAlgebra LG MG))
        (ω : Fin (finrank ℚ (PairAlgebra LG MG)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤
          (p + 2 + C) ^ C) ∧
        (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency η θ) (fun k => (P k : ℝ))
          (pairOrbitSymbol D E V.orbit W.orbit b ω hF)
          ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23)) := by
  obtain ⟨C, hC, hstep⟩ := exists_native_pair_affine_cell_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro A K X _ _ _ _ _ m J _ _ periodCap coverCap Lip twists P q S hq hlen p hp hS hP
    hperiod hLip N poly frame B hB hsum hslope LG MG _ _ _ _ d e _ _ _ _ _ _ _ _
    D E V W hV hW hWnorm η θ hηheight hθheight hη hθ hK a hbias
  have hbudget : 0 ≤ (p + 2 + C) ^ C := by positivity
  have hPfreeze (k : K) : Real.exp (p + (3 * (2 * p + 2) + 16)) ≤ (P k : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans (hP k)
  have hperiod' : ((∏ a, (twists a).modulus : ℕ) : ℝ) ≤ Real.exp (2 * p + 2) :=
    hperiod.trans (Real.exp_le_exp.mpr (by linarith))
  obtain ⟨T, hTq, hTlen, hTside, hcorr⟩ :=
    NormalizedPolynomialTwist.exists_niltest_pair_correlation_subrectangle twists S hq hlen
      (by linarith : 0 ≤ 2 * p + 2) hS hPfreeze hperiod' N poly frame B hB hslope
      V W hV hWnorm a (Real.exp_pos (-p)) hbias
  have herror := nativeTwistedSlice_freezing_error hp Lip.coe_nonneg hLip
    (Finset.sum_nonneg (fun k _ => hB a k)) (hsum a)
  have hbias' : Real.exp (-(p + 2)) ≤ ‖𝔼 x ∈ translatedIntegerBox (0 : K → ℤ) T.length,
      V.eval (fun k => ((q * ∏ a, (twists a).modulus : ℕ) : ℤ) * x k + T.start k) *
        W.eval (fun k => ((q * ∏ a, (twists a).modulus : ℕ) : ℤ) * x k + T.start k)‖ :=
    (nativeTwistedSlice_bias_precision p).trans (by linarith)
  have hTside' (k : K) : Real.exp (-(7 * p + 22)) * (P k : ℝ) ≤ T.length k := by
    simpa only [show p + (3 * (2 * p + 2) + 16) = 7 * p + 22 by ring] using hTside k
  have hlong (k : K) : Real.exp ((p + 2 + C) ^ C) ≤ (T.length k : ℝ) := by
    calc
      _ = Real.exp (-(7 * p + 22)) * Real.exp ((p + 2 + C) ^ C + 7 * p + 22) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(7 * p + 22)) * (P k : ℝ) :=
        mul_le_mul_of_nonneg_left (hP k) (Real.exp_nonneg _)
      _ ≤ _ := hTside' k
  have hPpos (k : K) : (0 : ℝ) < P k := (Real.exp_pos _).trans_le (hP k)
  have hphysical (k : K) : Real.exp (-(7 * p + 22)) *
      ((P k : ℝ) / (q * ∏ a, (twists a).modulus : ℕ)) ≤ T.length k := by
    apply le_trans _ (hTside' k)
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
    exact div_le_self (hPpos k).le (by exact_mod_cast hTq)
  obtain ⟨k₀⟩ := ‹Nonempty K›
  have htwo : 2 ≤ S.length k₀ := by
    have he := S.length_large_of_cost hS hPfreeze k₀
    have ht := Real.add_one_le_exp (3 * (2 * p + 2) + 16)
    have : (2 : ℝ) ≤ S.length k₀ := by linarith
    exact_mod_cast this
  have hstride : ((q * ∏ a, (twists a).modulus : ℕ) : ℝ) ≤ Real.exp (2 * p + 1) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ (2 * Real.exp p) * Real.exp p :=
        mul_le_mul (S.stride_le_twice_exp_cost k₀ htwo (hS k₀)) hperiod
          (Nat.cast_nonneg _) (by positivity)
      _ ≤ Real.exp 1 * (Real.exp p * Real.exp p) := by
        have := Real.add_one_le_exp 1
        nlinarith [mul_pos (Real.exp_pos p) (Real.exp_pos p)]
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hp' : p ≤ p + 2 := by linarith
  obtain ⟨b, ω, hF, hb, hf⟩ := hstep D E V W (by linarith : 2 ≤ p + 2)
    (by linarith : 0 ≤ 7 * p + 22) (by linarith : 0 ≤ 2 * p + 1)
    (hV.mono hp') (hW.mono hp') _ hTq hstride (fun k => (T.start k : ℤ)) η θ
    (fun i => (hηheight i).trans hp') (fun i => (hθheight i).trans hp') hη hθ
    0 T.length (fun k => (P k : ℝ)) hTlen hPpos (hK.trans hp') hlong hphysical hbias'
  refine ⟨b, ω, hF, hb, ?_⟩
  convert hf using 1; ring

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold BooleanCubeKernel VectorPolynomial
open scoped TensorProduct BigOperators NNReal

theorem exists_native_trimmed_twisted_slice_step_drop.{universeLevel} (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {A K X : Type*} [Fintype A]
      [Fintype K] [DecidableEq K] [Nonempty K] [Fintype X]
      {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)] [IsEmpty (Σ j, J j)]
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (twists : A → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (_hq : 0 < q)
      (hlen : ∀ k, 0 < S.length k) {p : ℝ} (_hp : 0 ≤ p)
      (_hS : ∀ k, Real.exp (-p) * (P k : ℝ) ≤ S.length k)
      (_hP : ∀ k, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (P k : ℝ))
      (_hperiod : ((∏ a, (twists a).modulus : ℕ) : ℝ) ≤ Real.exp p)
      (_hLip : (Lip : ℝ) ≤ Real.exp p)
      (N : X → ℕ) (_hN : ∀ x, 0 < N x) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (τ : ℝ) (_hτ : 0 ≤ τ) (_hτone : τ ≤ 1)
      (base : A → X → ℤ)
      (noise : A → rectangularWeightIndices 0
        (trimmedSpatialWidths (K := K) (∑ k, (P k : ℝ)) τ N) 1)
      {LG MG : Type universeLevel} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
      (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
      (V : D.Niltest (fun _ : K => 1)) (W : E.Niltest (fun _ : K => 1))
      (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p) (_hWnorm : W.normBound ≤ 1)
      (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
      (_hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
      (_hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
      (_hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        V.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x)
      (_hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
        W.observable (z • x) = CircleFourier.character
          ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x)
      (_hK : (Fintype.card K : ℝ) ≤ p) (a : A)
      (_hbias : Real.exp (-p) ≤ ‖(S.fullSliceLaw hlen).complexMean (fun t =>
        star ((twists a).eval N poly (jointIntegerPhysicalSite t.val (base a, (noise a).val))) *
          (V.eval t.val * W.eval t.val))‖),
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra LG MG))) ℚ (PairAlgebra LG MG))
        (ω : Fin (finrank ℚ (PairAlgebra LG MG)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤
          (p + 2 + C) ^ C) ∧
        (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency η θ) (fun k => (P k : ℝ))
          (pairOrbitSymbol D E V.orbit W.orbit b ω hF)
          ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23)) := by
  obtain ⟨C, hC, hstep⟩ := exists_native_twisted_slice_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro A K X _ _ _ _ _ m J _ _ periodCap coverCap Lip twists P q S hq hlen p hp hS hP
    hperiod hLip N hN poly τ hτ hτone base noise LG MG _ _ _ _ d e _ _ _ _ _ _ _ _
    D E V W hV hW hWnorm η θ hηheight hθheight hη hθ hK a hbias
  let total : ℝ := ∑ k, (P k : ℝ)
  have htotal : 0 ≤ total := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  let B : A → K → ℝ := fun _ k => τ * (P k : ℝ) / (8 * (1 + total))
  let frame : A → Option K × X → ℤ := fun a i =>
    jointIntegerFrame (base a, (noise a).val) i.1 i.2
  have hB (a : A) (k : K) : 0 ≤ B a k := by dsimp [B]; positivity
  have hsum (a : A) : ∑ k, B a k ≤ 1 := by
    change (∑ k, τ * (P k : ℝ) / (8 * (1 + total))) ≤ 1
    rw [← Finset.sum_div, ← Finset.mul_sum]
    change τ * total / (8 * (1 + total)) ≤ 1
    apply (div_le_iff₀ (by positivity : 0 < 8 * (1 + total))).mpr
    have hm := mul_le_mul_of_nonneg_right hτone htotal
    nlinarith
  have hslope (a : A) (k : K) (x : X) :
      |(frame a (some k, x) : ℝ) / N x| * P k ≤ B a k :=
    trimmedSpatial_normalized_parameter_slope P N hN htotal hτ (noise a) k x
  have hsite (t : K → ℤ) : integerPhysicalSite t (frame a) =
      jointIntegerPhysicalSite t (base a, (noise a).val) := by
    funext x
    simp only [integerPhysicalSite, frame, jointIntegerFrame, jointIntegerPhysicalSite,
      Pi.add_apply, add_assoc]
  exact hstep twists S hq hlen hp hS hP hperiod hLip N poly frame B hB hsum hslope
    D E V W hV hW hWnorm η θ hηheight hθheight hη hθ hK a
    (by simpa only [hsite] using hbias)

end Erdos3

end

end OAI
