import OAI.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def frozenAmbientCoefficientLip (m q : ℕ) : ℝ≥0 :=
  (∑ j : Fin m, ((boundedBooleanJetRows (Fin q) (j.val + 1)).card : ℝ≥0)) *
    ∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin q) (j.val + 1)) : ℝ≥0)

namespace NormalizedPolynomialTwist
variable {X : Type*} [Fintype X] {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def frozenAmbientObservable
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) (s : Finset (Fin q))
    (z : CoefficientAmbientIndex (Fin q) J → UnitAddCircle) : ℂ :=
  W.frozenTorus residue center (coefficientAmbientVertex s z)

theorem frozenAmbientObservable_lipschitz
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) (s : Finset (Fin q)) :
    LipschitzWith (L * frozenAmbientCoefficientLip m q)
      (W.frozenAmbientObservable residue center s) :=
  (W.frozenTorus_lipschitz residue center).comp (coefficientAmbientVertex_lipschitz s)

theorem norm_frozenAmbientObservable_le
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) (s : Finset (Fin q))
    (z : CoefficientAmbientIndex (Fin q) J → UnitAddCircle) :
    ‖W.frozenAmbientObservable residue center s z‖ ≤ 1 :=
  W.norm_frozenTorus_le _ _ _

theorem frozenAmbientObservable_sample
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) (s : Finset (Fin q))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (z : Option (Fin q) × X → ℤ) :
    W.frozenAmbientObservable residue center s (coefficientAmbientTorus U
      (affineCoefficientCoverSample U poly hm W.cover (fun k x => (z (k, x) : ℝ)))) =
      W.frozenTorus residue center (physicalGridFactorInput W.cover poly
        (fun x => (physicalCubeVertexValue (standardPhysicalCubeOutput z) s x : ℝ))) := by
  unfold frozenAmbientObservable
  have h := coefficientAmbientVertex_sample U W.cover poly hp hm s (standardPhysicalCubeOutput z)
  have hframe : standardPhysicalCubeFrame (standardPhysicalCubeOutput z) = z := by
    funext ⟨k, x⟩
    cases k <;> rfl
  rw [hframe] at h
  rw [h]

end NormalizedPolynomialTwist

theorem exists_normalizedTwist_frozen_cover_sampling (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X] {q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {P : ℝ},
    0 ≤ P → (Fintype.card X : ℝ) ≤ P →
    (Fintype.card (Option (Fin q) × X) : ℝ) ≤ P →
    ∀ (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)] [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
    (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
    ∀ (_hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L),
    (W.cover : ℝ) ≤ Real.exp P →
    ∀ (stride : X → ℕ), (∀ k, 0 < stride k) →
    ∀ {R S ρ ε : ℝ}, 0 ≤ S → S ≤ Real.exp P → 0 < ρ → 0 < ε →
    1 / ρ ≤ Real.exp P → 1 / ε ≤ Real.exp P → (∀ k, (stride k : ℝ) ≤ S) →
    ∀ (H : X → ℝ), (∀ k, Real.exp ((P + A) ^ A) ≤ H k) →
    (∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (poly j)) →
    Real.exp ((P + A) ^ A) ≤ R →
    ∀ (cells : Finset (ColumnResiduePattern (Option (Fin q)) X stride)), cells.Nonempty →
    ∀ (V : Option (Fin q) × X → ℝ) (hV : ∀ z, 0 < V z), (∀ z, ρ * H z.2 ≤ V z) →
    ∀ (residue : X → ZMod W.modulus) (center : X → ℝ) (s : Finset (Fin q)) {η Q : ℝ},
    0 < η → 0 ≤ Q → (Fintype.card (CoefficientAmbientIndex (Fin q) J) : ℝ) ≤ Q →
    ((L * frozenAmbientCoefficientLip m q : ℝ≥0) : ℝ) ≤ Real.exp Q →
    η⁻¹ ≤ Real.exp Q → Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * Q * (2 * Q + 2) ^ 4) ≤ Real.exp P →
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z,
      ‖(∑' z : Option (Fin q) × X → ℤ,
        ((selectedResidueSmoothPMF stride cells V hV hZ z).toReal : ℂ) *
          W.frozenTorus residue center (physicalGridFactorInput W.cover poly
            (fun x => (physicalCubeVertexValue (standardPhysicalCubeOutput z) s x : ℝ)))) -
        ∫ x, W.frozenAmbientObservable residue center s (coefficientAmbientTorus U x) ∂μ‖ ≤
      2 * η + ε := by
  obtain ⟨A, hA, hsample⟩ := exists_coefficient_ambient_cover_sampling m
  refine ⟨A, hA, ?_⟩
  intro X _ _ q J _ P hP hn hd U _ _ μ _ _ poly hp hm periodCap coverCap L W hcover
    stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR
    cells hcells V hV hwidth residue center s η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP
  obtain ⟨hZ, hcompare⟩ := hsample hP hn hd U μ poly hp hm W.cover W.cover_pos hcover
    stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR cells hcells V hV hwidth
    (W.frozenAmbientObservable residue center s) (L * frozenAmbientCoefficientLip m q) 1
    (W.frozenAmbientObservable_lipschitz residue center s) (W.norm_frozenAmbientObservable_le residue center s)
    hη hQ hdim hLQ hηQ hfreqP (by simpa only [NNReal.coe_one, mul_one] using hcoeffP)
  refine ⟨hZ, ?_⟩
  simpa only [W.frozenAmbientObservable_sample residue center s U poly hp hm] using hcompare

namespace NormalizedPolynomialTwist
variable {X : Type*} [Fintype X] {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def vertexResidue (modulus : ℕ)
    (r : ColumnResiduePattern (Option (Fin q)) X (fun _ => modulus))
    (s : Finset (Fin q)) : X → ZMod modulus :=
  fun x => r (none, x) + ∑ a ∈ s, r (some a, x)

theorem selected_frozenSpatialEval_eq
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (center : X → ℝ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (r : ColumnResiduePattern (Option (Fin q)) X (fun _ => W.modulus))
    (s : Finset (Fin q)) (V : Option (Fin q) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => W.modulus) {r} V z) :
    (∑' z : Option (Fin q) × X → ℤ,
      ((selectedResidueSmoothPMF (fun _ => W.modulus) {r} V hV hZ z).toReal : ℂ) *
        W.frozenSpatialEval center poly (physicalCubeVertexValue (standardPhysicalCubeOutput z) s)) =
    ∑' z : Option (Fin q) × X → ℤ,
      ((selectedResidueSmoothPMF (fun _ => W.modulus) {r} V hV hZ z).toReal : ℂ) *
        W.frozenTorus (vertexResidue W.modulus r s) center (physicalGridFactorInput W.cover poly
          (fun x => (physicalCubeVertexValue (standardPhysicalCubeOutput z) s x : ℝ))) := by
  apply tsum_congr
  intro z
  by_cases hz : columnResiduePattern (fun _ : X => W.modulus) z = r
  · have hres : (fun x => (physicalCubeVertexValue (standardPhysicalCubeOutput z) s x : ZMod W.modulus)) =
        vertexResidue W.modulus r s := by
      funext x
      simp only [physicalCubeVertexValue, standardPhysicalCubeOutput, Sum.elim_inl,
        Sum.elim_inr, Int.cast_add, Int.cast_sum, vertexResidue]
      congr 1
      · exact congrFun hz (none, x)
      · exact Finset.sum_congr rfl (fun i _ => congrFun hz (some i, x))
    simp only [frozenSpatialEval, hres]
  · have hweight : (selectedResidueSmoothPMF (fun _ => W.modulus) {r} V hV hZ z).toReal = 0 := by
      rw [selectedResidueSmoothPMF_toReal]
      simp only [selectedResidueSmoothWeight, Finset.mem_singleton, hz, ite_false, zero_div]
    simp only [hweight, Complex.ofReal_zero, zero_mul]

end NormalizedPolynomialTwist

theorem exists_normalizedTwist_residue_frozen_sampling (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X] {q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {P : ℝ},
    0 ≤ P → (Fintype.card X : ℝ) ≤ P →
    (Fintype.card (Option (Fin q) × X) : ℝ) ≤ P →
    ∀ (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)] [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
    (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
    ∀ (_hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L),
    (W.cover : ℝ) ≤ Real.exp P → (W.modulus : ℝ) ≤ Real.exp P →
    ∀ {R ρ ε : ℝ}, 0 < ρ → 0 < ε → 1 / ρ ≤ Real.exp P → 1 / ε ≤ Real.exp P →
    ∀ (H : X → ℝ), (∀ k, Real.exp ((P + A) ^ A) ≤ H k) →
    (∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (poly j)) →
    Real.exp ((P + A) ^ A) ≤ R →
    ∀ (V : Option (Fin q) × X → ℝ) (hV : ∀ z, 0 < V z), (∀ z, ρ * H z.2 ≤ V z) →
    ∀ (r : ColumnResiduePattern (Option (Fin q)) X (fun _ => W.modulus))
    (center : X → ℝ) (s : Finset (Fin q)) {η Q : ℝ},
    0 < η → 0 ≤ Q → (Fintype.card (CoefficientAmbientIndex (Fin q) J) : ℝ) ≤ Q →
    ((L * frozenAmbientCoefficientLip m q : ℝ≥0) : ℝ) ≤ Real.exp Q →
    η⁻¹ ≤ Real.exp Q → Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * Q * (2 * Q + 2) ^ 4) ≤ Real.exp P →
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => W.modulus) {r} V z,
      ‖(∑' z : Option (Fin q) × X → ℤ,
        ((selectedResidueSmoothPMF (fun _ => W.modulus) {r} V hV hZ z).toReal : ℂ) *
          W.frozenSpatialEval center poly (physicalCubeVertexValue (standardPhysicalCubeOutput z) s)) -
        ∫ x, W.frozenAmbientObservable (NormalizedPolynomialTwist.vertexResidue W.modulus r s)
          center s (coefficientAmbientTorus U x) ∂μ‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hsample⟩ := exists_normalizedTwist_frozen_cover_sampling m
  refine ⟨A, hA, ?_⟩
  intro X _ _ q J _ P hP hn hd U _ _ μ _ _ poly hp hm periodCap coverCap L W hcover hmodulus
    R ρ ε hρ hε hρP hεP H hsize hrank hR V hV hwidth r center s η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP
  obtain ⟨hZ, hcompare⟩ := hsample hP hn hd U μ poly hp hm W hcover
    (fun _ => W.modulus) (fun _ => W.modulus_pos) (Nat.cast_nonneg W.modulus) hmodulus
    hρ hε hρP hεP (fun _ => le_rfl) H hsize hrank hR {r} (Finset.singleton_nonempty r) V hV hwidth
    (NormalizedPolynomialTwist.vertexResidue W.modulus r s) center s hη hQ hdim hLQ hηQ hfreqP hcoeffP
  refine ⟨hZ, ?_⟩
  rw [W.selected_frozenSpatialEval_eq center poly r s V hV hZ]
  exact hcompare

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

namespace NormalizedPolynomialTwist
variable {X : Type*} [Fintype X] {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def frozenHaarReference
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U))
    (center : X → ℝ) (s : Finset (Fin q))
    (r : (Option (Fin q) × X) → ZMod W.modulus) : ℂ :=
  ∫ x, W.frozenAmbientObservable (vertexResidue W.modulus r s)
    center s (coefficientAmbientTorus U x) ∂μ

theorem norm_frozenHaarReference_le
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U)) [IsProbabilityMeasure μ]
    (center : X → ℝ) (s : Finset (Fin q))
    (r : (Option (Fin q) × X) → ZMod W.modulus) :
    ‖W.frozenHaarReference U μ center s r‖ ≤ 1 := by
  exact (norm_integral_le_of_norm_le_const (ae_of_all μ
    (fun _ => W.norm_frozenAmbientObservable_le _ _ _ _))).trans_eq (by simp)

noncomputable def frozenResidueSamplerMean
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (V : Option (Fin q) × X → ℝ) (hV : ∀ z, 0 < V z)
    (r : (Option (Fin q) × X) → ZMod W.modulus)
    (center : X → ℝ) (s : Finset (Fin q))
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => W.modulus) {r} V z) : ℂ :=
  ∑' z : Option (Fin q) × X → ℤ,
    ((selectedResidueSmoothPMF (fun _ => W.modulus) {r} V hV hZ z).toReal : ℂ) *
      W.frozenSpatialEval center poly (physicalCubeVertexValue (standardPhysicalCubeOutput z) s)

noncomputable def residueSamplerMean
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (M : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (V : Option (Fin q) × X → ℝ) (hV : ∀ z, 0 < V z)
    (r : (Option (Fin q) × X) → ZMod W.modulus) (s : Finset (Fin q))
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ => W.modulus) {r} V z) : ℂ :=
  ∑' z : Option (Fin q) × X → ℤ,
    ((selectedResidueSmoothPMF (fun _ => W.modulus) {r} V hV hZ z).toReal : ℂ) *
      W.eval M poly (physicalCubeVertexValue (standardPhysicalCubeOutput z) s)

end NormalizedPolynomialTwist

private theorem rational_forecast_sample_error
    {Ω A I B Z : Type*} [Fintype Ω] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype Z]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (lo hi : A → ℤ) (hlen : ∀ a, lo a < hi a)
    (out : B → MvPolynomial (A ⊕ I) ℤ) (inactiveCoord : Ω → I → ℤ)
    {d N : ℕ} [NeZero d] [NeZero N] (hd : d ∣ N)
    {gridVolume : ℝ} (hvol : gridVolume ≠ 0)
    (sample reference : Z → (B → ZMod d) → ℂ) {E : ℝ}
    (hcompare : ∀ z r, ‖sample z r - reference z r‖ ≤ E)
    (hbound : ∀ z r, ‖reference z r‖ ≤ 1)
    (hsmall : (∑ a, (d : ℝ) / ((hi a - lo a : ℤ) : ℝ)) ≤ 1 / 2) :
    ‖inactive.complexMean (fun i => (integerBoxUniformWeights lo hi hlen).complexMean
      (fun t => sample (gridPoint i) (fun j => (MvPolynomial.eval
        (Sum.elim (fun a => (t a).val) (inactiveCoord i)) (out j) : ZMod d)))) -
      (∑ z, 𝔼 b : B → ZMod N,
        ((rationalInactiveForecast inactive
          (fun _ => FiniteProbabilityWeights.uniform (A → ZMod N)) gridPoint
          (fun i => integerLongPolynomialOutput out (inactiveCoord i) N)
          N gridVolume z b / gridVolume : ℝ) : ℂ) *
            reference z (fun j => ZMod.castHom hd (ZMod d) (b j)))‖ ≤
      E + 2 * ∑ a, (d : ℝ) / ((hi a - lo a : ℤ) : ℝ) := by
  have hlocal := inactive.norm_complexMean_sub_le
    (fun i => (integerBoxUniformWeights lo hi hlen).complexMean
      (fun t => sample (gridPoint i) (fun j => (MvPolynomial.eval
        (Sum.elim (fun a => (t a).val) (inactiveCoord i)) (out j) : ZMod d))))
    (fun i => (integerBoxUniformWeights lo hi hlen).complexMean
      (fun t => reference (gridPoint i) (fun j => (MvPolynomial.eval
        (Sum.elim (fun a => (t a).val) (inactiveCoord i)) (out j) : ZMod d))))
    (fun _ => E) (fun i _ =>
      ((integerBoxUniformWeights lo hi hlen).norm_complexMean_sub_le _ _
        (fun _ => E) (fun _ _ => hcompare _ _)).trans_eq
          ((integerBoxUniformWeights lo hi hlen).mean_const _))
  rw [inactive.mean_const] at hlocal
  have hrat := rationalInactivePolynomialForecast_box_error inactive gridPoint lo hi hlen
    out inactiveCoord hd hvol reference hbound hsmall
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hlocal hrat)

structure FrozenSamplerComparison
    {X : Type*} [Fintype X] {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (V : Option (Fin q) × X → ℝ) (hV : ∀ z, 0 < V z)
    (s : Finset (Fin q)) (E : ℝ) : Prop where
  mass_pos : ∀ r : (Option (Fin q) × X) → ZMod W.modulus,
    0 < ∑' z, selectedResidueSmoothWeight (fun _ => W.modulus) {r} V z
  comparison : ∀ r center,
    ‖W.frozenResidueSamplerMean poly V hV r center s (mass_pos r) -
      W.frozenHaarReference U μ center s r‖ ≤ E

theorem exists_normalizedTwist_frozen_samplerComparison (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X] {q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {P : ℝ},
    0 ≤ P → (Fintype.card X : ℝ) ≤ P →
    (Fintype.card (Option (Fin q) × X) : ℝ) ≤ P →
    ∀ (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)] [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
    (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
    ∀ (_hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L),
    (W.cover : ℝ) ≤ Real.exp P → (W.modulus : ℝ) ≤ Real.exp P →
    ∀ {R ρ ε : ℝ}, 0 < ρ → 0 < ε → 1 / ρ ≤ Real.exp P → 1 / ε ≤ Real.exp P →
    ∀ (H : X → ℝ), (∀ k, Real.exp ((P + C) ^ C) ≤ H k) →
    (∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (poly j)) →
    Real.exp ((P + C) ^ C) ≤ R →
    ∀ (V : Option (Fin q) × X → ℝ) (hV : ∀ z, 0 < V z), (∀ z, ρ * H z.2 ≤ V z) →
    ∀ (s : Finset (Fin q)) {η Q : ℝ},
    0 < η → 0 ≤ Q → (Fintype.card (CoefficientAmbientIndex (Fin q) J) : ℝ) ≤ Q →
    ((L * frozenAmbientCoefficientLip m q : ℝ≥0) : ℝ) ≤ Real.exp Q →
    η⁻¹ ≤ Real.exp Q → Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * Q * (2 * Q + 2) ^ 4) ≤ Real.exp P →
    FrozenSamplerComparison W U μ poly V hV s (2 * η + ε) := by
  obtain ⟨C, hC, hsample⟩ := exists_normalizedTwist_residue_frozen_sampling m
  refine ⟨C, hC, ?_⟩
  intro X _ _ q J _ P hP hn hd U _ _ μ _ _ poly hp hm periodCap coverCap L W hcover hmodulus
    R ρ ε hρ hε hρP hεP H hsize hrank hR V hV hwidth s η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP
  have hs (r) (center : X → ℝ) :=
    hsample hP hn hd U μ poly hp hm W hcover hmodulus hρ hε hρP hεP H hsize hrank hR
      V hV hwidth r center s hη hQ hdim hLQ hηQ hfreqP hcoeffP
  choose hZ _ using fun r => hs r 0
  refine ⟨hZ, ?_⟩
  intro r center
  obtain ⟨_, hbound⟩ := hs r center
  exact hbound

theorem FrozenSamplerComparison.rational_forecast
    {X : Type*} [Fintype X] [DecidableEq X] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U)) [IsProbabilityMeasure μ]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (V : Option (Fin q) × X → ℝ) (hV : ∀ z, 0 < V z)
    (s : Finset (Fin q)) {E : ℝ} (h : FrozenSamplerComparison W U μ poly V hV s E)
    {Ω A I Z : Type*} [Fintype Ω] [Fintype A] [DecidableEq A] [Fintype Z]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z) (center : Z → X → ℝ)
    (lo hi : A → ℤ) (hlen : ∀ a, lo a < hi a)
    (out : (Option (Fin q) × X) → MvPolynomial (A ⊕ I) ℤ)
    (inactiveCoord : Ω → I → ℤ) {N : ℕ} [NeZero N] (hN : W.modulus ∣ N)
    {gridVolume : ℝ} (hvol : gridVolume ≠ 0)
    (hsmall : (∑ a, (W.modulus : ℝ) / ((hi a - lo a : ℤ) : ℝ)) ≤ 1 / 2) :
    ‖inactive.complexMean (fun i => (integerBoxUniformWeights lo hi hlen).complexMean
      (fun t => W.frozenResidueSamplerMean poly V hV
        (fun j => (MvPolynomial.eval (Sum.elim (fun a => (t a).val) (inactiveCoord i))
          (out j) : ZMod W.modulus)) (center (gridPoint i)) s (h.mass_pos _))) -
      (∑ z, 𝔼 b : (Option (Fin q) × X) → ZMod N,
        ((rationalInactiveForecast inactive
          (fun _ => FiniteProbabilityWeights.uniform (A → ZMod N)) gridPoint
          (fun i => integerLongPolynomialOutput out (inactiveCoord i) N)
          N gridVolume z b / gridVolume : ℝ) : ℂ) *
            W.frozenHaarReference U μ (center z) s
              (fun j => ZMod.castHom hN (ZMod W.modulus) (b j)))‖ ≤
      E + 2 * ∑ a, (W.modulus : ℝ) / ((hi a - lo a : ℤ) : ℝ) := by
  have : NeZero W.modulus := ⟨W.modulus_pos.ne'⟩
  exact rational_forecast_sample_error inactive gridPoint lo hi hlen out inactiveCoord hN hvol
    (fun z r => W.frozenResidueSamplerMean poly V hV r (center z) s (h.mass_pos r))
    (fun z => W.frozenHaarReference U μ (center z) s) (fun z r => h.comparison r (center z))
    (fun z r => W.norm_frozenHaarReference_le U μ (center z) s r) hsmall

theorem FrozenSamplerComparison.rational_forecast_eval
    {X : Type*} [Fintype X] [DecidableEq X] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U)) [IsProbabilityMeasure μ]
    (M : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (V : Option (Fin q) × X → ℝ) (hV : ∀ z, 0 < V z)
    (s : Finset (Fin q)) {E : ℝ} (h : FrozenSamplerComparison W U μ poly V hV s E)
    {Ω A I Z : Type*} [Fintype Ω] [Fintype A] [DecidableEq A] [Fintype Z]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z) (center : Z → X → ℝ)
    {centerRadius : ℝ} (hcenter : ∀ z, ‖center z‖ ≤ centerRadius)
    (lo hi : A → ℤ) (hlen : ∀ a, lo a < hi a)
    (out : (Option (Fin q) × X) → MvPolynomial (A ⊕ I) ℤ)
    (inactiveCoord : Ω → I → ℤ) {N : ℕ} [NeZero N] (hN : W.modulus ∣ N)
    {gridVolume : ℝ} (hvol : gridVolume ≠ 0)
    (hsmall : (∑ a, (W.modulus : ℝ) / ((hi a - lo a : ℤ) : ℝ)) ≤ 1 / 2) :
    ‖inactive.complexMean (fun i => (integerBoxUniformWeights lo hi hlen).complexMean
      (fun t => W.residueSamplerMean M poly V hV
        (fun j => (MvPolynomial.eval (Sum.elim (fun a => (t a).val) (inactiveCoord i))
          (out j) : ZMod W.modulus)) s (h.mass_pos _))) -
      (∑ z, 𝔼 b : (Option (Fin q) × X) → ZMod N,
        ((rationalInactiveForecast inactive
          (fun _ => FiniteProbabilityWeights.uniform (A → ZMod N)) gridPoint
          (fun i => integerLongPolynomialOutput out (inactiveCoord i) N)
          N gridVolume z b / gridVolume : ℝ) : ℂ) *
            W.frozenHaarReference U μ (center z) s
              (fun j => ZMod.castHom hN (ZMod W.modulus) (b j)))‖ ≤
      (L : ℝ) * (normalizedVertexRadius M V s + centerRadius) + E +
        2 * ∑ a, (W.modulus : ℝ) / ((hi a - lo a : ℤ) : ℝ) := by
  have : NeZero W.modulus := ⟨W.modulus_pos.ne'⟩
  apply rational_forecast_sample_error inactive gridPoint lo hi hlen out inactiveCoord hN hvol
    (fun _ r => W.residueSamplerMean M poly V hV r s (h.mass_pos r))
    (fun z => W.frozenHaarReference U μ (center z) s) ?_
    (fun z r => W.norm_frozenHaarReference_le U μ (center z) s r) hsmall
  intro z r
  have hsp := W.selected_eval_sub_frozenSpatialEval M (center z) poly
    (fun _ => W.modulus) {r} s V hV (h.mass_pos r)
  have hnear := (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (normalizedVertexRadius M V s)) (hcenter z)) L.coe_nonneg)
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (W.frozenResidueSamplerMean poly V hV r (center z) s (h.mass_pos r)) _).trans
      (add_le_add (hsp.trans hnear) (h.comparison r (center z)))

end Erdos3.VectorPolynomial

end

end OAI
