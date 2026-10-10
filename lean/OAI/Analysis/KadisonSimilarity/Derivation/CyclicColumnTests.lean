import OAI.Analysis.KadisonSimilarity.Derivation.CyclicColumnPolar
import OAI.Analysis.KadisonSimilarity.Derivation.DicksonDischarge
import OAI.Analysis.KadisonSimilarity.Derivation.CyclicDerivations
import OAI.Analysis.KadisonSimilarity.Tracial.FullColumnTheorem

namespace OAI

/-! Dense cyclic orbits give the bounded column tests needed for the
matrix derivation estimate. The unit vector may vary with the test. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped ComplexOrder Topology

variable {A K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def cyclicOrbitColumn (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    {n : ℕ} (a : Fin n → A) : HilbertCopies K n :=
  WithLp.toLp 2 (fun i => σ (a i) Ω)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem cyclicOrbitColumn_apply (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    {n : ℕ} (a : Fin n → A) (i : Fin n) : cyclicOrbitColumn σ Ω a i = σ (a i) Ω := rfl

/-- A finite orbit column and its positive square root have the same vector norm. -/
theorem norm_cyclicColumnRoot_action (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    {n : ℕ} (a : Fin n → A) :
    ‖σ (cyclicColumnRoot a) Ω‖ = ‖cyclicOrbitColumn σ Ω a‖ := by
  have hsa : (σ (cyclicColumnRoot a)).adjoint = σ (cyclicColumnRoot a) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star,
      (cyclicColumnRoot_nonneg a).star_eq]
  have hsq : (σ (cyclicColumnRoot a)).adjoint.comp (σ (cyclicColumnRoot a)) =
      ∑ i, (σ (a i)).adjoint.comp (σ (a i)) := by
    rw [hsa]
    change σ (cyclicColumnRoot a) * σ (cyclicColumnRoot a) = _
    rw [← map_mul, cyclicColumnRoot_sq, map_sum]
    simp only [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
  have hi := congrArg (fun T : K →L[ℂ] K => (inner ℂ Ω (T Ω)).re) hsq
  simp only [ContinuousLinearMap.comp_apply, sum_apply, inner_sum,
    ContinuousLinearMap.adjoint_inner_right] at hi
  have hre (f : Fin n → ℂ) : (∑ i, f i).re = ∑ i, (f i).re :=
    map_sum Complex.reLm f Finset.univ
  have hself (x : K) : (inner ℂ x x).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [hre, hself] at hi
  simp_rw [hself] at hi
  have hv := PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => K) (cyclicOrbitColumn σ Ω a)
  simp only [cyclicOrbitColumn_apply] at hv
  nlinarith [norm_nonneg (σ (cyclicColumnRoot a) Ω), norm_nonneg (cyclicOrbitColumn σ Ω a)]

/-- The shifted square root is the single input vector for the regularized column. -/
def cyclicShiftVector (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    {n : ℕ} (a : Fin n → A) (ε : ℝ) : K :=
  σ (cyclicColumnRoot a + ε • (1 : A)) Ω

theorem cyclicShiftVector_norm_le (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    {n : ℕ} (a : Fin n → A) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖cyclicShiftVector σ Ω a ε‖ ≤ ‖cyclicOrbitColumn σ Ω a‖ + ε * ‖Ω‖ := by
  have he : cyclicShiftVector σ Ω a ε = σ (cyclicColumnRoot a) Ω + ε • Ω := by
    change σ (cyclicColumnRoot a + ε • (1 : A)) Ω = _
    have hs : σ (ε • (1 : A)) = ε • σ 1 :=
      σ.toLinearMap.map_smul_of_tower ε (1 : A)
    rw [map_add, hs, map_one]
    rfl
  rw [he, ← norm_cyclicColumnRoot_action σ Ω a]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul, Real.norm_of_nonneg hε])

theorem cyclicPolarColumn_action_recover (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    {n : ℕ} (a : Fin n → A) {ε : ℝ} (hε : 0 < ε) :
    columnAction σ (cyclicPolarColumn a ε) (cyclicShiftVector σ Ω a ε) =
      cyclicOrbitColumn σ Ω a := by
  apply PiLp.ext
  intro i
  rw [columnAction_apply, cyclicShiftVector, cyclicOrbitColumn_apply]
  change ((σ (cyclicPolarColumn a ε i 0) * σ (cyclicColumnRoot a + ε • (1 : A))) Ω) = _
  rw [← map_mul, cyclicPolarColumn_recover a hε i]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Cyclicity supplies simultaneous approximation in every finite Hilbert sum. -/
theorem cyclicOrbitColumn_dense (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    (hΩ : DenseRange (fun a : A => σ a Ω)) (n : ℕ) :
    DenseRange (cyclicOrbitColumn (n := n) σ Ω) := by
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => K)).symm
  have hpi : DenseRange (Pi.map (fun _ : Fin n => fun a : A => σ a Ω)) :=
    DenseRange.piMap (fun _ => hΩ)
  exact e.surjective.denseRange.comp hpi e.continuous

/-- The approximation needed by the matrix estimate; the input vector may vary. -/
def CyclicColumnTests (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∀ n : ℕ, ∀ ξ : HilbertCopies K n, ‖ξ‖ = 1 → ∀ η : ℝ, 0 < η →
    ∃ ζ : K, ∃ W : Matrix (Fin n) (Fin 1) A,
      ‖ζ‖ = 1 ∧ ‖CStarMatrix.ofMatrix W‖ ≤ 2 ∧ ‖columnAction σ W ζ - ξ‖ < η

/-- A dense cyclic orbit gives all the required bounded column tests. -/
theorem cyclicColumnTests_of_dense_orbit (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (Ω : K)
    (hΩ : DenseRange (fun a : A => σ a Ω)) : CyclicColumnTests σ := by
  intro n ξ hξ η hη
  let δ := min η (1 / 4 : ℝ)
  have hδ : 0 < δ := lt_min hη (by norm_num)
  obtain ⟨a, ha⟩ := (cyclicOrbitColumn_dense σ Ω hΩ n).exists_dist_lt ξ hδ
  rw [dist_eq_norm, norm_sub_rev] at ha
  let c := cyclicOrbitColumn σ Ω a
  have hc : ‖c - ξ‖ < δ := ha
  have hcn : ‖c‖ < 1 + δ := by
    have h := norm_le_norm_sub_add c ξ
    rw [hξ] at h
    linarith
  have hc0 : c ≠ 0 := by
    intro he
    rw [he, zero_sub, norm_neg, hξ] at hc
    have hd := min_le_right η (1 / 4 : ℝ)
    change δ ≤ 1 / 4 at hd
    linarith
  let ε := (1 / 4 : ℝ) / (‖Ω‖ + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have he : ε * (‖Ω‖ + 1) = 1 / 4 := by
    dsimp [ε]
    exact div_mul_cancel₀ _ (by positivity)
  have hεΩ : ε * ‖Ω‖ ≤ 1 / 4 := by nlinarith [norm_nonneg Ω]
  let z := cyclicShiftVector σ Ω a ε
  let P : Matrix (Fin n) (Fin 1) A := cyclicPolarColumn a ε
  have hrec : columnAction σ P z = c := cyclicPolarColumn_action_recover σ Ω a hε
  have hzn : ‖z‖ ≤ 2 := by
    have h := cyclicShiftVector_norm_le σ Ω a hε.le
    have hd := min_le_right η (1 / 4 : ℝ)
    change δ ≤ 1 / 4 at hd
    change ‖z‖ ≤ ‖c‖ + ε * ‖Ω‖ at h
    linarith
  have hz0 : z ≠ 0 := by
    intro hz
    apply hc0
    rw [← hrec, hz]
    apply PiLp.ext
    intro i
    simp only [columnAction_apply, map_zero, PiLp.zero_apply]
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  let ζ := (‖z‖ : ℂ)⁻¹ • z
  let W : Matrix (Fin n) (Fin 1) A := (‖z‖ : ℂ) • P
  refine ⟨ζ, W, ?_, ?_, ?_⟩
  · change ‖(‖z‖ : ℂ)⁻¹ • z‖ = 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ hnz]
  · change ‖(‖z‖ : ℂ) • CStarMatrix.ofMatrix P‖ ≤ 2
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact (mul_le_of_le_one_right (norm_nonneg z) (cyclicPolarColumn_contract a hε)).trans hzn
  · have hv : columnAction σ W ζ = c := by
      apply PiLp.ext
      intro i
      rw [columnAction_apply]
      change σ ((‖z‖ : ℂ) • P i 0) ((‖z‖ : ℂ)⁻¹ • z) = c i
      have hscalar : σ ((‖z‖ : ℂ) • P i 0) = (‖z‖ : ℂ) • σ (P i 0) :=
        map_smul σ _ _
      rw [hscalar, smul_apply, map_smul, smul_smul,
        mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hnz), one_smul]
      simpa only [columnAction_apply] using
        congrArg (fun x : HilbertCopies K n => x i) hrec
    rw [hv]
    exact hc.trans_le (min_le_left _ _)

/-- Bounded cyclic column tests suffice for the full matrix estimate. -/
theorem rectangularDerivation_bound_of_cyclicColumnTests
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    {c : ℝ} (hc : 0 ≤ c) (hcol : ColumnBound δ c)
    (htests : CyclicColumnTests σ) (n : ℕ) (X : Matrix (Fin n) (Fin n) A) :
    ‖rectangularMatrixOperator (X.map δ)‖ ≤ (4 * c) * ‖CStarMatrix.ofMatrix X‖ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro ξ hξ
  let D := rectangularMatrixOperator (X.map δ)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨ζ, W, hζ, hW, herr⟩ := htests n ξ hξ (ε / (‖D‖ + 1)) (by positivity)
  let v := columnAction σ W ζ
  have hv := norm_derivation_on_column_le ρ σ δ hδ hc hcol X W hW ζ hζ
  have he : ‖D ξ - D v‖ ≤ ε := by
    rw [← map_sub]
    calc
      _ ≤ ‖D‖ * ‖ξ - v‖ := D.le_opNorm _
      _ ≤ ‖D‖ * (ε / (‖D‖ + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg D)
        simpa only [norm_sub_rev] using herr.le
      _ ≤ ε := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg D]
  exact (norm_le_norm_sub_add (D ξ) (D v)).trans (by linarith)

/-- A cyclic representation supplies the completely bounded derivation estimate directly. -/
theorem cyclic_derivation_implementation_of_column_tests
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (δ : A →L[ℂ] (K →L[ℂ] F))
    (hδ : ∀ a b, δ (a * b) = (ρ a).comp (δ b) + (δ a).comp (σ b))
    (htests : CyclicColumnTests σ)
    (paulsen : PaulsenSimilarityInput (normalizedRectangularRepresentation ρ σ δ hδ)) :
    ∃ V : K →L[ℂ] F, (∀ a, δ a = V.comp (σ a) - (ρ a).comp V) ∧
      ‖V‖ ≤ (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ‖δ‖ := by
  have hcol := (rectangularDerivation_row_column ρ σ δ hδ dicksonTwoBound_proved).2
  let D : ℝ := 4 * (4 * Real.sqrt 2) * ‖δ‖
  have hD : RectangularCompleteBound δ D := by
    intro n X
    convert rectangularDerivation_bound_of_cyclicColumnTests ρ σ δ hδ
      (by positivity : 0 ≤ (4 * Real.sqrt 2) * ‖δ‖) hcol htests n X using 1
    dsimp [D]
    ring
  obtain ⟨V, hV, hb⟩ := rectangular_inner_of_completeBound ρ σ δ hδ
    (by dsimp [D]; positivity : 0 ≤ D) hD paulsen
  refine ⟨V, hV, ?_⟩
  by_cases hz : ‖δ‖ = 0
  · simpa [hz, D] using hb
  have hcancel : D * ‖δ‖⁻¹ = 4 * (4 * Real.sqrt 2) := by
    dsimp [D]
    rw [mul_assoc, mul_inv_cancel₀ hz, mul_one]
  calc
    ‖V‖ ≤ ‖δ‖ * (1 + D * ‖δ‖⁻¹) ^ 2 := hb
    _ = (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ‖δ‖ := by rw [hcancel]; ring

/-- The corner correction needs only the direct cyclic column tests. -/
theorem exists_corner_intertwiner_of_column_tests
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (G : K →L[ℂ] F) {ε : ℝ} (hG : ‖cornerCommutator ρ σ G‖ ≤ ε)
    (htests : CyclicColumnTests σ)
    (paulsen : PaulsenSimilarityInput (normalizedRectangularRepresentation ρ σ
      (cornerCommutator ρ σ G) (cornerCommutator_leibniz ρ σ G))) :
    ∃ T : K →L[ℂ] F, (∀ a, T.comp (σ a) = (ρ a).comp T) ∧
      ‖G - T‖ ≤ (1 + 4 * (4 * Real.sqrt 2)) ^ 2 * ε := by
  obtain ⟨V, hV, hnV⟩ := cyclic_derivation_implementation_of_column_tests
    ρ σ (cornerCommutator ρ σ G) (cornerCommutator_leibniz ρ σ G) htests paulsen
  refine ⟨G - V, ?_, ?_⟩
  · intro a
    have h := hV a
    ext x
    have hx := congrArg (fun T : K →L[ℂ] F => T x) h
    simp only [cornerCommutator_apply, sub_apply, ContinuousLinearMap.comp_apply] at hx ⊢
    simp only [map_sub]
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using sub_eq_sub_iff_add_eq_add.mp hx
  · simpa only [sub_sub_cancel] using hnV.trans
      (mul_le_mul_of_nonneg_left hG (sq_nonneg _))

end KadisonSimilarity

end

end OAI
