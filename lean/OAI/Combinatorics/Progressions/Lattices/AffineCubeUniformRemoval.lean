import OAI.Combinatorics.Progressions.Dynamics.CubeModeUniformBudget

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators NNReal

theorem affine_cube_removal_of_widths {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {ζ R T S : ℝ} (hζ : 0 < ζ) (hT : 0 < T) (hS : 0 ≤ S)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (hH : ∀ k, 0 < H k)
    (hsize : ∀ k, (stride k : ℝ) * T * (finiteLayerBiasBudget m ζ + 1) ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : layerRemovalRankBudget m (Fintype.card I) C (cubeModePolynomialBudget q L)
      (finiteLayerBiasBudget m ζ) (2 * T) S ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (hV1 : ∀ z, 1 ≤ V z)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z, 1 / V z ≤ δ)
    (hsmall : (4 : ℝ) ^ Fintype.card (Option K × I) *
      ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * δ ≤ 1 / 2)
    {ρ r β : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (hmove : (m : ℝ) * cubeModePolynomialBudget q L ≤ r * ρ * T)
    (hβ : 0 ≤ β) (hpower : ∀ i : Fin m, ζ ≤ β ^ (2 ^ (i.val + 1))) :
    ‖∑' z : Option K × I → ℤ, ((smoothProductPMF V hV z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ))‖ ≤
      4 * (3 : ℝ) ^ Fintype.card (Option K × I) *
        ((Fintype.card (Option K × I) : ℝ) * probabilityProfileLipschitz) * r + β := by
  classical
  let B := finiteLayerBiasBudget m ζ
  let D := cubeModePolynomialBudget q L
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m hζ
  have hD : 0 ≤ D := (cubeModePolynomialBudget_pos q hL).le
  have hA : 0 ≤ 2 * T := by positivity
  have hb (i : Fin m) : multiaffineBiasBudget i.val ζ ≤ B :=
    multiaffineBiasBudget_le_finite i hζ
  obtain ⟨N, hN, hscale, hshift⟩ := exists_mode_shift_lengths m hT hB hρ hr hmove H stride hs hsize V hwidth
  have hbud (i : Fin m) := layerRemovalRankBudget_bounds i (Fintype.card I) hC hD
    (zero_le_one.trans hB) hA hS
  apply affine_cube_mode_smooth_removal U root difference hlin hL hC hsite frequency hbound hbad
    p hp hm N stride hs hζ (fun i k => (hb i).trans (hN k)) H hH hA hscale hrank
    (fun i => (hbud i).1.trans hR) _ _ Q hQ test htest V hV hV1 hδ hδ1 hmesh hsmall hr _ hβ hpower
  · intro i
    have hi := tensorDenominatorBound_le (H := Fin (i.val + 1))
      (multiaffineBiasBudget_pos i.val hζ).le (fun k => (stride k : ℝ))
      (fun k => Nat.cast_nonneg _) hstride
    have hi' : (∏ j : Fin (i.val + 1) → I,
        (multiaffineBiasBudget i.val ζ * ∏ r, (stride (j r) : ℝ))) ≤
        (multiaffineBiasBudget i.val ζ * S ^ (i.val + 1)) ^ (Fintype.card I ^ (i.val + 1)) := by
      simpa only [Fintype.card_fin] using hi
    apply hi'.trans
    apply le_trans _ ((hbud i).2.1.trans hR)
    exact pow_le_pow_left₀
      (mul_nonneg (multiaffineBiasBudget_pos i.val hζ).le (pow_nonneg hS _))
      (mul_le_mul_of_nonneg_right (hb i) (pow_nonneg hS _)) _
  · intro i
    apply le_trans _ ((hbud i).2.2.trans hR)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hb i) (pow_nonneg hA _))
      (pow_nonneg (Nat.cast_nonneg _) _)
  · intro i z
    have hi : ((i.val + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    apply le_trans _ (hshift z)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi hD)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem affine_cube_removal_at_error {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε)
    (hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (hsize : ∀ k, modeRemovalSideThreshold m (Fintype.card (Option K × I))
      (cubeModePolynomialBudget q L) S ρ ε ≤ H k)
    (hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (hR : modeRemovalRankThreshold m (Fintype.card I) (Fintype.card (Option K × I))
      C (cubeModePolynomialBudget q L) S ρ ε ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ t v, ‖test t v‖ ≤ 1)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hwidth : ∀ z, ρ * H z.2 ≤ V z) :
    ‖∑' z : Option K × I → ℤ, ((smoothProductPMF V hV z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ))‖ ≤ ε := by
  classical
  let d := Fintype.card (Option K × I)
  let D := cubeModePolynomialBudget q L
  let T := modeRemovalShrink m d D ρ ε
  let B := finiteLayerBiasBudget m (modeRemovalBias m ε)
  have hD : 0 ≤ D := (cubeModePolynomialBudget_pos q hL).le
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (modeRemovalShrink_one_le m d hD hρ hε)
  have hB : 1 ≤ B := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε)
  have hside := modeRemovalSideThreshold_bounds m d hD hS hρ hε
  have hH k : 0 < H k := hside.1.trans_le (hsize k)
  have hsize' k : (stride k : ℝ) * T * (B + 1) ≤ H k := by
    calc
      _ ≤ S * T * (B + 1) := by gcongr; exact hstride k
      _ ≤ H k := hside.2.1.trans (hsize k)
  have hv z : 1 ≤ V z ∧ 1 / V z ≤ modeRemovalMesh d := by
    apply modeRemovalMesh_of_width d (hV z)
    exact (hside.2.2.trans (mul_le_mul_of_nonneg_left (hsize z.2) hρ.le)).trans (hwidth z)
  have hout := affine_cube_removal_of_widths U root difference hlin hL hC hsite frequency hbound hbad
    p hp hm stride hs (modeRemovalBias_pos m hε) hT hS hstride H hH hsize' hrank hR
    Q hQ test htest V hV (fun z => (hv z).1) (modeRemovalMesh_pos d).le (modeRemovalMesh_le_one d)
    (fun z => (hv z).2) (modeRemovalMesh_small d) hρ (modeRemovalRadius_pos d hε).le hwidth
    (modeRemovalShrink_move m d hρ hε) (modeRemovalBeta_pos hε).le (fun i => modeRemovalBias_le i hε)
  exact hout.trans (modeRemovalError_bound d hε)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_uniform_removal (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ j d, d.degree ≤ j.val + 1 → ∀ a, |(frequency j d a : ℝ)| ≤ C)
    (_hbad : ∃ i, ¬∃ M : (Finset (Fin q) → U i) →ₗ[ℝ] ℝ,
      ∀ P, Homogeneous (i.val + 1) P →
        affineModeLift (coefficientFunctional (fun d a => (frequency i d a : ℝ))) (map (U i).subtype P) =
          M (VectorPolynomial.siteEvaluation
            (fun s => affineSite (fun k => (root k : ℝ)) (fun r k => (difference r k : ℝ)) s) P))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ‖∑' z : Option K × I → ℤ, ((smoothProductPMF V hV z).toReal : ℂ) *
      layeredModeTestedPhase
        (fun j => affineModeLift (coefficientFunctional (fun d a => (frequency j d a : ℝ))))
        p Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ))‖ ≤ ε := by
  obtain ⟨A, hA, hbudget⟩ := exists_cube_mode_threshold_exp_budget m q
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound hbad p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest V hV hwidth
  obtain ⟨hside, hrankBudget⟩ := hbudget (Fintype.card I) (Fintype.card (Option K × I))
    P C L S ρ ε hP hn hd hC hCP hL hLP hS hSP hρ hρP hε hεP
  exact affine_cube_removal_at_error U root difference hlin hL hC hsite frequency hbound hbad
    p hp hm stride hs hS hρ hε hstride H (fun k => hside.trans (hsize k)) hrank
    (hrankBudget.trans hR) Q hQ test htest V hV hwidth

end Erdos3.BooleanCubeKernel

end

end OAI
