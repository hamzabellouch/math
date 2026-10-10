import OAI.Combinatorics.Progressions.Fourier.SectionRetainedFourier

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial Polynomial
open scoped BigOperators

theorem exists_affine_cube_covered_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hK : (Fintype.card K : ℝ) ≤ P) (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∃ b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
      (∀ a j s t, |(b a j s t : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          affineCubeFourierSum frequency p c (fun k j => (z (k, j) : ℝ)))) -
      (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          retainedSiteFourierSum U root difference frequency b c
            (affineCoveredSiteSample U root difference D p hm (fun k j => (z (k, j) : ℝ)))))‖ ≤ ε := by
  obtain ⟨A₀, _, hprojection⟩ := exists_affine_cube_fourier_projection m q
  obtain ⟨A₁, _, hcover⟩ := exists_geometric_site_fourier_projection m q
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A₀) ^ A₀ + (X + Polynomial.C A₁) ^ A₁)
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hK hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound c B hB hBP hcoefficients p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth
  have hsum : (P + A₀) ^ A₀ + (P + A₁) ^ A₁ ≤ (P + A) ^ A := by
    simpa [Polynomial.eval₂_pow] using hbudget P hP
  have hb₀ : (P + A₀) ^ A₀ ≤ (P + A) ^ A := by
    linarith [pow_nonneg (add_nonneg hP (Nat.cast_nonneg A₁)) A₁]
  have hb₁ : (P + A₁) ^ A₁ ≤ (P + A) ^ A := by
    linarith [pow_nonneg (add_nonneg hP (Nat.cast_nonneg A₀)) A₀]
  obtain ⟨D, hD, hDP, hrows⟩ := hcover root difference hP hK (fun s k => (hsite s k).trans hLP)
  obtain ⟨b, hb, heq⟩ := hrows U frequency (fun a j d hd t => (hbound a j d hd t).trans hCP)
  obtain ⟨hZ, hproj⟩ := hprojection hP hn hd U root difference hlin hL hC hLP hCP hsite
    frequency hbound c hB hBP hcoefficients p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H (fun k => (Real.exp_le_exp.mpr hb₀).trans (hsize k)) hrank
    ((Real.exp_le_exp.mpr hb₀).trans hR) Q hQ test htest G hG V hV hwidth
  refine ⟨D, hD, hDP.trans (Real.exp_le_exp.mpr hb₁), b,
    fun a j s t => (hb a j s t).trans (Real.exp_le_exp.mpr hb₁), hZ, ?_⟩
  have hfun : affineCubeFourierProjection U root difference frequency p c =
      fun x => retainedSiteFourierSum U root difference frequency b c
        (affineCoveredSiteSample U root difference D p hm x) :=
    funext (fun x => heq p hp hm c x)
  rw [hfun] at hproj
  exact hproj

end Erdos3.BooleanCubeKernel

end

end OAI
