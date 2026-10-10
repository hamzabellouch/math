import OAI.Combinatorics.Progressions.Fourier.AnchoredCoefficientFourierNormalization

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem exists_affine_coefficient_approximated_mean (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f : (Option K × I → ℤ) → ℂ) {η : ℝ} (_hη : 0 ≤ η)
    (_hf : ∀ z ∈ rectangularWeightIndices 0 V 1,
      ‖f z - ∑ a, c a * layeredCoefficientCharacter
        (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
        p (fun k j => (z (k, j) : ℝ))‖ ≤ η),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) * f z) -
      (∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0)‖ ≤ η + ε := by
  obtain ⟨A, hA, hnormalization⟩ := exists_affine_coefficient_fourier_normalization m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth f η hη hf
  obtain ⟨hZ, hnorm⟩ := hnormalization hP hn hd U hC hCP frequency hbound c hB hBP hcoefficients
    p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  let g (z : Option K × I → ℤ) := ∑ a, c a * layeredCoefficientCharacter
    (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
    p (fun k j => (z (k, j) : ℝ))
  have ha := selectedResidueSmoothPMF_approximation stride G V hV hZ (fun _ => 1) f g hη
    (by intro z hz; simp) hf
  simp only [one_mul] at ha
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (∑' z, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) * g z) _).trans
    (add_le_add ha hnorm)

end Erdos3.VectorPolynomial

end

end OAI
