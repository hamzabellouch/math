import OAI.Combinatorics.Progressions.Polynomial.PreparedPolynomialIdentity

namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

theorem prepare_old_layer {I J : Type}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {j R : ℕ} {p δ : ℝ} (P : VectorPolynomial I ℝ (J → ℝ))
    (hP : DegreeLE (fun _ => 1) (j + 1) P) (hp : 0 ≤ p)
    (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p) (hδ : 0 < δ)
    (N : I → ℕ) (f : (∀ i, Fin (N i)) → ℝ) :
    let D := Fintype.card J
    let T := (j + 1) * D
    let M := preparationCoordinateCap (j + 1) D T
    let share := δ / ((T : ℝ) * M + 1)
    let budget := (p + 2) ^ (budgetDepthExponent 38 (j + 1) + 7)
    (M : ℝ) ≤ p → ((j + 1 : ℕ) : ℝ) ≤ p → (Fintype.card I : ℝ) ≤ p →
    (T : ℝ) + 1 ≤ p → share⁻¹ ≤ Real.exp p → (∀ i, Real.exp budget ≤ N i) →
    ∃ (q : ℕ) (S : ResidueBoxSlice N q) (L : RankPreparationFamily I J (j + 1))
      (ip : J → MvPolynomial I ℤ) (c : J → ℝ) (E : VectorPolynomial I ℝ (J → ℝ)),
      (∑ u, (L u).rank) ≤ T ∧ L.Sized D T ∧ L.PreparedHeights p R ∧
      (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ)) R (L u).space (L u).poly) ∧
      0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ Real.exp budget * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S.length i)), f (S.point x)) ∧
      (∀ k, (ip k).totalDegree ≤ j + 1) ∧ DegreeLE (fun _ => 1) (j + 1) E ∧
      substitute S.polynomial P = L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + E ∧
      ∀ (x : ∀ i, Fin (S.length i)) (k : J), |eval (fun i => ((x i).val : ℝ)) E k| ≤ δ := by
  intro D T M share budget hM hs hn hT hshareinv hN
  obtain ⟨q, S, L, ip, c, err, hrank, hsize, hheight, hgood, hq, hqbound,
    hlength, hscore, hip, herr, hid⟩ :=
    exists_prepared_polynomial_layer_exp P hP hp hR hRp hδ N f hM hs hn hT hshareinv hN
  obtain ⟨E, hE, hidentity, hbound⟩ := prepared_error_polynomial S P hP L
    (fun u => (hheight u).1) ip hip c err herr hid
  exact ⟨q, S, L, ip, c, E, hrank, hsize, hheight, hgood, hq, hqbound,
    hlength, hscore, hip, hE, hidentity, hbound⟩

end Erdos3

end

end OAI
