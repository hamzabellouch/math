import OAI.Combinatorics.MatchingPSD.PermutationSmoothing

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open scoped BigOperators

section GroupAveraging
variable {G : Type u_1} {I : Type u_2} [Fintype G] [Group G] [Fintype I]
  {P : I → Type u_3} [∀ i, Fintype (P i)] [∀ i, Nonempty (P i)]

lemma mean_right_translate (g : G) (f : G → ℝ) :
    (𝔼 a : G, f (a*g)) = 𝔼 a : G, f a := by
  exact Fintype.expect_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

omit [Fintype I] in
lemma mean_le_of_local_means (lift : (i : I) → P i → G)
    (err : I → G → ℝ) (b : I → ℝ)
    (hb : ∀ i a, (𝔼 p : P i, err i (a * lift i p)) ≤ b i) (i : I) :
    (𝔼 a : G, err i a) ≤ b i := by
  have hh : (𝔼 a : G, 𝔼 p : P i, err i (a * lift i p)) ≤ b i :=
    Finset.expect_le Finset.univ_nonempty (fun a _ => hb i a)
  rw [Finset.expect_comm] at hh
  simpa only [mean_right_translate, Fintype.expect_const] using hh

lemma exists_total_le_of_local_means (lift : (i : I) → P i → G)
    (err : I → G → ℝ) (b : I → ℝ)
    (hb : ∀ i a, (𝔼 p : P i, err i (a * lift i p)) ≤ b i) :
    ∃ a : G, (∑ i, err i a) ≤ ∑ i, b i := by
  have he (i : I) : (𝔼 a : G, err i a) ≤ b i :=
    mean_le_of_local_means lift err b hb i
  have htotal : (𝔼 a : G, ∑ i, err i a) ≤ ∑ i, b i := by
    rw [Finset.expect_sum_comm]
    exact Finset.sum_le_sum (fun i _ => he i)
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty htotal
  exact ⟨a,ha⟩

end GroupAveraging
end MatchingSmoothing

end OAI
