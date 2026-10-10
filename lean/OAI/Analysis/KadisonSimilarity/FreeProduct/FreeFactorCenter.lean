import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeCentralWords
import OAI.Analysis.KadisonSimilarity.Tensor.SubalgebraCentralPairing

namespace OAI

/-! An actual orthogonal unitary sequence and a dense matrix tower in one
free factor force the center of the generated tracial algebra to be scalar. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) {A D : StarSubalgebra ℂ P}

/-- Centering the last endpoint and cyclically moving the last other-factor
letter reduce every word to the centered terminal case. -/
theorem central_trace_pair_word
    (h1 : G.trace 1 = 1) (hfree : ScalarFree G.trace A D)
    (u : ℕ → unitary P) (hu : ∀ n, (u n : P) ∈ D)
    (hu0 : ∀ n, G.trace (u n : P) = 0)
    (huv : ∀ i j, G.trace ((u i : P) * star (u j : P)) = if i = j then 1 else 0)
    (c : P) (hc : ∀ a : P, a * c = c * a)
    (hD : ∀ d ∈ D, G.trace (c * d) = 0)
    {xs : List P} (hxs : CenteredPairWord G.trace A D xs)
    {d b : P} (hd : d ∈ D) (hb : b ∈ A) :
    G.trace (c * (d * xs.prod * b)) = 0 := by
  have htail {ys : List P} (hys : CenteredPairWord G.trace A D ys)
      {e a : P} (he : e ∈ D) (ha : a ∈ A) (ha0 : G.trace a = 0) :
      G.trace (c * (e * ys.prod * a)) = 0 :=
    G.central_trace_centered_pair_word h1 hfree u hu hu0 huv c hc hys he ha ha0
  have hshort : G.trace (c * (d * xs.prod)) = 0 := by
    rcases hxs.nil_or_snoc with hnil | ⟨ys, a, e, hys, ha, he, ha0, _, hsnoc⟩
    · simpa only [hnil, List.prod_nil, mul_one] using hD d hd
    · rw [hsnoc]
      calc
        _ = G.trace ((c * (d * ys.prod * a)) * e) := by
          simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
        _ = G.trace (e * (c * (d * ys.prod * a))) := G.tracial _ _
        _ = G.trace (c * ((e * d) * ys.prod * a)) := by
          rw [← mul_assoc, hc e]
          simp only [mul_assoc]
        _ = 0 := htail hys (D.mul_mem he hd) ha ha0
  calc
    _ = G.trace (c * (d * xs.prod * traceCentered G.trace b)) +
        G.trace b * G.trace (c * (d * xs.prod)) := by
      conv_lhs => rw [← traceCentered_add G.trace b]
      rw [mul_add, mul_add, mul_smul_comm, mul_one, mul_smul_comm,
        map_add, map_smul, smul_eq_mul]
    _ = 0 := by
      rw [htail hxs hd (traceCentered_mem G.trace A hb)
        (traceCentered_trace G.trace h1 b), hshort, mul_zero, add_zero]

variable [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)

include M in
/-- The generated free algebra has scalar center, proved using finite trace
pairings and Hilbert-space density. -/
theorem scalar_center_of_free_matrix_factor
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (hfree : ScalarFree G.trace A D) (hgen : ReducedWordGenerated G A D)
    (u : ℕ → unitary P) (hu : ∀ n, (u n : P) ∈ D)
    (hu0 : ∀ n, G.trace (u n : P) = 0)
    (huv : ∀ i j, G.trace ((u i : P) * star (u j : P)) = if i = j then 1 else 0) :
    ∀ c : P, (∀ a : P, a * c = c * a) → ∃ z : ℂ, c = z • (1 : P) := by
  intro c hc
  let c₀ := traceCentered G.trace c
  have hc₀ (a : P) : a * c₀ = c₀ * a := by
    simp only [c₀, traceCentered, mul_sub, sub_mul, mul_smul_comm,
      smul_mul_assoc, one_mul, mul_one, hc a]
  have hD (d : P) (hd : d ∈ D) : G.trace (c₀ * d) = 0 := by
    change G.trace ((c - G.trace c • 1) * d) = 0
    rw [sub_mul, smul_mul_assoc, one_mul, map_sub, map_smul, smul_eq_mul,
      G.ambient_central_pairing_of_matrix_tower D M c hc ⟨d, hd⟩, sub_self]
  have hw (x : H) (hx : x ∈ reducedWordVectors G A D) :
      inner ℂ (G.vector (star c₀)) x = 0 := by
    obtain ⟨n, d, b, a, e, ha0, he0, rfl⟩ := hx
    rw [G.inner_vector, star_star]
    have hp := CenteredPairWord.of_pairWord (fun i => (a i : P)) (fun i => (e i : P))
      (fun i => (a i).property) (fun i => (e i).property) ha0 he0
    simpa only [prod_pairWord, alternatingProduct] using
      G.central_trace_pair_word h1 hfree u hu hu0 huv c₀ hc₀ hD hp d.property b.property
  have hz : G.vector (star c₀) = 0 := by
    apply ext_inner_right ℂ
    intro x
    have hs : closure (Submodule.span ℂ (reducedWordVectors G A D) : Set H) ⊆
        {y | inner ℂ (G.vector (star c₀)) y = 0} := by
      apply closure_minimal ?_ (isClosed_eq (by fun_prop) (by fun_prop))
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact hw y hy
      | zero =>
        change inner ℂ (G.vector (star c₀)) (0 : H) = 0
        exact inner_zero_right _
      | add y z _ _ hy hz =>
        change inner ℂ (G.vector (star c₀)) (y + z) = 0
        change inner ℂ (G.vector (star c₀)) y = 0 at hy
        change inner ℂ (G.vector (star c₀)) z = 0 at hz
        simp only [inner_add_right, hy, hz, add_zero]
      | smul r y _ hy =>
        change inner ℂ (G.vector (star c₀)) (r • y) = 0
        change inner ℂ (G.vector (star c₀)) y = 0 at hy
        simp only [inner_smul_right, hy, mul_zero]
    have hx : x ∈ closure (Submodule.span ℂ (reducedWordVectors G A D) : Set H) := by
      change x ∈ (Submodule.span ℂ (reducedWordVectors G A D)).topologicalClosure
      rw [hgen]
      trivial
    rw [inner_zero_left]
    exact hs hx
  have hcz : c₀ = 0 := star_eq_zero.mp (hf (hz.trans (map_zero G.vector).symm))
  exact ⟨G.trace c, sub_eq_zero.mp hcz⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
