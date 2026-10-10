import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeConjugateWords
import OAI.Analysis.KadisonSimilarity.Tensor.OrthogonalConstantPairing
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeWordHilbert

namespace OAI

/-! Central pairings vanish on free words with a centered terminal letter.
The proof uses an actual infinite family of orthogonal unitary conjugates. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) {A D : StarSubalgebra ℂ P}

/-- The conjugates of a reduced word force its pairing with every central
element to vanish. Only the terminal `A` letter is required to be centered. -/
theorem central_trace_centered_pair_word
    (h1 : G.trace 1 = 1) (hfree : ScalarFree G.trace A D)
    (u : ℕ → unitary P) (hu : ∀ n, (u n : P) ∈ D)
    (hu0 : ∀ n, G.trace (u n : P) = 0)
    (huv : ∀ i j, G.trace ((u i : P) * star (u j : P)) = if i = j then 1 else 0)
    (c : P) (hc : ∀ a : P, a * c = c * a)
    {xs : List P} (hxs : CenteredPairWord G.trace A D xs)
    {d b : P} (hd : d ∈ D) (hb : b ∈ A) (hb0 : G.trace b = 0) :
    G.trace (c * (d * xs.prod * b)) = 0 := by
  classical
  let w := d * xs.prod * b
  let v : ℕ → H := fun n => G.vector ((u n : P) * w * star (u n : P))
  have hgram (i j : ℕ) : inner ℂ (v i) (v j) =
      if i = j then (‖G.vector w‖ : ℂ) ^ 2 else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      have he : star ((u i : P) * w * star (u i : P)) *
          ((u i : P) * w * star (u i : P)) =
          (u i : P) * (star w * w) * star (u i : P) := by
        simp only [star_mul, star_star]
        calc
          _ = (u i : P) * star w * (star (u i : P) * (u i : P)) *
              w * star (u i : P) := by noncomm_ring
          _ = _ := by rw [(u i).property.1]; simp only [mul_one, mul_assoc]
      change inner ℂ (G.vector _) (G.vector _) = _
      rw [G.inner_vector, he, trace_unitary_conjugate G.tracial,
        ← G.inner_vector, inner_self_eq_norm_sq_to_K]
      rfl
    · simp only [hij, ite_false]
      change inner ℂ (G.vector _) (G.vector _) = 0
      rw [G.inner_vector]
      simpa only [w, mul_assoc] using
        hfree.trace_conjugate_words_zero G.trace_star h1 hxs hb hb0 hd
          (hu i) (hu j) (hu0 i) (hu0 j) (by simpa only [hij, ite_false] using huv i j)
  have hp (n : ℕ) : inner ℂ (G.vector (star c)) (v n) = G.trace (c * w) := by
    change inner ℂ (G.vector (star c)) (G.vector _) = _
    rw [G.inner_vector]
    simpa only [star_star] using trace_central_conjugate G.tracial (star c) w (u n)
      (by simpa only [star_star] using (hc (u n)).symm)
  have hz := orthogonal_constant_pairing_eq_zero v ‖G.vector w‖ hgram
    (G.vector (star c)) ((starRingEnd ℂ) (G.trace (c * w))) (fun n => by
      simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) (hp n))
  change star (G.trace (c * w)) = 0 at hz
  exact star_eq_zero.mp hz

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
