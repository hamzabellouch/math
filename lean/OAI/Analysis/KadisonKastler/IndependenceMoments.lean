import OAI.Analysis.KadisonKastler.PublishedIndependence
import OAI.Analysis.KadisonKastler.ReducedExpectation

namespace OAI

/-! # Scalar free moments from finite-base independence

The endpoint form of Popa's independence identity gives exactly the
alternating moments used by the free diagonal construction. The final
Haar exponent may vanish; in that case its coefficient is an endpoint.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B]

omit [CStarAlgebra B] in
private theorem property_before_last {P : B × ℤ → Prop}
    (l : List (B × ℤ)) (z : B × ℤ)
    (h : (l ++ [z]).IsChain (fun x _ => P x)) : ∀ x ∈ l, P x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil =>
      have ha : P a := (List.isChain_cons_cons.mp h).1
      intro x hx
      exact (List.mem_singleton.mp hx) ▸ ha
    | cons b l =>
      have hh := List.isChain_cons_cons.mp h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hh.1
      · exact ih hh.2 x hx

namespace HaarEndpointIndependence

variable {τ : FaithfulTracialState B} {D : StarSubalgebra ℂ B}
    {X : Submodule ℂ B} {w : unitary B}

private theorem word_with_endpoint (h : HaarEndpointIndependence τ D X w)
    (l : List (B × ℤ)) (hl : l ≠ [])
    (hmem : ∀ z ∈ l, z.1 ∈ X ∧ z.2 ≠ 0)
    (b : B) (hb : b ∈ X ∨ b = 1) :
    τ.toLinearMap (centeredHaarWord w l * b) = 0 := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons a l =>
    have ha := hmem a (List.mem_cons_self ..)
    have hh := h a.1 b (Or.inl ha.1) hb a.2 ha.2 l
      (fun z hz => hmem z (List.mem_cons_of_mem _ hz)) 1 D.one_mem
    simpa only [one_mul, centeredHaarWord, List.map_cons, List.prod_cons, mul_assoc] using hh

/-- The endpoint identity also permits a zero final exponent, by absorbing
the final centered coefficient into the endpoint. -/
theorem centered_word (h : HaarEndpointIndependence τ D X w)
    (htrace : ∀ x ∈ X, τ.toLinearMap x = 0)
    (l : List (B × ℤ)) (hl : l ≠ [])
    (hmem : ∀ z ∈ l, z.1 ∈ X)
    (hexp : l.IsChain (fun x _ => x.2 ≠ 0)) :
    τ.toLinearMap (centeredHaarWord w l) = 0 := by
  obtain ⟨s, z, rfl⟩ := (List.eq_nil_or_concat' l).resolve_left hl
  have hz : z.1 ∈ X := hmem z (by simp)
  have hs : ∀ x ∈ s, x.1 ∈ X ∧ x.2 ≠ 0 := by
    intro x hx
    exact ⟨hmem x (List.mem_append_left _ hx), property_before_last s z hexp x hx⟩
  by_cases hk : z.2 = 0
  · have he : centeredHaarWord w (s ++ [z]) = centeredHaarWord w s * z.1 := by
      simp [centeredHaarWord, hk, List.prod_append]
    rw [he]
    by_cases hnil : s = []
    · simpa [hnil] using htrace z.1 hz
    · exact h.word_with_endpoint s hnil hs z.1 (Or.inl hz)
  · have hall : ∀ x ∈ s ++ [z], x.1 ∈ X ∧ x.2 ≠ 0 := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hs x hx
      · simp only [List.mem_singleton] at hx
        subst x
        exact ⟨hz, hk⟩
    simpa only [mul_one] using
      h.word_with_endpoint (s ++ [z]) (by simp) hall 1 (Or.inr rfl)

/-- The scalar freeness hypothesis needed downstream follows from the
published endpoint identity whenever the centered base lies in `X`. -/
theorem freeHaarMoments (h : HaarEndpointIndependence τ D X w)
    (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower w k) = 0)
    (htrace : ∀ x ∈ X, τ.toLinearMap x = 0)
    (A : StarSubalgebra ℂ B)
    (hAX : ∀ a ∈ A, τ.toLinearMap a = 0 → a ∈ X) :
    FreeHaarMoments τ A w := by
  refine ⟨hhaar, ?_⟩
  intro n hn a k ha ht hk
  let l : List (B × ℤ) := List.ofFn (fun i => (a i, k i))
  have hl : l ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [l, List.length_ofFn, List.length_nil] at hh
    omega
  have hm : ∀ z ∈ l, z.1 ∈ X := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hAX (a i) (ha i) (ht i)
  have he : l.IsChain (fun x _ => x.2 ≠ 0) := by
    apply List.isChain_ofFn.mpr
    intro i hi
    exact hk ⟨i, by omega⟩ hi
  simpa only [centeredHaarWord, l, List.map_ofFn, Function.comp_def] using
    h.centered_word htrace l hl hm he

end HaarEndpointIndependence

end

end KadisonKastler

end OAI
