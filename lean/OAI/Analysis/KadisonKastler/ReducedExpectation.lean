import OAI.Analysis.KadisonKastler.FreeHaarClosure

namespace OAI

/-! # Reduced Haar words are orthogonal to the base algebra

These finite word calculations are the algebraic part of the conditional
expectation argument. No conditional expectation existence or free-product
norm theorem is assumed.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

/-- An alternating word, with a base coefficient followed by each Haar power. -/
def centeredHaarWord (v : unitary B) (l : List (B × ℤ)) : B :=
  (l.map (fun x => x.1 * haarPower v x.2)).prod

@[simp]
theorem centeredHaarWord_nil (v : unitary B) : centeredHaarWord v [] = 1 := rfl

@[simp]
theorem centeredHaarWord_cons (v : unitary B) (x : B × ℤ) (l : List (B × ℤ)) :
    centeredHaarWord v (x :: l) = (x.1 * haarPower v x.2) * centeredHaarWord v l := rfl

/-- A reduced word with an initial Haar power. -/
def reducedHaarWord (v : unitary B) (q : ℤ) (l : List (B × ℤ)) : B :=
  haarPower v q * centeredHaarWord v l

private def appendLastExponent (q : ℤ) : List (B × ℤ) → List (B × ℤ)
  | [] => []
  | [x] => [(x.1, x.2 + q)]
  | x :: y :: l => x :: appendLastExponent q (y :: l)

omit [CStarAlgebra B] in
private theorem appendLastExponent_fst (q : ℤ) (l : List (B × ℤ)) :
    (appendLastExponent q l).map Prod.fst = l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases l with
    | nil => rfl
    | cons y l => simpa only [appendLastExponent, List.map_cons] using congrArg (x.1 :: ·) ih

omit [CStarAlgebra B] in
private theorem appendLastExponent_property (q : ℤ) (l : List (B × ℤ)) (P : B → Prop)
    (h : ∀ x ∈ l, P x.1) : ∀ x ∈ appendLastExponent q l, P x.1 := by
  intro x hx
  have hm : x.1 ∈ l.map Prod.fst := by
    rw [← appendLastExponent_fst q l]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
  simpa only [he] using h y hy

omit [CStarAlgebra B] in
private theorem appendLastExponent_chain (q : ℤ) (l : List (B × ℤ))
    (h : l.IsChain (fun x _ => x.2 ≠ 0)) :
    (appendLastExponent q l).IsChain (fun x _ => x.2 ≠ 0) := by
  induction l with
  | nil => exact List.isChain_nil
  | cons x l ih =>
    cases l with
    | nil => exact List.isChain_singleton _
    | cons y l =>
      have hh := List.isChain_cons_cons.mp h
      have ht := ih hh.2
      cases l with
      | nil =>
        simpa only [appendLastExponent, List.isChain_cons_cons,
          List.isChain_singleton, and_true] using hh.1
      | cons z l => exact List.isChain_cons_cons.mpr ⟨hh.1, ht⟩

private theorem centeredHaarWord_appendLastExponent (v : unitary B) (q : ℤ)
    (l : List (B × ℤ)) (hl : l ≠ []) :
    centeredHaarWord v (appendLastExponent q l) = centeredHaarWord v l * haarPower v q := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons x l ih =>
    cases l with
    | nil => simp [appendLastExponent, haarPower_add, mul_assoc]
    | cons y l =>
      simp only [appendLastExponent, centeredHaarWord_cons]
      rw [ih (by simp)]
      simp only [centeredHaarWord_cons, mul_assoc]

namespace FreeHaarMoments

variable {τ : FaithfulTracialState B} {A : StarSubalgebra ℂ B} {v : unitary B}

/-- The finite-list form of the assumed ordinary centered Haar moments. -/
theorem trace_centeredHaarWord_zero (h : FreeHaarMoments τ A v)
    (l : List (B × ℤ)) (hl : l ≠ [])
    (hmem : ∀ x ∈ l, x.1 ∈ A) (hz : ∀ x ∈ l, τ.toLinearMap x.1 = 0)
    (hk : l.IsChain (fun x _ => x.2 ≠ 0)) :
    τ.toLinearMap (centeredHaarWord v l) = 0 := by
  have ht := h.alternating_moment l.length (List.length_pos_iff.mpr hl)
    (fun i => (l.get i).1) (fun i => (l.get i).2)
    (fun i => hmem _ (List.get_mem _ _)) (fun i => hz _ (List.get_mem _ _))
    (fun i hi => by simpa using hk.getElem i.val hi)
  have he := congrArg (List.map (fun x : B × ℤ => x.1 * haarPower v x.2))
    (List.ofFn_get l)
  simp only [List.map_ofFn, Function.comp_def] at he
  simpa only [he, centeredHaarWord] using ht

/-- An initial Haar letter can be moved to the final exponent by traciality. -/
theorem trace_reducedHaarWord_zero (h : FreeHaarMoments τ A v)
    (q : ℤ) (hq : q ≠ 0) (l : List (B × ℤ))
    (hmem : ∀ x ∈ l, x.1 ∈ A) (hz : ∀ x ∈ l, τ.toLinearMap x.1 = 0)
    (hk : l.IsChain (fun x _ => x.2 ≠ 0)) :
    τ.toLinearMap (reducedHaarWord v q l) = 0 := by
  by_cases hl : l = []
  · simpa [hl, reducedHaarWord] using h.haar_moment q hq
  have hne : appendLastExponent q l ≠ [] := by
    intro he
    have he' := congrArg (List.map Prod.fst) he
    rw [appendLastExponent_fst] at he'
    exact hl (List.map_eq_nil_iff.mp he')
  rw [reducedHaarWord, τ.tracial, ← centeredHaarWord_appendLastExponent v q l hl]
  exact h.trace_centeredHaarWord_zero _ hne
    (appendLastExponent_property q l (fun x => x ∈ A) hmem)
    (appendLastExponent_property q l (fun x => τ.toLinearMap x = 0) hz)
    (appendLastExponent_chain q l hk)

/-- Every reduced word with a nonzero leading Haar exponent is trace
orthogonal to the whole base algebra. -/
theorem trace_base_mul_reducedHaarWord_zero (h : FreeHaarMoments τ A v)
    (q : ℤ) (hq : q ≠ 0) (l : List (B × ℤ))
    (hmem : ∀ x ∈ l, x.1 ∈ A) (hz : ∀ x ∈ l, τ.toLinearMap x.1 = 0)
    (hk : l.IsChain (fun x _ => x.2 ≠ 0)) {b : B} (hb : b ∈ A) :
    τ.toLinearMap (b * reducedHaarWord v q l) = 0 := by
  let b₀ := traceCenter τ b
  have hb₀ : b₀ ∈ A := A.sub_mem hb (A.smul_mem A.one_mem _)
  have hz₀ : τ.toLinearMap b₀ = 0 := trace_traceCenter τ b
  have hchain : ((b₀, q) :: l).IsChain (fun x _ => x.2 ≠ 0) := by
    cases l with
    | nil => exact List.isChain_singleton _
    | cons x l => exact List.isChain_cons_cons.mpr ⟨hq, hk⟩
  have ht := h.trace_centeredHaarWord_zero ((b₀, q) :: l) (by simp)
    (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hb₀
      · exact hmem x hx)
    (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hz₀
      · exact hz x hx)
    hchain
  have hw := h.trace_reducedHaarWord_zero q hq l hmem hz hk
  have ht' : τ.toLinearMap (b₀ * reducedHaarWord v q l) = 0 := by
    simpa only [centeredHaarWord_cons, reducedHaarWord, mul_assoc] using ht
  simpa only [b₀, traceCenter_apply, sub_mul, smul_mul_assoc, one_mul, map_sub, map_smul,
    smul_eq_mul, hw, mul_zero, sub_zero] using ht'

/-- Exterior base-algebra factors preserve the reduced-word orthogonality. -/
theorem trace_base_mul_sandwiched_reducedHaarWord_zero (h : FreeHaarMoments τ A v)
    (q : ℤ) (hq : q ≠ 0) (l : List (B × ℤ))
    (hmem : ∀ x ∈ l, x.1 ∈ A) (hz : ∀ x ∈ l, τ.toLinearMap x.1 = 0)
    (hk : l.IsChain (fun x _ => x.2 ≠ 0)) {b x y : B}
    (hb : b ∈ A) (hx : x ∈ A) (hy : y ∈ A) :
    τ.toLinearMap (b * (x * reducedHaarWord v q l * y)) = 0 := by
  calc
    _ = τ.toLinearMap ((b * x * reducedHaarWord v q l) * y) := by
      congr 1; noncomm_ring
    _ = τ.toLinearMap (y * (b * x * reducedHaarWord v q l)) := τ.tracial _ _
    _ = τ.toLinearMap ((y * b * x) * reducedHaarWord v q l) := by
      congr 1; noncomm_ring
    _ = 0 := h.trace_base_mul_reducedHaarWord_zero q hq l hmem hz hk
      (A.mul_mem (A.mul_mem hy hb) hx)

end FreeHaarMoments

/-- Faithfulness identifies a base element from all of its trace pairings. -/
theorem eq_zero_of_mem_base_of_trace_pairings (τ : FaithfulTracialState B)
    (A : StarSubalgebra ℂ B) {x : B} (hx : x ∈ A)
    (hpair : ∀ b ∈ A, τ.toLinearMap (b * x) = 0) : x = 0 := by
  exact τ.faithful x (hpair (star x) (A.star_mem' hx))

/-- Any trace-preserving base projection therefore kills the reduced word.
Only its defining range and trace-pairing properties are required here. -/
theorem FreeHaarMoments.reducedHaarWord_expectation_zero
    {τ : FaithfulTracialState B} {A : StarSubalgebra ℂ B} {v : unitary B}
    (h : FreeHaarMoments τ A v) (E : B →ₗ[ℂ] B)
    (hE : ∀ x, E x ∈ A)
    (hpair : ∀ b ∈ A, ∀ x, τ.toLinearMap (b * E x) = τ.toLinearMap (b * x))
    (q : ℤ) (hq : q ≠ 0) (l : List (B × ℤ))
    (hmem : ∀ x ∈ l, x.1 ∈ A) (hz : ∀ x ∈ l, τ.toLinearMap x.1 = 0)
    (hk : l.IsChain (fun x _ => x.2 ≠ 0)) :
    E (reducedHaarWord v q l) = 0 := by
  apply eq_zero_of_mem_base_of_trace_pairings τ A (hE _)
  intro b hb
  rw [hpair b hb]
  exact h.trace_base_mul_reducedHaarWord_zero q hq l hmem hz hk hb

end

end KadisonKastler

end OAI
