import OAI.Analysis.KadisonKastler.RelativeHaarBlocks

namespace OAI

/-! # Scalar freeness after the second finite-base independence step

Centered letters are split by the trace projection. Consecutive base
letters and Haar powers are retained as explicit reduced blocks; the
remaining letters are in the relative kernel and are killed by Popa's
endpoint identity.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B]

private def haarConjugate (w : unitary B) (x : B) : B :=
  (w : B) * x * star (w : B)

private theorem haarConjugate_mul (w : unitary B) (x y : B) :
    haarConjugate w (x * y) = haarConjugate w x * haarConjugate w y := by
  unfold haarConjugate
  calc
    _ = (w : B) * x * (star (w : B) * (w : B)) * y * star (w : B) := by
      rw [w.property.1, mul_one]
      noncomm_ring
    _ = _ := by noncomm_ring

private theorem haarConjugate_fixed (w : unitary B) {d : B} (hd : Commute (w : B) d) :
    haarConjugate w d = d := by
  rw [haarConjugate, hd.eq, mul_assoc, w.property.2, mul_one]

private theorem haarConjugate_right_base (w : unitary B) (x : B) {d : B}
    (hd : Commute (w : B) d) :
    haarConjugate w (x * d) = haarConjugate w x * d := by
  rw [haarConjugate_mul, haarConjugate_fixed w hd]

private theorem haarConjugate_left_base (w : unitary B) (x : B) {d : B}
    (hd : Commute (w : B) d) :
    haarConjugate w (d * x) = d * haarConjugate w x := by
  rw [haarConjugate_mul, haarConjugate_fixed w hd]

private theorem haarConjugate_power (w s : unitary B) (k : ℤ) :
    haarConjugate w (haarPower s k) = haarPower (w * s * star w) k :=
  (haarPower_unitary_conjugate w s k).symm

section SecondStage

variable {τ : FaithfulTracialState B} {D A T : StarSubalgebra ℂ B}
    {E : B →ₗ[ℂ] B} {s w : unitary B}
    (hE : TraceBaseProjection τ D E) (hfree : FreeHaarMoments τ D s)
    (hDT : D ≤ T) (hAT : A ≤ T) (hsT : (s : B) ∈ T)
    (hw : ∀ d ∈ D, Commute (w : B) d)
    (hind : HaarEndpointIndependence τ D (relativeHaarKernel E T) w)

include hE hDT hAT in
private theorem split_centered_letter {x : B} (hx : x ∈ A) (hτx : τ.toLinearMap x = 0) :
    E x ∈ D ∧ τ.toLinearMap (E x) = 0 ∧ x - E x ∈ relativeHaarKernel E T := by
  refine ⟨hE.mem x, (hE.trace x).trans hτx, ?_⟩
  constructor
  · exact T.sub_mem (hAT hx) (hDT (hE.mem x))
  · change E (x - E x) = 0
    rw [map_sub, hE.fixed (hE.mem x), sub_self]

include hE hfree hDT hsT in
private theorem block_kernel (r : RelativeHaarBlock τ D s) :
    r.value ∈ relativeHaarKernel E T :=
  ⟨r.mem T hDT hsT, r.expectation_zero hfree hE⟩

include hind in
private theorem completed_trace (a b r : B) (p : List (B × B))
    (ha : a ∈ relativeHaarKernel E T ∨ a = 1)
    (hb : b ∈ relativeHaarKernel E T ∨ b = 1)
    (hr : r ∈ relativeHaarKernel E T)
    (hp : ∀ z ∈ p, z.1 ∈ relativeHaarKernel E T ∧ z.2 ∈ relativeHaarKernel E T) :
    τ.toLinearMap (conjugateBlockPrefix w a p * haarConjugate w r * b) = 0 := by
  simpa only [one_mul, haarConjugate] using hind.completed_blocks a b r p ha hb hr hp 1 D.one_mem

include hE hfree hDT hAT hsT hw hind in
/-- The finite expansion induction, retaining each maximal base/Haar
segment as a reduced block rather than assuming an amalgamated-freeness theorem. -/
private theorem continuation_trace_zero
    (l : List (B × ℤ))
    (hm : ∀ z ∈ l, z.1 ∈ A) (hz : ∀ z ∈ l, τ.toLinearMap z.1 = 0)
    (hk : l.IsChain (fun z _ => z.2 ≠ 0))
    (a : B) (ha : a ∈ relativeHaarKernel E T ∨ a = 1)
    (p : List (B × B))
    (hp : ∀ z ∈ p, z.1 ∈ relativeHaarKernel E T ∧ z.2 ∈ relativeHaarKernel E T)
    (r : RelativeHaarBlock τ D s) :
    τ.toLinearMap (conjugateBlockPrefix w a p * haarConjugate w r.value *
      centeredHaarWord (w * s * star w) l) = 0 := by
  induction l generalizing a p r with
  | nil =>
    simpa only [centeredHaarWord_nil, mul_one] using
      completed_trace hind a 1 r.value p ha (Or.inr rfl)
        (block_kernel hE hfree hDT hsT r) hp
  | cons z l ih =>
    obtain ⟨hd, hdz, hx⟩ := split_centered_letter hE hDT hAT (hm z (by simp)) (hz z (by simp))
    let d := E z.1
    let x := z.1 - E z.1
    have hdx : z.1 = d + x := by dsimp [d, x]; abel
    have htailm : ∀ t ∈ l, t.1 ∈ A := fun t ht => hm t (List.mem_cons_of_mem z ht)
    have htailz : ∀ t ∈ l, τ.toLinearMap t.1 = 0 := fun t ht => hz t (List.mem_cons_of_mem z ht)
    have htailk : l.IsChain (fun t _ => t.2 ≠ 0) := hk.tail
    have hdterm : τ.toLinearMap
        (conjugateBlockPrefix w a p * haarConjugate w r.value *
          ((d * haarPower (w * s * star w) z.2) *
            centeredHaarWord (w * s * star w) l)) = 0 := by
      by_cases hkz : z.2 = 0
      · have hl : l = [] := by
          cases l with
          | nil => rfl
          | cons t l => exact ((List.isChain_cons_cons.mp hk).1 hkz).elim
        subst l
        have hrx : r.value * d ∈ relativeHaarKernel E T := by
          constructor
          · exact T.mul_mem (r.mem T hDT hsT) (hDT hd)
          · exact hE.kernel_right_mul hd (r.expectation_zero hfree hE)
        have ht := completed_trace hind a 1 (r.value * d) p ha (Or.inr rfl) hrx hp
        rw [haarConjugate_right_base w r.value (hw d hd)] at ht
        simpa only [hkz, haarPower_zero, centeredHaarWord_nil, mul_one, mul_assoc] using ht
      · let r' := r.append d hd hdz z.2 hkz
        have ht := ih htailm htailz htailk a ha p hp r'
        have he : haarConjugate w r'.value =
            haarConjugate w r.value * d * haarPower (w * s * star w) z.2 := by
          rw [RelativeHaarBlock.value_append, haarConjugate_mul,
            haarConjugate_right_base w r.value (hw d hd), haarConjugate_power]
        rw [he] at ht
        simpa only [mul_assoc] using ht
    have hxterm : τ.toLinearMap
        (conjugateBlockPrefix w a p * haarConjugate w r.value *
          ((x * haarPower (w * s * star w) z.2) *
            centeredHaarWord (w * s * star w) l)) = 0 := by
      by_cases hkz : z.2 = 0
      · have hl : l = [] := by
          cases l with
          | nil => rfl
          | cons t l => exact ((List.isChain_cons_cons.mp hk).1 hkz).elim
        subst l
        have ht := completed_trace hind a x r.value p ha (Or.inl hx)
          (block_kernel hE hfree hDT hsT r) hp
        simpa only [hkz, haarPower_zero, centeredHaarWord_nil, mul_one, mul_assoc] using ht
      · let p' := p ++ [(r.value, x)]
        have hp' : ∀ t ∈ p', t.1 ∈ relativeHaarKernel E T ∧ t.2 ∈ relativeHaarKernel E T := by
          intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · exact hp t ht
          · obtain rfl := List.mem_singleton.mp ht
            exact ⟨block_kernel hE hfree hDT hsT r, hx⟩
        let r' := RelativeHaarBlock.single (τ := τ) (s := s) 1 D.one_mem z.2 hkz
        have ht := ih htailm htailz htailk a ha p' hp' r'
        rw [conjugateBlockPrefix_append, RelativeHaarBlock.value_single, one_mul,
          haarConjugate_power] at ht
        simpa only [haarConjugate, mul_assoc] using ht
    rw [centeredHaarWord_cons, hdx]
    simp only [add_mul, mul_add, map_add, hdterm, hxterm, add_zero] at ⊢

include hE hfree hDT hAT hsT hw hind in
private theorem second_stage_centered_word
    (l : List (B × ℤ)) (hl : l ≠ [])
    (hm : ∀ z ∈ l, z.1 ∈ A) (hz : ∀ z ∈ l, τ.toLinearMap z.1 = 0)
    (hk : l.IsChain (fun z _ => z.2 ≠ 0)) :
    τ.toLinearMap (centeredHaarWord (w * s * star w) l) = 0 := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons z l =>
    by_cases hkz : z.2 = 0
    · have hl : l = [] := by
        cases l with
        | nil => rfl
        | cons t l => exact ((List.isChain_cons_cons.mp hk).1 hkz).elim
      subst l
      simpa only [centeredHaarWord_cons, centeredHaarWord_nil, hkz, haarPower_zero,
        mul_one] using hz z (by simp)
    · obtain ⟨hd, hdz, hx⟩ := split_centered_letter hE hDT hAT (hm z (by simp)) (hz z (by simp))
      have htailm : ∀ t ∈ l, t.1 ∈ A := fun t ht => hm t (List.mem_cons_of_mem z ht)
      have htailz : ∀ t ∈ l, τ.toLinearMap t.1 = 0 := fun t ht => hz t (List.mem_cons_of_mem z ht)
      have htailk : l.IsChain (fun t _ => t.2 ≠ 0) := hk.tail
      have hdterm := continuation_trace_zero hE hfree hDT hAT hsT hw hind l
        htailm htailz htailk 1 (Or.inr rfl) [] (by simp)
        (RelativeHaarBlock.single (τ := τ) (s := s) (E z.1) hd z.2 hkz)
      rw [RelativeHaarBlock.value_single, haarConjugate_left_base w (haarPower s z.2)
        (hw _ hd), haarConjugate_power] at hdterm
      have hxterm := continuation_trace_zero hE hfree hDT hAT hsT hw hind l
        htailm htailz htailk (z.1 - E z.1) (Or.inl hx) [] (by simp)
        (RelativeHaarBlock.single (τ := τ) (s := s) 1 D.one_mem z.2 hkz)
      rw [RelativeHaarBlock.value_single, one_mul, haarConjugate_power] at hxterm
      simp only [conjugateBlockPrefix, List.map_nil, List.prod_nil, mul_one, one_mul,
        mul_assoc] at hdterm hxterm
      have he : z.1 = E z.1 + (z.1 - E z.1) := by abel
      rw [centeredHaarWord_cons, he]
      simp only [add_mul, map_add, mul_assoc, hdterm, hxterm, add_zero]

include hE hfree hDT hAT hsT hw hind in
/-- The second-stage finite-base independence produces scalar free Haar
moments relative to the whole prescribed algebra. -/
theorem freeHaarMoments_of_second_independence :
    FreeHaarMoments τ A (w * s * star w) := by
  constructor
  · exact haar_moments_unitary_conjugate τ w s hfree.haar_moment
  · intro n hn a k ha hz hk
    let l : List (B × ℤ) := List.ofFn (fun i => (a i, k i))
    have hl : l ≠ [] := by
      intro he
      have hh := congrArg List.length he
      simp only [l, List.length_ofFn, List.length_nil] at hh
      omega
    have hm : ∀ z ∈ l, z.1 ∈ A := by
      intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact ha i
    have hc : ∀ z ∈ l, τ.toLinearMap z.1 = 0 := by
      intro z hzi
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hzi
      exact hz i
    have he : l.IsChain (fun z _ => z.2 ≠ 0) := by
      apply List.isChain_ofFn.mpr
      intro i hi
      exact hk ⟨i, by omega⟩ hi
    simpa only [centeredHaarWord, l, List.map_ofFn, Function.comp_def] using
      second_stage_centered_word hE hfree hDT hAT hsT hw hind l hl hm hc he

end SecondStage

end

end KadisonKastler

end OAI
