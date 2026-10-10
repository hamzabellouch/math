import OAI.Analysis.KadisonKastler.RelativeHaarExpectation

namespace OAI

/-! # Reduced blocks for the second-stage scalar freeness argument -/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [CStarAlgebra B]

theorem haarPower_mem_of_mem (T : StarSubalgebra ℂ B) (s : unitary B)
    (hs : (s : B) ∈ T) (k : ℤ) : haarPower s k ∈ T := by
  cases k with
  | ofNat n =>
    change haarPower s (n : ℤ) ∈ T
    rw [haarPower_natCast]
    exact T.pow_mem hs n
  | negSucc n =>
    rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by omega, haarPower_neg, haarPower_natCast]
    exact star_mem (T.pow_mem hs (n + 1))

omit [CStarAlgebra B] in
private theorem chain_nonzero {l : List (B × ℤ)} (h : ∀ z ∈ l, z.2 ≠ 0) :
    l.IsChain (fun z _ => z.2 ≠ 0) := by
  induction l with
  | nil => exact List.isChain_nil
  | cons x l ih =>
    cases l with
    | nil => exact List.isChain_singleton _
    | cons y l =>
      exact List.isChain_cons_cons.mpr ⟨h x (by simp),
        ih (fun z hz => h z (List.mem_cons_of_mem _ hz))⟩

/-- A nonempty Haar block with centered base separators and a base prefix. -/
structure RelativeHaarBlock (τ : FaithfulTracialState B) (D : StarSubalgebra ℂ B)
    (s : unitary B) where
  left : B
  left_mem : left ∈ D
  exponent : ℤ
  nonzero : exponent ≠ 0
  tail : List (B × ℤ)
  tail_mem : ∀ z ∈ tail, z.1 ∈ D
  tail_centered : ∀ z ∈ tail, τ.toLinearMap z.1 = 0
  tail_nonzero : ∀ z ∈ tail, z.2 ≠ 0

namespace RelativeHaarBlock

variable {τ : FaithfulTracialState B} {D : StarSubalgebra ℂ B} {s : unitary B}

def value (r : RelativeHaarBlock τ D s) : B :=
  r.left * reducedHaarWord s r.exponent r.tail

def single (d : B) (hd : d ∈ D) (q : ℤ) (hq : q ≠ 0) : RelativeHaarBlock τ D s :=
  ⟨d, hd, q, hq, [], by simp, by simp, by simp⟩

@[simp]
theorem value_single (d : B) (hd : d ∈ D) (q : ℤ) (hq : q ≠ 0) :
    (single (τ := τ) (s := s) d hd q hq).value = d * haarPower s q := by
  simp [single, value, reducedHaarWord]

def append (r : RelativeHaarBlock τ D s) (d : B) (hd : d ∈ D)
    (hz : τ.toLinearMap d = 0) (q : ℤ) (hq : q ≠ 0) : RelativeHaarBlock τ D s where
  left := r.left
  left_mem := r.left_mem
  exponent := r.exponent
  nonzero := r.nonzero
  tail := r.tail ++ [(d, q)]
  tail_mem := by
    intro z hz'
    rcases List.mem_append.mp hz' with hz' | hz'
    · exact r.tail_mem z hz'
    · exact (List.mem_singleton.mp hz') ▸ hd
  tail_centered := by
    intro z hz'
    rcases List.mem_append.mp hz' with hz' | hz'
    · exact r.tail_centered z hz'
    · exact (List.mem_singleton.mp hz') ▸ hz
  tail_nonzero := by
    intro z hz'
    rcases List.mem_append.mp hz' with hz' | hz'
    · exact r.tail_nonzero z hz'
    · exact (List.mem_singleton.mp hz') ▸ hq

theorem value_append (r : RelativeHaarBlock τ D s) (d : B) (hd : d ∈ D)
    (hz : τ.toLinearMap d = 0) (q : ℤ) (hq : q ≠ 0) :
    (r.append d hd hz q hq).value = r.value * d * haarPower s q := by
  simp only [value, append, reducedHaarWord, centeredHaarWord, List.map_append,
    List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  noncomm_ring

theorem mem (r : RelativeHaarBlock τ D s) (T : StarSubalgebra ℂ B)
    (hDT : D ≤ T) (hs : (s : B) ∈ T) : r.value ∈ T := by
  apply T.mul_mem (hDT r.left_mem)
  apply T.mul_mem (haarPower_mem_of_mem T s hs r.exponent)
  apply list_prod_mem
  intro x hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
  exact T.mul_mem (hDT (r.tail_mem z hz)) (haarPower_mem_of_mem T s hs z.2)

theorem expectation_zero (r : RelativeHaarBlock τ D s)
    (hfree : FreeHaarMoments τ D s) {E : B →ₗ[ℂ] B}
    (hE : TraceBaseProjection τ D E) : E r.value = 0 := by
  rw [value, hE.left_mul r.left_mem]
  rw [hfree.reducedHaarWord_expectation_zero E hE.mem hE.pairing r.exponent r.nonzero
    r.tail r.tail_mem r.tail_centered (chain_nonzero r.tail_nonzero), mul_zero]

end RelativeHaarBlock

/-- A completed alternating prefix: each pair is a conjugated block and
a following kernel letter. -/
def conjugateBlockPrefix (w : unitary B) (a : B) (l : List (B × B)) : B :=
  a * (l.map (fun z => (w : B) * z.1 * star (w : B) * z.2)).prod

theorem conjugateBlockPrefix_append (w : unitary B) (a : B) (l : List (B × B))
    (y x : B) :
    conjugateBlockPrefix w a (l ++ [(y, x)]) =
      conjugateBlockPrefix w a l * ((w : B) * y * star (w : B)) * x := by
  simp only [conjugateBlockPrefix, List.map_append, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  noncomm_ring

private def completedCoefficients (r : B) : List (B × B) → List (B × ℤ)
  | [] => [(r, -1)]
  | z :: l => (z.1, -1) :: (z.2, 1) :: completedCoefficients r l

private theorem completedCoefficients_word (w : unitary B) (r : B)
    (l : List (B × B)) :
    (w : B) * centeredHaarWord w (completedCoefficients r l) =
      (l.map (fun z => (w : B) * z.1 * star (w : B) * z.2)).prod *
        ((w : B) * r * star (w : B)) := by
  induction l with
  | nil => simp [completedCoefficients, centeredHaarWord, haarPower,
      ← Unitary.star_eq_inv, Unitary.coe_star, mul_assoc]
  | cons z l ih =>
    simp only [completedCoefficients, centeredHaarWord_cons, List.map_cons, List.prod_cons]
    have he : haarPower w (-1) = star (w : B) := by
      simp only [haarPower, zpow_neg_one, ← Unitary.star_eq_inv, Unitary.coe_star]
    have ho : haarPower w 1 = (w : B) := by simp [haarPower]
    rw [he, ho]
    calc
      _ = ((w : B) * z.1 * star (w : B) * z.2) *
          ((w : B) * centeredHaarWord w (completedCoefficients r l)) := by noncomm_ring
      _ = _ := by rw [ih]; noncomm_ring

/-- Every completed prefix and final kernel block is annihilated by the
published endpoint formula. -/
theorem HaarEndpointIndependence.completed_blocks
    {τ : FaithfulTracialState B} {D : StarSubalgebra ℂ B} {X : Submodule ℂ B}
    {w : unitary B} (h : HaarEndpointIndependence τ D X w)
    (a b r : B) (l : List (B × B)) (ha : a ∈ X ∨ a = 1) (hb : b ∈ X ∨ b = 1)
    (hr : r ∈ X) (hl : ∀ z ∈ l, z.1 ∈ X ∧ z.2 ∈ X) :
    TraceOrthogonal τ D
      (conjugateBlockPrefix w a l * ((w : B) * r * star (w : B)) * b) := by
  have hm : ∀ z ∈ completedCoefficients r l, z.1 ∈ X ∧ z.2 ≠ 0 := by
    induction l with
    | nil =>
      intro z hz
      obtain rfl := List.mem_singleton.mp hz
      exact ⟨hr, by norm_num⟩
    | cons p l ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨(hl p (by simp)).1, by norm_num⟩
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨(hl p (by simp)).2, by norm_num⟩
        · exact ih (fun z hz => hl z (List.mem_cons_of_mem p hz)) z hz
  have hh := h a b ha hb 1 (by norm_num) (completedCoefficients r l) hm
  have he := completedCoefficients_word w r l
  unfold TraceOrthogonal at hh ⊢
  intro d hd
  have ht := hh d hd
  have ho : haarPower w 1 = (w : B) := by simp [haarPower]
  rw [ho] at ht
  change τ.toLinearMap (d * (a * (w : B) * centeredHaarWord w (completedCoefficients r l) * b)) = 0 at ht
  rw [mul_assoc a (w : B), he] at ht
  simpa only [conjugateBlockPrefix, mul_assoc] using ht

end

end KadisonKastler

end OAI
