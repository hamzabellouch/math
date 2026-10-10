import OAI.GroupTheory.PolycyclicRecognition.Analysis.BoundedPathGrowth

namespace OAI

/-!
# Bounded-height chains as actual group words

The relative increments of a finite chain form a word. The prefix height bounds
are preserved exactly, as required by the triangular matrix estimates.
-/

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W]

theorem BoundedHeightChain.exists_word {π : G → W} {L M : ℝ} {n : ℕ} {x y : G}
    (h : BoundedHeightChain π L M n x y) :
    ∃ l : List G, l.length = n ∧ x * l.prod = y ∧
      (∀ a ∈ l, dist 1 a ≤ L) ∧
      ∀ p q : List G, p ++ q = l → ‖π (x * p.prod)‖ ≤ M := by
  induction h with
  | nil x hx =>
    refine ⟨[], rfl, by simp, by simp, ?_⟩
    intro p q hpq
    have hp : p = [] := (List.append_eq_nil_iff.mp hpq).1
    simpa only [hp, List.prod_nil, mul_one] using hx
  | @cons k x y z hx hxy _ ih =>
    obtain ⟨l, hlen, hprod, hstep, hprefix⟩ := ih
    let a := x⁻¹ * y
    have hxa : x * a = y := by simp [a]
    have ha : dist 1 a ≤ L := by
      have hd : dist 1 a = dist x y := by
        simpa only [mul_one, hxa] using (dist_mul_left x 1 a).symm
      rwa [hd]
    refine ⟨a :: l, by simp [hlen], ?_, ?_, ?_⟩
    · simpa only [List.prod_cons, ← mul_assoc, hxa] using hprod
    · intro b hb
      rcases List.mem_cons.mp hb with hba | hbl
      · simpa only [hba] using ha
      · exact hstep b hbl
    · intro p q hpq
      cases p with
      | nil => simpa only [List.prod_nil, mul_one] using hx
      | cons b p =>
        have he := List.cons.inj hpq
        have hb : b = a := he.1
        have hp : p ++ q = l := he.2
        subst b
        simpa only [List.prod_cons, ← mul_assoc, hxa] using hprefix p q hp

end PolycyclicRecognition

end OAI
