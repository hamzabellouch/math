import OAI.NumberTheory.Ostmann.QuadraticCenter.SquarefreeFrequency
import OAI.NumberTheory.Ostmann.Characters.TranslatedCharacterPoisson

namespace OAI

/-! # Finite reindexing by squarefree kernel and square part -/

namespace Ostmann

open scoped BigOperators

noncomputable def frequencyTriples (L U : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 U).product (L.divisors.product (Finset.Icc 1 U))).filter
    (fun z => Squarefree (z.1 * z.2.1) ∧ z.1.Coprime L ∧ z.1 * z.2.1 * z.2.2 ^ 2 ≤ U)

theorem mem_frequencyTriples {L U : ℕ} {z : ℕ × ℕ × ℕ} :
    z ∈ frequencyTriples L U ↔
      1 ≤ z.1 ∧ z.1 ≤ U ∧ z.2.1 ∈ L.divisors ∧ 1 ≤ z.2.2 ∧ z.2.2 ≤ U ∧
      Squarefree (z.1 * z.2.1) ∧ z.1.Coprime L ∧ z.1 * z.2.1 * z.2.2 ^ 2 ≤ U := by
  rcases z with ⟨s, v, w⟩
  simp only [frequencyTriples, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  tauto

private def frequencyTripleData {L U : ℕ} {z : ℕ × ℕ × ℕ}
    (hz : z ∈ frequencyTriples L U) : SquarefreeFrequency L (z.1 * z.2.1 * z.2.2 ^ 2) where
  s := z.1
  v := z.2.1
  w := z.2.2
  s_pos := (mem_frequencyTriples.mp hz).1
  v_pos := Nat.pos_of_mem_divisors (mem_frequencyTriples.mp hz).2.2.1
  w_pos := (mem_frequencyTriples.mp hz).2.2.2.1
  kernel_squarefree := (mem_frequencyTriples.mp hz).2.2.2.2.2.1
  v_dvd := (Nat.mem_divisors.mp (mem_frequencyTriples.mp hz).2.2.1).1
  s_coprime := (mem_frequencyTriples.mp hz).2.2.2.2.2.2.1
  value := rfl

theorem frequencyTriple_value_injective {L U : ℕ}
    {x y : ℕ × ℕ × ℕ} (hx : x ∈ frequencyTriples L U) (hy : y ∈ frequencyTriples L U)
    (h : x.1 * x.2.1 * x.2.2 ^ 2 = y.1 * y.2.1 * y.2.2 ^ 2) : x = y := by
  let a := frequencyTripleData hx
  let b : SquarefreeFrequency L (x.1 * x.2.1 * x.2.2 ^ 2) :=
    { frequencyTripleData hy with value := h.symm }
  have he := a.unique b
  apply Prod.ext
  · exact congrArg SquarefreeFrequency.s he
  · exact Prod.ext (congrArg SquarefreeFrequency.v he) (congrArg SquarefreeFrequency.w he)

theorem frequencyTriple_value_surjective {L U u : ℕ} (hL : 0 < L)
    (hu : u ∈ Finset.Icc 1 U) :
    ∃ z ∈ frequencyTriples L U, z.1 * z.2.1 * z.2.2 ^ 2 = u := by
  obtain ⟨hu, huU⟩ := Finset.mem_Icc.mp hu
  obtain ⟨a⟩ := exists_squarefreeFrequency hL hu
  refine ⟨(a.s, a.v, a.w), mem_frequencyTriples.mpr ?_, a.value⟩
  refine ⟨a.s_pos, a.s_le.trans huU, Nat.mem_divisors.mpr ⟨a.v_dvd, hL.ne'⟩,
    a.w_pos, ?_, a.kernel_squarefree, a.s_coprime, a.value.le.trans huU⟩
  have hsq := a.w_sq_le.trans huU
  nlinarith [a.w_pos]

theorem sum_squarefree_frequencies (L U : ℕ) (hL : 0 < L) (F : ℕ → ℂ) :
    (∑ u ∈ Finset.Icc 1 U, F u) =
      ∑ z ∈ frequencyTriples L U, F (z.1 * z.2.1 * z.2.2 ^ 2) := by
  symm
  apply Finset.sum_bij (fun z _ => z.1 * z.2.1 * z.2.2 ^ 2)
  · intro z hz
    let a := frequencyTripleData hz
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Nat.mul_pos a.s_pos a.v_pos) (pow_pos a.w_pos _),
      (mem_frequencyTriples.mp hz).2.2.2.2.2.2.2⟩
  · intro x hx y hy hxy
    exact frequencyTriple_value_injective hx hy hxy
  · intro u hu
    obtain ⟨z, hz, he⟩ := frequencyTriple_value_surjective hL hu
    exact ⟨z, hz, he⟩
  · intro z hz
    rfl

theorem quadratic_character_square {M : ℕ} (χ : DirichletCharacter ℂ M)
    (hχ : χ.IsQuadratic) (w : ℕ) :
    χ ((w : ZMod M) ^ 2) = if w.Coprime M then 1 else 0 := by
  classical
  by_cases hw : w.Coprime M
  · rw [ite_eq_left hw, map_pow, ← χ.pow_apply' two_ne_zero, hχ.sq_eq_one]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime w M).mpr hw)
  · rw [ite_eq_right hw, map_pow, MulChar.map_nonunit χ ((ZMod.isUnit_iff_coprime w M).not.mpr hw)]
    norm_num

theorem quadratic_character_frequency {M : ℕ} (χ : DirichletCharacter ℂ M)
    (hχ : χ.IsQuadratic) (s v w : ℕ) :
    χ ((s * v * w ^ 2 : ℕ) : ZMod M) =
      χ (s : ZMod M) * χ (v : ZMod M) * (if w.Coprime M then 1 else 0) := by
  push_cast
  rw [map_mul χ, map_mul χ, quadratic_character_square χ hχ]

end Ostmann

end OAI
