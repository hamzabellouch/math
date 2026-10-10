import Mathlib

namespace OAI

namespace Problem355.UniformAction

open scoped BigOperators

section Action

variable {G X : Type*} [Group G] [Fintype G] [finiteAction : Fintype X] [DecidableEq X]
  [MulAction G X] [MulAction.IsPretransitive G X]

theorem transporter_card_eq {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [DecidableEq X] [MulAction G X] [MulAction.IsPretransitive G X] (x y z : X) :
    Fintype.card {g : G // g • x = y} =
      Fintype.card {g : G // g • x = z} := by
  classical
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G y z
  apply Fintype.card_congr
  exact
    { toFun := fun g => ⟨h * g.1, by rw [mul_smul, g.2, hh]⟩
      invFun := fun g => ⟨h⁻¹ * g.1, by
        rw [mul_smul, g.2, ← hh, inv_smul_smul]⟩
      left_inv := fun g => by ext; simp
      right_inv := fun g => by ext; simp }

theorem card_smul_mem (x : X) (S : Finset X) :
    (Finset.univ.filter (fun g : G => g • x ∈ S)).card * Fintype.card X =
      Fintype.card G * S.card := by
  classical
  let c := (Finset.univ.filter (fun g : G => g • x = x)).card
  have hc (y : X) :
      (Finset.univ.filter (fun g : G => g • x = y)).card = c := by
    simpa only [Fintype.card_subtype] using transporter_card_eq (G := G) x y x
  have hs := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset G) S (fun g => g • x)
  simp_rw [hc] at hs
  simp only [Finset.sum_const, smul_eq_mul] at hs
  have ht := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset G) (Finset.univ : Finset X) (fun g => g • x)
  simp_rw [hc] at ht
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ,
    Finset.mem_univ, Finset.filter_true] at ht
  rw [← hs, ← ht]
  ring

theorem smul_probability (x : X) (S : Finset X) :
    ((Finset.univ.filter (fun g : G => g • x ∈ S)).card : ℝ) /
        Fintype.card G = (S.card : ℝ) / Fintype.card X := by
  classical
  let : Nonempty X := ⟨x⟩
  have hG : (Fintype.card G : ℝ) ≠ 0 := by positivity
  have hX : (Fintype.card X : ℝ) ≠ 0 := by positivity
  apply (div_eq_div_iff hG hX).2
  exact_mod_cast (card_smul_mem (G := G) x S).trans (Nat.mul_comm _ _)

end Action

section Conditioning

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem conditional_density_le (A E : Finset Ω) (hA : A.Nonempty)
    (K : ℝ) (hsize : (Fintype.card Ω : ℝ) ≤ K * A.card) :
    ((A ∩ E).card : ℝ) / A.card ≤
      K * ((E.card : ℝ) / Fintype.card Ω) := by
  let : Nonempty Ω := ⟨hA.choose⟩
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hNp : (0 : ℝ) < Fintype.card Ω := by positivity
  have hi : ((A ∩ E).card : ℝ) ≤ E.card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : A ∩ E ⊆ E)
  have h1 := mul_le_mul_of_nonneg_right hi hNp.le
  have h2 := mul_le_mul_of_nonneg_left hsize (show (0 : ℝ) ≤ E.card by positivity)
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hAp hNp).2
  nlinarith

theorem conditional_density_le_two (A E : Finset Ω) (hA : A.Nonempty)
    (hsize : Fintype.card Ω ≤ 2 * A.card) :
    ((A ∩ E).card : ℝ) / A.card ≤
      2 * ((E.card : ℝ) / Fintype.card Ω) := by
  apply conditional_density_le A E hA 2
  exact_mod_cast hsize

end Conditioning

variable {G X : Type*} [Group G] [Fintype G] [Fintype X]
  [DecidableEq G] [DecidableEq X] [MulAction G X]
  [MulAction.IsPretransitive G X]

theorem restricted_smul_probability (x : X) (S : Finset X) (A : Finset G)
    (hA : A.Nonempty) (hsize : Fintype.card G ≤ 2 * A.card) :
    ((A.filter (fun g => g • x ∈ S)).card : ℝ) / A.card ≤
      2 * ((S.card : ℝ) / Fintype.card X) := by
  have h := conditional_density_le_two A
    (Finset.univ.filter (fun g : G => g • x ∈ S)) hA hsize
  simpa only [Finset.inter_filter, Finset.inter_univ, smul_probability] using h

open scoped Pointwise in

theorem restricted_inv_smul_probability (x : X) (S : Finset X) (A : Finset G)
    (hA : A.Nonempty) (hsize : Fintype.card G ≤ 2 * A.card) :
    ((A.filter (fun g => g⁻¹ • x ∈ S)).card : ℝ) / A.card ≤
      2 * ((S.card : ℝ) / Fintype.card X) := by
  have hAi : A⁻¹.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨a⁻¹, Finset.inv_mem_inv ha⟩
  have h := restricted_smul_probability x S A⁻¹ hAi (by simpa using hsize)
  have hc : (A⁻¹.filter (fun g => g • x ∈ S)).card =
      (A.filter (fun g => g⁻¹ • x ∈ S)).card := by
    rw [← Finset.card_inv (A.filter (fun g => g⁻¹ • x ∈ S))]
    congr 1
    ext g
    simp
  simpa only [hc, Finset.card_inv] using h

end Problem355.UniformAction

end OAI
