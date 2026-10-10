import OAI.Geometry.HeilbronnTriangle.AuxiliaryWeights

namespace OAI

noncomputable section

namespace Problem355.AuxiliaryWeights

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem sum_uniform_indicator {Ω : Type*} (A : Finset Ω) (P : Ω → Prop) :
    (∑ a : A, (A.card : ℝ)⁻¹ * (if P a.1 then 1 else 0)) =
      ((A.filter P).card : ℝ) / A.card := by
  classical
  rw [Finset.sum_coe_sort A (fun a : Ω => (A.card : ℝ)⁻¹ * (if P a then 1 else 0)),
    ← Finset.mul_sum, Finset.sum_boole]
  ring

theorem affine_pair_normalization {Q s p : ℝ} (hQ : 2 ≤ Q) (hs : 0 < s)
    (hp : p ≤ 2 * s ^ 2 / (Q * (Q - 1))) :
    (Q / s) ^ 3 * p ≤ 4 * (Q / s) := by
  have hQ0 : 0 < Q := by linarith
  have hD : 0 < Q * (Q - 1) := mul_pos hQ0 (by linarith)
  have hp' : p / 2 ≤ s ^ 2 / (Q * (Q - 1)) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    calc
      p ≤ 2 * s ^ 2 / (Q * (Q - 1)) := hp
      _ = (s ^ 2 / (Q * (Q - 1))) * 2 := by ring
  have hd : Q ^ 2 ≤ 2 * (Q * (Q - 1)) := by nlinarith
  have h := pair_weight_le hQ0.le hs hD hp' hd
  nlinarith

theorem affine_singleton_normalization {Q s p : ℝ} (hQ : 0 < Q) (hs : 0 < s)
    (hp : p ≤ 2 * s / Q) :
    (Q / s) ^ 3 * p ≤ 2 * (Q / s) ^ 2 := by
  calc
    (Q / s) ^ 3 * p ≤ (Q / s) ^ 3 * (2 * s / Q) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 2 * (Q / s) ^ 2 := by field_simp

section FiniteField

variable {K : Type*} [Field K] [Fintype K]
  [finiteEquivalences : Fintype ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))]

theorem affine_pair_weight_le_four
    (p : AffineFamily K (Fin 3 → K) (Fin 2))
    (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)))
    (hA : A.Nonempty)
    (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card) :
    ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
      (((A.filter (fun e => ∀ i, e.symm (p.1 i) ∈ S)).card : ℝ) / A.card) ≤
      4 * ((Fintype.card K : ℝ) ^ 3 / S.card) := by
  classical
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hqpow : Fintype.card K ≤ Fintype.card K ^ 3 :=
    Nat.le_self_pow (by decide) _
  have h1 : 1 ≤ Fintype.card K ^ 3 := by omega
  have hp := affine_family_inverse_probability_le p S A hA hsize
  have hc : Nat.card (AffineFamily K (Fin 3 → K) (Fin 2)) =
      Fintype.card K ^ 3 * (Fintype.card K ^ 3 - 1) := by
    change Nat.card {p : Fin (1 + 1) → (Fin 3 → K) // AffineIndependent K p} = _
    rw [IndependentTupleCard.card_affineIndependent K (Fin 3 → K) (by simp)]
    simp [Nat.card_eq_fintype_card]
  simp only [Fintype.card_fin, hc, Nat.cast_mul, Nat.cast_sub h1,
    Nat.cast_pow, Nat.cast_one] at hp
  apply affine_pair_normalization
    (by exact_mod_cast (show 2 ≤ Fintype.card K ^ 3 by omega))
    (by exact_mod_cast hS.card_pos)
  convert hp using 1 <;> try ring_nf
  rw [mul_comm]
  congr 2
  congr 1
  ext e
  simp

theorem affine_singleton_weight_le_two
    (x : Fin 3 → K) (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)))
    (hA : A.Nonempty)
    (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card) :
    ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
      (((A.filter (fun e => e.symm x ∈ S)).card : ℝ) / A.card) ≤
      2 * ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 2 := by
  classical
  let p : AffineFamily K (Fin 3 → K) (Fin 1) :=
    ⟨fun _ => x, affineIndependent_of_subsingleton K _⟩
  have hp := affine_family_inverse_probability_le p S A hA hsize
  have hc : Nat.card (AffineFamily K (Fin 3 → K) (Fin 1)) = Fintype.card K ^ 3 := by
    change Nat.card {p : Fin (0 + 1) → (Fin 3 → K) // AffineIndependent K p} = _
    rw [IndependentTupleCard.card_affineIndependent K (Fin 3 → K) (by simp)]
    simp [Nat.card_eq_fintype_card]
  simp only [Fintype.card_fin, hc, Nat.cast_pow, pow_one] at hp
  apply affine_singleton_normalization (by positivity) (by exact_mod_cast hS.card_pos)
  convert hp using 1 <;> try ring_nf
  rw [mul_comm]
  congr 2
  congr 1
  ext e
  simp [p]

end FiniteField

variable {K : Type*} [Field K] [Fintype K]
  [finiteEquivalences : Fintype ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))]

def affineInclusionWeight
    (S : Finset (Fin 3 → K))
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)))
    (p : Fin 3 → (Fin 3 → K)) : ℝ :=
  ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
    (((A.filter (fun e => ∀ i, e.symm (p i) ∈ S)).card : ℝ) / A.card)

theorem affineInclusionWeight_nonneg {K : Type*} [Field K] [Fintype K]
    [Fintype ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))]
    (S : Finset (Fin 3 → K))
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)))
    (p : Fin 3 → (Fin 3 → K)) : 0 ≤ affineInclusionWeight S A p := by
  unfold affineInclusionWeight
  positivity

theorem affineInclusionWeight_eq_uniform_sum {K : Type*} [Field K] [Fintype K]
    [Fintype ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))]
    (S : Finset (Fin 3 → K))
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)))
    (p : Fin 3 → (Fin 3 → K)) :
    affineInclusionWeight S A p =
      ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
        (∑ e : A, (A.card : ℝ)⁻¹ *
          (if ∀ i, p i ∈ S.image (fun x => e.1 x) then 1 else 0)) := by
  classical
  have he (e : (Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) :
      (∀ i, p i ∈ S.image e) ↔ (∀ i, e.symm (p i) ∈ S) := by
    constructor
    · intro h i
      obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp (h i)
      simpa only [← hxe, e.symm_apply_apply] using hx
    · intro h i
      exact Finset.mem_image.mpr ⟨e.symm (p i), h i, e.apply_symm_apply (p i)⟩
  have hf : A.filter (fun e : (Fin 3 → K) ≃ᵃ[K] (Fin 3 → K) =>
      ∀ i, p i ∈ S.image (fun x => e x)) =
      A.filter (fun e => ∀ i, e.symm (p i) ∈ S) := by
    ext e
    simp only [Finset.mem_filter, he]
  simp_rw [he]
  unfold affineInclusionWeight
  congr 1
  convert (sum_uniform_indicator A
    (fun e : (Fin 3 → K) ≃ᵃ[K] (Fin 3 → K) =>
      ∀ i, e.symm (p i) ∈ S)).symm using 4 ; try simp
  ext e
  simp

theorem affineInclusionWeight_le_eight
    (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))) (hA : A.Nonempty)
    (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card)
    (p : Fin 3 → (Fin 3 → K)) (hp : AffineIndependent K p) :
    affineInclusionWeight S A p ≤ 8 := by
  exact affine_triple_weight_le_eight ⟨p, hp⟩ S hS A hA hsize

theorem affineInclusionWeight_le_four_of_ne
    (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))) (hA : A.Nonempty)
    (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card)
    (p : Fin 3 → (Fin 3 → K)) (i j : Fin 3) (hp : p i ≠ p j) :
    affineInclusionWeight S A p ≤ 4 * ((Fintype.card K : ℝ) ^ 3 / S.card) := by
  classical
  let t : AffineFamily K (Fin 3 → K) (Fin 2) :=
    ⟨![p i, p j], affineIndependent_of_ne K hp⟩
  have hsub : A.filter (fun e => ∀ k, e.symm (p k) ∈ S) ⊆
      A.filter (fun e => ∀ k, e.symm (t.1 k) ∈ S) := by
    intro e he
    obtain ⟨hea, he⟩ := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    refine ⟨hea, ?_⟩
    simpa only [Fin.forall_fin_two, t, Matrix.cons_val_zero,
      Matrix.cons_val_one] using And.intro (he i) (he j)
  have hc : ((A.filter (fun e => ∀ k, e.symm (p k) ∈ S)).card : ℝ) ≤
      (A.filter (fun e => ∀ k, e.symm (t.1 k) ∈ S)).card := by
    exact_mod_cast Finset.card_le_card hsub
  calc
    affineInclusionWeight S A p ≤
        ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
          (((A.filter (fun e => ∀ k, e.symm (t.1 k) ∈ S)).card : ℝ) / A.card) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hc (by positivity)) (by positivity)
    _ ≤ _ := affine_pair_weight_le_four t S hS A hA hsize

theorem affineInclusionWeight_le_two
    (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))) (hA : A.Nonempty)
    (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card)
    (p : Fin 3 → (Fin 3 → K)) :
    affineInclusionWeight S A p ≤ 2 * ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 2 := by
  classical
  have hsub : A.filter (fun e => ∀ k, e.symm (p k) ∈ S) ⊆
      A.filter (fun e => e.symm (p 0) ∈ S) := by
    intro e he
    obtain ⟨hea, he⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨hea, he 0⟩
  have hc : ((A.filter (fun e => ∀ k, e.symm (p k) ∈ S)).card : ℝ) ≤
      (A.filter (fun e => e.symm (p 0) ∈ S)).card := by
    exact_mod_cast Finset.card_le_card hsub
  calc
    affineInclusionWeight S A p ≤
        ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
          (((A.filter (fun e => e.symm (p 0) ∈ S)).card : ℝ) / A.card) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hc (by positivity)) (by positivity)
    _ ≤ _ := affine_singleton_weight_le_two (p 0) S hS A hA hsize

end Problem355.AuxiliaryWeights

end

end OAI
