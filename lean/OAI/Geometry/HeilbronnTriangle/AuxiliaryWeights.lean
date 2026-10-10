import OAI.Geometry.HeilbronnTriangle.UniformAction
import OAI.Geometry.HeilbronnTriangle.AffineTripleOrbit
import OAI.Geometry.HeilbronnTriangle.IndependentTupleCard

namespace OAI

noncomputable section

namespace Problem355.AuxiliaryWeights

open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Families

variable {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq V]

theorem card_families_mem_le (Q : (ι → V) → Prop) (S : Finset V) :
    Fintype.card {p : {v : ι → V // Q v} // ∀ i, p.1 i ∈ S} ≤
      S.card ^ Fintype.card ι := by
  let f : {p : {v : ι → V // Q v} // ∀ i, p.1 i ∈ S} → (ι → S) :=
    fun p i => ⟨p.1.1 i, p.2 i⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hpq i)
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fun, Fintype.card_coe] using h

end Families

section Affine

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev AffineFamily (K V ι : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  {p : ι → V // AffineIndependent K p}

theorem affine_family_probability_le [Fintype V] [Fintype ι] [Nonempty ι]
    [DecidableEq V] [Fintype (V ≃ᵃ[K] V)]
    (p : AffineFamily K V ι) (S : Finset V) (A : Finset (V ≃ᵃ[K] V))
    (hA : A.Nonempty) (hsize : Fintype.card (V ≃ᵃ[K] V) ≤ 2 * A.card) :
    ((A.filter (fun e => ∀ i, e (p.1 i) ∈ S)).card : ℝ) / A.card ≤
      2 * ((S.card : ℝ) ^ Fintype.card ι /
        Nat.card (AffineFamily K V ι)) := by
  classical
  let T : Finset (AffineFamily K V ι) :=
    Finset.univ.filter (fun q => ∀ i, q.1 i ∈ S)
  have h := UniformAction.restricted_smul_probability p T A hA hsize
  have hT : T.card ≤ S.card ^ Fintype.card ι := by
    simpa only [T, Fintype.card_subtype] using
      card_families_mem_le (ι := ι) (AffineIndependent K) S
  have hTr : (T.card : ℝ) ≤ (S.card : ℝ) ^ Fintype.card ι := by
    exact_mod_cast hT
  calc
    ((A.filter (fun e => ∀ i, e (p.1 i) ∈ S)).card : ℝ) / A.card ≤
        2 * ((T.card : ℝ) / Fintype.card (AffineFamily K V ι)) := by
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and,
        AffineTripleOrbit.affineTuple_smul_apply] using h
    _ ≤ 2 * ((S.card : ℝ) ^ Fintype.card ι /
        Nat.card (AffineFamily K V ι)) := by
      rw [Nat.card_eq_fintype_card]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hTr (by positivity)) (by norm_num)

end Affine

section AffineInverse

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem affine_family_inverse_probability_le [Fintype V] [Fintype ι] [Nonempty ι]
    [DecidableEq V] [Fintype (V ≃ᵃ[K] V)]
    (p : AffineFamily K V ι) (S : Finset V) (A : Finset (V ≃ᵃ[K] V))
    (hA : A.Nonempty) (hsize : Fintype.card (V ≃ᵃ[K] V) ≤ 2 * A.card) :
    ((A.filter (fun e => ∀ i, e.symm (p.1 i) ∈ S)).card : ℝ) / A.card ≤
      2 * ((S.card : ℝ) ^ Fintype.card ι /
        Nat.card (AffineFamily K V ι)) := by
  classical
  let T : Finset (AffineFamily K V ι) :=
    Finset.univ.filter (fun q => ∀ i, q.1 i ∈ S)
  have h := UniformAction.restricted_inv_smul_probability p T A hA hsize
  have hT : T.card ≤ S.card ^ Fintype.card ι := by
    simpa only [T, Fintype.card_subtype] using
      card_families_mem_le (ι := ι) (AffineIndependent K) S
  have hTr : (T.card : ℝ) ≤ (S.card : ℝ) ^ Fintype.card ι := by
    exact_mod_cast hT
  calc
    _ ≤ 2 * ((T.card : ℝ) / Fintype.card (AffineFamily K V ι)) := by
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and,
        AffineTripleOrbit.affineTuple_smul_apply, AffineEquiv.inv_def] using h
    _ ≤ _ := by
      rw [Nat.card_eq_fintype_card]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hTr (by positivity)) (by norm_num)

end AffineInverse

section Linear

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev LinearFamily (K V ι : Type*) [Field K] [AddCommGroup V] [Module K V] :=
  {p : ι → V // LinearIndependent K p}

theorem linear_family_probability_le [Fintype V] [Fintype ι]
    [DecidableEq V] [Fintype (V ≃ₗ[K] V)]
    (p : LinearFamily K V ι) (S : Finset V) :
    ((Finset.univ.filter (fun e : V ≃ₗ[K] V => ∀ i, e (p.1 i) ∈ S)).card : ℝ) /
        Fintype.card (V ≃ₗ[K] V) ≤
      (S.card : ℝ) ^ Fintype.card ι / Nat.card (LinearFamily K V ι) := by
  classical
  let T : Finset (LinearFamily K V ι) :=
    Finset.univ.filter (fun q => ∀ i, q.1 i ∈ S)
  have h := UniformAction.smul_probability (G := V ≃ₗ[K] V) p T
  have hT : T.card ≤ S.card ^ Fintype.card ι := by
    simpa only [T, Fintype.card_subtype] using
      card_families_mem_le (ι := ι) (fun p : ι → V => LinearIndependent K p) S
  have hTr : (T.card : ℝ) ≤ (S.card : ℝ) ^ Fintype.card ι := by
    exact_mod_cast hT
  calc
    _ = (T.card : ℝ) / Fintype.card (LinearFamily K V ι) := by
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and,
        AffineTripleOrbit.linearTuple_smul_apply] using h
    _ ≤ _ := by
      rw [Nat.card_eq_fintype_card]
      exact div_le_div_of_nonneg_right hTr (by positivity)

open scoped Pointwise in
theorem linear_family_inverse_probability_le [Fintype V] [Fintype ι]
    [DecidableEq V] [Fintype (V ≃ₗ[K] V)]
    (p : LinearFamily K V ι) (S : Finset V) :
    ((Finset.univ.filter (fun e : V ≃ₗ[K] V => ∀ i, e.symm (p.1 i) ∈ S)).card : ℝ) /
        Fintype.card (V ≃ₗ[K] V) ≤
      (S.card : ℝ) ^ Fintype.card ι / Nat.card (LinearFamily K V ι) := by
  classical
  have hc :
      (Finset.univ.filter (fun e : V ≃ₗ[K] V => ∀ i, e.symm (p.1 i) ∈ S)).card =
      (Finset.univ.filter (fun e : V ≃ₗ[K] V => ∀ i, e (p.1 i) ∈ S)).card := by
    rw [← Finset.card_inv
      (Finset.univ.filter (fun e : V ≃ₗ[K] V => ∀ i, e (p.1 i) ∈ S))]
    congr 1
    ext e
    simp
  rw [hc]
  exact linear_family_probability_le p S

end Linear

section Normalization

theorem cubic_space_denominators {q : ℝ} (hq : 2 ≤ q) :
    0 < q ^ 3 - 1 ∧ 0 < q ^ 3 - q ∧
      q ^ 3 ≤ 2 * (q ^ 3 - 1) ∧
      (q ^ 3) ^ 2 ≤ 4 * ((q ^ 3 - 1) * (q ^ 3 - q)) ∧
      (q ^ 3) ^ 3 ≤ 4 * (q ^ 3 * ((q ^ 3 - 1) * (q ^ 3 - q))) := by
  have hq0 : 0 ≤ q := by linarith
  have hsq : 4 ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 2)]
  have hcub : 4 * q ≤ q ^ 3 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hsq)]
  have hQ : 0 ≤ q ^ 3 := by positivity
  have h1 : q ^ 3 ≤ 2 * (q ^ 3 - 1) := by nlinarith
  have h2 : q ^ 3 ≤ 2 * (q ^ 3 - q) := by nlinarith
  have hp : (q ^ 3) ^ 2 ≤ 4 * ((q ^ 3 - 1) * (q ^ 3 - q)) := by
    have h := mul_le_mul h1 h2 hQ (by nlinarith : 0 ≤ 2 * (q ^ 3 - 1))
    nlinarith
  refine ⟨by nlinarith, by nlinarith, h1, hp, ?_⟩
  have h := mul_le_mul_of_nonneg_left hp hQ
  nlinarith

theorem affine_weight_le {Q s D p C : ℝ}
    (hQ : 0 ≤ Q) (hs : 0 < s) (hD : 0 < D)
    (hp : p ≤ 2 * s ^ 3 / D) (hden : Q ^ 3 ≤ C * D) :
    (Q / s) ^ 3 * p ≤ 2 * C := by
  calc
    (Q / s) ^ 3 * p ≤ (Q / s) ^ 3 * (2 * s ^ 3 / D) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 2 * Q ^ 3 / D := by field_simp
    _ ≤ 2 * C := by
      apply (div_le_iff₀ hD).2
      nlinarith

theorem pair_weight_le {Q s D p C : ℝ}
    (hQ : 0 ≤ Q) (hs : 0 < s) (hD : 0 < D)
    (hp : p ≤ s ^ 2 / D) (hden : Q ^ 2 ≤ C * D) :
    (Q / s) ^ 3 * p ≤ C * (Q / s) := by
  calc
    (Q / s) ^ 3 * p ≤ (Q / s) ^ 3 * (s ^ 2 / D) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (Q / s) * (Q ^ 2 / D) := by field_simp
    _ ≤ (Q / s) * C := mul_le_mul_of_nonneg_left
      ((div_le_iff₀ hD).2 hden) (by positivity)
    _ = C * (Q / s) := mul_comm _ _

theorem singleton_weight_le {Q s D p C : ℝ}
    (hQ : 0 ≤ Q) (hs : 0 < s) (hD : 0 < D)
    (hp : p ≤ s / D) (hden : Q ≤ C * D) :
    (Q / s) ^ 3 * p ≤ C * (Q / s) ^ 2 := by
  calc
    (Q / s) ^ 3 * p ≤ (Q / s) ^ 3 * (s / D) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (Q / s) ^ 2 * (Q / D) := by field_simp
    _ ≤ (Q / s) ^ 2 * C := mul_le_mul_of_nonneg_left
      ((div_le_iff₀ hD).2 hden) (by positivity)
    _ = C * (Q / s) ^ 2 := mul_comm _ _

theorem affine_weight_le_eight {q s p : ℝ} (hq : 2 ≤ q) (hs : 0 < s)
    (hp : p ≤ 2 * s ^ 3 /
      (q ^ 3 * ((q ^ 3 - 1) * (q ^ 3 - q)))) :
    (q ^ 3 / s) ^ 3 * p ≤ 8 := by
  obtain ⟨h1, h2, -, -, hden⟩ := cubic_space_denominators hq
  have hq0 : 0 < q := by linarith
  convert (affine_weight_le (by positivity) hs (by positivity) hp hden) using 1 ; norm_num

theorem pair_weight_le_four {q s p : ℝ} (hq : 2 ≤ q) (hs : 0 < s)
    (hp : p ≤ s ^ 2 / ((q ^ 3 - 1) * (q ^ 3 - q))) :
    (q ^ 3 / s) ^ 3 * p ≤ 4 * (q ^ 3 / s) := by
  obtain ⟨h1, h2, -, hden, -⟩ := cubic_space_denominators hq
  have hq0 : 0 < q := by linarith
  exact pair_weight_le (by positivity) hs (by positivity) hp hden

theorem singleton_weight_le_two {q s p : ℝ} (hq : 2 ≤ q) (hs : 0 < s)
    (hp : p ≤ s / (q ^ 3 - 1)) :
    (q ^ 3 / s) ^ 3 * p ≤ 2 * (q ^ 3 / s) ^ 2 := by
  obtain ⟨h1, -, hden, -, -⟩ := cubic_space_denominators hq
  have hq0 : 0 < q := by linarith
  exact singleton_weight_le (by positivity) hs h1 hp hden

end Normalization

section FiniteFieldWeights

variable {K : Type*} [Field K] [Fintype K]

theorem affine_triple_weight_le_eight
    [Fintype ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K))]
    (p : AffineFamily K (Fin 3 → K) (Fin 3))
    (S : Finset (Fin 3 → K)) (hS : S.Nonempty)
    (A : Finset ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)))
    (hA : A.Nonempty)
    (hsize : Fintype.card ((Fin 3 → K) ≃ᵃ[K] (Fin 3 → K)) ≤ 2 * A.card) :
    ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
      (((A.filter (fun e => ∀ i, e.symm (p.1 i) ∈ S)).card : ℝ) / A.card) ≤ 8 := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hqpow : Fintype.card K ≤ Fintype.card K ^ 3 :=
    Nat.le_self_pow (by decide) _
  have h1 : 1 ≤ Fintype.card K ^ 3 := by omega
  have hp := affine_family_inverse_probability_le p S A hA hsize
  have hcard :
      (Nat.card (AffineFamily K (Fin 3 → K) (Fin 3)) : ℝ) =
        (Fintype.card K : ℝ) ^ 3 *
          (((Fintype.card K : ℝ) ^ 3 - 1) *
            ((Fintype.card K : ℝ) ^ 3 - Fintype.card K)) := by
    change (Nat.card {p : Fin 3 → (Fin 3 → K) // AffineIndependent K p} : ℝ) = _
    rw [IndependentTupleCard.card_affineIndependent_triples K]
    simp only [Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub hqpow,
      Nat.cast_pow, Nat.cast_one, mul_assoc]
  simp only [Fintype.card_fin, hcard] at hp
  apply affine_weight_le_eight (by exact_mod_cast hq)
    (by exact_mod_cast hS.card_pos)
  convert hp using 1 <;> try ring_nf
  rw [mul_comm]
  congr 2
  congr 1
  ext e
  simp

theorem linear_pair_weight_le_four
    [Fintype ((Fin 3 → K) ≃ₗ[K] (Fin 3 → K))]
    (p : LinearFamily K (Fin 3 → K) (Fin 2))
    (S : Finset (Fin 3 → K)) (hS : S.Nonempty) :
    ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
      (((Finset.univ.filter (fun e : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) =>
        ∀ i, e.symm (p.1 i) ∈ S)).card : ℝ) /
          Fintype.card ((Fin 3 → K) ≃ₗ[K] (Fin 3 → K))) ≤
      4 * ((Fintype.card K : ℝ) ^ 3 / S.card) := by
  classical
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hqpow : Fintype.card K ≤ Fintype.card K ^ 3 :=
    Nat.le_self_pow (by decide) _
  have h1 : 1 ≤ Fintype.card K ^ 3 := by omega
  have hp := linear_family_inverse_probability_le p S
  have hcard :
      (Nat.card (LinearFamily K (Fin 3 → K) (Fin 2)) : ℝ) =
        ((Fintype.card K : ℝ) ^ 3 - 1) *
          ((Fintype.card K : ℝ) ^ 3 - Fintype.card K) := by
    change (Nat.card {p : Fin 2 → (Fin 3 → K) // LinearIndependent K p} : ℝ) = _
    rw [IndependentTupleCard.card_independent_pairs K]
    simp only [Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub hqpow,
      Nat.cast_pow, Nat.cast_one]
  simp only [Fintype.card_fin, hcard] at hp
  apply pair_weight_le_four (by exact_mod_cast hq)
    (by exact_mod_cast hS.card_pos)
  convert hp using 1 ; try ring_nf
  rw [mul_comm]
  congr 2
  congr 1
  ext e
  simp

theorem nonzero_vector_weight_le_two
    [Fintype ((Fin 3 → K) ≃ₗ[K] (Fin 3 → K))]
    (x : Fin 3 → K) (hx : x ≠ 0)
    (S : Finset (Fin 3 → K)) (hS : S.Nonempty) :
    ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 3 *
      (((Finset.univ.filter (fun e : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) =>
        e.symm x ∈ S)).card : ℝ) /
          Fintype.card ((Fin 3 → K) ≃ₗ[K] (Fin 3 → K))) ≤
      2 * ((Fintype.card K : ℝ) ^ 3 / S.card) ^ 2 := by
  classical
  let p : LinearFamily K (Fin 3 → K) (Fin 1) :=
    ⟨fun _ => x, linearIndependent_unique_iff.mpr hx⟩
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have h1 : 1 ≤ Fintype.card K ^ 3 :=
    Nat.one_le_pow _ _ Fintype.card_pos
  have hp := linear_family_inverse_probability_le p S
  have hcard :
      (Nat.card (LinearFamily K (Fin 3 → K) (Fin 1)) : ℝ) =
        (Fintype.card K : ℝ) ^ 3 - 1 := by
    change (Nat.card {p : Fin 1 → (Fin 3 → K) // LinearIndependent K p} : ℝ) = _
    rw [card_linearIndependent (by simp)]
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      Fin.prod_univ_one, Fin.val_zero, pow_zero, Nat.cast_sub h1,
      Nat.cast_pow, Nat.cast_one]
  simp only [Fintype.card_fin, hcard, pow_one] at hp
  apply singleton_weight_le_two (by exact_mod_cast hq)
    (by exact_mod_cast hS.card_pos)
  convert hp using 1 ; try ring_nf
  rw [mul_comm]
  congr 2
  congr 1
  ext e
  simp [p]

end FiniteFieldWeights

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype V] [DecidableEq V] [Fintype (V ≃ᵃ[K] V)]

def affineMapsWithInputShift (A : Finset V) : Finset (V ≃ᵃ[K] V) :=
  Finset.univ.filter (fun e => (AffineTripleOrbit.inputShiftEquiv e).2 ∈ A)

theorem affineMapsWithInputShift_halfDensity (A : Finset V)
    (hA : Fintype.card V ≤ 2 * A.card) :
    Fintype.card (V ≃ᵃ[K] V) ≤ 2 * (affineMapsWithInputShift (K := K) A).card := by
  classical
  have h := AffineTripleOrbit.card_affineEquiv_le_two_restricted (F := K)
    (A : Set V) (by simpa [Nat.card_eq_fintype_card] using hA)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.mem_coe, affineMapsWithInputShift] using h

theorem affineMapsWithInputShift_nonempty (A : Finset V)
    (hA : Fintype.card V ≤ 2 * A.card) :
    (affineMapsWithInputShift (K := K) A).Nonempty := by
  have h := affineMapsWithInputShift_halfDensity (K := K) A hA
  have hp : 0 < Fintype.card (V ≃ᵃ[K] V) := Fintype.card_pos
  apply Finset.card_pos.mp
  omega

theorem allowed_shift_affine_weight_le_eight
    {F : Type*} [Field F] [Fintype F]
    [Fintype ((Fin 3 → F) ≃ᵃ[F] (Fin 3 → F))]
    (p : AffineFamily F (Fin 3 → F) (Fin 3))
    (S : Finset (Fin 3 → F)) (hS : S.Nonempty)
    (A : Finset (Fin 3 → F))
    (hA : Fintype.card F ^ 3 ≤ 2 * A.card) :
    ((Fintype.card F : ℝ) ^ 3 / S.card) ^ 3 *
      ((((affineMapsWithInputShift (K := F) A).filter
        (fun e => ∀ i, e.symm (p.1 i) ∈ S)).card : ℝ) /
          (affineMapsWithInputShift (K := F) A).card) ≤ 8 := by
  have hA' : Fintype.card (Fin 3 → F) ≤ 2 * A.card := by simpa using hA
  exact affine_triple_weight_le_eight p S hS (affineMapsWithInputShift A)
    (affineMapsWithInputShift_nonempty A hA')
    (affineMapsWithInputShift_halfDensity A hA')

end Problem355.AuxiliaryWeights

end

end OAI
