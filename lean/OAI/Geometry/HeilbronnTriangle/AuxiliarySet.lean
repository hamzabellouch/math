import OAI.Geometry.HeilbronnTriangle.AuxiliaryCap
import OAI.Geometry.HeilbronnTriangle.ShortRelations
import OAI.Geometry.HeilbronnTriangle.AllowedShifts
import OAI.Geometry.HeilbronnTriangle.CapInBox

namespace OAI


namespace Problem355.AuxiliarySet

open scoped BigOperators

variable {F : Type*} [Field F]

theorem affineIndependent_of_mem_cap
    {S : Set (Fin 3 → F)} (hS : AuxiliaryCap.IsCap S)
    {p : Fin 3 → (Fin 3 → F)} (hp : ∀ i, p i ∈ S)
    (hinj : Function.Injective p) : AffineIndependent F p := by
  have hcol := hS (p 0) (hp 0) (p 1) (hp 1) (p 2) (hp 2)
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
  have h := affineIndependent_iff_not_collinear_set.mpr hcol
  convert h using 1
  funext i
  fin_cases i <;> rfl

noncomputable def transformed (S : Finset (Fin 3 → F)) (a : Fin 3 → F)
    (G : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) : Finset (Fin 3 → F) := by
  classical
  exact S.image (fun v => G (a + v))

@[simp] theorem mem_transformed (S : Finset (Fin 3 → F)) (a : Fin 3 → F)
    (G : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) (u : Fin 3 → F) :
    u ∈ transformed S a G ↔ ∃ v ∈ S, G (a + v) = u := by
  classical
  simp [transformed]

@[simp] theorem card_transformed (S : Finset (Fin 3 → F)) (a : Fin 3 → F)
    (G : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) :
    (transformed S a G).card = S.card := by
  classical
  apply Finset.card_image_iff.mpr
  intro v hv w hw heq
  exact add_left_cancel (G.injective heq)

theorem isCap_transformed {S : Finset (Fin 3 → F)}
    (hS : AuxiliaryCap.IsCap (S : Set (Fin 3 → F)))
    (a : Fin 3 → F) (G : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) :
    AuxiliaryCap.IsCap (transformed S a G : Set (Fin 3 → F)) := by
  have h := (hS.translate a).image G.toAffineEquiv.toAffineMap G.injective
  convert h using 1
  ext v
  simp only [Finset.mem_coe, mem_transformed, Set.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨a + w, ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩

theorem zero_not_mem_transformed {S : Finset (Fin 3 → F)} {a : Fin 3 → F}
    (ha : ∀ v ∈ S, a + v ≠ 0)
    (G : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) :
    (0 : Fin 3 → F) ∉ transformed S a G := by
  rintro h
  obtain ⟨v, hv, hzero⟩ := (mem_transformed S a G 0).mp h
  exact ha v hv (G.map_eq_zero_iff.mp hzero)

theorem short_sum_zero_relation_excluded
    {q H : ℕ} [Fact q.Prime]
    {S : Finset (Fin 3 → ZMod q)}
    (hS : AuxiliaryCap.IsCap (S : Set (Fin 3 → ZMod q)))
    (a : Fin 3 → ZMod q)
    (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q))
    {p : Fin 3 → (Fin 3 → ZMod q)}
    (hp : ∀ i, p i ∈ transformed S a G) (hinj : Function.Injective p)
    {x : Fin 3 → ℤ} (hsum : ∑ i, x i = 0)
    (hshort : ∀ i, |x i| ≤ (H : ℤ)) (hHq : H < q) (hne : x ≠ 0) :
    (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
  exact ShortRelations.sum_smul_ne_zero_of_bounded_coefficients
    (affineIndependent_of_mem_cap (isCap_transformed hS a G) hp hinj)
    hsum hshort hHq hne

theorem short_nonzero_sum_relation_excluded
    {q H w : ℕ} [Fact q.Prime]
    {S : Finset (Fin 3 → ZMod q)}
    (hbox : ∀ v ∈ S, (v 0).val < w)
    (a : Fin 3 → ZMod q)
    (ha : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a 0 ∉ Auxiliary.integerWindow q (3 * H * w))
    (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q))
    {p : Fin 3 → (Fin 3 → ZMod q)}
    (hp : ∀ i, p i ∈ transformed S a G)
    {x : Fin 3 → ℤ} (hsum : ∑ i, x i ≠ 0)
    (hshort : ∀ i, |x i| ≤ (H : ℤ)) :
    (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
  classical
  choose v hv heq using fun i => (mem_transformed S a G (p i)).mp (hp i)
  let z : Fin 3 → Fin 3 → ℤ := fun i j => (v i j).val
  have hz : ∀ i, (fun j => (z i j : ZMod q)) = v i := by
    intro i
    funext j
    simp [z]
  have hb : ∀ i, 0 ≤ z i 0 ∧ z i 0 ≤ (w : ℤ) := by
    intro i
    constructor
    · exact Int.natCast_nonneg _
    · dsimp [z]
      exact_mod_cast (hbox (v i) (hv i)).le
  have h := Auxiliary.shifted_vector_short_relation_ne_zero q H w a ha x z
    hshort hb hsum G
  simpa only [hz, heq] using h

theorem zero_not_mem_of_allowed
    {q H w : ℕ} [Fact q.Prime] (hH : 1 ≤ H)
    {S : Finset (Fin 3 → ZMod q)}
    (hbox : ∀ v ∈ S, (v 0).val < w)
    (a : Fin 3 → ZMod q)
    (ha : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a 0 ∉ Auxiliary.integerWindow q (3 * H * w))
    (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q)) :
    (0 : Fin 3 → ZMod q) ∉ transformed S a G := by
  intro hzero
  have h := short_nonzero_sum_relation_excluded hbox a ha G
    (p := fun _ => 0) (fun _ => hzero) (x := ![1, 0, 0])
    (by norm_num [Fin.sum_univ_succ])
    (by
      intro i
      fin_cases i
      · simpa using (show (1 : ℤ) ≤ H by exact_mod_cast hH)
      · simp
      · simp)
  exact h (by simp)

theorem short_relation_excluded
    {q H w : ℕ} [Fact q.Prime]
    {S : Finset (Fin 3 → ZMod q)}
    (hS : AuxiliaryCap.IsCap (S : Set (Fin 3 → ZMod q)))
    (hbox : ∀ v ∈ S, (v 0).val < w)
    (a : Fin 3 → ZMod q)
    (ha : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a 0 ∉ Auxiliary.integerWindow q (3 * H * w))
    (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q))
    {p : Fin 3 → (Fin 3 → ZMod q)}
    (hp : ∀ i, p i ∈ transformed S a G) (hinj : Function.Injective p)
    {x : Fin 3 → ℤ} (hshort : ∀ i, |x i| ≤ (H : ℤ))
    (hHq : H < q) (hne : x ≠ 0) :
    (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
  by_cases hsum : ∑ i, x i = 0
  · exact short_sum_zero_relation_excluded hS a G hp hinj hsum hshort hHq hne
  · exact short_nonzero_sum_relation_excluded hbox a ha G hp hsum hshort

theorem transformed_properties
    {q H w : ℕ} [Fact q.Prime] (hH : 1 ≤ H) (hHq : H < q)
    {S : Finset (Fin 3 → ZMod q)}
    (hS : AuxiliaryCap.IsCap (S : Set (Fin 3 → ZMod q)))
    (hbox : ∀ v ∈ S, (v 0).val < w)
    (a : Fin 3 → ZMod q)
    (ha : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a 0 ∉ Auxiliary.integerWindow q (3 * H * w))
    (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q)) :
    (transformed S a G).card = S.card ∧
      (0 : Fin 3 → ZMod q) ∉ transformed S a G ∧
      AuxiliaryCap.IsCap (transformed S a G : Set (Fin 3 → ZMod q)) ∧
      ∀ p : Fin 3 → (Fin 3 → ZMod q),
        (∀ i, p i ∈ transformed S a G) → Function.Injective p →
        ∀ x : Fin 3 → ℤ, (∀ i, |x i| ≤ (H : ℤ)) → x ≠ 0 →
          (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
  refine ⟨card_transformed S a G, zero_not_mem_of_allowed hH hbox a ha G,
    isCap_transformed hS a G, ?_⟩
  intro p hp hinj x hx hne
  exact short_relation_excluded hS hbox a ha G hp hinj hx hHq hne

theorem exists_set_excluding_short_relations
    {q H w : ℕ} [Fact q.Prime] (hH : 1 ≤ H)
    (hq : 2000 * H ^ 2 ≤ q) (hw : 1000 * H ^ 2 * w ≤ q)
    {S : Finset (Fin 3 → ZMod q)}
    (hS : AuxiliaryCap.IsCap (S : Set (Fin 3 → ZMod q)))
    (hbox : ∀ v ∈ S, (v 0).val < w) :
    ∃ V : Finset (Fin 3 → ZMod q), V.card = S.card ∧
      (0 : Fin 3 → ZMod q) ∉ V ∧
      AuxiliaryCap.IsCap (V : Set (Fin 3 → ZMod q)) ∧
      ∀ p : Fin 3 → (Fin 3 → ZMod q),
        (∀ i, p i ∈ V) → Function.Injective p →
        ∀ x : Fin 3 → ℤ, (∀ i, |x i| ≤ (H : ℤ)) → x ≠ 0 →
          (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
  obtain ⟨a₀, ha₀⟩ := Auxiliary.exists_auxiliary_allowed_shift q H w hH hq hw
  let a : Fin 3 → ZMod q := ![a₀, 0, 0]
  let G := LinearEquiv.refl (ZMod q) (Fin 3 → ZMod q)
  refine ⟨transformed S a G, transformed_properties hH ?_ hS hbox a ?_ G⟩
  · have h := Auxiliary.auxiliary_multiplier_range q H hH hq
    omega
  · simpa only [a, Matrix.cons_val_zero] using ha₀

theorem le_twice_mul_div {q d : ℕ} (hd : 0 < d) (hdq : d ≤ q) :
    q ≤ 2 * d * (q / d) := by
  have hquot : 1 ≤ q / d := (Nat.le_div_iff_mul_le hd).mpr (by simpa using hdq)
  have hrem := Nat.mod_lt q hd
  have hsplit := Nat.mod_add_div q d
  have hprod : d ≤ d * (q / d) := by
    simpa using Nat.mul_le_mul_left d hquot
  nlinarith

theorem exists_large_auxiliary_set
    {q H : ℕ} [Fact q.Prime] (hH : 1 ≤ H) (hq : 2000 * H ^ 2 ≤ q) :
    ∃ V : Finset (Fin 3 → ZMod q),
      q ^ 2 ≤ 2000 ^ 3 * H ^ 6 * V.card ∧
      (0 : Fin 3 → ZMod q) ∉ V ∧
      AuxiliaryCap.IsCap (V : Set (Fin 3 → ZMod q)) ∧
      ∀ p : Fin 3 → (Fin 3 → ZMod q),
        (∀ i, p i ∈ V) → Function.Injective p →
        ∀ x : Fin 3 → ℤ, (∀ i, |x i| ≤ (H : ℤ)) → x ≠ 0 →
          (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
  let w := q / (1000 * H ^ 2)
  have hHsq : 1 ≤ H ^ 2 := by nlinarith
  have hd : 0 < 1000 * H ^ 2 := by positivity
  have hdq : 1000 * H ^ 2 ≤ q := by omega
  have hq2 : q ≠ 2 := by omega
  have hwq : w ≤ q := Nat.div_le_self _ _
  obtain ⟨S, hbox, hsize, hcap⟩ := AuxiliaryCap.exists_cap_in_residueBox hq2 hwq
  have hw : 1000 * H ^ 2 * w ≤ q := Nat.mul_div_le _ _
  obtain ⟨V, hcard, hzero, hVcap, hrel⟩ :=
    exists_set_excluding_short_relations hH hq hw hcap (fun v hv => hbox v hv 0)
  refine ⟨V, ?_, hzero, hVcap, hrel⟩
  rw [hcard]
  have hfloor : q ≤ 2000 * H ^ 2 * w := by
    calc
      q ≤ 2 * (1000 * H ^ 2) * w := le_twice_mul_div hd hdq
      _ = 2000 * H ^ 2 * w := by ring
  have hcube : q ^ 3 ≤ (2000 * H ^ 2 * w) ^ 3 := by gcongr
  have hmul : q * q ^ 2 ≤ q * (2000 ^ 3 * H ^ 6 * S.card) := by
    calc
      q * q ^ 2 = q ^ 3 := by ring
      _ ≤ (2000 * H ^ 2 * w) ^ 3 := hcube
      _ = (2000 ^ 3 * H ^ 6) * w ^ 3 := by ring
      _ ≤ (2000 ^ 3 * H ^ 6) * (q * S.card) := Nat.mul_le_mul_left _ hsize
      _ = q * (2000 ^ 3 * H ^ 6 * S.card) := by ring
  exact Nat.le_of_mul_le_mul_left hmul (Fact.out : q.Prime).pos

theorem exists_large_auxiliary_set_real
    {q H : ℕ} [Fact q.Prime] (hH : 1 ≤ H) (hq : 2000 * H ^ 2 ≤ q) :
    ∃ V : Finset (Fin 3 → ZMod q),
      (q : ℝ) ^ 2 / (2000 ^ 3 * (H : ℝ) ^ 6) ≤ V.card ∧ V.Nonempty ∧
      (0 : Fin 3 → ZMod q) ∉ V ∧
      AuxiliaryCap.IsCap (V : Set (Fin 3 → ZMod q)) ∧
      ∀ p : Fin 3 → (Fin 3 → ZMod q),
        (∀ i, p i ∈ V) → Function.Injective p →
        ∀ x : Fin 3 → ℤ, (∀ i, |x i| ≤ (H : ℤ)) → x ≠ 0 →
          (∑ i, (x i : ZMod q) • p i) ≠ 0 := by
  obtain ⟨V, hsize, hzero, hcap, hrel⟩ := exists_large_auxiliary_set hH hq
  have hHp : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hsizeR : (q : ℝ) ^ 2 ≤ (2000 ^ 3 * (H : ℝ) ^ 6) * V.card := by
    exact_mod_cast hsize
  have hVpos : 0 < V.card := by
    by_contra hnot
    have hv : V.card = 0 := by omega
    have hqp : 0 < q ^ 2 := pow_pos (Fact.out : q.Prime).pos 2
    simp only [hv, mul_zero] at hsize
    omega
  refine ⟨V, ?_, Finset.card_pos.mp hVpos, hzero, hcap, hrel⟩
  exact (div_le_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hsizeR)

end Problem355.AuxiliarySet

end OAI
