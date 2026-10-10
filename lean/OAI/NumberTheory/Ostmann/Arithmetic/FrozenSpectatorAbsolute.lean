import OAI.NumberTheory.Ostmann.Arithmetic.FrozenSpectatorAverage
import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyBulkNorm

namespace OAI

/-! # Absolute spectator moments under the unchanged bulk-unit law -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem frozenBulkSpectatorPair_absolute_mean_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (hq : 3 ≤ q) (base : σ → ℕ) (n m : ℕ) (hm : 0 < m)
    (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (hfreq : ∀ b, movingGiantFrequencyUnits q n (t b))
    (hsmall : ∀ b, ((treeLeafProduct n (movingSlotValues base n (small b)) : ℕ) : ZMod q) ≠ 0)
    (hsamples : ∀ b, ((samples b).values base).UnitsAt q)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (g : ZMod q → ℂ) (hg : g 0 = 0) (henergy : ∑ x : ZMod q, ‖g x‖ ^ 2 ≤ (q : ℝ))
    (a : (ZMod q)ˣ × (ZMod q)ˣ) :
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod q)ˣ) : ℝ)⁻¹ *
      (∑ z : TreeLeafIndex n × Fin m → (ZMod q)ˣ,
        ‖frozenBulkSpectatorPair base n m t small samples D e g a z‖) ≤ (3 : ℝ) ^ (2 ^ n) := by
  have hex (b : Bool) := (buildMovingGiantTree n (t b)
    (movingSlotValues base n (small b)) ((samples b).values base)).exists_field_diagram
      (buildMovingGiantTree_units (t b) _ _ (hfreq b) (hsmall b) (hsamples b))
  choose U R _ _ hR using hex
  let d (b : Bool) : SpectatorDiagram q n :=
    ⟨D b, U b, R b, a.1, a.2, transferConjugations n false⟩
  have he (z : TreeLeafIndex n × Fin m → (ZMod q)ˣ) :
      frozenBulkSpectatorPair base n m t small samples D e
        g a z =
      (d false).bulkValue g z *
        conj ((d true).bulkValue g (z ∘ e.symm)) := by
    unfold frozenBulkSpectatorPair
    rw [show movingFieldGiantAmplitude g (D false)
        (buildMovingGiantTree n (t false) (movingSlotValues base n (small false))
          ((samples false).values base)) a.1 a.2 _ = _ from
        hR false g (D false) a.1 a.2 _ false,
      show movingFieldGiantAmplitude g (D true)
        (buildMovingGiantTree n (t true) (movingSlotValues base n (small true))
          ((samples true).values base)) a.1 a.2 _ = _ from
        hR true g (D true) a.1 a.2 _ false]
    rfl
  simp_rw [he]
  exact spectator_bulk_absolute_le hq hm g hg henergy (d false) (d true) e

theorem frozenBulkSpectatorHaar_absolute_mean_le {σ : Type*} {q : ℕ} [Fact q.Prime]
    (hq : 3 ≤ q) (base : σ → ℕ) (n m : ℕ) (hm : 0 < m)
    (t : Bool → FrequencyTree ℤ n)
    (small : Bool → TreeLeafTuple (List σ) n) (samples : Bool → MovingSampleSlots σ n)
    (hfreq : ∀ b, movingGiantFrequencyUnits q n (t b))
    (hsmall : ∀ b, ((treeLeafProduct n (movingSlotValues base n (small b)) : ℕ) : ZMod q) ≠ 0)
    (hsamples : ∀ b, ((samples b).values base).UnitsAt q)
    (D : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex n × Fin m))
    (g : ZMod q → ℂ) (hg : g 0 = 0) (henergy : ∑ x : ZMod q, ‖g x‖ ^ 2 ≤ (q : ℝ)) :
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod q)ˣ) : ℝ)⁻¹ *
      (∑ z : TreeLeafIndex n × Fin m → (ZMod q)ˣ,
        ‖frozenBulkSpectatorHaar base n m t small samples D e g z‖) ≤ (3 : ℝ) ^ (2 ^ n) := by
  let F := frozenBulkSpectatorPair base n m t small samples D e g
  have hmean := uniform_average_norm_average_mul_le
    (A := TreeLeafIndex n × Fin m → (ZMod q)ˣ)
    (B := (ZMod q)ˣ × (ZMod q)ˣ) (fun z a => F a z) (fun _ => 1) 1 ((3 : ℝ) ^ (2 ^ n))
    (by norm_num) (fun _ => by simp)
    (fun a => frozenBulkSpectatorPair_absolute_mean_le hq base n m hm t small samples
      hfreq hsmall hsamples D e g hg henergy a)
  simp only [mul_one, one_mul] at hmean
  have hratio : ‖(Fintype.card (ZMod q)ˣ : ℂ) / (q : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    apply (div_le_one (by positivity : (0 : ℝ) < q)).mpr
    exact_mod_cast (ZMod.card_units q ▸ Nat.sub_le q 1)
  apply le_trans _ hmean
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro z _
  rw [frozenBulkSpectatorHaar, norm_mul]
  exact (mul_le_mul_of_nonneg_right hratio (norm_nonneg _)).trans_eq (one_mul _)

end Ostmann

end OAI
