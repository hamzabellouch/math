import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.IdealEuler
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace OAI

namespace SevenEighths.UnitSexticWitness

open ActualEisensteinCubic CanonicalRowCompletion CanonicalUnitEuler
open ConcreteTraceCRT
open scoped Classical
noncomputable section
local notation "lambda" => ConcretePrimeRowBridge.goodLambda

lemma idealRowHom_unit_eq_of_norm_mod_seven (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hodd : ringChar (O ⧸ P) ≠ 2)
    (hmod : Ideal.absNorm P % 36 = 7) (u : Oˣ) :
    idealRowHom u.val P = eisEmbedding u.val := by
  rw [idealRowHom_prime _ P hg, actualSextic_unit_euler P hg hodd]
  have hcard : Nat.card (O ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard]
  have hm : (Ideal.absNorm P - 1) / 6 ≡ 1 [MOD 6] := by
    dsimp [Nat.ModEq]
    omega
  have he := pow_eq_pow_of_modEq hm (unit_pow_six u)
  simpa only [pow_one] using congrArg eisEmbedding he

lemma prime_norm_good {p : ℕ} (_hp : p.Prime) (hp3 : 3 < p)
    (P : Ideal O) (hP : Ideal.absNorm P = p) : lambda ∉ P := by
  intro hl
  have hd := Ideal.absNorm_dvd_absNorm_of_le
    ((Ideal.span_singleton_le_iff_mem P).mpr hl)
  have hlambda : Ideal.absNorm (Ideal.span {lambda}) = 3 := CubicEisenstein.absNorm_span_lambda
  rw [hP, hlambda] at hd
  have := Nat.le_of_dvd (by decide : 0 < 3) hd
  omega

lemma prime_norm_ringChar {p : ℕ} (hp : p.Prime)
    (P : Ideal O) [P.IsMaximal] (hP : Ideal.absNorm P = p) :
    ringChar (O ⧸ P) = p := by
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let : Fact p.Prime := ⟨hp⟩
  have hcard : Fintype.card (O ⧸ P) = p := by
    rw [← Nat.card_eq_fintype_card]
    exact hP
  let : CharP (O ⧸ P) p := charP_of_card_eq_prime hcard
  exact ringChar.eq (O ⧸ P) p

lemma exists_primeIdeal_norm {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ P : Ideal O, P.IsMaximal ∧ Ideal.absNorm P = p := by
  have hc := ShortDraftHeckeBridge.split_count_of_mod_one hp hmod
  have hne : ((Ideal.span {(p : ℤ)}).primesOver O).Nonempty := by
    exact Set.nonempty_of_ncard_ne_zero (by rw [hc]; decide)
  obtain ⟨P, hP⟩ := hne
  let : P.IsPrime := hP.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  have hn := ShortDraftHeckeBridge.absNorm_split hp hmod P
  have hP0 : P ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hn
    exact hp.ne_zero hn.symm
  exact ⟨P, hP.1.isMaximal hP0, hn⟩

theorem exists_prime_unit_embedding (S : Finset (Ideal O)) (B : ℕ) :
    ∃ P : Ideal O, P.IsMaximal ∧ P ∉ S ∧ B < Ideal.absNorm P ∧
      Ideal.absNorm P % 36 = 7 ∧ lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2 ∧
      ∀ u : Oˣ, idealRowHom u.val P = eisEmbedding u.val := by
  obtain ⟨p, hpB, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max (max B 3) (S.sup Ideal.absNorm)) (q := 36) (a := 7) (by decide) (by decide)
  have hp36 : p % 36 = 7 := by simpa only [Nat.ModEq, Nat.reduceMod] using hmod
  have hp3 : 3 < p := lt_of_le_of_lt ((le_max_right B 3).trans (le_max_left _ _)) hpB
  have hpmod : p % 3 = 1 := by omega
  obtain ⟨P, hmax, hn⟩ := exists_primeIdeal_norm hp hpmod
  let : P.IsMaximal := hmax
  have hg : lambda ∉ P := prime_norm_good hp hp3 P hn
  have hodd : ringChar (O ⧸ P) ≠ 2 := by
    rw [prime_norm_ringChar hp P hn]
    omega
  refine ⟨P, hmax, ?_, ?_, hn ▸ hp36, hg, hodd, ?_⟩
  · intro hPS
    have hle := Finset.le_sup (f := Ideal.absNorm) hPS
    rw [hn] at hle
    have := le_max_right (max B 3) (S.sup Ideal.absNorm)
    omega
  · rw [hn]
    exact lt_of_le_of_lt ((le_max_left B 3).trans (le_max_left _ _)) hpB
  · exact idealRowHom_unit_eq_of_norm_mod_seven P hg hodd (hn ▸ hp36)

theorem exists_unit_witness (u : Oˣ) (hu : u ≠ 1)
    (S : Finset (Ideal O)) (B : ℕ) :
    ∃ P : Ideal O, P.IsMaximal ∧ P ∉ S ∧ B < Ideal.absNorm P ∧
      lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2 ∧
      idealRowHom u.val P ≠ 0 ∧ idealRowHom u.val P ≠ 1 := by
  obtain ⟨P, hp, hs, hb, hm, hg, ho, he⟩ := exists_prime_unit_embedding S B
  refine ⟨P, hp, hs, hb, hg, ho, ?_, ?_⟩
  · rw [he u]
    intro hz
    exact Units.ne_zero u (eisEmbedding_injective (by simpa using hz))
  · rw [he u]
    intro hh
    apply hu
    apply Units.ext
    exact eisEmbedding_injective (by simpa using hh)

theorem exists_prime_embedding_after_deletion
    (S : Finset SmoothMobiusCorrection.PrimeIdeal) (B : ℕ) :
    ∃ P : SmoothMobiusCorrection.PrimeIdeal, P ∉ S ∧ B < Ideal.absNorm P.val ∧
      lambda ∉ P.val ∧ ringChar (O ⧸ P.val) ≠ 2 ∧
      ∀ u : Oˣ, IdealEuler.deletePrimes S (idealRowHom u.val) P.val = eisEmbedding u.val := by
  obtain ⟨P, hp, hs, hb, hm, hg, ho, he⟩ :=
    exists_prime_unit_embedding (S.image Subtype.val) B
  let : P.IsMaximal := hp
  let Q : SmoothMobiusCorrection.PrimeIdeal :=
    ⟨P, Ideal.prime_of_isPrime (NeZero.ne P) inferInstance⟩
  have hQ : Q ∉ S := fun h => hs (Finset.mem_image.mpr ⟨Q, h, rfl⟩)
  refine ⟨Q, hQ, hb, hg, ho, ?_⟩
  intro u
  rw [IdealEuler.deletePrimes_prime, ite_eq_right hQ]
  exact he u

theorem deleted_unit_row_ne_principal (u : Oˣ) (hu : u ≠ 1)
    (S : Finset SmoothMobiusCorrection.PrimeIdeal) :
    IdealEuler.deletePrimes S (idealRowHom u.val) ≠
      IdealEuler.deletePrimes S (idealRowHom (1 : O)) := by
  obtain ⟨P, hs, hb, hg, ho, he⟩ := exists_prime_embedding_after_deletion S 0
  intro h
  have hp := DFunLike.congr_fun h P.val
  rw [he u, show (1 : O) = (1 : Oˣ).val from rfl, he 1, Units.val_one, map_one] at hp
  apply hu
  apply Units.ext
  exact eisEmbedding_injective (by simpa using hp)

end
end SevenEighths.UnitSexticWitness

end OAI
