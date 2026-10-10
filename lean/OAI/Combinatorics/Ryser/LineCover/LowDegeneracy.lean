import OAI.Combinatorics.Ryser.Geometry.ProjectiveJoins
import OAI.Combinatorics.Ryser.LineCover.InjectionSampling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.LineCover.LowDegeneracy

open InjectionSampling

private theorem natCard_le_mul_of_fibers
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (R : ℕ)
    (h : ∀ b, Nat.card {a : A // f a = b} ≤ R) :
    Nat.card A ≤ Nat.card B * R := by
  classical
  calc
    Nat.card A = ∑ b : B, Nat.card {a : A // f a = b} := by
      rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f)]
      exact Nat.card_sigma
    _ ≤ ∑ _b : B, R := Finset.sum_le_sum (fun b _ => h b)
    _ = Nat.card B * R := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
        Nat.card_eq_fintype_card]

variable {F : Type*} [instFieldF : Field F] [instDecidableEqF : DecidableEq F]

def SameDirection {L : Finset (AffineLine F)} (u : Fin 2 ↪ ↥L) : Prop :=
  (u 0).val.1 = (u 1).val.1

def Concurrent {L : Finset (AffineLine F)} (u : Fin 3 ↪ ↥L) : Prop :=
  ∃ p : ProjectivePoint F, ∀ i, ProjectiveIncidence p (some (u i).val)

def firstPair {L : Finset (AffineLine F)} (u : Fin 3 ↪ ↥L) : Fin 2 ↪ ↥L :=
  (Fin.castLEEmb (by decide : 2 ≤ 3)).trans u

@[simp] theorem firstPair_zero {L : Finset (AffineLine F)} (u : Fin 3 ↪ ↥L) :
    firstPair u 0 = u 0 := let _ := instFieldF; let _ := instDecidableEqF; rfl

@[simp] theorem firstPair_one {L : Finset (AffineLine F)} (u : Fin 3 ↪ ↥L) :
    firstPair u 1 = u 1 := let _ := instFieldF; let _ := instDecidableEqF; rfl

private theorem pair_lines_ne {L : Finset (AffineLine F)} (u : Fin 2 ↪ ↥L) :
    (u 0).val ≠ (u 1).val := let _ := instFieldF; let _ := instDecidableEqF; by
  intro h
  have h01 : (0 : Fin 2) = 1 := u.injective (Subtype.ext h)
  exact (by decide : (0 : Fin 2) ≠ 1) h01

def pairMeet {L : Finset (AffineLine F)} (u : Fin 2 ↪ ↥L) : ProjectivePoint F :=
  Classical.choose (existsUnique_projective_incident_of_ne_lines (pair_lines_ne u))

theorem pairMeet_incident {L : Finset (AffineLine F)} (u : Fin 2 ↪ ↥L) :
    ProjectiveIncidence (pairMeet u) (some (u 0).val) ∧
      ProjectiveIncidence (pairMeet u) (some (u 1).val) :=
  (Classical.choose_spec
    (existsUnique_projective_incident_of_ne_lines (pair_lines_ne u))).1

theorem eq_pairMeet {L : Finset (AffineLine F)} (u : Fin 2 ↪ ↥L)
    {p : ProjectivePoint F}
    (h0 : ProjectiveIncidence p (some (u 0).val))
    (h1 : ProjectiveIncidence p (some (u 1).val)) : p = pairMeet u :=
  (Classical.choose_spec
    (existsUnique_projective_incident_of_ne_lines (pair_lines_ne u))).2 p ⟨h0, h1⟩

theorem card_sameDirection_le (L : Finset (AffineLine F)) (R : ℕ)
    (hR : ∀ d : Direction F, (L.filter fun l => l.1 = d).card ≤ R) :
    Nat.card {u : Fin 2 ↪ ↥L // SameDirection u} ≤ L.card * R := let _ := instFieldF; by
  classical
  let A := {u : Fin 2 ↪ ↥L // SameDirection u}
  let f : A → ↥L := fun u => u.val 0
  have hf : ∀ l, Nat.card {u : A // f u = l} ≤ R := by
    intro l
    let g : {u : A // f u = l} → ↥(L.filter fun k => k.1 = l.val.1) :=
      fun u => ⟨(u.val.val 1).val, Finset.mem_filter.mpr
        ⟨(u.val.val 1).property,
          u.val.property.symm.trans
            (congrArg (fun k : ↥L => k.val.1) u.property)⟩⟩
    have hg : Function.Injective g := by
      intro u v huv
      apply Subtype.ext
      apply Subtype.ext
      apply Function.Embedding.ext
      intro i
      fin_cases i
      · exact u.property.trans v.property.symm
      · apply Subtype.ext
        exact congrArg (fun z : ↥(L.filter fun k => k.1 = l.val.1) => z.val) huv
    exact (Nat.card_le_card_of_injective g hg).trans
      (by simpa only [Nat.card_eq_finsetCard] using hR l.val.1)
  simpa only [Nat.card_eq_finsetCard] using natCard_le_mul_of_fibers f R hf

theorem card_concurrent_le (L : Finset (AffineLine F)) (R : ℕ)
    (hR : ∀ p : ProjectivePoint F,
      (L.filter fun l => ProjectiveIncidence p (some l)).card ≤ R) :
    Nat.card {u : Fin 3 ↪ ↥L // Concurrent u} ≤
      L.card.descFactorial 2 * R := by
  classical
  let A := {u : Fin 3 ↪ ↥L // Concurrent u}
  let f : A → (Fin 2 ↪ ↥L) := fun u => firstPair u.val
  have hf : ∀ e, Nat.card {u : A // f u = e} ≤ R := by
    intro e
    let g : {u : A // f u = e} →
        ↥(L.filter fun l => ProjectiveIncidence (pairMeet e) (some l)) :=
      fun u => ⟨(u.val.val 2).val, by
        refine Finset.mem_filter.mpr ⟨(u.val.val 2).property, ?_⟩
        obtain ⟨p, hp⟩ := u.val.property
        have h0 : u.val.val 0 = e 0 :=
          congrArg (fun b : Fin 2 ↪ ↥L => b 0) u.property
        have h1 : u.val.val 1 = e 1 :=
          congrArg (fun b : Fin 2 ↪ ↥L => b 1) u.property
        have heq : p = pairMeet e := eq_pairMeet e
          (by rw [← h0]; exact hp 0) (by rw [← h1]; exact hp 1)
        exact heq ▸ hp 2⟩
    have hg : Function.Injective g := by
      intro u v huv
      have he : firstPair u.val.val = firstPair v.val.val :=
        u.property.trans v.property.symm
      apply Subtype.ext
      apply Subtype.ext
      apply Function.Embedding.ext
      intro i
      fin_cases i
      · exact congrArg (fun b : Fin 2 ↪ ↥L => b 0) he
      · exact congrArg (fun b : Fin 2 ↪ ↥L => b 1) he
      · apply Subtype.ext
        exact congrArg (fun z :
          ↥(L.filter fun l => ProjectiveIncidence (pairMeet e) (some l)) => z.val) huv
    exact (Nat.card_le_card_of_injective g hg).trans
      (by simpa only [Nat.card_eq_finsetCard] using hR (pairMeet e))
  simpa only [natCard_embeddings, Nat.card_fin, Nat.card_eq_finsetCard] using
    natCard_le_mul_of_fibers f R hf

private theorem prob_le_of_card
    {Ω : Type*} [Fintype Ω] (k R : ℕ)
    (hle : Nat.card (Fin (k + 1)) ≤ Nat.card Ω)
    (P : (Fin (k + 1) ↪ Ω) → Prop)
    (hcard : Nat.card {u : Fin (k + 1) ↪ Ω // P u} ≤
      (Nat.card Ω).descFactorial k * R) :
    (law (Fin (k + 1)) Ω hle).prob P ≤
      (R : ℝ) / ((Nat.card Ω - k : ℕ) : ℝ) := by
  have hk : k ≤ Nat.card Ω := by
    have h := hle
    rw [Nat.card_fin] at h
    omega
  have hn : ((Nat.card Ω).descFactorial k : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hk).ne'
  rw [law_prob, Nat.card_fin]
  calc
    _ ≤ (((Nat.card Ω).descFactorial k * R : ℕ) : ℝ) /
        ((Nat.card Ω).descFactorial (k + 1) : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)
    _ = (R : ℝ) / ((Nat.card Ω - k : ℕ) : ℝ) := by
      rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul]
      rw [mul_comm (((Nat.card Ω - k : ℕ) : ℝ))
        (((Nat.card Ω).descFactorial k : ℝ))]
      exact mul_div_mul_left _ _ hn

theorem prob_sameDirection_le (L : Finset (AffineLine F)) (R : ℕ)
    (hL : 2 ≤ L.card)
    (hR : ∀ d : Direction F, (L.filter fun l => l.1 = d).card ≤ R) :
    (law (Fin 2) ↥L (by simpa using hL)).prob SameDirection ≤
      (R : ℝ) / ((L.card - 1 : ℕ) : ℝ) := by
  have hcard : Nat.card {u : Fin 2 ↪ ↥L // SameDirection u} ≤
      (Nat.card ↥L).descFactorial 1 * R := by
    simpa only [Nat.card_eq_finsetCard, Nat.descFactorial_one] using
      card_sameDirection_le L R hR
  simpa only [Nat.card_eq_finsetCard] using
    prob_le_of_card (Ω := ↥L) 1 R (by simpa using hL) SameDirection hcard

theorem prob_concurrent_le (L : Finset (AffineLine F)) (R : ℕ)
    (hL : 3 ≤ L.card)
    (hR : ∀ p : ProjectivePoint F,
      (L.filter fun l => ProjectiveIncidence p (some l)).card ≤ R) :
    (law (Fin 3) ↥L (by simpa using hL)).prob Concurrent ≤
      (R : ℝ) / ((L.card - 2 : ℕ) : ℝ) := by
  have hcard : Nat.card {u : Fin 3 ↪ ↥L // Concurrent u} ≤
      (Nat.card ↥L).descFactorial 2 * R := by
    simpa only [Nat.card_eq_finsetCard] using card_concurrent_le L R hR
  simpa only [Nat.card_eq_finsetCard] using
    prob_le_of_card (Ω := ↥L) 2 R (by simpa using hL) Concurrent hcard

theorem prob_exists_restrict_le
    {I Ω : Type*} [Fintype I] [Fintype Ω] (k : ℕ)
    (hI : Nat.card I ≤ Nat.card Ω) (hk : Nat.card (Fin k) ≤ Nat.card Ω)
    (P : (Fin k ↪ Ω) → Prop) (B : ℝ)
    (hP : (law (Fin k) Ω hk).prob P ≤ B) :
    (law I Ω hI).prob (fun u => ∃ j : Fin k ↪ I, P (restrict j u)) ≤
      ((Nat.card I).descFactorial k : ℝ) * B := by
  classical
  calc
    _ ≤ ∑ j : Fin k ↪ I, (law I Ω hI).prob (fun u => P (restrict j u)) :=
      FiniteLaw.prob_exists_le _ _
    _ = ∑ _j : Fin k ↪ I, (law (Fin k) Ω hk).prob P := by
      apply Finset.sum_congr rfl
      intro j _
      exact prob_law_restrict j hI hk P
    _ ≤ ∑ _j : Fin k ↪ I, B := Finset.sum_le_sum (fun _ _ => hP)
    _ = ((Nat.card I).descFactorial k : ℝ) * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_embedding_eq, Fintype.card_fin, Nat.card_eq_fintype_card]

def AnyParallel {I : Type*} {L : Finset (AffineLine F)} (u : I ↪ ↥L) : Prop :=
  ∃ j : Fin 2 ↪ I, SameDirection (restrict j u)

def AnyConcurrent {I : Type*} {L : Finset (AffineLine F)} (u : I ↪ ↥L) : Prop :=
  ∃ j : Fin 3 ↪ I, Concurrent (restrict j u)

theorem anyParallel_iff {I : Type*} {L : Finset (AffineLine F)} (u : I ↪ ↥L) :
    AnyParallel u ↔ ∃ i j, i ≠ j ∧ (u i).val.1 = (u j).val.1 := let _ := instFieldF; let _ := instDecidableEqF; by
  classical
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j 0, j 1, fun h => (by decide : (0 : Fin 2) ≠ 1) (j.injective h), hj⟩
  · rintro ⟨i, j, hij, hdir⟩
    let e : Fin 2 ↪ I :=
      { toFun := ![i, j]
        inj' := by
          intro a b hab
          fin_cases a <;> fin_cases b <;> simp_all }
    exact ⟨e, hdir⟩

theorem anyConcurrent_iff {I : Type*} {L : Finset (AffineLine F)} (u : I ↪ ↥L) :
    AnyConcurrent u ↔ ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ∃ p : ProjectivePoint F,
        ProjectiveIncidence p (some (u i).val) ∧
        ProjectiveIncidence p (some (u j).val) ∧
        ProjectiveIncidence p (some (u k).val) := let _ := instDecidableEqF; by
  classical
  constructor
  · rintro ⟨j, p, hp⟩
    refine ⟨j 0, j 1, j 2, ?_, ?_, ?_, p, hp 0, hp 1, hp 2⟩
    · exact fun h => (by decide : (0 : Fin 3) ≠ 1) (j.injective h)
    · exact fun h => (by decide : (0 : Fin 3) ≠ 2) (j.injective h)
    · exact fun h => (by decide : (1 : Fin 3) ≠ 2) (j.injective h)
  · rintro ⟨i, j, k, hij, hik, hjk, p, hi, hj, hk⟩
    let e : Fin 3 ↪ I :=
      { toFun := ![i, j, k]
        inj' := by
          intro a b hab
          fin_cases a <;> fin_cases b <;> simp_all }
    refine ⟨e, p, ?_⟩
    intro a
    fin_cases a
    · exact hi
    · exact hj
    · exact hk

theorem prob_anyParallel_le {I : Type*} [Fintype I]
    (L : Finset (AffineLine F)) (R : ℕ)
    (hI : Nat.card I ≤ Nat.card ↥L) (hL : 2 ≤ L.card)
    (hR : ∀ d : Direction F, (L.filter fun l => l.1 = d).card ≤ R) :
    (law I ↥L hI).prob AnyParallel ≤
      ((Nat.card I).descFactorial 2 : ℝ) * R / ((L.card - 1 : ℕ) : ℝ) := by
  have hevent : (AnyParallel : (I ↪ ↥L) → Prop) =
      (fun u => ∃ j : Fin 2 ↪ I, SameDirection (restrict j u)) := by
    funext u
    rfl
  rw [hevent]
  simpa only [mul_div_assoc] using
    prob_exists_restrict_le 2 hI (by simpa using hL) SameDirection
      ((R : ℝ) / ((L.card - 1 : ℕ) : ℝ)) (prob_sameDirection_le L R hL hR)

theorem prob_anyConcurrent_le {I : Type*} [Fintype I]
    (L : Finset (AffineLine F)) (R : ℕ)
    (hI : Nat.card I ≤ Nat.card ↥L) (hL : 3 ≤ L.card)
    (hR : ∀ p : ProjectivePoint F,
      (L.filter fun l => ProjectiveIncidence p (some l)).card ≤ R) :
    (law I ↥L hI).prob AnyConcurrent ≤
      ((Nat.card I).descFactorial 3 : ℝ) * R / ((L.card - 2 : ℕ) : ℝ) := by
  have hevent : (AnyConcurrent : (I ↪ ↥L) → Prop) =
      (fun u => ∃ j : Fin 3 ↪ I, Concurrent (restrict j u)) := by
    funext u
    rfl
  rw [hevent]
  simpa only [mul_div_assoc] using
    prob_exists_restrict_le 3 hI (by simpa using hL) Concurrent
      ((R : ℝ) / ((L.card - 2 : ℕ) : ℝ)) (prob_concurrent_le L R hL hR)

theorem prob_tuple_parallel_le (L : Finset (AffineLine F)) (t R : ℕ)
    (ht : 2 * t ≤ L.card) (hL : 2 ≤ L.card)
    (hR : ∀ d : Direction F, (L.filter fun l => l.1 = d).card ≤ R) :
    (law (Fin t ⊕ Fin t) ↥L (by simpa [Nat.card_sum, two_mul] using ht)).prob
        AnyParallel ≤
      ((2 * t).descFactorial 2 : ℝ) * R / ((L.card - 1 : ℕ) : ℝ) := by
  simpa only [Nat.card_sum, Nat.card_fin, ← two_mul] using
    prob_anyParallel_le (I := Fin t ⊕ Fin t) L R
      (by simpa [Nat.card_sum, two_mul] using ht) hL hR

theorem prob_tuple_concurrent_le (L : Finset (AffineLine F)) (t R : ℕ)
    (ht : 2 * t ≤ L.card) (hL : 3 ≤ L.card)
    (hR : ∀ p : ProjectivePoint F,
      (L.filter fun l => ProjectiveIncidence p (some l)).card ≤ R) :
    (law (Fin t ⊕ Fin t) ↥L (by simpa [Nat.card_sum, two_mul] using ht)).prob
        AnyConcurrent ≤
      ((2 * t).descFactorial 3 : ℝ) * R / ((L.card - 2 : ℕ) : ℝ) := by
  simpa only [Nat.card_sum, Nat.card_fin, ← two_mul] using
    prob_anyConcurrent_le (I := Fin t ⊕ Fin t) L R
      (by simpa [Nat.card_sum, two_mul] using ht) hL hR

end RyserCoveringCounterexample.LineCover.LowDegeneracy

end

end OAI
