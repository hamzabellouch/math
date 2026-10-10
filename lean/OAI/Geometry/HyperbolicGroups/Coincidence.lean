import Mathlib
import OAI.Geometry.HyperbolicGroups.TableSelection

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace Coincidence

variable {V S I : Type*} [Fintype V] [Fintype S] [Fintype I]
  [DecidableEq V] [DecidableEq S] [DecidableEq I]

/-- Signs remain separate at every position, even inside one unsigned class. -/
def signedAssignment {k n : ℕ} (c : V → Fin k) (ε : V → Bool) (a : Fin k → Fin (n+1)) :
    V → IncidenceTemplate.SymmetricAlphabet n := fun v => (a (c v), ε v)

def unsignedValues {n : ℕ} (σ : V → IncidenceTemplate.SymmetricAlphabet n) : Finset (Fin (n+1)) :=
  Finset.univ.image (fun v => (σ v).1)

def unsignedRank {n : ℕ} (σ : V → IncidenceTemplate.SymmetricAlphabet n) : ℕ :=
  Fintype.card V - (unsignedValues σ).card

omit [DecidableEq V] in
lemma unsignedValues_card_le {n : ℕ} (σ : V → IncidenceTemplate.SymmetricAlphabet n) :
    (unsignedValues σ).card ≤ Fintype.card V := Finset.card_image_le

omit [DecidableEq V] in
lemma signed_factorization {n : ℕ} (σ : V → IncidenceTemplate.SymmetricAlphabet n) :
    ∃ (c : V → Fin (unsignedValues σ).card) (ε : V → Bool)
      (a : Fin (unsignedValues σ).card → Fin (n+1)), signedAssignment c ε a = σ := by
  let e : unsignedValues σ ≃ Fin (unsignedValues σ).card :=
    (Fintype.equivFin _).trans (finCongr (Fintype.card_coe _))
  refine ⟨fun v => e ⟨(σ v).1,Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩⟩,
    fun v => (σ v).2, fun i => (e.symm i).val, ?_⟩
  funext v
  simp only [signedAssignment,Equiv.symm_apply_apply,Prod.eta]

omit [Fintype V] [DecidableEq V] [DecidableEq S] in
/-- A specified unsigned coincidence pattern is rare exactly when its number
of classes is smaller than the total independent trial cost. Distinctness is
explicit, so repeated occurrences are not incorrectly charged twice. -/
theorem signed_pattern_bound {k n : ℕ} (c : V → Fin k) (ε : V → Bool)
    (row : (V → IncidenceTemplate.SymmetricAlphabet n) → S → I)
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (q : S → ℝ) (hq : ∀ σ s, p (row σ s) = q s) :
    (FiniteLaw.bernoulliProduct p hp).prob (fun w => ∃ a : Fin k → Fin (n+1),
      Function.Injective (row (signedAssignment c ε a)) ∧
      BernoulliCandidates.Present row w (signedAssignment c ε a)) ≤
      (n+1:ℝ)^k * ∏ s, q s := by
  classical
  let μ := FiniteLaw.bernoulliProduct p hp
  apply (μ.prob_exists_le (fun a w => Function.Injective (row (signedAssignment c ε a)) ∧
    BernoulliCandidates.Present row w (signedAssignment c ε a))).trans
  have hq0 : 0 ≤ ∏ s, q s := by
    exact Finset.prod_nonneg fun s _ =>
      (hq (signedAssignment c ε (fun _ => 0)) s ▸ (hp _).1)
  calc
    _ ≤ ∑ a : Fin k → Fin (n+1), ∏ s, q s := by
      apply Finset.sum_le_sum
      intro a _
      by_cases hi : Function.Injective (row (signedAssignment c ε a))
      · simp only [hi,true_and]
        change (FiniteLaw.bernoulliProduct p hp).prob _ ≤ _
        rw [BernoulliCandidates.prob_present row p hp _ hi]
        simp only [hq,le_refl]
      · simp only [hi,false_and,FiniteLaw.prob,ite_false,FiniteLaw.expect_const]
        exact hq0
    _ = _ := by simp [Nat.cast_pow,Nat.cast_add]


omit [DecidableEq S] in
lemma patterns_bound {k n : ℕ}
    (row : (V → IncidenceTemplate.SymmetricAlphabet n) → S → I)
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (q : S → ℝ) (hq : ∀ σ s, p (row σ s) = q s) :
    (FiniteLaw.bernoulliProduct p hp).prob (fun w => ∃ (c : V → Fin k) (ε : V → Bool)
      (a : Fin k → Fin (n+1)), Function.Injective (row (signedAssignment c ε a)) ∧
      BernoulliCandidates.Present row w (signedAssignment c ε a)) ≤
      (k:ℝ)^Fintype.card V * 2^Fintype.card V * ((n+1:ℝ)^k * ∏ s, q s) := by
  classical
  let μ := FiniteLaw.bernoulliProduct p hp
  apply (μ.prob_exists_le _).trans
  calc
    _ ≤ ∑ c : V → Fin k, ∑ ε : V → Bool, ((n+1:ℝ)^k * ∏ s, q s) := by
      apply Finset.sum_le_sum
      intro c _
      exact (μ.prob_exists_le _).trans (Finset.sum_le_sum fun ε _ =>
        signed_pattern_bound c ε row p hp q hq)
    _ = _ := by simp [Nat.cast_pow,mul_assoc]

def rankRate (J : ℕ) (cost N : ℝ) : ℝ :=
  ∑ k : Fin (J+1), if (k:ℝ)+cost < 0 then
    (k:ℝ)^J * 2^J * N^((k:ℝ)+cost) else 0

lemma rankRate_nonneg (J : ℕ) (cost : ℝ) {N : ℝ} (hN : 0 ≤ N) :
    0 ≤ rankRate J cost N := by
  unfold rankRate
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> positivity

lemma rankRate_tendsto (J : ℕ) (cost : ℝ) :
    Tendsto (rankRate J cost) atTop (𝓝 0) := by
  unfold rankRate
  have hh (k : Fin (J+1)) : Tendsto (fun N : ℝ => if (k:ℝ)+cost < 0 then
      (k:ℝ)^J * 2^J * N^((k:ℝ)+cost) else 0) atTop (𝓝 0) := by
    split_ifs with h
    · have ht := (tendsto_rpow_neg_atTop (neg_pos.mpr h)).const_mul ((k:ℝ)^J * 2^J)
      simpa only [neg_neg,mul_zero] using ht
    · exact tendsto_const_nhds
  simpa only [rankRate,Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun k _ => hh k)

/-- Concrete bad event: an included collection of distinct trials has more
unsigned coincidences than its information budget permits. -/
def RankBad {n : ℕ} (row : (V → IncidenceTemplate.SymmetricAlphabet n) → S → I)
    (cost : ℝ) (w : I → Bool) : Prop :=
  ∃ σ, Function.Injective (row σ) ∧ BernoulliCandidates.Present row w σ ∧
    (Fintype.card V:ℝ)+cost < unsignedRank σ

instance {n : ℕ} (row : (V → IncidenceTemplate.SymmetricAlphabet n) → S → I)
    (cost : ℝ) : DecidablePred (RankBad row cost) := fun _ => Classical.propDecidable _

omit [Fintype S] [Fintype I] [DecidableEq V] [DecidableEq S] [DecidableEq I] in
lemma rank_bad_classes {n : ℕ}
    (row : (V → IncidenceTemplate.SymmetricAlphabet n) → S → I) (cost : ℝ) (w : I → Bool)
    (h : RankBad row cost w) :
    ∃ k : Fin (Fintype.card V+1), (k:ℝ)+cost < 0 ∧
      ∃ (c : V → Fin k) (ε : V → Bool) (a : Fin k → Fin (n+1)),
        Function.Injective (row (signedAssignment c ε a)) ∧
        BernoulliCandidates.Present row w (signedAssignment c ε a) := by
  obtain ⟨σ,hi,hp,hr⟩ := h
  have hk := unsignedValues_card_le σ
  have hr' : ((unsignedValues σ).card:ℝ)+cost < 0 := by
    rw [unsignedRank,Nat.cast_sub hk] at hr
    linarith
  obtain ⟨c,ε,a,ha⟩ := signed_factorization σ
  exact ⟨⟨_,Nat.lt_succ_of_le hk⟩,hr',c,ε,a,by simpa only [ha] using hi,by simpa only [ha] using hp⟩

omit [DecidableEq S] in
/-- The finite first-moment coincidence estimate, including every sign choice
and every unsigned partition. -/
theorem rank_bad_bound {n : ℕ}
    (row : (V → IncidenceTemplate.SymmetricAlphabet n) → S → I)
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (cost : S → ℝ) (hq : ∀ σ s,
      p (row σ s) = (Fintype.card (IncidenceTemplate.SymmetricAlphabet n):ℝ)^(cost s)) :
    (FiniteLaw.bernoulliProduct p hp).prob (RankBad row (∑ s, cost s)) ≤
      rankRate (Fintype.card V) (∑ s, cost s)
        (Fintype.card (IncidenceTemplate.SymmetricAlphabet n)) := by
  classical
  let μ := FiniteLaw.bernoulliProduct p hp
  let N : ℝ := Fintype.card (IncidenceTemplate.SymmetricAlphabet n)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hbase : (n+1:ℝ) ≤ N := by
    dsimp [N]
    rw [IncidenceTemplate.card_symmetricAlphabet]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  let E (k : Fin (Fintype.card V+1)) (w : I → Bool) : Prop :=
    (k:ℝ)+(∑ s, cost s) < 0 ∧
      ∃ (c : V → Fin k) (ε : V → Bool) (a : Fin k → Fin (n+1)),
        Function.Injective (row (signedAssignment c ε a)) ∧
        BernoulliCandidates.Present row w (signedAssignment c ε a)
  have hmono : μ.prob (RankBad row (∑ s, cost s)) ≤
      μ.prob (fun w => ∃ k, E k w) :=
    μ.prob_mono (fun w h => rank_bad_classes row (∑ s, cost s) w h)
  have hunion : μ.prob (fun w => ∃ k, E k w) ≤ ∑ k, μ.prob (E k) := by
    convert μ.prob_exists_le E using 1
    congr 1
  apply hmono.trans (hunion.trans _)
  unfold rankRate
  apply Finset.sum_le_sum
  intro k _
  dsimp only [E]
  by_cases hk : (k:ℝ)+(∑ s, cost s) < 0
  · simp only [hk,true_and,ite_true]
    apply (patterns_bound row p hp (fun s => N^(cost s)) hq).trans
    have hpow : (n+1:ℝ)^k.val ≤ N^k.val := pow_le_pow_left₀ (by positivity) hbase _
    have he : N^k.val * (∏ s, N^(cost s)) = N^((k:ℝ)+(∑ s, cost s)) := by
      rw [← Real.rpow_sum_of_pos hN,← Real.rpow_natCast,← Real.rpow_add hN]
    rw [← he]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpow (Finset.prod_nonneg fun s _ => Real.rpow_nonneg hN.le _))
      (by positivity)
  · simp only [hk,false_and,ite_false,FiniteLaw.prob,FiniteLaw.expect_const,le_refl]

end Coincidence
end HyperbolicObstruction
end
end

section

end
end

end OAI
