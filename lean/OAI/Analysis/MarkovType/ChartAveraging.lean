import OAI.Analysis.MarkovType.FiniteCharts
import OAI.Analysis.MarkovType.FiniteRamsey
import OAI.Analysis.MarkovType.FiniteAveraging

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity

private abbrev OrderedComparison (k : ℕ) :=
  Σ m : Fin (k + 1), ((Fin m.val ↪o Fin k) × (Fin m.val ↪o Fin k))

theorem exists_finite_order_averaging (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (B : ℕ) (ν : (Fin k ↪o Fin B) → ℝ),
      (∀ C, 0 ≤ ν C) ∧ (∑ C, ν C = 1) ∧
      ∀ (m : Fin (k + 1)) (s t : Fin m.val ↪o Fin k),
        finiteTotalVariation (finitePushforward ν (fun C => s.trans C))
          (finitePushforward ν (fun C => t.trans C)) < ε := by
  classical
  let R := OrderedComparison k
  let δ : ℝ := ε / ((Fintype.card R : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsum : (Fintype.card R : ℝ) * δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < (Fintype.card R : ℝ) + 1)]
    nlinarith
  obtain ⟨J, bin, hJ, hbin⟩ := exists_finite_interval_coloring δ hδ
  let : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
  let Pair (m : Fin (k + 1)) := (Fin m.val ↪o Fin k) × (Fin m.val ↪o Fin k)
  let colors : Fin (k + 1) → ℕ := fun m => Fintype.card (Pair m → Fin J)
  have hcolors (m : Fin (k + 1)) : 0 < colors m := by
    exact Fintype.card_pos
  obtain ⟨B, hB, hRamsey⟩ := finite_ordered_simultaneous_ramsey k k colors hcolors
  have hkB : k ≤ B := (le_max_left k k).trans hB
  let : Nonempty (Fin k ↪o Fin B) := ⟨Fin.castLEOrderEmb hkB⟩
  let T : R → Type := fun r => Fin r.1.val ↪o Fin B
  let F : (r : R) → (Fin k ↪o Fin B) → T r := fun r C => r.2.1.trans C
  let G : (r : R) → (Fin k ↪o Fin B) → T r := fun r C => r.2.2.trans C
  have hdual : ∀ a : (r : R) → T r → ℝ, (∀ r t, |a r t| ≤ 1) →
      ∃ C, |∑ r, (a r (F r C) - a r (G r C))| < ε := by
    intro a ha
    let χ : (m : Fin (k + 1)) → (Fin m.val ↪o Fin B) → Fin (colors m) :=
      fun m t => Fintype.equivFin (Pair m → Fin J)
        (fun p => bin ⟨a ⟨m, p⟩ t, abs_le.mp (ha ⟨m, p⟩ t)⟩)
    obtain ⟨C, hC⟩ := hRamsey χ
    have hdiff (r : R) : |a r (F r C) - a r (G r C)| < δ := by
      rcases r with ⟨m, s, t⟩
      have heq := hC m s t
      have hfunctions := (Fintype.equivFin (Pair m → Fin J)).injective heq
      have hcoordinate := congrFun hfunctions (s, t)
      exact hbin
        ⟨a ⟨m, (s, t)⟩ (s.trans C), abs_le.mp (ha _ _)⟩
        ⟨a ⟨m, (s, t)⟩ (t.trans C), abs_le.mp (ha _ _)⟩ hcoordinate
    refine ⟨C, ?_⟩
    calc
      |∑ r, (a r (F r C) - a r (G r C))|
          ≤ ∑ r, |a r (F r C) - a r (G r C)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : R, δ := Finset.sum_le_sum (fun r _ => (hdiff r).le)
      _ = (Fintype.card R : ℝ) * δ := by simp
      _ < ε := hδsum
  obtain ⟨ν, hν, hνsum, havg⟩ := exists_simultaneous_finite_averaging F G ε hε hdual
  exact ⟨B, ν, hν, hνsum, fun m s t => havg ⟨m, (s, t)⟩⟩

theorem finitePushforward_equiv {A D T : Type*} [Fintype A] [Fintype D]
    (e : A ≃ D) (ν : A → ℝ) (f : D → T) (t : T) :
    finitePushforward (fun d => ν (e.symm d)) f t =
      finitePushforward ν (fun a => f (e a)) t := by
  classical
  unfold finitePushforward
  exact (Equiv.sum_comp e (fun d => if f d = t then ν (e.symm d) else 0)).symm.trans
    (by simp)

theorem exists_chart_averaging (Λ : Finset ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (B : ℕ) (ν : Chart Λ B → ℝ), (∀ C, 0 ≤ ν C) ∧ (∑ C, ν C = 1) ∧
      ∀ (m : ℕ) (s t : Fin m ↪o ↥Λ),
        finiteTotalVariation (finitePushforward ν (fun C => s.trans C))
          (finitePushforward ν (fun C => t.trans C)) < ε := by
  classical
  let k := Λ.card
  let e : Fin k ≃o ↥Λ := Λ.orderIsoOfFin rfl
  obtain ⟨B, ν, hν, hνsum, havg⟩ := exists_finite_order_averaging k ε hε
  let chartEquiv : (Fin k ↪o Fin B) ≃ Chart Λ B :=
    { toFun := fun C => e.symm.toOrderEmbedding.trans C
      invFun := fun C => e.toOrderEmbedding.trans C
      left_inv := by intro C; ext i; simp
      right_inv := by intro C; ext x; simp }
  let μ : Chart Λ B → ℝ := fun C => ν (chartEquiv.symm C)
  refine ⟨B, μ, fun C => hν _, ?_, ?_⟩
  · change (∑ C, ν (chartEquiv.symm C)) = 1
    rw [Equiv.sum_comp chartEquiv.symm]
    exact hνsum
  · intro m s t
    have hmk : m ≤ k := by
      have h := Fintype.card_le_of_injective s s.injective
      simpa only [Fintype.card_fin, Fintype.card_coe] using h
    let m' : Fin (k + 1) := ⟨m, Nat.lt_succ_of_le hmk⟩
    have h := havg m' (s.trans e.symm.toOrderEmbedding) (t.trans e.symm.toOrderEmbedding)
    have hs : finitePushforward μ (fun C => s.trans C) =
        finitePushforward ν (fun C => (s.trans e.symm.toOrderEmbedding).trans C) := by
      ext v
      change finitePushforward (fun C => ν (chartEquiv.symm C)) (fun C => s.trans C) v = _
      rw [finitePushforward_equiv chartEquiv]
      rfl
    have ht : finitePushforward μ (fun C => t.trans C) =
        finitePushforward ν (fun C => (t.trans e.symm.toOrderEmbedding).trans C) := by
      ext v
      change finitePushforward (fun C => ν (chartEquiv.symm C)) (fun C => t.trans C) v = _
      rw [finitePushforward_equiv chartEquiv]
      rfl
    rw [hs, ht]
    exact h

end MarkovSuperreflexivity

end OAI
