import OAI.Probability.ThorpShuffle.Main

namespace OAI


noncomputable section
open scoped BigOperators
open Filter

namespace Thorp

abbrev LabelList (d k : ℕ) := Fin k ↪ Position d

def coordinateRun (d t : ℕ) (ω : History d t) : State d :=
  (rotate d)⁻¹ ^ t * run d t ω

def images {d k : ℕ} (t : ℕ) (start : State d) (labels : LabelList d k)
    (ω : History d t) : LabelList d k :=
  labels.trans ((coordinateRun d t ω * start).toEmbedding)

def listTV {d k : ℕ} (t : ℕ) (start : State d) (labels : LabelList d k) : ℝ :=
  tv (fairMass (images t start labels)) (fun _ => 1 / Fintype.card (LabelList d k))

namespace FixedLists
open Conditional

theorem uniform_list_mass {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ} (e : Fin k ↪ α) :
    fairMass (fun g : Equiv.Perm α => e.trans g.toEmbedding) =
      fun _ => (1 : ℝ) / Fintype.card (Fin k ↪ α) := by
  classical
  let : Nonempty (Fin k ↪ α) := ⟨e⟩
  let μ := fairMass (fun g : Equiv.Perm α => e.trans g.toEmbedding)
  have hconst (z w : Fin k ↪ α) : μ z = μ w := by
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair z w z.injective w.injective
    have heq (g : Equiv.Perm α) : e.trans ((σ * g).toEmbedding) = w ↔ e.trans g.toEmbedding = z := by
      constructor
      · intro h
        ext i
        apply σ.injective
        exact (congrArg (fun a : Fin k ↪ α => a i) h).trans (hσ i).symm
      · intro h
        ext i
        change σ (g (e i)) = w i
        rw [show g (e i) = z i from congrArg (fun a : Fin k ↪ α => a i) h, hσ]
    have hh := mean_equiv (Equiv.mulLeft σ)
      (fun g : Equiv.Perm α => if e.trans g.toEmbedding = w then (1 : ℝ) else 0)
    change mean (fun g : Equiv.Perm α => if e.trans ((σ * g).toEmbedding) = w then (1 : ℝ) else 0) = _ at hh
    dsimp only [μ]
    simp only [fairMass_eq_mean]
    simpa only [heq] using hh
  have hs : ∑ z, μ z = 1 := fairMass_sum _
  funext z
  have hz : (Fintype.card (Fin k ↪ α) : ℝ) * μ z = 1 := by
    have hh : (∑ w, μ w) = (Fintype.card (Fin k ↪ α) : ℝ) * μ z := by
      simp only [hconst _ z, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  change μ z = _
  exact (eq_div_iff (by exact_mod_cast Fintype.card_ne_zero (α := Fin k ↪ α))).mpr (by linarith)

theorem uniform_list_mass_frame {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (e : Fin k ↪ α) (r : Equiv.Perm α) :
    fairMass (fun g : Equiv.Perm α => e.trans ((r * g).toEmbedding)) =
      fun _ => (1 : ℝ) / Fintype.card (Fin k ↪ α) := by
  classical
  calc
    _ = fairMass (fun g : Equiv.Perm α => e.trans g.toEmbedding) := by
      funext z
      simp only [fairMass_eq_mean]
      exact mean_equiv (Equiv.mulLeft r)
        (fun g : Equiv.Perm α => if e.trans g.toEmbedding = z then (1 : ℝ) else 0)
    _ = _ := uniform_list_mass e

end FixedLists
end Thorp

end

end OAI
