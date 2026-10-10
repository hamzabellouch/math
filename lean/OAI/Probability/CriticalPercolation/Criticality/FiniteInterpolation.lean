import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinaryEventBound
import OAI.Probability.CriticalPercolation.Entropy.BinaryCostBound

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure

variable {V E : Type*} [Fintype V] [Fintype E]
local instance interpolationFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

def allDarts (G : BondGraph V E) : List (LazyDFS.Dart V E) :=
  (Finset.univ.filter (fun a : LazyDFS.Dart V E => G.ends a.2.1 = s(a.1,a.2.2))).toList

lemma allDarts_good (G : BondGraph V E) : LazyDFS.GoodDarts G (allDarts G) := by
  intro a ha
  simpa only [allDarts,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and] using ha

lemma allDarts_exhaustive (G : BondGraph V E) : LazyDFS.Exhaustive G (allDarts G) := by
  intro v e t h
  simp only [allDarts,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and]
  exact h

theorem finite_interpolation_index (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (hd : 2≤d) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0<c)
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x j) (x k)))
    (s : ℕ) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s)) :
    ∃ j<d, 0 < prob w (endpointEvent G (x j) (x (j+1)) s) ∧
      -Real.log (prob w (endpointEvent G (x j) (x (j+1)) s)) ≤
      (4*(16/(2*p*(1-p)))+6)*(Real.log (1/prob w (endpointEvent G (x 0) (x d) s)) +
          (Nat.clog 2 d)*(Real.log 8+Real.log (1/c))) +
        (2*(16/(2*p*(1-p)))+5)*(Nat.clog 2 d)*Real.log 4 := by
  let order := allDarts G
  let n := Nat.clog 2 d
  have hc1 : c≤1 := (hconn 0 1 (by omega) (by omega) (by omega)).trans
    (prob_le_one w (homogeneous_normalized w p h0 h1)
      (fun e b => (homogeneous_positive w hp h0 h1 e b).le) _)
  obtain ⟨D,hD⟩ := exists_descriptor G order d x p w s n
    (jointMass_normalized G order d x p w s n (allDarts_exhaustive G) hd hp h0 h1 hc hconn hδ)
  have hD0 : 0 < descriptorMass G order d x p w s n D :=
    (zpow_pos (by norm_num : (0:ℝ)<8) _).trans_le hD
  have he := conditioned_event_bound G order d x p w s n D (allDarts_good G)
    (allDarts_exhaustive G) (by omega) hp h0 h1 hc hc1
    (fun j hj hjd => hconn 0 j hj hjd.le (by simpa only [Nat.sub_zero] using hjd)) hδ hD0
  let h := fromWords (E := E) n (fun j => (D j).1) (fun _ => none)
  have hadj := interval_adjacent (by omega : 0<d) (le_refl (Nat.clog 2 d)) h
  have hb := interval_bounds (by omega : 0<d) n h
  refine ⟨(interval d n h).1,by omega,?_⟩
  change 0 < prob w (endpointEvent G (x (interval d n h).1) (x (interval d n h).2) s) ∧ _ at he
  rw [hadj] at he
  refine ⟨he.1,he.2.trans ?_⟩
  apply add_le_add ?_ le_rfl
  apply mul_le_mul_of_nonneg_left (constructionCost_le G order d x p w s n D hc hδ hD)
  have : 0 < 2*p*(1-p) := mul_pos (mul_pos (by norm_num) hp.1) (sub_pos.mpr hp.2)
  positivity

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
