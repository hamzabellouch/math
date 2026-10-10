import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.FiniteEventEntropy
import OAI.Probability.CriticalPercolation.Entropy.BinaryOutputEntropy

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits

variable {V E : Type*} [Fintype V] [Fintype E]
local instance eventBoundFinDec (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

lemma prob_bits (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (P : Set E → Prop) :
    (∑ ω : E → Bool, if P (configuration ω) then FiniteProduct.density (QueryTree.bitWeight p) ω else 0) =
      prob w P := by
  have hw : QueryTree.bitWeight p = fun e (b : Bool) => w e (b = true) := by
    funext e b
    cases b <;> simp [QueryTree.bitWeight,h0,h1]
  have he := expect_configuration w (fun η => if P η then (1:ℝ) else 0)
  rw [← hw] at he
  simpa only [expect,prob,mul_ite,mul_one,mul_zero] using he

theorem conditioned_event_bound (horder : LazyDFS.GoodDarts G order)
    (ho : LazyDFS.Exhaustive G order) (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0<c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    let t := interval d n (fromWords (E := E) n (fun j => (D j).1) (fun _ => none))
    0 < prob w (endpointEvent G (x t.1) (x t.2) s) ∧
      -Real.log (prob w (endpointEvent G (x t.1) (x t.2) s)) ≤
      (4*(16/(2*p*(1-p)))+6)*constructionCost G order d x p w c s n D +
        (2*(16/(2*p*(1-p)))+5)*n*Real.log 4 := by
  dsimp only
  let t := interval d n (fromWords (E := E) n (fun j => (D j).1) (fun _ => none))
  let P := endpointEvent G (x t.1) (x t.2) s
  let Q := conditionedMass G order d x p w s n D
  let f : ((E → Bool) × (Fin n → Option E)) → (E → Bool) := fun z => stage n D z.1 z.2 n
  have hQ := conditionedMass_nonneg G order d x p w s n hp h0 h1 hδ D hD
  have hQ1 : ∑ z, Q z=1 := by
    have he := conditionedMass_normalized G order d x p w s n D hD
    refine Eq.trans ?_ he
    apply Finset.sum_congr
    · ext z; simp only [Finset.mem_univ]
    · intro z _; rfl
  have hh := supported_event_entropy (pushMass f Q) (FiniteProduct.density (QueryTree.bitWeight p))
    (pushMass_nonneg f Q hQ) ((pushMass_sum f Q).trans hQ1)
    (fun ω => Finset.prod_pos fun e _ => QueryTree.bitWeight_pos hp e (ω e))
    {ω | P (configuration ω)}
    (pushMass_supported Q f {ω | P (configuration ω)} (fun z hz =>
      stage_endpointEvent G order d x p w s n D z.1 z.2 hz))
  have hb := prob_bits p w h0 h1 P
  change (∑ ω : E → Bool, if P (configuration ω) then FiniteProduct.density (QueryTree.bitWeight p) ω else 0) = _ at hb
  change 0 < (∑ ω : E → Bool, if P (configuration ω) then FiniteProduct.density (QueryTree.bitWeight p) ω else 0) ∧ _ at hh
  rw [hb] at hh
  have hl := conditioned_output_entropy G order d x p w s n D horder ho hd hp h0 h1 hc hc1 hconn hδ hD
  refine ⟨hh.1,?_⟩
  have he := hh.2.trans hl
  simp only [Set.mem_ofPred_eq] at he
  rw [hb] at he
  simpa only [one_div,Real.log_inv] using he

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
