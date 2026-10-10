import OAI.Analysis.CircleDomains.Selection.FiniteChainPotential

namespace OAI

/-! Every finite chain in an increasing union already belongs to one finite
stage. This passes the retained barrier lower bound to all installed levels. -/

open Set
open scoped ENNReal

namespace CircleDomainRigidity

namespace PaidChain

variable {X : Type*} {R S : X → X → ℝ≥0∞ → Prop}

theorem mono_relation (hRS : ∀x y c, R x y c → S x y c)
    {x y : X} {c : ℝ≥0∞} (hc : PaidChain R x y c) : PaidChain S x y c := by
  induction hc with
  | refl x => exact .refl x
  | cons h _ ih => exact .cons (hRS _ _ _ h) ih

theorem exists_stage {R : ℕ → X → X → ℝ≥0∞ → Prop}
    (hmono : ∀n k, n ≤ k → ∀x y c, R n x y c → R k x y c)
    {x y : X} {c : ℝ≥0∞}
    (hc : PaidChain (fun x y c => ∃n, R n x y c) x y c) :
    ∃n, PaidChain (R n) x y c := by
  induction hc with
  | refl x => exact ⟨0, .refl x⟩
  | @cons x y z a b h _ ih =>
      obtain ⟨n, hn⟩ := h
      obtain ⟨k, hk⟩ := ih
      exact ⟨max n k, .cons (hmono n _ (le_max_left _ _) _ _ _ hn)
        (hk.mono_relation (hmono k _ (le_max_right _ _)))⟩

end PaidChain

theorem increasing_union_chain_lower_bound {X : Type*}
    (R : ℕ → X → X → ℝ≥0∞ → Prop)
    (hmono : ∀n k, n ≤ k → ∀x y c, R n x y c → R k x y c)
    (F H : Set X) (β : ℝ≥0∞)
    (hlower : ∀n x, x ∈ F → ∀y, y ∈ H → ∀c, PaidChain (R n) x y c → β ≤ c) :
    ∀x ∈ F, ∀y ∈ H, ∀c,
      PaidChain (fun x y c => ∃n, R n x y c) x y c → β ≤ c := by
  intro x hx y hy c hc
  obtain ⟨n, hn⟩ := hc.exists_stage hmono
  exact hlower n x hx y hy c hn

end CircleDomainRigidity

end OAI
