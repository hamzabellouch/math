import Mathlib
import OAI.Combinatorics.TriangleRemoval.Coupling.UnitTime

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave
section Reindex
variable {ι τ ι' τ' : Type*} [Fintype ι] [Fintype τ] [Fintype ι'] [Fintype τ']
  [DecidableEq ι] [DecidableEq τ] [DecidableEq ι'] [DecidableEq τ']
  (H : τ → Finset ι) (H' : τ' → Finset ι') (f : ι' ↪ ι) (g : τ' ↪ τ)
  (hH : ∀ T, H (g T) = (H' T).map f)
  (hlocal : ∀ e : ι', ∀ T, f e ∈ H T → ∃ T', g T' = T)
include hH hlocal

omit [Fintype ι] [Fintype ι'] in

theorem messageCandidates_reindex (e : ι') (p : Option τ') :
    messageCandidates H (f e) (p.map g) = (messageCandidates H' e p).map g := by
  ext T
  simp only [messageCandidates, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_map]
  constructor
  · rintro ⟨he, hp⟩
    obtain ⟨T', rfl⟩ := hlocal e T he
    refine ⟨T', ⟨?_, ?_⟩, rfl⟩
    · rw [hH] at he
      exact Finset.mem_map.mp he |>.elim (fun _ hz => f.injective hz.2 ▸ hz.1)
    · intro hh
      exact hp (by rw [← hh]; rfl)
  · rintro ⟨T', ⟨he, hp⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hH]
      exact Finset.mem_map.mpr ⟨e, he, rfl⟩
    · intro hh
      apply hp
      cases p with
      | none => contradiction
      | some S =>
        simp only [Option.map_some, Option.some.injEq] at hh ⊢
        exact g.injective hh

omit [Fintype ι] [Fintype ι'] in

theorem cavityDepth_reindex (k : ℕ) (e : ι') (p : Option τ') (t : ℝ) :
    cavityDepth H k (f e) (p.map g) t = cavityDepth H' k e p t := by
  induction k generalizing e p t with
  | zero => rfl
  | succ k ih =>
    simp only [cavityDepth, cavityOperator, messageCandidates_reindex H H' f g hH hlocal,
      Finset.prod_map]
    apply Finset.prod_congr rfl
    intro T _
    congr 1
    unfold messageIntegral
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [hH, ← Finset.map_erase, Finset.prod_map]
    apply Finset.prod_congr rfl
    intro e' _
    exact ih e' (some T) s

theorem cavityLimit_reindex (e : ι') (p : Option τ') (t : ℝ) :
    cavityLimit H (f e) (p.map g) t = cavityLimit H' e p t := by
  apply tendsto_nhds_unique (tendsto_cavityDepth H (f e) (p.map g) t)
  convert tendsto_cavityDepth H' e p t using 1
  funext k
  exact cavityDepth_reindex H H' f g hH hlocal k e p t

end Reindex
end SharpTerminalLeave

end

end OAI
