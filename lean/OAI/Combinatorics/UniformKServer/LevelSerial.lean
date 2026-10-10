import Mathlib
import OAI.Combinatorics.UniformKServer.LevelTierEdits
import OAI.Combinatorics.UniformKServer.LevelTierLedger
import OAI.Combinatorics.UniformKServer.LevelHeavyEdits

namespace OAI

noncomputable section

/-! The source edit order: first heavy, then tiers in order. Each tier ledger
retains its higher-priority shadow and its old lower-priority suffix. -/
namespace UniformKServer.LevelMap.Data
open Finset FiniteProbability FirstStructure
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}
local instance indexDecEqSerial : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEqSerial : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEqSerial : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def serialEdit (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X)
    (e : Tape D→Option (Label D)) (ω : Tape D) : ℝ :=
  editSum (fun i=>D.tierKey ω n.val i p) (fun i=>D.tierKey ω (n.val+1) i p)
    (Sum.inr (Sum.inr p)) (e ω) is

def tierPotential (D : Data X N H) (is : List (Fin H)) (t : ℕ) (p : X) (ω : Tape D) : ℝ :=
  (is.map fun i=>D.tierUncovered ω t i p).sum

theorem serial_ledger (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p q : X)
    (e : Tape D→Option (Label D)) (shadow : Prop) (he : shadow→∀ ω,(e ω).isSome=true)
    (b : Fin H→ℝ)
    (h : ∀ i∈is, ∀ (earlier : Tape D→Option (Label D)) (later : Tape D→Label D),
      (shadow→∀ ω,(earlier ω).isSome=true)→
      D.r*D.law.expect (fun ω=>D.tierEdit n i p earlier later ω+
        D.tierUncovered ω (n.val+1) i q-D.tierUncovered ω n.val i p)≤b i) :
    D.r*D.law.expect (fun ω=> D.serialEdit n is p e ω+
      D.tierPotential is (n.val+1) q ω-D.tierPotential is n.val p ω)≤(is.map b).sum := by
  induction is generalizing e with
  | nil => simp only [serialEdit,editSum,tierPotential,List.map_nil,List.sum_nil,add_zero,sub_zero,Law.expect_const,mul_zero,le_refl]
  | cons i is ih =>
    let later : Tape D→Label D := fun ω=>
      (first is (fun j=>D.tierKey ω n.val j p)).getD (Sum.inr (Sum.inr p))
    let e' : Tape D→Option (Label D) := fun ω=>(e ω).or (D.tierKey ω (n.val+1) i p)
    have he' : shadow→∀ ω,(e' ω).isSome=true := by
      intro hs ω
      have ho := he hs ω
      cases hω : e ω with
      | none => simp [hω] at ho
      | some l => simp only [e',hω,Option.some_or,Option.isSome_some]
    have head := h i (List.mem_cons_self ..) e later he
    have tail := ih e' he' (fun j hj=>h j (List.mem_cons_of_mem _ hj))
    have heq (ω : Tape D) : D.serialEdit n (i::is) p e ω+
        D.tierPotential (i::is) (n.val+1) q ω-D.tierPotential (i::is) n.val p ω=
        (D.tierEdit n i p e later ω+D.tierUncovered ω (n.val+1) i q-D.tierUncovered ω n.val i p)+
        (D.serialEdit n is p e' ω+D.tierPotential is (n.val+1) q ω-D.tierPotential is n.val p ω) := by
      dsimp only [serialEdit,editSum,tierPotential,List.map_cons,List.sum_cons,tierEdit,e',later]
      simp only [List.map_cons,List.sum_cons]
      ring
    simp_rw [heq]
    rw [Law.expect_add,mul_add,List.map_cons,List.sum_cons]
    exact add_le_add head tail

theorem serial_stationary (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X)
    (γ : ℝ) (hγ : γ≤1/2) (e : Tape D→Option (Label D))
    (he : D.heavy n→dist (D.center n) p≤γ*D.r→∀ ω,(e ω).isSome=true) :
    D.r*D.law.expect (fun ω=>D.serialEdit n is p e ω+
      D.tierPotential is (n.val+1) p ω-D.tierPotential is n.val p ω)≤
        (is.map fun i=>D.stationaryBudget γ n i p).sum := by
  apply serial_ledger D n is p p e (D.heavy n ∧ dist (D.center n) p≤γ*D.r)
    (fun h=>he h.1 h.2)
  intro i _ earlier later he'
  exact D.stationary_ledger n i p γ hγ earlier later (fun hh hp=>he' ⟨hh,hp⟩)

theorem serial_mover (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X)
    (γ : ℝ) (e : Tape D→Option (Label D))
    (he : D.heavy n→dist (D.center n) p≤γ*D.r→∀ ω,(e ω).isSome=true) :
    D.r*D.law.expect (fun ω=>D.serialEdit n is p e ω+
      D.tierPotential is (n.val+1) (D.center n) ω-D.tierPotential is n.val p ω)≤
        (is.map fun i=>D.moverBudget γ n i p).sum := by
  apply serial_ledger D n is p (D.center n) e (D.heavy n ∧ dist (D.center n) p≤γ*D.r)
    (fun h=>he h.1 h.2)
  intro i _ earlier later he'
  exact D.mover_ledger n i p γ earlier later (fun hh hp=>he' ⟨hh,hp⟩)

theorem actual_shadow (D : Data X N H) (n : Fin N) (p : X) (γ : ℝ) (hγ : γ≤1/2)
    (hh : D.heavy n) (hp : dist (D.center n) p≤γ*D.r) (ω : Tape D) :
    (D.heavyKey ω (n.val+1) p).isSome=true := by
  obtain ⟨l,_,hl⟩ := D.heavy_agreement n hh ω p (by nlinarith [D.positive])
  simp only [hl,Option.isSome_some]

theorem key_edit_bound (D : Data X N H) (n : Fin N) (is : List (Fin H)) (p : X) (ω : Tape D) :
    indicator (D.key is ω n.val p) (D.key is ω (n.val+1) p)≤
      D.heavyEdit n p ω+D.serialEdit n is p (fun z=>D.heavyKey z (n.val+1) p) ω := by
  let z : Label D := Sum.inr (Sum.inr p)
  let f := fun i=>D.tierKey ω n.val i p
  let g := fun i=>D.tierKey ω (n.val+1) i p
  have h := indicator_triangle (D.key is ω n.val p)
    (overlayKey (D.heavyKey ω (n.val+1) p) is f z) (D.key is ω (n.val+1) p)
  have hm := indicator_map (fun e=>overlayKey e is f z)
    (D.heavyKey ω n.val p) (D.heavyKey ω (n.val+1) p)
  have hs := serial_bound (D.heavyKey ω (n.val+1) p) is f g z
  exact h.trans (add_le_add hm hs)

end UniformKServer.LevelMap.Data

end

end OAI
