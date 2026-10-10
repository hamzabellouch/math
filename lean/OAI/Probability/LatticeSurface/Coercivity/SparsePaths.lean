import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparsePaths

attribute [local instance] Classical.propDecidable

lemma walk_sum_abs {W : Type*} (G : SimpleGraph W) (h : W → ℝ)
    {x y : W} (p : G.Walk x y) :
    |h x-h y| ≤ (p.darts.map (fun e => |h e.fst-h e.snd|)).sum := by
  induction p with
  | nil => simp
  | @cons x y z hxy p ih =>
    simpa only [SimpleGraph.Walk.darts_cons,List.map_cons,List.sum_cons] using
      (abs_sub_le (h x) (h y) (h z)).trans (add_le_add le_rfl ih)

def dartsMap {W E : Type*} {G : SimpleGraph W} (v : W → E) (e : G.Dart) : E × E :=
  (v e.fst, v e.snd)

lemma dartsMap_injective {W E : Type*} {G : SimpleGraph W} (v : W → E)
    (hv : Function.Injective v) : Function.Injective (dartsMap (G := G) v) := by
  intro e f hef
  apply SimpleGraph.Dart.ext
  exact Prod.ext (hv (congrArg Prod.fst hef)) (hv (congrArg Prod.snd hef))

def edges {W E : Type*} [DecidableEq E] {G : SimpleGraph W} (v : W → E)
    {x y : W} (p : G.Walk x y) : Finset (E × E) :=
  (p.darts.map (dartsMap v)).toFinset

lemma card_edges {W E : Type*} [DecidableEq E] {G : SimpleGraph W}
    (v : W → E) (hv : Function.Injective v) {x y : W}
    (p : G.Walk x y) (hp : p.IsPath) : (edges v p).card = p.length := by
  rw [edges,List.toFinset_card_of_nodup]
  · simp
  · exact (p.darts_nodup_of_support_nodup hp.support_nodup).map (dartsMap_injective v hv)

lemma sum_edges {W E : Type*} [DecidableEq E] {G : SimpleGraph W}
    (v : W → E) (hv : Function.Injective v) {x y : W}
    (p : G.Walk x y) (hp : p.IsPath) (h : E → ℝ) :
    |h (v x)-h (v y)| ≤ ∑ e ∈ edges v p, |h e.1-h e.2| := by
  have hn := (p.darts_nodup_of_support_nodup hp.support_nodup).map (dartsMap_injective v hv)
  rw [edges,List.sum_toFinset _ hn]
  simpa only [List.map_map,Function.comp_def,dartsMap] using walk_sum_abs G (h ∘ v) p

lemma cap_count {E : Type*} [DecidableEq E] (F : Finset E) (a : E → ℝ)
    (ε : ℝ) (hε : 0 < ε) (ha : ∀ e ∈ F, a e ≤ 1)
    (hbad : (1-ε/2)*(F.card : ℝ) < ∑ e ∈ F, a e) :
    (F.card : ℝ)/2 ≤ ((F.filter (fun e => 1-ε ≤ a e)).card : ℝ) := by
  have hup : ∑ e ∈ F, a e ≤ (1-ε)*(F.card : ℝ) +
      ε*((F.filter (fun e => 1-ε ≤ a e)).card : ℝ) := by
    calc
      _ ≤ ∑ e ∈ F, ((1-ε) + if 1-ε ≤ a e then ε else 0) := by
        apply Finset.sum_le_sum
        intro e he
        split_ifs with hh
        · linarith [ha e he]
        · linarith
      _ = _ := by
        simp [Finset.sum_add_distrib,Finset.sum_ite,Finset.sum_const,mul_comm]
        ring
  nlinarith

end SparsePaths

end

end OAI
