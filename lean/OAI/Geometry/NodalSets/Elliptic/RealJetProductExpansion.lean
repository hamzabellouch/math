import OAI.Geometry.NodalSets.Elliptic.RealFiniteJetSquare

namespace OAI

namespace Yau.Geometry
open Yau.Analysis
open scoped ContDiff
noncomputable section

def realJetProductSum (a b : Yau.Jets.Coord → ℝ)
    (ts : List (List (Fin 4) × List (Fin 4))) (x : Yau.Jets.Coord) : ℝ :=
  (ts.map (fun t ↦ partialJet a t.1 x * partialJet b t.2 x)).sum

lemma realJetProductSum_smooth (a b : Yau.Jets.Coord → ℝ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (ts : List (List (Fin 4) × List (Fin 4))) :
    ContDiff ℝ ∞ (realJetProductSum a b ts) := by
  induction ts with
  | nil => exact contDiff_const
  | cons t ts ih =>
    exact ((partialJet_smooth a ha t.1).mul (partialJet_smooth b hb t.2)).add ih

lemma realJetProductSum_partial (a b : Yau.Jets.Coord → ℝ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (ts : List (List (Fin 4) × List (Fin 4))) (l : Fin 4) (x : Yau.Jets.Coord) :
    Yau.coordPartial (realJetProductSum a b ts) x l =
      realJetProductSum a b (ts.map (fun t ↦ (l::t.1,t.2))) x +
      realJetProductSum a b (ts.map (fun t ↦ (t.1,l::t.2))) x := by
  induction ts with
  | nil =>
    change Yau.coordPartial (fun _ ↦ (0:ℝ)) x l = 0+0
    simp [Yau.coordPartial]
  | cons t ts ih =>
    change Yau.coordPartial (fun y ↦ partialJet a t.1 y*partialJet b t.2 y +
      realJetProductSum a b ts y) x l = _
    rw [Yau.real_coordPartial_add _ _
      ((partialJet_smooth a ha t.1).mul (partialJet_smooth b hb t.2))
      (realJetProductSum_smooth a b ha hb ts),
      Yau.real_coordPartial_mul _ _ (partialJet_smooth a ha t.1) (partialJet_smooth b hb t.2),ih]
    simp only [realJetProductSum,List.map_cons,List.sum_cons,partialJet,Yau.coordPartial]
    ring

def realJetErrorTerms (extra : List (Fin 4)) :
    List (Fin 4) → List (List (Fin 4) × List (Fin 4))
  | [] => []
  | l::ds =>
    (realJetErrorTerms extra ds).map (fun t ↦ (l::t.1,t.2)) ++
    (realJetErrorTerms extra ds).map (fun t ↦ (t.1,l::t.2)) ++ [([l],extra++ds)]

lemma realJetErrorTerms_orders (extra ds : List (Fin 4)) (he : extra.length ≤ 1)
    (t : List (Fin 4) × List (Fin 4)) (ht : t ∈ realJetErrorTerms extra ds) :
    t.1.length ≤ ds.length ∧ t.2.length ≤ ds.length := by
  induction ds generalizing t with
  | nil => simp [realJetErrorTerms] at ht
  | cons l ds ih =>
    simp only [realJetErrorTerms,List.mem_append,List.mem_map,List.mem_singleton] at ht
    rcases ht with (⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩) | rfl
    · have h := ih s hs; simp only [List.length_cons]; omega
    · have h := ih s hs; simp only [List.length_cons]; omega
    · simp only [List.length_cons,List.length_nil,List.length_append]; omega

lemma realJetErrorTerms_length (extra ds : List (Fin 4)) :
    (realJetErrorTerms extra ds).length ≤ 3^ds.length := by
  induction ds with
  | nil => simp [realJetErrorTerms]
  | cons l ds ih =>
    have hp : 1 ≤ (3:ℕ)^ds.length := Nat.one_le_pow _ _ (by decide)
    simp only [realJetErrorTerms,List.length_append,List.length_map,List.length_cons,
      List.length_nil,pow_succ]
    omega

lemma realJetProductSum_error_cons (a b : Yau.Jets.Coord → ℝ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (extra ds : List (Fin 4)) (l : Fin 4) (x : Yau.Jets.Coord) :
    realJetProductSum a b (realJetErrorTerms extra (l::ds)) x =
      Yau.coordPartial (realJetProductSum a b (realJetErrorTerms extra ds)) x l +
        Yau.coordPartial a x l * partialJet b (extra++ds) x := by
  rw [realJetProductSum_partial a b ha hb]
  simp [realJetErrorTerms,realJetProductSum,partialJet,Yau.coordPartial,add_assoc]

end
end Yau.Geometry

end OAI
