import OAI.Combinatorics.ContingencyTables.Machines.DirectedBFSProgram

namespace OAI

/-! # Polynomial size of the materialized BFS path store -/

namespace ContingencyTables.DirectedBFSBounds

open MatchingFPRAS.TreeTyped DirectedBFSCode

def Bounded (P : Store) (B : ℕ) : Prop := ∀ o∈P,weight o≤B

lemma none_weight : weight (none : Option (List ℕ))≤5 := by decide

lemma lookup_weight (P : Store) (B : ℕ) (hB : 5≤B) (hP : Bounded P B) (v : ℕ) :
    weight (lookup P v)≤B := by
  by_cases hv : v<P.length
  · have he : lookup P v=P[v] := by simp [lookup,List.getD_eq_getElem?_getD,hv]
    rw [he]
    exact hP _ (List.getElem_mem hv)
  · have he : lookup P v=none := by simp [lookup,List.getD_eq_getElem?_getD,hv]
    rw [he]
    exact none_weight.trans hB

lemma append_weight (xs : List ℕ) (v : ℕ) :
    weight (Option.some (xs++[v]))=weight (Option.some xs)+weight v+1 := by
  change weight (true,xs++[v])=weight (true,xs)+weight v+1
  have h := weight_append xs [v]
  simp only [weight_cons,weight_nil] at h
  simp only [weight_prod]
  omega

lemma row_weight (g : Graph) (P : Store) (B : ℕ) (hB : 5≤B)
    (hP : Bounded P B) (v : ℕ) (hv : v<g.length) :
    weight (roundRow g P v)≤B+4*g.length+2 := by
  have hwv : weight v≤4*g.length+1 := (weight_nat_numeric v).trans (by omega)
  cases hc : lookup P v with
  | some xs =>
    have h := lookup_weight P B hB hP v
    simp only [hc] at h
    simpa only [roundRow,hc] using h.trans (by omega)
  | none =>
    cases hp : predecessor g P v with
    | none =>
      simpa only [roundRow,hc,hp,Option.bind_none] using none_weight.trans (by omega)
    | some u =>
      cases hu : lookup P u with
      | none =>
        simpa only [roundRow,hc,hp,Option.bind_some,hu,Option.map_none] using
          none_weight.trans (by omega)
      | some xs =>
        have h := lookup_weight P B hB hP u
        simp only [hu] at h
        simp only [roundRow,hc,hp,Option.bind_some,hu,Option.map_some,append_weight]
        omega

lemma round_bounded (g : Graph) (P : Store) (B : ℕ) (hB : 5≤B)
    (hP : Bounded P B) : Bounded (round g P) (B+4*g.length+2) := by
  intro o ho
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ho
  exact row_weight g P B hB hP v (List.mem_range.mp hv)

lemma round_length (g : Graph) (P : Store) : (round g P).length=g.length := by
  simp [DirectedBFSCode.round]

lemma fold_bounded (g : Graph) (P : Store) (B : ℕ) (hB : 5≤B)
    (hP : Bounded P B) (steps : List ℕ) :
    Bounded (steps.foldl (fun P _=>round g P) P) (B+steps.length*(4*g.length+2)) := by
  induction steps generalizing P B with
  | nil => simpa using hP
  | cons a steps ih =>
    have h := ih (round g P) (B+4*g.length+2) (by omega) (round_bounded g P B hB hP)
    have he : B+(a::steps).length*(4*g.length+2)=
        B+4*g.length+2+steps.length*(4*g.length+2) := by
      simp only [List.length_cons]
      ring
    rw [List.foldl_cons,he]
    exact h

lemma fold_length_le (g : Graph) (P : Store) (steps : List ℕ) :
    (steps.foldl (fun P _=>round g P) P).length≤ max P.length g.length := by
  induction steps generalizing P with
  | nil => exact le_max_left _ _
  | cons a steps ih =>
    have h := ih (round g P)
    simp only [List.foldl_cons]
    exact h.trans (by rw [round_length,max_self]; exact le_max_right _ _)

lemma store_weight (P : Store) (B : ℕ) (hP : Bounded P B) :
    weight P≤P.length*(B+1)+1 := by
  have h := weight_map_bound (as:=P) (f:=id) (N:=B) hP
  simpa only [List.map_id] using h

lemma initial_bounded (g : Graph) (s : ℕ) : Bounded (initial g s) (weight s+10) := by
  intro o ho
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp ho
  by_cases h : v=s
  · simp only [h,ite_true]
    change weight (true,[s])≤weight s+10
    have hb := weight_bool_le true
    simp only [weight_prod,weight_cons,weight_nil]
    omega
  · simpa only [h,ite_false] using none_weight.trans (by omega)

lemma initial_length (g : Graph) (s : ℕ) : (initial g s).length=g.length := by
  simp [initial]

end ContingencyTables.DirectedBFSBounds

end OAI
