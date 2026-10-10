import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.ProducedCapExclusion

namespace OAI

namespace SharpRamseyFive.ReverseCap
open FiniteEntropy
open scoped Classical BigOperators
variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def ambientCapLaw (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (n : ℕ) (q M : ℝ) : Law (Option (Finset A)) :=
  map (map (iid (iid (uniformOn W hW) (Fin n)) (Fin (uniformCutoff q C W n)))
    (firstAccepted (validationRows R S U C n q M)))
    (Option.map (cap R Finset.univ q))

lemma cap_inter (R : A→B→Prop) (U : Finset A) {n : ℕ} (q : ℝ) (row : Fin n→B) :
    U∩cap R Finset.univ q row=cap R U q row := by
  ext a
  simp [cap]

lemma ambientCapLaw_restrict (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (n : ℕ) (q M : ℝ) :
    map (ambientCapLaw R S U C W hW n q M) (Option.map fun Y=>U∩Y)=
      publicCapLaw R S U C W hW n q M := by
  unfold ambientCapLaw publicCapLaw
  rw [map_comp]
  congr 1
  funext row
  cases row with
  | none => rfl
  | some row =>
    change some (U∩cap R Finset.univ q row)=some (cap R U q row)
    rw [cap_inter]

lemma ambientCapLaw_none (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (n : ℕ) (q M : ℝ) :
    ambientCapLaw R S U C W hW n q M none=publicCapLaw R S U C W hW n q M none := by
  simp [ambientCapLaw,publicCapLaw,map,Fintype.sum_option]

lemma ambientCapLaw_positive (R : A→B→Prop) (S U : Finset A)
    (C W : Finset B) (hW : W.Nonempty) (n : ℕ) (q M : ℝ)
    (Y : Finset A) (hY : 0<ambientCapLaw R S U C W hW n q M (some Y)) :
    ValidCap S U M (U∩Y) := by
  obtain ⟨row,hr,he⟩ := map_positive _ _ _ hY
  cases row with
  | none => simp at he
  | some row =>
    have he' : cap R Finset.univ q row=Y := Option.some.inj he
    subst Y
    rw [cap_inter]
    obtain ⟨t,_,ht⟩ := map_positive _ _ _ hr
    obtain ⟨i,hi,hm⟩ := firstAccepted_index _ _ ht
    exact ⟨cap_subset _ _ _ _,(Finset.mem_filter.mp hm).2.2⟩

theorem ambientCapLaw_domination (R : A→B→Prop) (S U : Finset A)
    (C X W : Finset B) (hC : C.Nonempty) (hW : W.Nonempty)
    (hCW : C⊆W) (hCX : C⊆X) (n : ℕ) (hn : 0<n)
    (q c M : ℝ) (hq : 0<q) (hc : 0<c) (hsize : c*X.card≤C.card)
    (hE : (9:ℝ)/10≤eventMass (iid (uniformOn C hC) (Fin n))
      (validationRows R S U C n q M)) (a : A) :
    eventMass (ambientCapLaw R S U C W hW n q M) (Finset.univ.filter (Excludes a))≤
      (50*q/(9*c))*(((X.filter (R a)).card:ℝ)/X.card) := by
  have heq : eventMass (ambientCapLaw R S U C W hW n q M)
      (Finset.univ.filter (Excludes a))=
      freshRejection (fun b a=>R a b) q W hW n (uniformCutoff q C W n)
        (validationRows R S U C n q M) a := by
    unfold ambientCapLaw freshRejection
    rw [eventMass_map_filter]
    apply congrArg (eventMass _)
    apply Finset.ext
    intro row
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ,true_and,Finset.mem_image]
    cases row with
    | none => simp only [Option.map_none,Excludes,Option.some_ne_none,and_false,exists_false]
    | some row =>
      simp only [Option.map_some,Excludes,Finset.mem_filter,cap,Finset.mem_univ,true_and,
        not_lt,Option.some.injEq,exists_eq_right]
      change hits (neighbors R a) row ≥ (n:ℝ)/(5*q) ↔ _
      rw [show (n:ℝ)/(5*q)=(1/(5*q))*n by ring]
      rfl
  rw [heq]
  have h := fresh_test_domination C X W (Finset.univ.filter (R a)) hC hW hCW hCX
    q c hq hc hsize n (uniformCutoff q C W n) hn (uniformCutoff_pos q hq C W hC hW n)
    (validationRows R S U C n q M) (fun row hr=>(Finset.mem_filter.mp hr).2.1) hE
  have he : (Finset.univ.filter (R a))∩X=X.filter (R a) := by ext b;simp [and_comm]
  simpa only [freshRejection,he] using h

end SharpRamseyFive.ReverseCap

end OAI
