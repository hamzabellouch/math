import Mathlib
import OAI.Combinatorics.HoneycombCorridor.Basic

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

def reverseGerm (g : Germ) : Germ := (neighbor g.1 g.2, g.2)

def reverseTurns (w : List Bool) : List Bool := w.reverse.map Bool.not

@[simp] theorem reverseGerm_reverseGerm (g : Germ) :
    reverseGerm (reverseGerm g) = g := by
  rcases g with ⟨v,k⟩
  simp [reverseGerm]

@[simp] theorem reverseTurns_reverseTurns (w : List Bool) :
    reverseTurns (reverseTurns w) = w := by
  simp [reverseTurns, List.map_reverse, List.map_map, Function.comp_def]

@[simp] theorem reverseTurns_nil : reverseTurns [] = [] := rfl

@[simp] theorem reverseTurns_cons (b : Bool) (w : List Bool) :
    reverseTurns (b :: w) = reverseTurns w ++ [!b] := by
  simp [reverseTurns]

@[simp] theorem terminalGerm_append (g : Germ) (u w : List Bool) :
    terminalGerm g (u ++ w) = terminalGerm (terminalGerm g u) w := by
  induction u generalizing g with
  | nil => rfl
  | cons b u ih => simpa [terminalGerm] using ih (advance g b)

@[simp] theorem traced_append (g : Germ) (u w : List Bool) :
    traced g (u ++ w) = traced g u ++ traced (terminalGerm g u) w := by
  induction u generalizing g with
  | nil => rfl
  | cons b u ih => simp [traced, terminalGerm, ih]

@[simp] theorem advance_reverse (g : Germ) (b : Bool) :
    advance (reverseGerm (advance g b)) (!b) = reverseGerm g := by
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [advance, outgoingSlot, reverseGerm]

@[simp] theorem terminalGerm_reverse (g : Germ) (w : List Bool) :
    terminalGerm (reverseGerm (terminalGerm g w)) (reverseTurns w) = reverseGerm g := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    rw [reverseTurns_cons, terminalGerm_append]
    simp only [terminalGerm, ih, advance_reverse]

@[simp] theorem traced_reverse (g : Germ) (w : List Bool) :
    traced (reverseGerm (terminalGerm g w)) (reverseTurns w) = (traced g w).reverse := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    rw [reverseTurns_cons, traced_append]
    simp only [terminalGerm, ih, terminalGerm_reverse, traced, List.reverse_cons]
    simp [reverseGerm, advance]

@[simp] theorem stepWeight_not (b : Bool) :
    stepWeight (!b) = (starRingEnd ℂ) (stepWeight b) := by
  have ha : turnAngle (!b) = -turnAngle b := by cases b <;> simp [turnAngle]
  rw [stepWeight, ha, stepWeight, map_mul, ← Complex.exp_conj]
  simp only [Complex.conj_ofReal, map_mul, Complex.conj_I]
  congr 1
  push_cast
  ring_nf

@[simp] theorem wordWeight_reverse (w : List Bool) :
    wordWeight (reverseTurns w) = (starRingEnd ℂ) (wordWeight w) := by
  unfold wordWeight reverseTurns
  rw [List.map_map]
  simp only [Function.comp_def, stepWeight_not]
  rw [show (fun b => (starRingEnd ℂ) (stepWeight b)) =
    (starRingEnd ℂ) ∘ stepWeight from rfl, ← List.map_map, map_list_prod]
  simp only [List.map_reverse, List.prod_reverse]

theorem stopped_of_trace (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hD : ∀ v ∈ traced g w, v ∈ D)
    (ht : (terminalGerm g w).1 ∉ D) : Stopped D g w := by
  induction w generalizing D g with
  | nil => exact ht
  | cons b w ih =>
    simp only [traced, List.nodup_cons] at hN
    refine ⟨hD _ (by simp [traced]), ih _ _ hN.2 ?_ ?_⟩
    · intro v hv
      exact Finset.mem_erase.mpr ⟨fun he => hN.1 (he ▸ hv),
        hD _ (by simp [traced, hv])⟩
    · exact fun hm => ht (Finset.mem_of_mem_erase hm)

def IsExcursion (D : Finset Vertex) (e : Germ × List Bool) : Prop :=
  e.1.1 ∈ D ∧ (reverseGerm e.1).1 ∉ D ∧ Stopped D e.1 e.2 ∧
    (terminalGerm e.1 e.2).1 ∉ D

noncomputable def excursions (D : Finset Vertex) : Finset (Germ × List Bool) := by
  classical
  exact ((D.product Finset.univ).biUnion fun g =>
    (leaves D g).image fun w => (g, w)).filter (IsExcursion D)

@[simp] theorem mem_excursions (D : Finset Vertex) (e : Germ × List Bool) :
    e ∈ excursions D ↔ IsExcursion D e := by
  classical
  rw [excursions, Finset.mem_filter]
  constructor
  · exact And.right
  · intro he
    refine ⟨?_, he⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨e.1, Finset.mem_product.mpr ⟨he.1, Finset.mem_univ _⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨e.2, (mem_leaves_iff _ _ _).mpr he.2.2.1, rfl⟩

def reverseExcursion (e : Germ × List Bool) : Germ × List Bool :=
  (reverseGerm (terminalGerm e.1 e.2), reverseTurns e.2)

@[simp] theorem reverseExcursion_reverseExcursion (e : Germ × List Bool) :
    reverseExcursion (reverseExcursion e) = e := by
  rcases e with ⟨g,w⟩
  simp [reverseExcursion]

theorem IsExcursion.nonempty {D : Finset Vertex} {e : Germ × List Bool}
    (he : IsExcursion D e) : e.2 ≠ [] := by
  intro hw
  exact he.2.2.2 (by simpa [hw, terminalGerm] using he.1)

theorem reverse_first_mem (g : Germ) (w : List Bool) (hw : w ≠ []) :
    (reverseGerm (terminalGerm g w)).1 ∈ traced g w := by
  have hr : reverseTurns w ≠ [] := by
    intro he
    have := congrArg reverseTurns he
    exact hw (by simpa using this)
  obtain ⟨b,u,hu⟩ := List.exists_cons_of_ne_nil hr
  have hm : (reverseGerm (terminalGerm g w)).1 ∈
      traced (reverseGerm (terminalGerm g w)) (reverseTurns w) := by
    simp [hu, traced]
  simpa using hm

theorem IsExcursion.reverse {D : Finset Vertex} {e : Germ × List Bool}
    (he : IsExcursion D e) : IsExcursion D (reverseExcursion e) := by
  obtain ⟨hN,hD⟩ := stopped_traced D e.1 e.2 he.2.2.1
  refine ⟨hD _ (reverse_first_mem _ _ he.nonempty), ?_, ?_, ?_⟩
  · simpa [reverseExcursion] using he.2.2.2
  · apply stopped_of_trace
    · simpa [reverseExcursion] using hN
    · intro v hv
      apply hD v
      simpa [reverseExcursion] using hv
    · simpa [reverseExcursion] using he.2.1
  · simpa [reverseExcursion] using he.2.1

@[simp] theorem reverseExcursion_mem (D : Finset Vertex) (e : Germ × List Bool) :
    reverseExcursion e ∈ excursions D ↔ e ∈ excursions D := by
  rw [mem_excursions, mem_excursions]
  exact ⟨fun he => by simpa using he.reverse, IsExcursion.reverse⟩

noncomputable def visitSum (D : Finset Vertex) (v : Vertex) : ℂ := by
  classical
  exact ∑ e ∈ excursions D, if v ∈ traced e.1 e.2 then wordWeight e.2 else 0

theorem visitSum_conj (D : Finset Vertex) (v : Vertex) :
    (starRingEnd ℂ) (visitSum D v) = visitSum D v := by
  classical
  simp only [visitSum, map_sum]
  simp_rw [apply_ite (starRingEnd ℂ), map_zero]
  apply Finset.sum_bij (fun e _ => reverseExcursion e)
  · intro e he
    exact (reverseExcursion_mem D e).mpr he
  · intro e he f hf hef
    have := congrArg reverseExcursion hef
    simpa using this
  · intro e he
    exact ⟨reverseExcursion e, (reverseExcursion_mem D e).mpr he, by simp⟩
  · intro e he
    simp [reverseExcursion]

theorem visitSum_im (D : Finset Vertex) (v : Vertex) : (visitSum D v).im = 0 :=
  Complex.conj_eq_iff_im.mp (visitSum_conj D v)

noncomputable def markedLeaves (D : Finset Vertex) (g : Germ) (v : Vertex) : ℂ := by
  classical
  exact ∑ w ∈ leaves D g, if v ∈ traced g w then wordWeight w else 0

noncomputable def firstArrival (D : Finset Vertex) (g : Germ) (v : Vertex) : ℂ := by
  classical
  exact ∑ w ∈ leaves (D.erase v) g,
    if (terminalGerm g w).1 = v then wordWeight w else 0

theorem sum_leaves_of_mem (D : Finset Vertex) (g : Germ) (hg : g.1 ∈ D)
    (f : List Bool → ℂ) :
    ∑ w ∈ leaves D g, f w =
      (∑ w ∈ leaves (D.erase g.1) (advance g true), f (true :: w)) +
      (∑ w ∈ leaves (D.erase g.1) (advance g false), f (false :: w)) := by
  rw [leaves, ite_eq_left hg, Finset.sum_union (disjoint_cons_images _ _)]
  congr 1 <;> apply Finset.sum_image <;> intro a ha b hb hab <;>
    exact (List.cons.inj hab).2

theorem leaves_of_not_mem (D : Finset Vertex) (g : Germ) (hg : g.1 ∉ D) :
    leaves D g = {[]} := by rw [leaves, ite_eq_right hg]

theorem markedLeaves_eq_firstArrival (D : Finset Vertex) (g : Germ) (v : Vertex)
    (hv : v ∈ D) : markedLeaves D g v = firstArrival D g v := by
  classical
  induction D using Finset.strongInductionOn generalizing g with
  | _ D ih =>
      by_cases hgv : g.1 = v
      · have hg : g.1 ∈ D := hgv ▸ hv
        have hm : markedLeaves D g v = 1 := by
          unfold markedLeaves
          convert leaf_balance D g using 1
          apply Finset.sum_congr rfl
          intro w hw
          have hne : w ≠ [] := by
            intro he
            subst w
            have := (mem_leaves_iff D g []).mp hw
            exact this hg
          obtain ⟨b,u,rfl⟩ := List.exists_cons_of_ne_nil hne
          simp [traced, hgv]
        rw [hm]
        simp [firstArrival, leaves_of_not_mem (D.erase v) g (by simp [hgv]), terminalGerm, hgv]
      · by_cases hg : g.1 ∈ D
        · have hers : D.erase g.1 ⊂ D := Finset.erase_ssubset hg
          have hve : v ∈ D.erase g.1 := Finset.mem_erase.mpr ⟨Ne.symm hgv, hv⟩
          have hge : g.1 ∈ D.erase v := Finset.mem_erase.mpr ⟨hgv,hg⟩
          unfold markedLeaves firstArrival
          rw [sum_leaves_of_mem _ _ hg, sum_leaves_of_mem _ _ hge]
          simp +instances only [traced, List.mem_cons, eq_comm (a := v), hgv, false_or,
            terminalGerm, wordWeight_cons, ← mul_ite_zero, ← Finset.mul_sum]
          rw [Finset.erase_right_comm (a := v) (b := g.1)]
          change _ =
            (∑ w ∈ leaves ((D.erase g.1).erase v) (advance g true),
              if (terminalGerm (advance g true) w).1 = v then
                stepWeight true * wordWeight w else 0) +
            (∑ w ∈ leaves ((D.erase g.1).erase v) (advance g false),
              if (terminalGerm (advance g false) w).1 = v then
                stepWeight false * wordWeight w else 0)
          simp_rw [← mul_ite_zero, ← Finset.mul_sum]
          change stepWeight true * markedLeaves (D.erase g.1) (advance g true) v +
            stepWeight false * markedLeaves (D.erase g.1) (advance g false) v =
            stepWeight true * firstArrival (D.erase g.1) (advance g true) v +
            stepWeight false * firstArrival (D.erase g.1) (advance g false) v
          rw [ih _ hers _ hve, ih _ hers _ hve]
        · have hge : g.1 ∉ D.erase v := fun h => hg (Finset.mem_of_mem_erase h)
          simp [markedLeaves, firstArrival, leaves_of_not_mem _ _ hg,
            leaves_of_not_mem _ _ hge, traced, terminalGerm, hgv]

noncomputable def exitSum (D : Finset Vertex) (g : Germ) : ℂ := by
  classical
  exact ∑ w ∈ leaves D g, if (terminalGerm g w).1 ∉ D then wordWeight w else 0

noncomputable def collisionSum (D : Finset Vertex) (g : Germ) : ℂ := by
  classical
  exact ∑ w ∈ leaves D g, if (terminalGerm g w).1 ∈ D then wordWeight w else 0

theorem exit_add_collision (D : Finset Vertex) (g : Germ) :
    exitSum D g + collisionSum D g = 1 := by
  classical
  unfold exitSum collisionSum
  rw [← Finset.sum_add_distrib]
  convert leaf_balance D g using 1
  apply Finset.sum_congr rfl
  intro w hw
  by_cases ht : (terminalGerm g w).1 ∈ D <;> simp [ht]

noncomputable def boundaryGerms (D : Finset Vertex) : Finset Germ := by
  classical
  exact (D.product Finset.univ).filter fun g => (reverseGerm g).1 ∉ D

@[simp] theorem mem_boundaryGerms (D : Finset Vertex) (g : Germ) :
    g ∈ boundaryGerms D ↔ g.1 ∈ D ∧ (reverseGerm g).1 ∉ D := by
  classical
  simp [boundaryGerms]

noncomputable def firstArrivals (D : Finset Vertex) (v : Vertex) :
    Finset (Germ × List Bool) := by
  classical
  exact ((boundaryGerms D).biUnion fun g =>
    (leaves (D.erase v) g).image fun w => (g,w)).filter fun e =>
      (terminalGerm e.1 e.2).1 = v

@[simp] theorem mem_firstArrivals (D : Finset Vertex) (v : Vertex)
    (e : Germ × List Bool) : e ∈ firstArrivals D v ↔
    e.1 ∈ boundaryGerms D ∧ Stopped (D.erase v) e.1 e.2 ∧
      (terminalGerm e.1 e.2).1 = v := by
  classical
  simp only [firstArrivals, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨⟨g,hg,w,hw,he⟩,ht⟩
    subst e
    exact ⟨hg, (mem_leaves_iff _ _ _).mp hw,ht⟩
  · rintro ⟨hg,hw,ht⟩
    exact ⟨⟨e.1,hg,e.2,(mem_leaves_iff _ _ _).mpr hw,rfl⟩,ht⟩

noncomputable def rayExits (D : Finset Vertex) (v : Vertex) :
    Finset (Fin 3 × List Bool) := by
  classical
  exact (Finset.univ.biUnion fun k : Fin 3 =>
    (leaves (D.erase v) (neighbor v k,k)).image fun w => (k,w)).filter fun e =>
      (terminalGerm (neighbor v e.1,e.1) e.2).1 ∉ D

@[simp] theorem mem_rayExits (D : Finset Vertex) (v : Vertex)
    (e : Fin 3 × List Bool) : e ∈ rayExits D v ↔
    Stopped (D.erase v) (neighbor v e.1,e.1) e.2 ∧
      (terminalGerm (neighbor v e.1,e.1) e.2).1 ∉ D := by
  classical
  simp only [rayExits, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨⟨k,hk,w,hw,he⟩,ht⟩
    subst e
    exact ⟨(mem_leaves_iff _ _ _).mp hw,ht⟩
  · rintro ⟨hw,ht⟩
    exact ⟨⟨e.1,Finset.mem_univ _,e.2,(mem_leaves_iff _ _ _).mpr hw,rfl⟩,ht⟩

def reversePrefix (e : Germ × List Bool) : Fin 3 × List Bool :=
  ((terminalGerm e.1 e.2).2, reverseTurns e.2)

def reverseRay (v : Vertex) (e : Fin 3 × List Bool) : Germ × List Bool :=
  (reverseGerm (terminalGerm (neighbor v e.1,e.1) e.2), reverseTurns e.2)

theorem reversePrefix_initial {v : Vertex} {e : Germ × List Bool}
    (ht : (terminalGerm e.1 e.2).1 = v) :
    (neighbor v (reversePrefix e).1,(reversePrefix e).1) =
      reverseGerm (terminalGerm e.1 e.2) := by
  simp [reversePrefix,reverseGerm,ht]

theorem reversePrefix_mem {D : Finset Vertex} {v : Vertex}
    {e : Germ × List Bool} (he : e ∈ firstArrivals D v) :
    reversePrefix e ∈ rayExits D v := by
  classical
  obtain ⟨hg,hs,ht⟩ := (mem_firstArrivals D v e).mp he
  obtain ⟨hgD,hgb⟩ := (mem_boundaryGerms D e.1).mp hg
  obtain ⟨hN,hD⟩ := stopped_traced _ _ _ hs
  rw [mem_rayExits,reversePrefix_initial ht]
  constructor
  · apply stopped_of_trace
    · simpa [reversePrefix] using hN
    · intro u hu
      apply hD u
      simpa [reversePrefix] using hu
    · simpa [reversePrefix] using
        (fun hu => hgb (Finset.mem_of_mem_erase hu) : (reverseGerm e.1).1 ∉ D.erase v)
  · simpa [reversePrefix] using hgb

theorem reverseRay_mem {D : Finset Vertex} {v : Vertex} (hv : v ∈ D)
    {e : Fin 3 × List Bool} (he : e ∈ rayExits D v) :
    reverseRay v e ∈ firstArrivals D v := by
  classical
  obtain ⟨hs,ht⟩ := (mem_rayExits D v e).mp he
  obtain ⟨hN,hD⟩ := stopped_traced _ _ _ hs
  rw [mem_firstArrivals,mem_boundaryGerms]
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · by_cases hw : e.2 = []
    · simpa [reverseRay,hw,terminalGerm,reverseGerm] using hv
    · exact Finset.mem_of_mem_erase
        (hD _ (reverse_first_mem (neighbor v e.1,e.1) e.2 hw))
  · simpa [reverseRay] using ht
  · apply stopped_of_trace
    · simpa [reverseRay] using hN
    · intro u hu
      apply hD u
      simpa [reverseRay] using hu
    · simp only [reverseRay, terminalGerm_reverse]
      simp [reverseGerm]
  · simp only [reverseRay, terminalGerm_reverse]
    simp [reverseGerm]

@[simp] theorem reversePrefix_reverseRay (v : Vertex) (e : Fin 3 × List Bool) :
    reversePrefix (reverseRay v e) = e := by
  simp only [reversePrefix,reverseRay, terminalGerm_reverse,
    reverseTurns_reverseTurns]
  rfl

theorem reverseRay_reversePrefix (v : Vertex) (e : Germ × List Bool)
    (ht : (terminalGerm e.1 e.2).1 = v) : reverseRay v (reversePrefix e) = e := by
  unfold reverseRay
  rw [reversePrefix_initial ht]
  simp [reversePrefix]

theorem prefix_ray_reversal (D : Finset Vertex) (v : Vertex) (hv : v ∈ D) :
    (∑ e ∈ firstArrivals D v, wordWeight e.2) =
      (starRingEnd ℂ) (∑ e ∈ rayExits D v, wordWeight e.2) := by
  classical
  rw [map_sum]
  apply Finset.sum_bij (fun e _ => reversePrefix e)
  · intro e he
    exact reversePrefix_mem he
  · intro e he f hf hef
    have het := ((mem_firstArrivals D v e).mp he).2.2
    have hft := ((mem_firstArrivals D v f).mp hf).2.2
    have h := congrArg (reverseRay v) hef
    simpa [reverseRay_reversePrefix _ _ het,reverseRay_reversePrefix _ _ hft] using h
  · intro e he
    exact ⟨reverseRay v e,reverseRay_mem hv he,reversePrefix_reverseRay _ _⟩
  · intro e he
    simp [reversePrefix]

theorem IsExcursion.distinct_ports {D : Finset Vertex} {e : Germ × List Bool}
    (he : IsExcursion D e) : reverseGerm (terminalGerm e.1 e.2) ≠ e.1 := by
  intro hp
  obtain ⟨b,w,hw⟩ := List.exists_cons_of_ne_nil he.nonempty
  have hN := (stopped_traced D e.1 e.2 he.2.2.1).1
  rw [hw,traced,List.nodup_cons] at hN
  cases w with
  | nil =>
      have hk := congrArg Prod.snd hp
      simp only [hw,terminalGerm,reverseGerm,advance] at hk
      rcases e.1 with ⟨v,k⟩
      fin_cases k <;> cases b <;> simp [outgoingSlot] at hk
  | cons c w =>
      apply hN.1
      have hm := reverse_first_mem (advance e.1 b) (c :: w) (by simp)
      have hx : (reverseGerm (terminalGerm (advance e.1 b) (c :: w))).1 = e.1.1 :=
        congrArg Prod.fst (by simpa only [hw,terminalGerm] using hp)
      exact hx ▸ hm

end PolynomialVacuumBridge.Corridor

end

end OAI
