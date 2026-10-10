import Mathlib
import OAI.Combinatorics.HoneycombCorridor.BoundaryContainment
import OAI.Combinatorics.HoneycombCorridor.CycleSplice

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

@[simp] theorem turnUnits_append (u w : List Bool) :
    turnUnits (u ++ w) = turnUnits u + turnUnits w := by
  simp [turnUnits]

@[simp] theorem reverse_stem_false (g : Germ) :
    reverseGerm (stemGerm g false) = advance g true := rfl

@[simp] theorem reverse_advance_true (g : Germ) :
    reverseGerm (advance g true) = stemGerm g false := by
  rw [← reverse_stem_false,reverseGerm_reverseGerm]

theorem chord_close_trace (g h e : Germ) (B w : List Bool)
    (hb : terminalGerm h (false :: B) = g)
    (he : terminalGerm e w = stemGerm h false) :
    traced e (w ++ (true :: B) ++ [true]) =
      traced e w ++ (traced h (false :: B) ++ [g.1]) := by
  simp only [traced_append,terminalGerm_append,he]
  have htr := stem_forward_trace h false B
  have htm := stem_forward_terminal h false B
  simp only [Bool.not_false] at htr htm
  rw [htr,htm,hb]
  simp [traced,List.append_assoc]

theorem chord_close_terminal (g h e : Germ) (B w : List Bool)
    (hb : terminalGerm h (false :: B) = g)
    (he : terminalGerm e w = stemGerm h false) (he' : e = advance g true) :
    terminalGerm e (w ++ (true :: B) ++ [true]) = e := by
  simp only [terminalGerm_append,he]
  have htm := stem_forward_terminal h false B
  simp only [Bool.not_false] at htm
  rw [htm,hb]
  simpa only [terminalGerm] using he'.symm

theorem chord_close_turn (g : Germ) (A B : List Bool) (e : Germ) (w : List Bool)
    (hN : (traced g ((false :: A) ++ (false :: B))).Nodup)
    (hc : terminalGerm g ((false :: A) ++ (false :: B)) = g)
    (he : e = advance g true)
    (ht : terminalGerm e w = stemGerm (terminalGerm g (false :: A)) false)
    (hwN : (traced e w).Nodup)
    (hd : ∀ v ∈ traced e w, v ∉ traced g ((false :: A) ++ (false :: B))) :
    turnUnits w + turnUnits (false :: B) + 3 = 6 ∨
      turnUnits w + turnUnits (false :: B) + 3 = -6 := by
  let h := terminalGerm g (false :: A)
  have hb : terminalGerm h (false :: B) = g := by
    exact (terminalGerm_append g (false :: A) (false :: B)).symm.trans hc
  have hN' : (g.1 :: (traced (advance g false) A ++ traced h (false :: B))).Nodup := by
    simpa only [h,traced_append,traced,terminalGerm,List.cons_append] using hN
  have hgnot : g.1 ∉ traced h (false :: B) := by
    intro hm
    exact (List.nodup_cons.mp hN').1 (List.mem_append_right _ hm)
  have hBN : (traced h (false :: B)).Nodup :=
    (List.nodup_append.mp (List.nodup_cons.mp hN').2).2.1
  have hBN' : (traced h (false :: B) ++ [g.1]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hBN,by simp,?_⟩
    intro a ha b hb hab
    have hb' := List.mem_singleton.mp hb
    exact hgnot ((hab.trans hb') ▸ ha)
  have hsub : ∀ v ∈ traced h (false :: B) ++ [g.1],
      v ∈ traced g ((false :: A) ++ (false :: B)) := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rw [traced_append]
      exact List.mem_append_right _ hv
    · have heq := List.mem_singleton.mp hv
      subst v
      simp [traced_append,traced]
  have hjoinN : (traced e (w ++ (true :: B) ++ [true])).Nodup := by
    rw [chord_close_trace g h e B w hb ht]
    apply List.nodup_append.mpr
    refine ⟨hwN,hBN',?_⟩
    intro a ha b hb hab
    subst b
    exact hd a ha (hsub a hb)
  have hjoinC := chord_close_terminal g h e B w hb ht he
  have hn : w ++ (true :: B) ++ [true] ≠ [] := by simp
  have h := simple_polygon_turning e _ hn hjoinN hjoinC
  have heq : turnUnits (w ++ (true :: B) ++ [true]) =
      turnUnits w + turnUnits (false :: B) + 3 := by
    simp [turnUnit,turnUnits]
    ring
  rwa [heq] at h

theorem cycle_chord_turn_bound (g : Germ) (A B : List Bool) (e : Germ) (w : List Bool)
    (hN : (traced g ((false :: A) ++ (false :: B))).Nodup)
    (hc : terminalGerm g ((false :: A) ++ (false :: B)) = g)
    (he : e = advance g true)
    (ht : terminalGerm e w = stemGerm (terminalGerm g (false :: A)) false)
    (hwN : (traced e w).Nodup)
    (hd : ∀ v ∈ traced e w, v ∉ traced g ((false :: A) ++ (false :: B)))
    (hturn : turnUnits ((false :: A) ++ (false :: B)) = 6)
    (hA : 0 ≤ turnUnits (false :: A)) (hB : 0 ≤ turnUnits (false :: B)) :
    -3 ≤ turnUnits w ∧ turnUnits w ≤ 3 := by
  have h₁ := chord_close_turn g A B e w hN hc he ht hwN hd
  let h := terminalGerm g (false :: A)
  let e' := reverseGerm (terminalGerm e w)
  have hrot := closed_word_rotate g (false :: A) (false :: B) hN hc
  have hback : terminalGerm h (false :: B) = g := by
    exact (terminalGerm_append g (false :: A) (false :: B)).symm.trans hc
  have he' : e' = advance h true := by simp only [e',ht,reverse_stem_false]; rfl
  have ht' : terminalGerm e' (reverseTurns w) =
      stemGerm (terminalGerm h (false :: B)) false := by
    rw [hback]
    simp only [e',terminalGerm_reverse,he,reverse_advance_true]
  have hwN' : (traced e' (reverseTurns w)).Nodup := by
    simpa only [e',traced_reverse,List.nodup_reverse] using hwN
  have hd' : ∀ v ∈ traced e' (reverseTurns w),
      v ∉ traced h ((false :: B) ++ (false :: A)) := by
    intro v hv hmem
    have hv' : v ∈ traced e w := by simpa only [e',traced_reverse,List.mem_reverse] using hv
    apply hd v hv'
    rw [traced_append,hback] at hmem
    rw [traced_append]
    exact List.mem_append.mpr (List.mem_append.mp hmem |>.symm)
  have h₂ := chord_close_turn h B A e' (reverseTurns w) hrot.1 hrot.2.1
    he' ht' hwN' hd'
  rw [turnUnits_reverse] at h₂
  rw [turnUnits_append] at hturn
  omega



theorem faceBoundaryWord_append (S : Finset FaceIndex) (g : FaceBoundary S) (m n : ℕ) :
    faceBoundaryWord S g (m+n) = faceBoundaryWord S g m ++
      faceBoundaryWord S ((faceBoundaryNext S)^[m] g) n := by
  induction m generalizing g with
  | zero => simp [faceBoundaryWord]
  | succ m ih =>
    simp only [Nat.succ_add,faceBoundaryWord,List.cons_append,Function.iterate_succ_apply]
    rw [ih]

@[simp] theorem boundary_stem_port (v : Vertex) (k : Fin 3) :
    stemGerm (v,k+1) false = (v,k) := by
  fin_cases k <;> simp [stemGerm,unusedSlot,outgoingSlot]

@[simp] theorem boundary_inward_port (v : Vertex) (k : Fin 3) :
    advance (v,k+1) true = reverseGerm (v,k) := by
  rw [← reverse_stem_false,boundary_stem_port]

theorem convex_distinct_outer_vertices (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (e : Germ × List Bool) (he : IsExcursion D e) :
    (terminalGerm e.1 e.2).1 ≠ (reverseGerm e.1).1 := by
  intro hv
  have hstart := (outside_boundary_germ D hD (reverseGerm e.1).1 e.1.2 he.2.1
    (by simpa only [reverseGerm,neighbor_neighbor] using he.1)).1
  have hend := (outside_boundary_germ D hD (terminalGerm e.1 e.2).1
    (terminalGerm e.1 e.2).2 he.2.2.2 he.reverse.1).1
  rw [hv] at hend
  have hk := faceBoundary_germ_unique (starFaces D) (reverseGerm e.1).1
    ((terminalGerm e.1 e.2).2+1) (e.1.2+1) hend hstart
  have hk' : (terminalGerm e.1 e.2).2 = e.1.2 := add_right_cancel hk
  have heq : terminalGerm e.1 e.2 = reverseGerm e.1 := Prod.ext hv hk'
  apply he.distinct_ports
  rw [heq,reverseGerm_reverseGerm]

theorem boundary_chord_turn_bound (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ)
    (hN : (traced g.val (faceBoundaryWord (starFaces D) g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord (starFaces D) g n) = g.val)
    (hg : faceBoundaryTurn (starFaces D) g.val = false)
    (i : ℕ) (hi : 0 < i) (hin : i < n)
    (hgi : faceBoundaryTurn (starFaces D) ((faceBoundaryNext (starFaces D))^[i] g).val = false)
    (e : Germ) (w : List Bool) (he : e = advance g.val true)
    (ht : terminalGerm e w = stemGerm ((faceBoundaryNext (starFaces D))^[i] g).val false)
    (hwN : (traced e w).Nodup) (hd : ∀ v ∈ traced e w, v ∈ D) :
    -3 ≤ turnUnits w ∧ turnUnits w ≤ 3 := by
  let G := (faceBoundaryNext (starFaces D))^[i] g
  have hn : 0 < n := lt_trans hi hin
  have hperiod : (faceBoundaryNext (starFaces D))^[n] g = g := by
    apply Subtype.ext
    rwa [faceBoundaryWord_terminal] at hc
  have hend : (faceBoundaryNext (starFaces D))^[n-i] G = g := by
    simp only [G,← Function.iterate_add_apply]
    rw [Nat.sub_add_cancel (Nat.le_of_lt hin),hperiod]
  have hAi := star_boundary_word_charge D hD g i
  have hBi := star_boundary_word_charge D hD G (n-i)
  simp only [G,hgi,hg,hend,boundaryCharge,Bool.false_eq_true,ite_false,sub_self] at hAi hBi
  obtain ⟨a,hai⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  obtain ⟨b,hbi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.sub_pos_of_lt hin))
  let A := faceBoundaryWord (starFaces D) (faceBoundaryNext (starFaces D) g) a
  let B := faceBoundaryWord (starFaces D) (faceBoundaryNext (starFaces D) G) b
  have hA : faceBoundaryWord (starFaces D) g i = false :: A := by
    rw [hai,faceBoundaryWord,hg]
  have hB : faceBoundaryWord (starFaces D) G (n-i) = false :: B := by
    rw [hbi,faceBoundaryWord,hgi]
  have hW : faceBoundaryWord (starFaces D) g n = (false :: A) ++ (false :: B) := by
    conv_lhs => rw [← Nat.add_sub_cancel' (Nat.le_of_lt hin)]
    rw [faceBoundaryWord_append,hA,hB]
  have hterminal : terminalGerm g.val (false :: A) = G.val := by
    rw [← hA,faceBoundaryWord_terminal]
  apply cycle_chord_turn_bound g.val A B e w (by rwa [← hW]) (by rwa [← hW]) he
    (by rwa [hterminal]) hwN
  · intro v hv hm
    rw [← hW] at hm
    exact star_boundary_trace_outside D g n v hm (hd v hv)
  · rw [← hW]
    exact star_boundary_cycle_turn D hD g n hn hN hc
  · rwa [← hA]
  · rwa [← hB]



theorem convex_excursion_turn_bound (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (e : Germ × List Bool) (he : IsExcursion D e) :
    -3 ≤ turnUnits e.2 ∧ turnUnits e.2 ≤ 3 := by
  classical
  have hs := outside_boundary_germ D hD (reverseGerm e.1).1 e.1.2 he.2.1
    (by simpa only [reverseGerm,neighbor_neighbor] using he.1)
  let g : FaceBoundary (starFaces D) := ⟨((reverseGerm e.1).1,e.1.2+1),hs.1⟩
  have hge : e.1 = advance g.val true := by
    change e.1 = advance ((reverseGerm e.1).1,e.1.2+1) true
    rw [boundary_inward_port]
    exact (reverseGerm_reverseGerm e.1).symm
  obtain ⟨n,hn,hN,hc⟩ := faceBoundary_closed_word (starFaces D) g
  obtain ⟨hwN,hwD⟩ := stopped_traced D e.1 e.2 he.2.2.1
  have hm := star_boundary_endpoint D hD g n hn hN hc hs.2 e.1 e.2 hge hwD
    he.2.2.2 he.reverse.1
  rw [faceBoundaryWord_traced,List.mem_ofFn] at hm
  obtain ⟨i,hi⟩ := hm
  have hi0 : 0 < i.val := by
    by_contra hn
    have hz : i.val = 0 := by omega
    have hv : (terminalGerm e.1 e.2).1 = (reverseGerm e.1).1 := by
      simpa only [hz,Function.iterate_zero,id_eq,g] using hi.symm
    exact convex_distinct_outer_vertices D hD e he hv
  have hu := outside_boundary_germ D hD (terminalGerm e.1 e.2).1
    (terminalGerm e.1 e.2).2 he.2.2.2 he.reverse.1
  let u : FaceBoundary (starFaces D) :=
    ⟨((terminalGerm e.1 e.2).1,(terminalGerm e.1 e.2).2+1),hu.1⟩
  have hiu : (faceBoundaryNext (starFaces D))^[i.val] g = u :=
    faceBoundary_vertex_injective (starFaces D) hi
  apply boundary_chord_turn_bound D hD g n hN hc hs.2 i.val hi0 i.isLt
    (by rw [hiu]; exact hu.2) e.1 e.2 hge _ hwN hwD
  rw [hiu]
  change terminalGerm e.1 e.2 = stemGerm
    ((terminalGerm e.1 e.2).1,(terminalGerm e.1 e.2).2+1) false
  exact (boundary_stem_port _ _).symm

end PolynomialVacuumBridge.Corridor

end

end OAI
