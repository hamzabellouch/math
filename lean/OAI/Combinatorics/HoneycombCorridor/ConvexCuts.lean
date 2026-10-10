import Mathlib
import OAI.Combinatorics.HoneycombCorridor.BoundaryFlux

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def upperCut (D : Finset Vertex) (k : Fin 3) (A : ℤ) : Finset Vertex :=
  D.filter fun v => boxIndex v k < A

@[simp] theorem mem_upperCut (D : Finset Vertex) (k : Fin 3) (A : ℤ) (v : Vertex) :
    v ∈ upperCut D k A ↔ v ∈ D ∧ boxIndex v k < A := by
  simp [upperCut]

theorem upperCut_subset (D : Finset Vertex) (k : Fin 3) (A : ℤ) : upperCut D k A ⊆ D :=
  Finset.filter_subset _ _

theorem admissiblyConvex_of_box (D : Finset Vertex) (lo hi : Fin 3 → ℤ)
    (h : ∀ v, v ∈ D ↔ BoxMem lo hi v) : AdmissiblyConvex D := by
  refine ⟨lo,hi,fun v => ?_⟩
  rw [h]
  apply forall_congr'
  intro k
  obtain ⟨a,ha,ha',he⟩ := tilingCoordinate_index v k
  rw [he]
  exact (integer_bounds_fraction _ _ _ _ ha ha').symm

theorem upperCut_convex (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (k : Fin 3) (A : ℤ) : AdmissiblyConvex (upperCut D k A) := by
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  apply admissiblyConvex_of_box _ lo (fun l => if l = k then min (hi l) A else hi l)
  intro v
  simp only [mem_upperCut,hbox,BoxMem]
  constructor
  · rintro ⟨hv,hA⟩ l
    by_cases hl : l = k
    · subst l; simpa only [ite_true,lt_min_iff] using ⟨(hv k).1,(hv k).2,hA⟩
    · simpa only [hl,ite_false] using hv l
  · intro hv
    constructor
    · intro l
      by_cases hl : l = k
      · subst l
        have hh := hv k
        simp only [ite_true,lt_min_iff] at hh
        exact ⟨hh.1,hh.2.1⟩
      · simpa only [hl,ite_false] using hv l
    · have hh := hv k
      simp only [ite_true,lt_min_iff] at hh
      exact hh.2.2

theorem sourceExits_restrict_iff (D E : Finset Vertex) (hED : E ⊆ D)
    (g : Germ) (w : List Bool) (hw : w ∈ sourceExits D g) :
    w ∈ sourceExits E g ↔ ∀ v ∈ traced g w, v ∈ E := by
  obtain ⟨hs,ht⟩ := (mem_sourceExits D g w).mp hw
  constructor
  · intro he
    exact (stopped_traced E g w ((mem_sourceExits E g w).mp he).1).2
  · intro he
    have hn := (stopped_traced D g w hs).1
    have hout : (terminalGerm g w).1 ∉ E := fun hm => ht (hED hm)
    exact (mem_sourceExits E g w).mpr ⟨stopped_of_trace E g w hn he hout,hout⟩

theorem new_exit_terminal_inside (D E : Finset Vertex) (hED : E ⊆ D)
    (g : Germ) (w : List Bool) (hw : w ∈ sourceExits E g \ sourceExits D g) :
    (terminalGerm g w).1 ∈ D := by
  classical
  obtain ⟨he,hd⟩ := Finset.mem_sdiff.mp hw
  obtain ⟨hs,ht⟩ := (mem_sourceExits E g w).mp he
  obtain ⟨hn,hm⟩ := stopped_traced E g w hs
  by_contra hout
  apply hd
  exact (mem_sourceExits D g w).mpr
    ⟨stopped_of_trace D g w hn (fun v hv => hED (hm v hv)) hout,hout⟩

theorem flux_subtraction (D E : Finset Vertex) (g : Germ)
    (hD : Filled D) (hE : Filled E)
    (hgD : (reverseGerm g).1 ∉ D) (hgE : (reverseGerm g).1 ∉ E) :
    (∑ w ∈ sourceExits D g \ sourceExits E g, wordWeight w) =
      ∑ w ∈ sourceExits E g \ sourceExits D g, wordWeight w := by
  apply sub_eq_zero.mp
  rw [Finset.sum_sdiff_sub_sum_sdiff,boundary_source_flux D g hD hgD,
    boundary_source_flux E g hE hgE,sub_self]

theorem mem_lost_upperCut (D : Finset Vertex) (g : Germ) (k : Fin 3) (A : ℤ)
    (w : List Bool) : w ∈ sourceExits D g \ sourceExits (upperCut D k A) g ↔
      w ∈ sourceExits D g ∧ ∃ v ∈ traced g w, A ≤ boxIndex v k := by
  classical
  simp only [Finset.mem_sdiff]
  by_cases hw : w ∈ sourceExits D g
  · simp only [hw,true_and,sourceExits_restrict_iff D _ (upperCut_subset D k A) g w hw]
    have hm := (stopped_traced D g w ((mem_sourceExits D g w).mp hw).1).2
    simp only [mem_upperCut,not_forall,not_and,not_lt]
    constructor
    · rintro ⟨v,hv,hnot⟩
      exact ⟨v,hv,hnot (hm v hv)⟩
    · rintro ⟨v,hv,hA⟩
      exact ⟨v,hv,fun _ => hA⟩
  · simp [hw]

theorem bottomSource_outside_of_strip (h : ℕ) (D : Finset Vertex)
    (hstrip : ∀ v ∈ D, InStrip h v) : (reverseGerm bottomSource).1 ∉ D := by
  intro hv
  have hh := (hstrip _ hv).1
  norm_num [bottomSource,reverseGerm,neighbor,boxIndex] at hh

theorem bottomSource_mem_upperCut (D : Finset Vertex) (hg : bottomSource.1 ∈ D)
    (k : Fin 3) (A : ℤ) (hA : 0 < A) : bottomSource.1 ∈ upperCut D k A := by
  apply (mem_upperCut _ _ _ _).mpr
  refine ⟨hg,?_⟩
  fin_cases k <;> simpa [bottomSource,boxIndex] using hA

theorem new_upperCut_direction (D : Finset Vertex) (k : Fin 3) (A : ℤ)
    (hg : bottomSource.1 ∈ upperCut D k A) (w : List Bool)
    (hw : w ∈ sourceExits (upperCut D k A) bottomSource \ sourceExits D bottomSource) :
    boxIndex (reverseGerm (terminalGerm bottomSource w)).1 k < A ∧
      A ≤ boxIndex (terminalGerm bottomSource w).1 k := by
  classical
  have he := (mem_sourceExits _ _ _).mp (Finset.mem_sdiff.mp hw).1
  have hn : w ≠ [] := by
    intro h
    exact he.2 (by simpa [h,terminalGerm] using hg)
  have hpred := (stopped_traced _ _ _ he.1).2 _ (reverse_first_mem bottomSource w hn)
  have hu := new_exit_terminal_inside D _ (upperCut_subset D k A) _ _ hw
  exact ⟨((mem_upperCut _ _ _ _).mp hpred).2,by
    by_contra hx
    exact he.2 ((mem_upperCut _ _ _ _).mpr ⟨hu,by omega⟩)⟩

theorem new_upperCut_turn (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hg' : (reverseGerm bottomSource).1 ∉ D)
    (A : ℤ) (hA : 0 < A) (k : Fin 3) (w : List Bool)
    (hw : w ∈ sourceExits (upperCut D k A) bottomSource \ sourceExits D bottomSource) :
    (k = 1 → turnUnits w = -2) ∧ (k = 2 → turnUnits w = -1) := by
  have hmem := bottomSource_mem_upperCut D hg k A hA
  obtain ⟨hl,hu⟩ := new_upperCut_direction D k A hmem w hw
  have ht := convex_source_direction_turn _ (upperCut_convex D hD k A) hmem
    (fun hm => hg' (upperCut_subset D k A hm)) w (Finset.mem_sdiff.mp hw).1
  constructor
  · intro hk; subst k
    apply ht.1
    have hd := right_cut_direction_one (reverseGerm (terminalGerm bottomSource w)).1
      (terminalGerm bottomSource w).2 A hl
      (by simpa only [reverseGerm,neighbor_neighbor] using hu)
    simpa only [reverseGerm,neighbor_neighbor] using hd
  · intro hk; subst k
    apply ht.2
    have hd := right_cut_direction_two (reverseGerm (terminalGerm bottomSource w)).1
      (terminalGerm bottomSource w).2 A hl
      (by simpa only [reverseGerm,neighbor_neighbor] using hu)
    simpa only [reverseGerm,neighbor_neighbor] using hd

end PolynomialVacuumBridge.Corridor

end

end OAI
