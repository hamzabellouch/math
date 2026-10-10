import OAI.NumberTheory.Ostmann.Characters.FrequencyExposure
import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyLabelsModulus

namespace OAI

noncomputable section
namespace Ostmann.Characters.HistoryFrequencyLabels
abbrev NodeFrequencies := ℤ × (ℤ × ℤ)

def nodes : (k : ℕ) → List Bool → ℤ → HistoryReconstruction.Tree k →
    List (List Bool × NodeFrequencies)
  | 0, _, _, _ => []
  | k+1, p, s, t => (p,(s,t.1.1,t.1.2)) ::
      (nodes k (false::p) t.1.1 t.2.1 ++ nodes k (true::p) t.1.2 t.2.2)

theorem nodes_address_extension {k : ℕ} {p : List Bool} {s : ℤ}
    {t : HistoryReconstruction.Tree k} {q : List Bool} {a : NodeFrequencies}
    (h : (q,a) ∈ nodes k p s t) : ∃ r : List Bool, q = r ++ p := by
  induction k generalizing p s with
  | zero => exact False.elim (List.not_mem_nil h)
  | succ k ih =>
    rcases List.mem_cons.mp h with he | h
    · cases he
      exact ⟨[],rfl⟩
    · rcases List.mem_append.mp h with hl | hr
      · obtain ⟨r,hr⟩ := ih hl
        exact ⟨r++[false],by simpa only [List.append_assoc,List.singleton_append] using hr⟩
      · obtain ⟨r,hr⟩ := ih hr
        exact ⟨r++[true],by simpa only [List.append_assoc,List.singleton_append] using hr⟩

private theorem root_not_child {k : ℕ} {p : List Bool} {s : ℤ}
    {t : HistoryReconstruction.Tree k} {a : NodeFrequencies} (b : Bool) :
    (p,a) ∉ nodes k (b::p) s t := by
  intro h
  obtain ⟨r,hr⟩ := nodes_address_extension h
  have hl := congrArg List.length hr
  simp only [List.length_append,List.length_cons] at hl
  omega

private theorem child_addresses_disjoint {k l : ℕ} {p q : List Bool} {s s' : ℤ}
    {t : HistoryReconstruction.Tree k} {u : HistoryReconstruction.Tree l}
    {a b : NodeFrequencies} (hl : (q,a) ∈ nodes k (false::p) s t)
    (hr : (q,b) ∈ nodes l (true::p) s' u) : False := by
  obtain ⟨r,heL⟩ := nodes_address_extension hl
  obtain ⟨r',heR⟩ := nodes_address_extension hr
  have he : (r++[false])++p = (r'++[true])++p := by
    simpa only [List.append_assoc,List.singleton_append] using heL.symm.trans heR
  have he' := List.append_cancel_right he
  have hlast := congrArg List.getLast? he'
  simp at hlast

theorem nodes_functional {k : ℕ} {p : List Bool} {s : ℤ}
    {t : HistoryReconstruction.Tree k} {q : List Bool} {a b : NodeFrequencies}
    (ha : (q,a) ∈ nodes k p s t) (hb : (q,b) ∈ nodes k p s t) : a = b := by
  induction k generalizing p s with
  | zero => exact False.elim (List.not_mem_nil ha)
  | succ k ih =>
    simp only [nodes,List.mem_cons,List.mem_append] at ha hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
    · exact (Prod.mk.inj ha).2.trans (Prod.mk.inj hb).2.symm
    · have hq := (Prod.mk.inj ha).1
      subst q
      exact False.elim (root_not_child false hb)
    · have hq := (Prod.mk.inj ha).1
      subst q
      exact False.elim (root_not_child true hb)
    · have hq := (Prod.mk.inj hb).1
      subst q
      exact False.elim (root_not_child false ha)
    · exact ih ha hb
    · exact False.elim (child_addresses_disjoint ha hb)
    · have hq := (Prod.mk.inj hb).1
      subst q
      exact False.elim (root_not_child true ha)
    · exact False.elim (child_addresses_disjoint hb ha)
    · exact ih ha hb

theorem nodes_mem_labels {k : ℕ} {p : List Bool} {s : ℤ}
    {t : HistoryReconstruction.Tree k} {q : List Bool} {a : NodeFrequencies}
    (ha : (q,a) ∈ nodes k p s t) : (q,a.1) ∈ labels k p s t := by
  induction k generalizing p s with
  | zero => exact False.elim (List.not_mem_nil ha)
  | succ k ih =>
    rcases List.mem_cons.mp ha with he | ha
    · cases he
      exact root_mem_labels _ _ _ _
    · rcases List.mem_append.mp ha with hl | hr
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ih hl))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih hr))

def diagonalData (k : ℕ) (p : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree k)
    (q : List Bool) : FrequencyExposure.Data (modulus k p s t) := by
  classical
  by_cases h : ∃ a : NodeFrequencies, (q,a) ∈ nodes k p s t
  · let a := h.choose
    have ha : a.1.natAbs ∣ modulus k p s t :=
      frequency_dvd_modulus (nodes_mem_labels h.choose_spec)
    exact ⟨a.1,a.1,a.2.1,a.2.2,a.2.1,a.2.2,ha,ha⟩
  · exact ⟨1,1,0,0,0,0,one_dvd _,one_dvd _⟩

theorem diagonalData_at {k : ℕ} {p : List Bool} {s : ℤ}
    {t : HistoryReconstruction.Tree k} {q : List Bool} {a : NodeFrequencies}
    (ha : (q,a) ∈ nodes k p s t) :
    (diagonalData k p s t q).s = a.1 ∧ (diagonalData k p s t q).s' = a.1 ∧
    (diagonalData k p s t q).v = a.2.1 ∧ (diagonalData k p s t q).w = a.2.2 ∧
    (diagonalData k p s t q).v' = a.2.1 ∧ (diagonalData k p s t q).w' = a.2.2 := by
  classical
  have h : ∃ b : NodeFrequencies, (q,b) ∈ nodes k p s t := ⟨a,ha⟩
  have he : h.choose = a := nodes_functional h.choose_spec ha
  simp only [diagonalData,dite_eq_left h,he,and_self]

end Ostmann.Characters.HistoryFrequencyLabels

end

end OAI
