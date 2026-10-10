import Mathlib
import OAI.Combinatorics.UniformKServer.ExactOptimum
import OAI.Combinatorics.UniformKServer.FiniteFlow

namespace OAI

namespace UniformKServer.FiniteTable
open EffectiveLP

/-- The source's least allowed serving label, including zero marginal rows. -/
def fallback {n k : ℕ} [NeZero k] (c : Config n k) (r : Fin n) : Fin k :=
  if h : (labels c r).Nonempty then (labels c r).min' h else 0

def next {n k : ℕ} (c : Config n k) (r : Fin n) (j : Fin k) : Config n k :=
  if h : j ∈ labels c r then step c r ⟨j,h⟩ else c

def globalFlow {n k H : ℕ} (F : BoundedFlow n k H ℚ) :
    FiniteFlow.Data (Fin n) (Config n k) (Fin k) where
  mass w c := if h : w.length ≤ H then F.mass ⟨w,(mem_words w).mpr h⟩ c else 0
  flow w r c j := if h : w.length < H then
    if hj : j ∈ labels c r then
      F.flow ⟨⟨w,(mem_words w).mpr h.le⟩,h⟩ r c ⟨j,hj⟩ else 0 else 0

def charge {n k : ℕ} (d : RationalMetric n) (c : Config n k) (r : Fin n) (j : Fin k) : ℚ :=
  d.distance (c.val j) r

def row {n k H : ℕ} [NeZero k] (F : BoundedFlow n k H ℚ) :
    List (Fin n) → Fin n → Config n k → Fin k → ℚ :=
  FiniteFlow.row (globalFlow F) fallback H

theorem labels_nonempty {n k : ℕ} [NeZero k] (c : Config n k) (r : Fin n) :
    (labels c r).Nonempty := by
  unfold labels
  split_ifs with h
  · obtain ⟨j,hj⟩ := h
    exact ⟨j, by simp [hj]⟩
  · exact Finset.univ_nonempty

theorem fallback_mem {n k : ℕ} [NeZero k] (c : Config n k) (r : Fin n) :
    fallback c r ∈ labels c r := by
  simp only [fallback, dite_eq_left (labels_nonempty c r)]
  exact Finset.min'_mem _ _

theorem sum_labels {n k : ℕ} {K : Type*} [AddCommMonoid K]
    (c : Config n k) (r : Fin n) (f : Label c r → K) :
    (∑ j, if hj : j ∈ labels c r then f ⟨j,hj⟩ else 0) = ∑ j, f j := by
  exact (Finset.sum_attach_eq_sum_dite (labels c r) f).symm

theorem global_valid {n k H : ℕ} [NeZero k]
    (d : RationalMetric n) (u : Config n k) (F : BoundedFlow n k H ℚ) (a : ℚ)
    (hF : EffectiveLP.Valid d u F a) :
    FiniteFlow.Valid (globalFlow F) next (fun c r j => j ∈ labels c r) u H := by
  rcases hF with ⟨ha,hn,ht,hi,hfn,ho,hii,hcost⟩
  constructor
  · intro w hw c
    simpa only [globalFlow, dite_eq_left hw] using hn ⟨w,(mem_words w).mpr hw⟩ c
  · intro w hw
    simpa only [globalFlow, dite_eq_left hw] using ht ⟨w,(mem_words w).mpr hw⟩
  · intro c
    change (if h : [].length ≤ H then F.mass ⟨[], (mem_words []).mpr h⟩ c else 0) = _
    split
    · exact hi c
    · rename_i h
      exact (h (Nat.zero_le H)).elim
  · intro w hw r c j
    simp only [globalFlow, dite_eq_left hw]
    split_ifs with hj
    · exact hfn ⟨⟨w,(mem_words w).mpr hw.le⟩,hw⟩ r c ⟨j,hj⟩
    · exact le_refl _
  · intro w hw r c j hj
    simp only [globalFlow, dite_eq_left hw, dite_eq_right hj]
  · intro w hw r c
    simp only [globalFlow, dite_eq_left hw, dite_eq_left hw.le, sum_labels]
    exact ho ⟨⟨w,(mem_words w).mpr hw.le⟩,hw⟩ r c
  · intro w hw r c'
    have hext : (w++[r]).length ≤ H := by simp only [List.length_append, List.length_singleton]; omega
    simp only [globalFlow, dite_eq_left hw, dite_eq_left hext]
    have hs (c : Config n k) :
        (∑ j, if next c r j = c' then
          (if hj : j ∈ labels c r then F.flow ⟨⟨w,(mem_words w).mpr hw.le⟩,hw⟩ r c ⟨j,hj⟩ else 0)
          else 0) =
        ∑ j : Label c r, if step c r j = c' then
          F.flow ⟨⟨w,(mem_words w).mpr hw.le⟩,hw⟩ r c j else 0 := by
      rw [← sum_labels c r]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ labels c r
      · simp only [next, dite_eq_left hj]
      · simp only [dite_eq_right hj, ite_self]
    simp only [hs]
    exact hii ⟨⟨w,(mem_words w).mpr hw.le⟩,hw⟩ r c'

theorem flowCost_prefix {R C J : Type*} [Fintype C] [Fintype J]
    (F : FiniteFlow.Data R C J) (d : C → R → J → ℚ) (pre w : List R) :
    FiniteFlow.flowCost F d pre w =
      ∑ i : Fin w.length, ∑ c, ∑ j, F.flow (pre++w.take i) w[i] c j * d c w[i] j := by
  induction w generalizing pre with
  | nil => simp [FiniteFlow.flowCost]
  | cons r w ih =>
    simp only [FiniteFlow.flowCost, List.length_cons]
    rw [Fin.sum_univ_succ, ih]
    simp [Fin.getElem_fin, List.append_assoc]

theorem flowCost_exact {n k H : ℕ} (d : RationalMetric n) (F : BoundedFlow n k H ℚ)
    (w : Word n H) :
    FiniteFlow.flowCost (globalFlow F) (charge d) [] w.val =
      ∑ i : Fin w.val.length, ∑ c, ∑ j : Label c w.val[i],
        F.flow (prefixNode w i) w.val[i] c j * d.distance (c.val j.val) w.val[i] := by
  rw [flowCost_prefix]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro c _
  have hi : (w.val.take i).length < H := (prefixNode w i).property
  simp only [globalFlow, List.nil_append, dite_eq_left hi, charge]
  rw [← sum_labels c w.val[i]]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [zero_mul]
  rfl

theorem realize_proof {n k H : ℕ} [NeZero k]
    (d : RationalMetric n) (u : Config n k) (F : BoundedFlow n k H ℚ) (a : ℚ)
    (hF : EffectiveLP.Valid d u F a) :
    (∀ w r c j, 0 ≤ row F w r c j) ∧
    (∀ w r c, ∑ j, row F w r c j = 1) ∧
    (∀ w r c j, j ∉ labels c r → row F w r c j = 0) ∧
    (∀ w, w.length ≤ H →
      FiniteFlow.cost (row F) next (charge d) [] u w ≤
        a * OfflineDynamic.optRat d u.val w) := by
  have hv := global_valid d u F a hF
  obtain ⟨hn,hs,hp,hc⟩ := FiniteFlow.realization (globalFlow F) next
    (fun c r j => j ∈ labels c r) u H fallback fallback_mem hv
  refine ⟨hn,hs,hp,?_⟩
  intro w hw
  let w' : Word n H := ⟨w,(mem_words w).mpr hw⟩
  calc
    FiniteFlow.cost (row F) next (charge d) [] u w =
        FiniteFlow.flowCost (globalFlow F) (charge d) [] w := hc (charge d) w hw
    _ = _ := flowCost_exact d F w'
    _ ≤ _ := hF.2.2.2.2.2.2.2 w'


-- The exact new obligation: actual causal rows from the source finite LP,
-- including all zero-marginal rows and zero optimum words.
theorem realize {n k H : ℕ} [NeZero k]
    (d : RationalMetric n) (u : Config n k) (F : BoundedFlow n k H ℚ) (a : ℚ)
    (hF : EffectiveLP.Valid d u F a) :
    (∀ w r c j, 0 ≤ row F w r c j) ∧
    (∀ w r c, ∑ j, row F w r c j = 1) ∧
    (∀ w r c j, j ∉ labels c r → row F w r c j = 0) ∧
    (∀ w, w.length ≤ H →
      FiniteFlow.cost (row F) next (charge d) [] u w ≤
        a * OfflineDynamic.optRat d u.val w) := by
  exact realize_proof d u F a hF

end UniformKServer.FiniteTable



end OAI
