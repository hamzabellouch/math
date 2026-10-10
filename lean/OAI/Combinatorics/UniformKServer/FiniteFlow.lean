import Mathlib

namespace OAI

namespace UniformKServer.FiniteFlow
variable {R C J : Type*} [Fintype C] [Fintype J] [DecidableEq C] [DecidableEq J]

structure Data (R C J : Type*) where
  mass : List R → C → ℚ
  flow : List R → R → C → J → ℚ

structure Valid (F : Data R C J) (T : C → R → J → C)
    (allowed : C → R → J → Prop) (initial : C) (H : ℕ) : Prop where
  mass_nonneg : ∀ w, w.length ≤ H → ∀ c, 0 ≤ F.mass w c
  mass_total : ∀ w, w.length ≤ H → ∑ c, F.mass w c = 1
  initial : ∀ c, F.mass [] c = if c = initial then 1 else 0
  flow_nonneg : ∀ w, w.length < H → ∀ r c j, 0 ≤ F.flow w r c j
  support : ∀ w, w.length < H → ∀ r c j, ¬allowed c r j → F.flow w r c j = 0
  outflow : ∀ w, w.length < H → ∀ r c, ∑ j, F.flow w r c j = F.mass w c
  inflow : ∀ w, w.length < H → ∀ r c',
    ∑ c, ∑ j, (if T c r j = c' then F.flow w r c j else 0) = F.mass (w++[r]) c'

/-- All rows are explicitly defined, even outside the construction horizon. -/
def row (F : Data R C J) (fallback : C → R → J) (H : ℕ)
    (w : List R) (r : R) (c : C) (j : J) : ℚ :=
  if w.length < H ∧ F.mass w c ≠ 0 then F.flow w r c j / F.mass w c
  else if j = fallback c r then 1 else 0

def cost (q : List R → R → C → J → ℚ) (T : C → R → J → C)
    (d : C → R → J → ℚ) : List R → C → List R → ℚ
  | _, _, [] => 0
  | w, c, r :: rs => ∑ j, q w r c j * (d c r j + cost q T d (w++[r]) (T c r j) rs)

def flowCost (F : Data R C J) (d : C → R → J → ℚ) : List R → List R → ℚ
  | _, [] => 0
  | w, r :: rs => (∑ c, ∑ j, F.flow w r c j*d c r j) + flowCost F d (w++[r]) rs

-- PROOFS

variable (F : Data R C J) (T : C → R → J → C)
  (allowed : C → R → J → Prop) (initial : C) (H : ℕ)
  (fallback : C → R → J)
  (hF : Valid F T allowed initial H)

include hF

omit [DecidableEq J] in
theorem zero_flow (w : List R) (hw : w.length < H) (r : R) (c : C)
    (hp : F.mass w c = 0) (j : J) : F.flow w r c j = 0 := by
  have hn := hF.flow_nonneg w hw r c j
  have hs := Finset.single_le_sum (fun j _ => hF.flow_nonneg w hw r c j) (Finset.mem_univ j)
  rw [hF.outflow w hw r c, hp] at hs
  exact le_antisymm hs hn

theorem mass_row (w : List R) (hw : w.length < H) (r : R) (c : C) (j : J) :
    F.mass w c * row F fallback H w r c j = F.flow w r c j := by
  by_cases hp : F.mass w c = 0
  · rw [hp, zero_mul, zero_flow F T allowed initial H hF w hw r c hp j]
  · rw [row, ite_eq_left ⟨hw, hp⟩]
    exact mul_div_cancel₀ _ hp

theorem row_nonneg (w : List R) (r : R) (c : C) (j : J) :
    0 ≤ row F fallback H w r c j := by
  unfold row
  split_ifs with hh hzero
  · exact div_nonneg (hF.flow_nonneg w hh.1 r c j) (hF.mass_nonneg w hh.1.le c)
  all_goals norm_num

theorem row_sum (w : List R) (r : R) (c : C) :
    ∑ j, row F fallback H w r c j = 1 := by
  by_cases hh : w.length < H ∧ F.mass w c ≠ 0
  · simp only [row, ite_eq_left hh, ← Finset.sum_div, hF.outflow w hh.1 r c,
      div_self hh.2]
  · simp [row, hh]

theorem row_support (hfallback : ∀ c r, allowed c r (fallback c r))
    (w : List R) (r : R) (c : C) (j : J) (hj : ¬allowed c r j) :
    row F fallback H w r c j = 0 := by
  have hne : j ≠ fallback c r := by intro he; subst j; exact hj (hfallback c r)
  unfold row
  split_ifs with hh
  · rw [hF.support w hh.1 r c j hj, zero_div]
  all_goals simp_all

omit [DecidableEq J] in
theorem inflow_average (w : List R) (hw : w.length < H) (r : R) (v : C → ℚ) :
    (∑ c, ∑ j, F.flow w r c j*v (T c r j)) = ∑ c', F.mass (w++[r]) c'*v c' := by
  simp_rw [← hF.inflow w hw r]
  symm
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [ite_mul]

theorem cost_average (d : C → R → J → ℚ) (rs w : List R)
    (hw : w.length + rs.length ≤ H) :
    (∑ c, F.mass w c * cost (row F fallback H) T d w c rs) = flowCost F d w rs := by
  induction rs generalizing w with
  | nil => simp [cost, flowCost]
  | cons r rs ih =>
    have hlen : w.length < H := by simp only [List.length_cons] at hw; omega
    have hnext : (w++[r]).length+rs.length ≤ H := by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega
    simp only [cost, Finset.mul_sum, ← mul_assoc]
    simp_rw [mass_row F T allowed initial H fallback hF w hlen r]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [inflow_average F T allowed initial H hF w hlen r (fun c => cost (row F fallback H) T d (w++[r]) c rs)]
    rw [ih (w++[r]) hnext]
    rfl



omit hF in
/-- The precise finite flow realization obligation. -/
theorem realization (F : Data R C J) (T : C → R → J → C)
    (allowed : C → R → J → Prop) (initial : C) (H : ℕ)
    (fallback : C → R → J) (hfallback : ∀ c r, allowed c r (fallback c r))
    (hF : Valid F T allowed initial H) :
    (∀ w r c j, 0 ≤ row F fallback H w r c j) ∧
    (∀ w r c, ∑ j, row F fallback H w r c j = 1) ∧
    (∀ w r c j, ¬allowed c r j → row F fallback H w r c j = 0) ∧
    (∀ d rs, rs.length ≤ H → cost (row F fallback H) T d [] initial rs = flowCost F d [] rs) := by
  refine ⟨row_nonneg F T allowed initial H fallback hF,
    row_sum F T allowed initial H fallback hF,
    row_support F T allowed initial H fallback hF hfallback, ?_⟩
  intro d rs hrs
  have hh := cost_average F T allowed initial H fallback hF d rs [] (by simpa using hrs)
  simpa only [hF.initial, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] using hh

end UniformKServer.FiniteFlow


end OAI
