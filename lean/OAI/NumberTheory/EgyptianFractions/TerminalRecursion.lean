import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.TerminalDescent

/-- Unit-fraction lists in the intermediate construction may repeat denominators. -/
def UnitList (x : ℚ) (s : List ℕ) : Prop :=
  (∀ d ∈ s, 0 < d) ∧ (s.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum = x

lemma reciprocal_sum_scale (s : List ℕ) (z : ℕ) :
    ((s.map (fun d => z * d)).map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
      (s.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum / (z : ℚ) := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_mul, ih, add_div]
    rw [div_div, mul_comm (z : ℚ)]

lemma UnitList.scale {x : ℚ} {s : List ℕ} (hs : UnitList x s)
    {z : ℕ} (hz : 0 < z) :
    UnitList (x / (z : ℚ)) (s.map (fun d => z * d)) := by
  constructor
  · intro d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    exact Nat.mul_pos hz (hs.1 a ha)
  · rw [reciprocal_sum_scale, hs.2]

lemma unitList_zero : UnitList 0 [] := by simp [UnitList]

/-- A power-saving step contracts the logarithmic potential. -/
lemma log_potential_step {u h q : ℝ} (hu : 0 < u) (hh : 0 < h)
    (hq : 0 ≤ q) (hstep : h ≤ u ^ q) (N : ℕ) :
    q ^ N * Real.log h ≤ q ^ (N + 1) * Real.log u := by
  have hr := Real.log_le_log hh hstep
  rw [Real.log_rpow hu] at hr
  calc
    q ^ N * Real.log h ≤ q ^ N * (q * Real.log u) :=
      mul_le_mul_of_nonneg_left hr (pow_nonneg hq N)
    _ = q ^ (N + 1) * Real.log u := by rw [pow_succ]; ring

/-- Terminal descent: each residue step adds one unit fraction; the
logarithmic contraction gives an explicit upper bound on the depth. -/
theorem short_unit_list_of_descent
    (M T U B : ℕ) (hT : 0 < T) (q : ℝ) (hq : 0 ≤ q)
    (hbase : ∀ u : ℕ, u ≤ U → u ≤ T →
      ∃ s : List ℕ, UnitList ((u : ℚ) / (M : ℚ)) s ∧ s.length ≤ B)
    (hstep : ∀ u : ℕ, u ≤ U → T < u →
      ∃ a z h : ℕ, 0 < a ∧ 0 < z ∧ h ≤ U ∧
        (h : ℝ) ≤ (u : ℝ) ^ q ∧
        (u : ℚ) / (M : ℚ) = (1 : ℚ) / (a : ℚ) +
          ((h : ℚ) / (M : ℚ)) / (z : ℚ)) :
    ∀ N u : ℕ, u ≤ U →
      q ^ N * Real.log (u : ℝ) ≤ Real.log (T : ℝ) →
      ∃ s : List ℕ, UnitList ((u : ℚ) / (M : ℚ)) s ∧ s.length ≤ B + N := by
  intro N
  induction N with
  | zero =>
    intro u hu hpot
    have huT : u ≤ T := by
      by_cases hu0 : u = 0
      · omega
      have huR : (0 : ℝ) < u := by exact_mod_cast (Nat.pos_of_ne_zero hu0)
      have hTR : (0 : ℝ) < T := by exact_mod_cast hT
      simp only [pow_zero, one_mul] at hpot
      exact_mod_cast (Real.log_le_log_iff huR hTR).mp hpot
    simpa using hbase u hu huT
  | succ N ih =>
    intro u hu hpot
    by_cases huT : u ≤ T
    · obtain ⟨s, hs, hlen⟩ := hbase u hu huT
      exact ⟨s, hs, by omega⟩
    have hTu : T < u := by omega
    obtain ⟨a, z, h, ha, hz, hhU, hsmall, hid⟩ := hstep u hu hTu
    have hex : ∃ s : List ℕ, UnitList ((h : ℚ) / (M : ℚ)) s ∧
        s.length ≤ B + N := by
      by_cases hh0 : h = 0
      · subst h
        exact ⟨[], by simpa using unitList_zero, by simp⟩
      apply ih h hhU
      have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
      have hhR : (0 : ℝ) < h := by exact_mod_cast (Nat.pos_of_ne_zero hh0)
      exact (log_potential_step huR hhR hq hsmall N).trans hpot
    obtain ⟨s, hs, hlen⟩ := hex
    refine ⟨a :: s.map (fun d => z * d), ?_, ?_⟩
    · constructor
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact ha
        · exact (hs.scale hz).1 d hd
      · simp only [List.map_cons, List.sum_cons]
        rw [(hs.scale hz).2]
        exact hid.symm
    · simp only [List.length_cons, List.length_map]
      omega

end Problem337.TerminalDescent

end

end OAI
