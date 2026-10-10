import OAI.Combinatorics.HoneycombChords.PhysicalMass

namespace OAI

/-!
# Uniform critical strict bridge mass estimates

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section

namespace CriticalHoneycomb
open scoped ENNReal

/-- Straight vertical bridge, parametrized by height minus one. -/
def verticalTrace : ℕ → List Center
  | 0 => [up 0 0,down 0 0]
  | n+1 => verticalTrace n ++ [up 0 (n+1),down 0 (n+1)]

lemma verticalTrace_bounds (n : ℕ) {v : Center} (hv : v ∈ verticalTrace n) :
    0 ≤ v.2.1 ∧ v.2.1 ≤ (n:ℤ) := by
  induction n with
  | zero => simp only [verticalTrace,List.mem_cons,List.not_mem_nil,or_false] at hv; rcases hv with rfl|rfl <;> simp [up,down]
  | succ n ih =>
    simp only [verticalTrace,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with hv|rfl|rfl
    · have h:=ih hv
      constructor
      · exact h.1
      · push_cast; omega
    · simp [up]; omega
    · simp [down]; omega

lemma verticalTrace_last (n : ℕ) : (verticalTrace n).getLast?=some (down 0 n) := by
  cases n with
  | zero => simp [verticalTrace]
  | succ n => simp [verticalTrace]
lemma verticalTrace_head (n : ℕ) : (verticalTrace n).head?=some (up 0 0) := by
  induction n with
  | zero => simp [verticalTrace]
  | succ n ih => simp [verticalTrace,List.head?_append,ih]

lemma verticalTrace_nodup (n : ℕ) : (verticalTrace n).Nodup := by
  induction n with
  | zero => simp [verticalTrace,up,down]
  | succ n ih =>
    rw [verticalTrace,List.nodup_append]
    refine ⟨ih,by simp [up,down],?_⟩
    intro a ha b hb hab
    subst b
    have h:=verticalTrace_bounds n ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl <;> simp only [up,down] at h <;> omega

lemma verticalTrace_chain (n : ℕ) : (verticalTrace n).IsChain Adj := by
  induction n with
  | zero => simp [verticalTrace,Adj,up,down]
  | succ n ih =>
    rw [verticalTrace,List.isChain_append]
    refine ⟨ih,by simp [Adj,up,down],?_⟩
    intro x hx y hy
    simp only [verticalTrace_last,Option.mem_some_iff] at hx
    simp only [List.head?_cons,Option.mem_some_iff] at hy
    subst x; subst y
    simp [Adj,up,down]

noncomputable def straightBridge (n : ℕ) : StrictBridge (n+1) :=
  ⟨verticalTrace n,⟨verticalTrace_nodup n,verticalTrace_chain n,by
      intro v hv
      have h:=verticalTrace_bounds n hv
      exact ⟨h.1,by push_cast; omega⟩⟩,
    verticalTrace_head n,0,by simpa using verticalTrace_last n⟩

lemma bridgeMass_pos (h : ℕ) : 0<bridgeMass h := by
  cases h with
  | zero => simp [bridgeMass]
  | succ n =>
    have hκ : 0<kappa := by unfold kappa; positivity
    have hw : 0<weight (straightBridge n).val := ENNReal.ofReal_pos.mpr (pow_pos hκ _)
    simp only [bridgeMass,Nat.add_one_ne_zero,ite_false]
    exact hw.trans_le (ENNReal.le_tsum (f := fun p : StrictBridge (n+1) ↦ weight p.val) (straightBridge n))

end CriticalHoneycomb

end


section

namespace CriticalHoneycomb
open Filter Topology StripExhaustion

/-- Uniform two-sided bounds for the critical strict bridge path sum. -/
def FiniteBridgeMassEstimate : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ h : ℕ,
    ENNReal.ofReal (c * (1 + (h : ℝ)) ^ (-(1 : ℝ) / 4)) ≤ bridgeMass h ∧
    bridgeMass h ≤ ENNReal.ofReal (C * (1 + (h : ℝ)) ^ (-(1 : ℝ) / 4))

private lemma finite_positive_bounds {f : ℕ → ℝ} (hf : ∀ n,0<f n) (K : ℕ) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ n<K,c≤f n ∧ f n≤C := by
  induction K with
  | zero => exact ⟨1,1,by norm_num,by norm_num,by simp⟩
  | succ K ih =>
    obtain ⟨c,C,hc,hC,h⟩:=ih
    refine ⟨min c (f K),max C (f K),lt_min hc (hf K),lt_of_lt_of_le hC (le_max_left _ _),?_⟩
    intro n hn
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn|rfl
    · exact ⟨(min_le_left _ _).trans (h n hn).1,(h n hn).2.trans (le_max_left _ _)⟩
    · exact ⟨min_le_right _ _,le_max_right _ _⟩

/-- The critical strict bridge mass is comparable to `(1 + h)^(-1/4)` at every height. -/
theorem finiteBridgeMassEstimate : FiniteBridgeMassEstimate := by
  obtain ⟨a,ha,hlo⟩:=FiniteFunctional.physical_bridge_mass_lower
  obtain ⟨A,hA,hup⟩:=FiniteFunctional.physical_bridge_mass_upper
  obtain ⟨K,hK⟩:=eventually_atTop.mp (hlo.and hup)
  let P : ℕ → ℝ := fun n ↦ (1+(n:ℝ))^(-(1:ℝ)/4)
  have hP n : 0<P n := Real.rpow_pos_of_pos (by positivity) _
  have hf n : 0<(bridgeMass n).toReal/P n :=
    div_pos (ENNReal.toReal_pos (bridgeMass_pos n).ne' (bridgeMass_finite n).ne) (hP n)
  obtain ⟨c,C,hc,hC,hfinite⟩:=finite_positive_bounds hf K
  refine ⟨min a c,max A C,lt_min ha hc,lt_of_lt_of_le hA (le_max_left _ _),?_⟩
  intro n
  change ENNReal.ofReal (min a c*P n)≤bridgeMass n ∧
    bridgeMass n≤ENNReal.ofReal (max A C*P n)
  by_cases hn : K≤n
  · have h:=(hK n hn)
    simp only [add_comm (n:ℝ) 1] at h
    exact ⟨(ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left a c) (hP n).le)).trans h.1,
      h.2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left A C) (hP n).le))⟩
  · have h:=hfinite n (Nat.lt_of_not_ge hn)
    have hl : min a c*P n≤(bridgeMass n).toReal :=
      (le_div_iff₀ (hP n)).mp ((min_le_right a c).trans h.1)
    have hu : (bridgeMass n).toReal ≤ max A C*P n :=
      (div_le_iff₀ (hP n)).mp (h.2.trans (le_max_right A C))
    constructor
    · have t:=ENNReal.ofReal_le_ofReal hl
      rwa [ENNReal.ofReal_toReal (bridgeMass_finite n).ne] at t
    · have t:=ENNReal.ofReal_le_ofReal hu
      rwa [ENNReal.ofReal_toReal (bridgeMass_finite n).ne] at t

end CriticalHoneycomb

end

end OAI
