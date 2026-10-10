import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterBlocks
import OAI.Analysis.IrrationalRotation.Couplings.CouplingMarginalBounds

namespace OAI

noncomputable section
open scoped BigOperators

namespace Invariant233.TailScaleCover

theorem exists_window_of_overlap (left right : ℕ → ℝ) (j : ℕ) (t : ℝ)
    (hunbounded : ∀ R : ℝ, ∃ s : ℕ, j ≤ s ∧ R ≤ right s)
    (hoverlap : ∀ s : ℕ, j ≤ s → left (s + 1) ≤ right s) :
    ∃ s : ℕ, j ≤ s ∧ t ≤ right s ∧ (s = j ∨ left s ≤ t) := by
  have hex : ∃ n : ℕ, t ≤ right (j + n) := by
    obtain ⟨s, hjs, hs⟩ := hunbounded t
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjs
    exact ⟨n, hs⟩
  let n := Nat.find hex
  have hn : t ≤ right (j + n) := Nat.find_spec hex
  refine ⟨j + n, by omega, hn, ?_⟩
  by_cases hn0 : n = 0
  · left
    simp [hn0]
  · right
    have hprev : ¬ t ≤ right (j + (n - 1)) :=
      Nat.find_min hex (show n - 1 < Nat.find hex by change n - 1 < n; omega)
    have hstep := hoverlap (j + (n - 1)) (by omega)
    have heq : j + (n - 1) + 1 = j + n := by omega
    rw [heq] at hstep
    exact hstep.trans (le_of_lt (lt_of_not_ge hprev))

theorem lower_intensity_eq (κ G m : ℝ) (hG : 0 ≤ G) (hm : 0 < m) :
    m * (κ * Real.sqrt ((G / m) / m)) = κ * Real.sqrt G := by
  have hdiv : (G / m) / m = G / m ^ 2 := by ring
  rw [hdiv, Real.sqrt_div hG, Real.sqrt_sq hm.le]
  field_simp

theorem upper_intensity_eq (κ m : ℝ) (hm : 0 < m) :
    m * (κ * Real.sqrt (m ^ (-(19 / 20 : ℝ)) / m)) =
      κ * m ^ (1 / 40 : ℝ) := by
  have hdiv : m ^ (-(19 / 20 : ℝ)) / m = m ^ (-(39 / 20 : ℝ)) := by
    calc
      _ = m ^ (-(19 / 20 : ℝ)) / m ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = m ^ (-(19 / 20 : ℝ) - 1) := (Real.rpow_sub hm _ _).symm
      _ = _ := by norm_num
  have hsqrt : Real.sqrt (m ^ (-(19 / 20 : ℝ)) / m) =
      m ^ (-(39 / 40 : ℝ)) := by
    rw [hdiv, Real.sqrt_eq_rpow, ← Real.rpow_mul hm.le]
    norm_num
  rw [hsqrt]
  calc
    _ = κ * (m ^ (1 : ℝ) * m ^ (-(39 / 40 : ℝ))) := by
      rw [Real.rpow_one]
      ring
    _ = κ * m ^ ((1 : ℝ) + -(39 / 40 : ℝ)) := by rw [Real.rpow_add hm]
    _ = _ := by norm_num

end TailScaleCover

namespace CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem index_le_tail_horizon (s : ℕ) (hs : 1 ≤ s) :
    (s : ℝ) ≤ (p.m s : ℝ) ^ ((4 / 5 : ℝ) * p.m s) := by
  have hsm : s ≤ p.m s := (Nat.lt_two_pow_self.le).trans (hp.m_ge_pow s hs)
  have hm200 : (200 : ℝ) ≤ p.m s := by exact_mod_cast hp.m_ge_200 s hs
  calc
    (s : ℝ) ≤ (p.m s : ℝ) := by exact_mod_cast hsm
    _ = (p.m s : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem tail_windows_cover (j : ℕ) (hj : 1 ≤ j) (t : ℝ)
    (ht : p.N j / 4 ≤ t) :
    ∃ s : ℕ, j ≤ s ∧ t ≤ (p.m s : ℝ) ^ ((4 / 5 : ℝ) * p.m s) ∧
      ((s = j ∧ p.N s / 4 ≤ t) ∨ (j < s ∧ (p.G s : ℝ) * p.K s ≤ t)) := by
  obtain ⟨s, hjs, hs, hleft⟩ := TailScaleCover.exists_window_of_overlap
    (fun s => (p.G s : ℝ) * p.K s)
    (fun s => (p.m s : ℝ) ^ ((4 / 5 : ℝ) * p.m s)) j t
    (by
      intro R
      obtain ⟨n, hn⟩ := exists_nat_gt (max R (j : ℝ))
      have hjn : j ≤ n := by
        have hlt : (j : ℝ) < n := (le_max_right _ _).trans_lt hn
        exact_mod_cast hlt.le
      refine ⟨n, hjn, ?_⟩
      exact ((le_max_left _ _).trans hn.le).trans
        (hp.index_le_tail_horizon n (hj.trans hjn)))
    (fun s hs => (hp.next_G_gap s (hj.trans hs)).le)
  refine ⟨s, hjs, hs, ?_⟩
  rcases hleft with hsj | hleft
  · left
    exact ⟨hsj, hsj ▸ ht⟩
  · by_cases hsj : s = j
    · left
      exact ⟨hsj, hsj ▸ ht⟩
    · right
      exact ⟨lt_of_le_of_ne hjs (Ne.symm hsj), hleft⟩

theorem upper_crossing_intensity (j s : ℕ) (hj : 1 ≤ j) (hjs : j ≤ s) :
    p.L j ≤ (p.m s : ℝ) *
      (kappa s * Real.sqrt (p.b s / (p.m s : ℝ))) := by
  have hs := hj.trans hjs
  have hm : 0 < (p.m s : ℝ) := by exact_mod_cast hp.m_pos s hs
  rw [CircleParameterData.b, TailScaleCover.upper_intensity_eq _ _ hm]
  exact (hp.L_monotone j s hj hjs).trans (hp.attenuation_m s hs)

theorem lower_crossing_intensity (j s : ℕ) (hj : 1 ≤ j) (hjs : j < s) :
    p.L j ≤ (p.m s : ℝ) *
      (kappa s * Real.sqrt (p.a s / (p.m s : ℝ))) := by
  have hs : 1 ≤ s := by omega
  have hm : 0 < (p.m s : ℝ) := by exact_mod_cast hp.m_pos s hs
  rw [CircleParameterData.a, TailScaleCover.lower_intensity_eq _ _ _
    (Nat.cast_nonneg _) hm]
  have hatten := hp.attenuation_G (s - 1) (by omega)
  have heq : s - 1 + 1 = s := by omega
  rw [heq] at hatten
  exact (hp.L_monotone j (s - 1) hj (by omega)).trans hatten

theorem exists_tail_crossing_set (j : ℕ) (hj : 1 ≤ j) (k : ℤ)
    (hk : p.N j / 4 ≤ |(k : ℝ)|) :
    ∃ (s : ℕ) (w : ℝ) (I : Finset ℕ),
      j ≤ s ∧ (w = p.b s ∨ (j < s ∧ w = p.a s)) ∧
      I ⊆ p.block s ∧ (p.m s : ℝ) / 20 ≤ (I.card : ℝ) ∧
      (∀ i ∈ I, 1 - Int.fract ((k : ℝ) * p.alpha θ i) ∈ Set.Icc w (1 - w)) ∧
      p.L j ≤ (p.m s : ℝ) * (kappa s * Real.sqrt (w / (p.m s : ℝ))) ∧
      p.L j ≤ p.C s := by
  classical
  obtain ⟨s, hjs, htop, hleft⟩ := hp.tail_windows_cover j hj |(k : ℝ)| hk
  have hs : 1 ≤ s := hj.trans hjs
  have hcost : p.L j ≤ p.C s := by
    rw [hp.C_eq s hs]
    exact (hp.L_monotone j s hj hjs).trans (le_max_left _ _)
  by_cases hhigh : p.N s / 4 ≤ |(k : ℝ)|
  · let I := (p.block s).filter (fun i =>
      1 - Int.fract ((k : ℝ) * p.alpha θ i) ∈ Set.Icc (p.b s) (1 - p.b s))
    refine ⟨s, p.b s, I, hjs, Or.inl rfl, Finset.filter_subset _ _,
      hp.spread_high s hs k hhigh htop, ?_,
      hp.upper_crossing_intensity j s hj hjs, hcost⟩
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  · have hlow : j < s ∧ (p.G s : ℝ) * p.K s ≤ |(k : ℝ)| := by
      rcases hleft with ⟨hsj, hstart⟩ | hlow
      · exact False.elim (hhigh hstart)
      · exact hlow
    refine ⟨s, p.a s, p.block s, hjs, Or.inr ⟨hlow.1, rfl⟩,
      Finset.Subset.refl _, ?_, hp.spread_low s hs k hlow.2 (le_of_not_ge hhigh),
      hp.lower_crossing_intensity j s hj hlow.1, hcost⟩
    rw [p.card_block s hs]
    have hm : 0 ≤ (p.m s : ℝ) := Nat.cast_nonneg _
    linarith

end CircleParameterLaws
end Invariant233

noncomputable section
open Set
open scoped BigOperators

namespace Invariant233.TailScaleCover

theorem exists_window
    (a b Q : ℕ → ℝ) (j : ℕ)
    (hgap : ∀ s, j ≤ s → a (s + 1) ≤ Q s)
    (hunbounded : ∀ R : ℝ, ∃ s, j ≤ s ∧ R ≤ Q s)
    {t : ℝ} (ht : b j ≤ t) :
    ∃ s, j ≤ s ∧
      ((b s ≤ t ∧ t ≤ Q s) ∨ (j < s ∧ a s ≤ t ∧ t ≤ b s)) := by
  classical
  let h := hunbounded t
  let s := Nat.find h
  have hs : j ≤ s ∧ t ≤ Q s := Nat.find_spec h
  refine ⟨s, hs.1, ?_⟩
  by_cases hb : b s ≤ t
  · exact Or.inl ⟨hb, hs.2⟩
  · right
    have hjs : j < s := by
      apply lt_of_le_of_ne hs.1
      intro heq
      exact hb (heq ▸ ht)
    have hprev : Q (s - 1) < t := by
      by_contra hnot
      have hsmall : s ≤ s - 1 := Nat.find_min' h ⟨by omega, le_of_not_gt hnot⟩
      omega
    have ha : a s ≤ t := by
      have hg := hgap (s - 1) (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ s)] at hg
      exact hg.trans hprev.le
    exact ⟨hjs, ha, le_of_not_ge hb⟩

def upperHorizon (m : ℕ) : ℝ := (m : ℝ) ^ ((4 / 5 : ℝ) * m)

theorem self_le_upperHorizon {m : ℕ} (hm : 2 ≤ m) :
    (m : ℝ) ≤ upperHorizon m := by
  apply Real.self_le_rpow_of_one_le
  · exact_mod_cast (show 1 ≤ m by omega)
  · have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith

theorem intensity_small (κ m G : ℝ) (hm : 0 < m) (hG : 0 ≤ G) :
    m * CouplingMarginalBounds.rho κ m (G / m) = κ * Real.sqrt G := by
  unfold CouplingMarginalBounds.rho
  have hdiv : (G / m) / m = G / m ^ 2 := by ring
  rw [hdiv, Real.sqrt_div hG, Real.sqrt_sq_eq_abs, abs_of_pos hm]
  field_simp

theorem intensity_large (κ m : ℝ) (hm : 0 < m) :
    m * CouplingMarginalBounds.rho κ m (m ^ (-(19 / 20 : ℝ))) =
      κ * m ^ (1 / 40 : ℝ) := by
  unfold CouplingMarginalBounds.rho
  rw [Real.sqrt_eq_rpow]
  have hdiv : m ^ (-(19 / 20 : ℝ)) / m = m ^ (-(39 / 20 : ℝ)) := by
    rw [show (-(39 / 20 : ℝ)) = -(19 / 20 : ℝ) - 1 by norm_num,
      Real.rpow_sub hm, Real.rpow_one]
  rw [hdiv, ← Real.rpow_mul hm.le]
  have hpow : m * m ^ ((-(39 / 20 : ℝ)) * (1 / 2 : ℝ)) =
      m ^ (1 / 40 : ℝ) := by
    calc
      _ = m ^ (1 : ℝ) * m ^ ((-(39 / 20 : ℝ)) * (1 / 2 : ℝ)) := by
        rw [Real.rpow_one]
      _ = m ^ (1 + (-(39 / 20 : ℝ)) * (1 / 2 : ℝ)) :=
        (Real.rpow_add hm _ _).symm
      _ = _ := by norm_num
  calc
    m * (κ * m ^ ((-(39 / 20 : ℝ)) * (1 / 2 : ℝ))) =
        κ * (m * m ^ ((-(39 / 20 : ℝ)) * (1 / 2 : ℝ))) := by ring
    _ = _ := by rw [hpow]

theorem widths_mem_Icc {m G : ℝ} (hm : 16 ≤ m) (hG : 1 ≤ G)
    (hGm : 4 * G ≤ m) :
    G / m ∈ Set.Icc (1 / m) (1 / 4) ∧
      m ^ (-(19 / 20 : ℝ)) ∈ Set.Icc (1 / m) (1 / 4) := by
  have hmpos : 0 < m := by linarith
  have hmone : 1 ≤ m := by linarith
  constructor
  · constructor
    · exact div_le_div_of_nonneg_right hG hmpos.le
    · apply (div_le_iff₀ hmpos).mpr
      linarith
  · rw [Real.rpow_neg hmpos.le, inv_eq_one_div]
    constructor
    · apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos hmpos _)
      calc
        m ^ (19 / 20 : ℝ) ≤ m ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hmone (by norm_num)
        _ = m := Real.rpow_one _
    · apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
      have hsqrt : 4 ≤ Real.sqrt m := by
        nlinarith [Real.sq_sqrt hmpos.le, Real.sqrt_nonneg m]
      calc
        4 ≤ Real.sqrt m := hsqrt
        _ = m ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
        _ ≤ m ^ (19 / 20 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hmone (by norm_num)

end Invariant233.TailScaleCover

namespace Invariant233.CircleParameterLaws

open CircleParameterData TailScaleCover

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem upperHorizon_unbounded (j : ℕ) (hj : 1 ≤ j) (R : ℝ) :
    ∃ s, j ≤ s ∧ R ≤ upperHorizon (p.m s) := by
  obtain ⟨n, hn⟩ := exists_nat_gt R
  let s := max j n
  have hjs : j ≤ s := le_max_left _ _
  have hs : 1 ≤ s := hj.trans hjs
  have hsm : s ≤ p.m s :=
    (Nat.lt_two_pow_self (n := s)).le.trans (hp.m_ge_pow s hs)
  refine ⟨s, hjs, ?_⟩
  calc
    R ≤ (n : ℝ) := hn.le
    _ ≤ (s : ℝ) := by exact_mod_cast (le_max_right j n)
    _ ≤ (p.m s : ℝ) := by exact_mod_cast hsm
    _ ≤ upperHorizon (p.m s) := self_le_upperHorizon (by
      have := hp.m_ge_200 s hs
      omega)

theorem exists_tail_window (j : ℕ) (hj : 1 ≤ j) {t : ℝ}
    (ht : p.N j / 4 ≤ t) :
    ∃ s, j ≤ s ∧
      ((p.N s / 4 ≤ t ∧ t ≤ upperHorizon (p.m s)) ∨
        (j < s ∧ (p.G s : ℝ) * p.K s ≤ t ∧ t ≤ p.N s / 4)) := by
  apply exists_window (fun s => (p.G s : ℝ) * p.K s)
    (fun s => p.N s / 4) (fun s => upperHorizon (p.m s)) j
  · intro s hs
    exact (hp.next_G_gap s (hj.trans hs)).le
  · exact hp.upperHorizon_unbounded j hj
  · exact ht

theorem exists_tail_thresholds (j : ℕ) (hj : 1 ≤ j) (k : ℤ)
    (hk : p.N j / 4 ≤ |(k : ℝ)|) :
    ∃ (s : ℕ) (w : ℝ) (I : Finset ℕ),
      j ≤ s ∧ (w = p.b s ∨ (j < s ∧ w = p.a s)) ∧
      I ⊆ p.block s ∧ (p.m s : ℝ) / 20 ≤ I.card ∧
      (∀ i ∈ I, 1 - Int.fract ((k : ℝ) * p.alpha θ i) ∈ Set.Icc w (1 - w)) ∧
      p.L j ≤ (p.m s : ℝ) * CouplingMarginalBounds.rho (kappa s) (p.m s) w ∧
      p.L j ≤ p.C s := by
  classical
  obtain ⟨s, hjs, hs⟩ := hp.exists_tail_window j hj hk
  have hspos : 1 ≤ s := hj.trans hjs
  have hm : (0 : ℝ) < p.m s := by exact_mod_cast hp.m_pos s hspos
  have hL : p.L j ≤ p.L s := hp.L_monotone j s hj hjs
  have hC : p.L j ≤ p.C s := by
    rw [hp.C_eq s hspos]
    exact hL.trans (le_max_left _ _)
  rcases hs with hhigh | hlow
  · refine ⟨s, p.b s, (p.block s).filter (fun i =>
        1 - Int.fract ((k : ℝ) * p.alpha θ i) ∈ Set.Icc (p.b s) (1 - p.b s)),
      hjs, Or.inl rfl, Finset.filter_subset _ _,
      hp.spread_high s hspos k hhigh.1 hhigh.2, ?_, ?_, hC⟩
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · rw [CircleParameterData.b, intensity_large _ _ hm]
      exact hL.trans (hp.attenuation_m s hspos)
  · refine ⟨s, p.a s, p.block s, hjs, Or.inr ⟨hlow.1, rfl⟩,
      Finset.Subset.refl _, ?_, hp.spread_low s hspos k hlow.2.1 hlow.2.2, ?_, hC⟩
    · rw [p.card_block s hspos]
      linarith [hm.le]
    · rw [CircleParameterData.a, intensity_small _ _ _ hm (Nat.cast_nonneg _)]
      have hprev : 1 ≤ s - 1 := by omega
      have hjs' : j ≤ s - 1 := by omega
      have hbound := hp.attenuation_G (s - 1) hprev
      rw [Nat.sub_add_cancel (by omega : 1 ≤ s)] at hbound
      exact (hp.L_monotone j (s - 1) hj hjs').trans hbound

theorem exists_admissible_tail_thresholds (j : ℕ) (hj : 1 ≤ j) (k : ℤ)
    (hk : p.N j / 4 ≤ |(k : ℝ)|) :
    ∃ (s : ℕ) (w : ℝ) (I : Finset ℕ),
      j ≤ s ∧ (w = p.b s ∨ (j < s ∧ w = p.a s)) ∧
      w ∈ Set.Icc (1 / (p.m s : ℝ)) (1 / 4) ∧
      I ⊆ p.block s ∧ (p.m s : ℝ) / 20 ≤ I.card ∧
      (∀ i ∈ I, 1 - Int.fract ((k : ℝ) * p.alpha θ i) ∈ Set.Icc w (1 - w)) ∧
      p.L j ≤ (p.m s : ℝ) * CouplingMarginalBounds.rho (kappa s) (p.m s) w ∧
      p.L j ≤ p.C s := by
  obtain ⟨s, w, I, hjs, hw, hI, hcard, hphase, hintensity, hC⟩ :=
    hp.exists_tail_thresholds j hj k hk
  have hs : 1 ≤ s := hj.trans hjs
  have hwidths := widths_mem_Icc
    (show (16 : ℝ) ≤ p.m s by
      have hm : (200 : ℝ) ≤ p.m s := by exact_mod_cast hp.m_ge_200 s hs
      linarith)
    (show (1 : ℝ) ≤ p.G s by exact_mod_cast hp.G_pos s hs)
    (show 4 * (p.G s : ℝ) ≤ p.m s by exact_mod_cast hp.m_ge_G s hs)
  refine ⟨s, w, I, hjs, hw, ?_, hI, hcard, hphase, hintensity, hC⟩
  rcases hw with rfl | ⟨_, rfl⟩
  · exact hwidths.2
  · exact hwidths.1

end Invariant233.CircleParameterLaws

end
end

end OAI
