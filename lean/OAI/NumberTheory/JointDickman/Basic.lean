import Mathlib.Data.Nat.MaxPrimeFac
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace OAI

/-!
# Arithmetic and counting conventions for the joint Dickman law

`Nat.maxPrimeFac` has exactly the paper's convention `P⁺(1) = 1`.
The counting endpoint below is an integer; the paper's real endpoint is
obtained by flooring it.
-/

namespace JointDickman

/-- The logarithmic size of the largest prime factor of `n`, measured at `base`. -/
noncomputable def normalizedPrimeFactor (base n : ℕ) : ℝ :=
  Real.log (n.maxPrimeFac : ℝ) / Real.log (base : ℝ)

/-- The fixed-scale smoothness event in the proof of the joint law. -/
def fixedScaleEvent (a b : ℝ) (N n : ℕ) : Prop :=
  (n.maxPrimeFac : ℝ) ≤ (N : ℝ) ^ a ∧
    ((n + 1).maxPrimeFac : ℝ) ≤ (N : ℝ) ^ b

/-- The moving-threshold event in the main theorem. -/
def movingEvent (a b : ℝ) (n : ℕ) : Prop :=
  (n.maxPrimeFac : ℝ) ≤ (n : ℝ) ^ a ∧
    ((n + 1).maxPrimeFac : ℝ) ≤ (n : ℝ) ^ b

/-- Ordinary counting on the paper's interval `2 ≤ n ≤ N`. -/
noncomputable def empiricalCount (P : ℕ → Prop) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 2 N).filter P).card

/-- Ordinary, unweighted density normalized by the counting endpoint. -/
noncomputable def empiricalDensity (P : ℕ → Prop) (N : ℕ) : ℝ :=
  (empiricalCount P N : ℝ) / N

theorem maxPrimeFac_ne_succ {n : ℕ} (hn : 2 ≤ n) :
    n.maxPrimeFac ≠ (n + 1).maxPrimeFac := by
  intro heq
  have hcop : n.Coprime (n + 1) := by simp
  have hcommon : n.maxPrimeFac ∣ n + 1 := heq ▸ Nat.maxPrimeFac_dvd
  have hone : n.maxPrimeFac = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop Nat.maxPrimeFac_dvd hcommon
  have hp := Nat.prime_maxPrimeFac_of_one_lt (show 1 < n by omega)
  exact hp.ne_one hone

theorem maxPrimeFac_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < (n.maxPrimeFac : ℝ) := by
  have h := Nat.one_le_maxPrimeFac_iff.mpr hn
  exact_mod_cast (show 0 < n.maxPrimeFac by omega)

theorem normalizedPrimeFactor_nonneg {base n : ℕ} (hn : 1 ≤ n) :
    0 ≤ normalizedPrimeFactor base n := by
  apply div_nonneg
  · apply Real.log_nonneg
    exact_mod_cast Nat.one_le_maxPrimeFac_iff.mpr hn
  · exact Real.log_natCast_nonneg base

theorem normalizedPrimeFactor_le_one {n : ℕ} (hn : 2 ≤ n) :
    normalizedPrimeFactor n n ≤ 1 := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  rw [normalizedPrimeFactor, div_le_one (Real.log_pos hn')]
  apply Real.log_le_log (maxPrimeFac_pos (by omega))
  exact_mod_cast Nat.maxPrimeFac_le (n := n)

/-- The second coordinate can exceed one only by the indicated vanishing error. -/
theorem normalizedPrimeFactor_succ_le {n : ℕ} (hn : 2 ≤ n) :
    normalizedPrimeFactor n (n + 1) ≤
      1 + 1 / ((n : ℝ) * Real.log (n : ℝ)) := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnpos : (0 : ℝ) < n := lt_trans zero_lt_one hn'
  have hn1pos : (0 : ℝ) < n + 1 := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hn1pos hnpos)
  rw [Real.log_div (ne_of_gt hn1pos) (ne_of_gt hnpos)] at hlog
  have hquot : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
  rw [hquot] at hlog
  have hmax : Real.log ((n + 1).maxPrimeFac : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
    apply Real.log_le_log (maxPrimeFac_pos (by omega))
    exact_mod_cast Nat.maxPrimeFac_le (n := n + 1)
  rw [normalizedPrimeFactor, div_le_iff₀ (Real.log_pos hn')]
  have hlogne : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hn')
  have hid : (1 + 1 / ((n : ℝ) * Real.log n)) * Real.log n =
      Real.log n + 1 / n := by field_simp
  rw [hid]
  linarith

theorem normalizedPrimeFactor_le_iff {base n : ℕ} (hbase : 2 ≤ base)
    (hn : 1 ≤ n) (a : ℝ) :
    normalizedPrimeFactor base n ≤ a ↔ (n.maxPrimeFac : ℝ) ≤ (base : ℝ) ^ a := by
  have hbase' : (1 : ℝ) < base := by exact_mod_cast (show 1 < base by omega)
  rw [normalizedPrimeFactor, div_le_iff₀ (Real.log_pos hbase')]
  exact (Real.le_rpow_iff_log_le (maxPrimeFac_pos hn) (by linarith)).symm

theorem normalizedPrimeFactor_lt_iff {base n : ℕ} (hbase : 2 ≤ base)
    (hn : 1 ≤ n) (a : ℝ) :
    normalizedPrimeFactor base n < a ↔ (n.maxPrimeFac : ℝ) < (base : ℝ) ^ a := by
  have hbase' : (1 : ℝ) < base := by exact_mod_cast (show 1 < base by omega)
  rw [normalizedPrimeFactor, div_lt_iff₀ (Real.log_pos hbase')]
  exact (Real.lt_rpow_iff_log_lt (maxPrimeFac_pos hn) (by linarith)).symm

theorem normalizedPrimeFactor_order_iff {base m n : ℕ}
    (hbase : 2 ≤ base) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    normalizedPrimeFactor base m < normalizedPrimeFactor base n ↔
      m.maxPrimeFac < n.maxPrimeFac := by
  have hbase' : (1 : ℝ) < base := by exact_mod_cast (show 1 < base by omega)
  rw [normalizedPrimeFactor, normalizedPrimeFactor,
    div_lt_div_iff_of_pos_right (Real.log_pos hbase'),
    Real.log_lt_log_iff (maxPrimeFac_pos hm) (maxPrimeFac_pos hn)]
  exact Nat.cast_lt

theorem movingEvent_iff_normalized {n : ℕ} (hn : 2 ≤ n) (a b : ℝ) :
    movingEvent a b n ↔
      normalizedPrimeFactor n n ≤ a ∧ normalizedPrimeFactor n (n + 1) ≤ b := by
  rw [movingEvent, normalizedPrimeFactor_le_iff hn (by omega),
    normalizedPrimeFactor_le_iff hn (by omega)]

theorem fixedScaleEvent_iff_normalized {N n : ℕ} (hN : 2 ≤ N) (hn : 1 ≤ n)
    (a b : ℝ) :
    fixedScaleEvent a b N n ↔
      normalizedPrimeFactor N n ≤ a ∧ normalizedPrimeFactor N (n + 1) ≤ b := by
  rw [fixedScaleEvent, normalizedPrimeFactor_le_iff hN hn,
    normalizedPrimeFactor_le_iff hN (by omega)]

theorem empiricalDensity_nonneg (P : ℕ → Prop) (N : ℕ) :
    0 ≤ empiricalDensity P N := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem empiricalCount_mono {P Q : ℕ → Prop} {N : ℕ}
    (h : ∀ n ∈ Finset.Icc 2 N, P n → Q n) :
    empiricalCount P N ≤ empiricalCount Q N := by
  classical
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, h n hn.1 hn.2⟩

theorem empiricalDensity_mono {P Q : ℕ → Prop} {N : ℕ}
    (h : ∀ n ∈ Finset.Icc 2 N, P n → Q n) :
    empiricalDensity P N ≤ empiricalDensity Q N := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast empiricalCount_mono h

/-- The two strict orderings partition all consecutive pairs in the counting range. -/
theorem orderingCounts_add (N : ℕ) :
    empiricalCount (fun n => n.maxPrimeFac < (n + 1).maxPrimeFac) N +
      empiricalCount (fun n => (n + 1).maxPrimeFac < n.maxPrimeFac) N = N - 1 := by
  classical
  have hfilter : (Finset.Icc 2 N).filter (fun n => (n + 1).maxPrimeFac < n.maxPrimeFac) =
      (Finset.Icc 2 N).filter (fun n => ¬n.maxPrimeFac < (n + 1).maxPrimeFac) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1, not_lt.mpr h.2.le⟩
    · rintro ⟨hmem, h⟩
      exact ⟨hmem, lt_of_le_of_ne (not_lt.mp h)
        (maxPrimeFac_ne_succ (Finset.mem_Icc.mp hmem).1).symm⟩
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc 2 N) (fun n => n.maxPrimeFac < (n + 1).maxPrimeFac)
  rw [← hfilter] at hsum
  simp only [Nat.card_Icc] at hsum
  convert hsum using 1
  all_goals
    first
    | omega
    | simp only [empiricalCount]
      congr 2 <;> ext n <;> simp

end JointDickman

end OAI
