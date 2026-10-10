import OAI.Analysis.MarkovType.DyadicTree
import OAI.Analysis.MarkovType.HomogeneousPotential
import OAI.Analysis.MarkovType.MidpointPotential
import OAI.Analysis.MarkovType.RenormingBasic
import OAI.Analysis.MarkovType.PowerConvexity
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Module

namespace OAI

namespace MarkovSuperreflexivity

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

def FiniteDyadicCotype (q A : ℝ) : Prop :=
  ∀ t : DyadicTree E, DyadicTree.root t = 0 →
    DyadicTree.energy q t ≤ A * DyadicTree.moment q t

variable {E}

namespace DyadicConvex

open DyadicTree

noncomputable def cost (q β : ℝ) (t : DyadicTree E) : ℝ :=
  moment q t - β * energy q t

def values (q β : ℝ) (x : E) : Set ℝ :=
  {z | ∃ t : DyadicTree E, root t = x ∧ cost q β t = z}

noncomputable def potential (q β : ℝ) (x : E) : ℝ :=
  sInf (values q β x)

theorem values_nonempty (q β : ℝ) (x : E) : (values q β x).Nonempty :=
  ⟨cost q β (leaf x), leaf x, rfl, rfl⟩

theorem cost_leaf (q β : ℝ) (x : E) : cost q β (leaf x) = ‖x‖ ^ q := by
  simp only [cost, moment_leaf, energy_leaf, mul_zero, sub_zero]

theorem cost_node (q β : ℝ) (t u : DyadicTree E) :
    cost q β (node t u) = (cost q β t + cost q β u) / 2 -
      β * ‖(2 : ℝ)⁻¹ • (root t - root u)‖ ^ q := by
  simp only [cost, moment_node, energy_node]
  ring

theorem cost_scale (q β a : ℝ) (t : DyadicTree E) :
    cost q β (scale a t) = ‖a‖ ^ q * cost q β t := by
  simp only [cost, moment_scale, energy_scale, Real.norm_eq_abs]
  ring

theorem root_add_energy_le {q A : ℝ} (hc : FiniteDyadicCotype E q A)
    (t : DyadicTree E) : ‖root t‖ ^ q + energy q t ≤ A * moment q t := by
  have hr : root (node t (scale (-1 : ℝ) t)) = 0 := by
    rw [root_node, root_scale]
    simp only [neg_one_smul, add_neg_cancel, smul_zero]
  have h := hc (node t (scale (-1 : ℝ) t)) hr
  simp only [energy_node, moment_node, energy_scale, moment_scale, root_scale,
    abs_neg, abs_one, Real.one_rpow, one_mul, neg_one_smul] at h
  have he : (2 : ℝ)⁻¹ • (root t - -root t) = root t := by module
  rw [he] at h
  nlinarith only [h]

theorem cost_lower {q A : ℝ} (hA : 0 < A) (hc : FiniteDyadicCotype E q A)
    (t : DyadicTree E) : A⁻¹ * ‖root t‖ ^ q ≤ cost q A⁻¹ t := by
  have h := mul_le_mul_of_nonneg_left (root_add_energy_le hc t)
    (inv_nonneg.mpr hA.le)
  have h' : A⁻¹ * ‖root t‖ ^ q + A⁻¹ * energy q t ≤ moment q t := by
    simpa only [mul_add, ← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul] using h
  unfold cost
  linarith only [h']

theorem values_bddBelow {q A : ℝ} (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x : E) : BddBelow (values q A⁻¹ x) := by
  refine ⟨A⁻¹ * ‖x‖ ^ q, ?_⟩
  rintro z ⟨t, ht, rfl⟩
  simpa only [ht] using cost_lower hA hc t

theorem potential_lower {q A : ℝ} (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x : E) :
    A⁻¹ * ‖x‖ ^ q ≤ potential q A⁻¹ x := by
  apply le_csInf (values_nonempty q A⁻¹ x)
  rintro z ⟨t, ht, rfl⟩
  simpa only [ht] using cost_lower hA hc t

theorem potential_le_cost {q A : ℝ} (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (t : DyadicTree E) {x : E}
    (ht : root t = x) : potential q A⁻¹ x ≤ cost q A⁻¹ t :=
  csInf_le (values_bddBelow hA hc x) ⟨t, ht, rfl⟩

theorem potential_upper {q A : ℝ} (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x : E) :
    potential q A⁻¹ x ≤ ‖x‖ ^ q := by
  simpa only [cost_leaf] using potential_le_cost hA hc (leaf x) (x := x) rfl

theorem potential_nonneg {q A : ℝ} (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x : E) : 0 ≤ potential q A⁻¹ x :=
  (mul_nonneg (inv_nonneg.mpr hA.le) (Real.rpow_nonneg (norm_nonneg x) q)).trans
    (potential_lower hA hc x)

theorem potential_zero {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) : potential q A⁻¹ (0 : E) = 0 := by
  apply le_antisymm _ (potential_nonneg hA hc 0)
  simpa only [norm_zero, Real.zero_rpow hq.ne'] using potential_upper hA hc (0 : E)

theorem exists_cost_lt (q β : ℝ) (x : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : DyadicTree E, root t = x ∧ cost q β t < potential q β x + ε := by
  have hlt : potential q β x < potential q β x + ε := lt_add_of_pos_right _ hε
  obtain ⟨z, ⟨t, ht, hz⟩, hzt⟩ :=
    exists_lt_of_csInf_lt (values_nonempty q β x) hlt
  exact ⟨t, ht, by simpa only [hz] using hzt⟩

theorem potential_midpoint {q A : ℝ} (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x y : E) :
    potential q A⁻¹ ((2 : ℝ)⁻¹ • (x + y)) +
        A⁻¹ * ‖(2 : ℝ)⁻¹ • (x - y)‖ ^ q ≤
      (potential q A⁻¹ x + potential q A⁻¹ y) / 2 := by
  have happrox (ε : ℝ) (hε : 0 < ε) :
      potential q A⁻¹ ((2 : ℝ)⁻¹ • (x + y)) +
          A⁻¹ * ‖(2 : ℝ)⁻¹ • (x - y)‖ ^ q ≤
        (potential q A⁻¹ x + potential q A⁻¹ y) / 2 + ε := by
    obtain ⟨t, ht, hcostt⟩ := exists_cost_lt q A⁻¹ x ε hε
    obtain ⟨u, hu, hcostu⟩ := exists_cost_lt q A⁻¹ y ε hε
    have hroot : root (node t u) = (2 : ℝ)⁻¹ • (x + y) := by
      rw [root_node, ht, hu]
    have hcost := potential_le_cost hA hc (node t u) hroot
    rw [cost_node, ht, hu] at hcost
    linarith only [hcost, hcostt, hcostu]
  by_contra h
  have hgap : 0 < potential q A⁻¹ ((2 : ℝ)⁻¹ • (x + y)) +
      A⁻¹ * ‖(2 : ℝ)⁻¹ • (x - y)‖ ^ q -
      (potential q A⁻¹ x + potential q A⁻¹ y) / 2 := sub_pos.mpr (lt_of_not_ge h)
  have hε := happrox
    ((potential q A⁻¹ ((2 : ℝ)⁻¹ • (x + y)) +
      A⁻¹ * ‖(2 : ℝ)⁻¹ • (x - y)‖ ^ q -
      (potential q A⁻¹ x + potential q A⁻¹ y) / 2) / 2)
    (half_pos hgap)
  linarith only [hε, hgap]

theorem potential_convex {q A : ℝ} (hq : 0 ≤ q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) : ConvexOn ℝ Set.univ (potential q A⁻¹ : E → ℝ) := by
  apply convexOn_of_midpoint_norm_power_bound q hq (potential q A⁻¹)
    (potential_nonneg hA hc) (potential_upper hA hc)
  intro x y
  have h := potential_midpoint hA hc x y
  have hterm : 0 ≤ A⁻¹ * ‖(2 : ℝ)⁻¹ • (x - y)‖ ^ q :=
    mul_nonneg (inv_nonneg.mpr hA.le) (Real.rpow_nonneg (norm_nonneg _) q)
  linarith only [h, hterm]

theorem potential_scale_le {q A : ℝ} (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (a : ℝ) (ha : a ≠ 0) (x : E) :
    potential q A⁻¹ (a • x) ≤ ‖a‖ ^ q * potential q A⁻¹ x := by
  have hpos : 0 < ‖a‖ ^ q := Real.rpow_pos_of_pos (norm_pos_iff.mpr ha) q
  have hquot : potential q A⁻¹ (a • x) / (‖a‖ ^ q) ≤ potential q A⁻¹ x := by
    apply le_csInf (values_nonempty q A⁻¹ x)
    rintro z ⟨t, ht, rfl⟩
    apply (div_le_iff₀ hpos).mpr
    have hroot : root (scale a t) = a • x := by rw [root_scale, ht]
    have h := potential_le_cost hA hc (scale a t) hroot
    simpa only [cost_scale, mul_comm] using h
  simpa only [mul_comm] using (div_le_iff₀ hpos).mp hquot

theorem potential_homogeneous {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (a : ℝ) (x : E) :
    potential q A⁻¹ (a • x) = ‖a‖ ^ q * potential q A⁻¹ x := by
  by_cases ha : a = 0
  · subst a
    simp only [zero_smul, potential_zero hq hA hc, norm_zero,
      Real.zero_rpow hq.ne', zero_mul]
  · apply le_antisymm (potential_scale_le hA hc a ha x)
    have h := potential_scale_le hA hc a⁻¹ (inv_ne_zero ha) (a • x)
    have he : a⁻¹ • (a • x) = x := by
      rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [he, norm_inv, Real.inv_rpow (norm_nonneg a)] at h
    have hpos : 0 < ‖a‖ ^ q := Real.rpow_pos_of_pos (norm_pos_iff.mpr ha) q
    have hm := mul_le_mul_of_nonneg_left h hpos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] using hm

noncomputable def seminorm {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) : Seminorm ℝ E :=
  potentialSeminorm q hq (potential q A⁻¹) (potential_nonneg hA hc)
    (potential_homogeneous hq hA hc) (potential_convex hq.le hA hc)

theorem seminorm_rpow {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x : E) :
    (seminorm hq hA hc x) ^ q = potential q A⁻¹ x :=
  potentialRoot_rpow q hq (potential q A⁻¹) (potential_nonneg hA hc) x

theorem seminorm_upper {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x : E) : seminorm hq hA hc x ≤ ‖x‖ :=
  (potentialRoot_le_iff q hq (potential q A⁻¹) (potential_nonneg hA hc)
    x ‖x‖ (norm_nonneg x)).mpr (potential_upper hA hc x)

theorem seminorm_lower {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x : E) :
    (A⁻¹ ^ (1 / q)) * ‖x‖ ≤ seminorm hq hA hc x := by
  have hβ : 0 ≤ A⁻¹ := inv_nonneg.mpr hA.le
  apply (le_potentialRoot_iff q hq (potential q A⁻¹) (potential_nonneg hA hc)
    x ((A⁻¹ ^ (1 / q)) * ‖x‖)
    (mul_nonneg (Real.rpow_nonneg hβ _) (norm_nonneg x))).mpr
  rw [Real.mul_rpow (Real.rpow_nonneg hβ _) (norm_nonneg x), one_div,
    Real.rpow_inv_rpow hβ hq.ne']
  exact potential_lower hA hc x

noncomputable def equivalentNorm {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) : EquivalentNorm E where
  p := seminorm hq hA hc
  lower := A⁻¹ ^ (1 / q)
  upper := 1
  lower_pos := Real.rpow_pos_of_pos (inv_pos.mpr hA) _
  upper_pos := zero_lt_one
  lower_bound := seminorm_lower hq hA hc
  upper_bound x := by simpa only [one_mul] using seminorm_upper hq hA hc x

theorem seminorm_symmetric_original {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x y : E) :
    (seminorm hq hA hc x) ^ q + A⁻¹ * ‖y‖ ^ q ≤
      ((seminorm hq hA hc (x + y)) ^ q + (seminorm hq hA hc (x - y)) ^ q) / 2 := by
  have h := potential_midpoint hA hc (x + y) (x - y)
  have hx : (2 : ℝ)⁻¹ • ((x + y) + (x - y)) = x := by module
  have hy : (2 : ℝ)⁻¹ • ((x + y) - (x - y)) = y := by module
  rw [hx, hy] at h
  simpa only [seminorm_rpow hq hA hc] using h

theorem seminorm_symmetric {q A : ℝ} (hq : 0 < q) (hA : 0 < A)
    (hc : FiniteDyadicCotype E q A) (x y : E) :
    (seminorm hq hA hc x) ^ q + A⁻¹ * (seminorm hq hA hc y) ^ q ≤
      ((seminorm hq hA hc (x + y)) ^ q + (seminorm hq hA hc (x - y)) ^ q) / 2 := by
  have h := seminorm_symmetric_original hq hA hc x y
  have hnonneg : 0 ≤ seminorm hq hA hc y :=
    potentialRoot_nonneg q (potential q A⁻¹) (potential_nonneg hA hc) y
  have hpow := Real.rpow_le_rpow hnonneg (seminorm_upper hq hA hc y) hq.le
  have hm := mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hA.le)
  linarith only [h, hm]

theorem equivalentNorm_uniformConvex {q A : ℝ} (hq : 0 < q) (hA : 1 ≤ A)
    (hc : FiniteDyadicCotype E q A) :
    UniformConvex (equivalentNorm hq (zero_lt_one.trans_le hA) hc).p := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hβone : A⁻¹ ≤ 1 := by
    simpa only [one_div] using (div_le_one hApos).mpr hA
  exact uniformConvex_of_symmetric_power (seminorm hq hApos hc) q A⁻¹ hq
    (inv_pos.mpr hApos) hβone (seminorm_symmetric hq hApos hc)

end DyadicConvex

theorem hasEquivalentUCNorm_of_finiteDyadicCotype {q A : ℝ}
    (hq : 2 ≤ q) (hA : 1 ≤ A) (hc : FiniteDyadicCotype E q A) :
    HasEquivalentUCNorm E := by
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hq
  have hApos : 0 < A := zero_lt_one.trans_le hA
  exact ⟨DyadicConvex.equivalentNorm hqpos hApos hc,
    DyadicConvex.equivalentNorm_uniformConvex hqpos hA hc⟩

end MarkovSuperreflexivity

end OAI
