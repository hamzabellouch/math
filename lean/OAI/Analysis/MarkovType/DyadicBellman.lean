import OAI.Analysis.MarkovType.DyadicTree
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Positivity

namespace OAI

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

open Set DyadicTree

def FiniteDyadicUpperEstimate (p A K : ℝ) : Prop :=
  ∀ t : DyadicTree X, moment p t ≤ A * ‖root t‖ ^ p + K * energy p t

noncomputable def dyadicObjective (p K : ℝ) (t : DyadicTree X) : ℝ :=
  moment p t - K * energy p t

def bellmanValues (p K : ℝ) (x : X) : Set ℝ :=
  {v | ∃ t : DyadicTree X, root t = x ∧ v = dyadicObjective p K t}

noncomputable def bellmanPotential (p K : ℝ) (x : X) : ℝ :=
  sSup (bellmanValues p K x)

theorem bellmanValues_nonempty (p K : ℝ) (x : X) :
    (bellmanValues p K x).Nonempty := by
  refine ⟨‖x‖ ^ p, leaf x, rfl, ?_⟩
  simp [dyadicObjective]

theorem bellmanValues_bddAbove {p A K : ℝ}
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (x : X) :
    BddAbove (bellmanValues p K x) := by
  refine ⟨A * ‖x‖ ^ p, ?_⟩
  rintro v ⟨t, ht, rfl⟩
  have h := hMT t
  rw [ht] at h
  dsimp [dyadicObjective]
  linarith

theorem dyadicObjective_le_bellman {p A K : ℝ}
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (t : DyadicTree X) :
    dyadicObjective p K t ≤ bellmanPotential p K (root t) :=
  le_csSup (bellmanValues_bddAbove hMT _) ⟨t, rfl, rfl⟩

theorem bellmanPotential_bounds {p A K : ℝ}
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (x : X) :
    ‖x‖ ^ p ≤ bellmanPotential p K x ∧
      bellmanPotential p K x ≤ A * ‖x‖ ^ p := by
  constructor
  · simpa [dyadicObjective] using dyadicObjective_le_bellman hMT (leaf x)
  · apply csSup_le (bellmanValues_nonempty p K x)
    rintro v ⟨t, ht, rfl⟩
    have h := hMT t
    rw [ht] at h
    dsimp [dyadicObjective]
    linarith

theorem bellmanPotential_nonneg {p A K : ℝ}
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (x : X) :
    0 ≤ bellmanPotential p K x :=
  (Real.rpow_nonneg (norm_nonneg x) p).trans (bellmanPotential_bounds hMT x).1

@[simp] theorem bellmanPotential_zero {p A K : ℝ} (hp : 0 < p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) :
    bellmanPotential p K (0 : X) = 0 := by
  have h := bellmanPotential_bounds hMT (0 : X)
  simp only [norm_zero, Real.zero_rpow hp.ne', mul_zero] at h
  exact le_antisymm h.2 h.1

@[simp] theorem dyadicObjective_scale (p K a : ℝ) (t : DyadicTree X) :
    dyadicObjective p K (scale a t) = |a| ^ p * dyadicObjective p K t := by
  simp only [dyadicObjective, moment_scale, energy_scale]
  ring

theorem bellmanPotential_smul {p A K : ℝ} (hp : 0 < p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (a : ℝ) (x : X) :
    bellmanPotential p K (a • x) = |a| ^ p * bellmanPotential p K x := by
  by_cases ha : a = 0
  · subst a
    simp [bellmanPotential_zero hp hMT, Real.zero_rpow hp.ne']
  have hk : 0 < |a| ^ p := Real.rpow_pos_of_pos (abs_pos.mpr ha) p
  apply le_antisymm
  · apply csSup_le (bellmanValues_nonempty p K (a • x))
    rintro v ⟨t, ht, rfl⟩
    have hr : root (scale a⁻¹ t) = x := by
      rw [root_scale, ht, smul_smul, inv_mul_cancel₀ ha, one_smul]
    have hc := dyadicObjective_le_bellman hMT (scale a⁻¹ t)
    rw [hr] at hc
    have hm := mul_le_mul_of_nonneg_left hc hk.le
    rw [← dyadicObjective_scale, scale_scale, mul_inv_cancel₀ ha, scale_one] at hm
    exact hm
  · have hh : bellmanPotential p K x ≤ bellmanPotential p K (a • x) / (|a| ^ p) := by
      apply csSup_le (bellmanValues_nonempty p K x)
      rintro v ⟨t, ht, rfl⟩
      apply (le_div_iff₀ hk).2
      have hc := dyadicObjective_le_bellman hMT (scale a t)
      rw [root_scale, ht, dyadicObjective_scale] at hc
      simpa only [mul_comm] using hc
    have hh' := (le_div_iff₀ hk).1 hh
    simpa only [mul_comm] using hh'

theorem norm_rpow_convex {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : X => ‖x‖ ^ p) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hn : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
  have hpow := (convexOn_rpow hp).2 (norm_nonneg x) (norm_nonneg y) ha hb hab
  exact (Real.rpow_le_rpow (norm_nonneg _) hn (by linarith)).trans hpow

theorem moment_translate_convex {p : ℝ} (hp : 1 ≤ p) (t : DyadicTree X)
    (x y : X) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    moment p (translate (a • x + b • y) t) ≤
      a * moment p (translate x t) + b * moment p (translate y t) := by
  change terminal (translate (a • x + b • y) t) (fun z => ‖z‖ ^ p) ≤ _
  rw [terminal_translate]
  calc
    terminal t (fun z => ‖a • x + b • y + z‖ ^ p) ≤
        terminal t (fun z => a * ‖x + z‖ ^ p + b * ‖y + z‖ ^ p) := by
      apply terminal_mono
      intro z
      have he : a • x + b • y + z = a • (x + z) + b • (y + z) := by
        calc
          _ = a • x + b • y + (a + b) • z := by rw [hab, one_smul]
          _ = _ := by module
      rw [he]
      exact (norm_rpow_convex hp).2 (mem_univ _) (mem_univ _) ha hb hab
    _ = a * moment p (translate x t) + b * moment p (translate y t) := by
      rw [terminal_linear]
      simp only [moment, terminal_translate]

theorem bellmanPotential_convex {p A K : ℝ} (hp : 1 ≤ p)
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) :
    ConvexOn ℝ Set.univ (bellmanPotential (X := X) p K) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  apply csSup_le (bellmanValues_nonempty p K (a • x + b • y))
  rintro v ⟨t, ht, rfl⟩
  let z := a • x + b • y
  let u := translate (-z) t
  have hu : root u = 0 := by
    change root (translate (-z) t) = 0
    rw [root_translate, ht]
    exact neg_add_cancel z
  have huz : translate z u = t := by simp [u]
  have huE : energy p u = energy p t := by simp [u]
  have hm := moment_translate_convex hp u x y ha hb hab
  change moment p (translate z u) ≤ _ at hm
  rw [huz] at hm
  have hJ : dyadicObjective p K t ≤
      a * dyadicObjective p K (translate x u) +
        b * dyadicObjective p K (translate y u) := by
    have hweight : a * (K * energy p t) + b * (K * energy p t) =
        K * energy p t := by
      rw [← add_mul, hab, one_mul]
    simp only [dyadicObjective, energy_translate, huE]
    nlinarith only [hm, hweight]
  have hxJ := dyadicObjective_le_bellman hMT (translate x u)
  have hyJ := dyadicObjective_le_bellman hMT (translate y u)
  simp only [root_translate, hu, add_zero] at hxJ hyJ
  exact hJ.trans (add_le_add (mul_le_mul_of_nonneg_left hxJ ha)
    (mul_le_mul_of_nonneg_left hyJ hb))

theorem exists_dyadicObjective_gt {p A K : ℝ}
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (x : X)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : DyadicTree X, root t = x ∧
      bellmanPotential p K x - ε < dyadicObjective p K t := by
  have hh : bellmanPotential p K x - ε < sSup (bellmanValues p K x) := by
    change bellmanPotential p K x - ε < bellmanPotential p K x
    linarith
  obtain ⟨v, ⟨t, ht, rfl⟩, hv⟩ :=
    (lt_csSup_iff (bellmanValues_bddAbove hMT x)
      (bellmanValues_nonempty p K x)).1 hh
  exact ⟨t, ht, hv⟩

theorem bellmanPotential_add_sub_le {p A K : ℝ}
    (hMT : FiniteDyadicUpperEstimate (X := X) p A K) (x y : X) :
    (bellmanPotential p K (x + y) + bellmanPotential p K (x - y)) / 2 ≤
      bellmanPotential p K x + K * ‖y‖ ^ p := by
  by_contra hn
  have hg : 0 < (bellmanPotential p K (x + y) +
      bellmanPotential p K (x - y)) / 2 -
        (bellmanPotential p K x + K * ‖y‖ ^ p) := by linarith
  let ε := ((bellmanPotential p K (x + y) + bellmanPotential p K (x - y)) / 2 -
    (bellmanPotential p K x + K * ‖y‖ ^ p)) / 2
  have hε : 0 < ε := div_pos hg (by norm_num)
  obtain ⟨t, ht, htJ⟩ := exists_dyadicObjective_gt hMT (x + y) hε
  obtain ⟨s, hs, hsJ⟩ := exists_dyadicObjective_gt hMT (x - y) hε
  have hr : root (node t s) = x := by rw [root_node, ht, hs]; module
  have hd : (2 : ℝ)⁻¹ • (root t - root s) = y := by rw [ht, hs]; module
  have hJ : dyadicObjective p K (node t s) =
      (dyadicObjective p K t + dyadicObjective p K s) / 2 - K * ‖y‖ ^ p := by
    simp only [dyadicObjective, moment_node, energy_node, hd]
    ring
  have hle := dyadicObjective_le_bellman hMT (node t s)
  rw [hr, hJ] at hle
  dsimp [ε] at htJ hsJ
  linarith

end MarkovSuperreflexivity

end OAI
