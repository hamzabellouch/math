import OAI.InformationTheory.BooleanNoise.EntropyScalars
import Mathlib.Data.Set.Function
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.MonotoneContinuity

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

def psiInv (s : ℝ) : ℝ := Function.invFunOn psi (Set.Icc 0 1) s

def r (s : ℝ) : ℝ := psiInv s * Real.artanh (psiInv s)

def rDeriv (s : ℝ) : ℝ :=
  if s ≤ 0 then 2 else
    1 + psiInv s / ((1 - (psiInv s) ^ 2) * Real.artanh (psiInv s))

def rSecondDeriv (s : ℝ) : ℝ :=
  if s ≤ 0 then 4 / 3 else
    (((1 + (psiInv s) ^ 2) * Real.artanh (psiInv s) - psiInv s) /
      ((1 - (psiInv s) ^ 2) ^ 2 * (Real.artanh (psiInv s)) ^ 3))

def rGap (s : ℝ) : ℝ := r s - 2 * s

def L (x : ℝ) : ℝ :=
  if 0 < x ∧ x < ell then rGap (ell - x) else 0

def LDeriv (x : ℝ) : ℝ :=
  if 0 < x ∧ x < ell then 2 - rDeriv (ell - x) else 0

def s0 : ℝ := psi (1 / 5)

def K (s : ℝ) : ℝ :=
  if s ≤ 0 then 0 else
    if s ≤ s0 then rGap s else rGap s0 + (rDeriv s0 - 2) * (s - s0)

def KDeriv (s : ℝ) : ℝ :=
  if s ≤ 0 then 0 else
    if s ≤ s0 then rDeriv s - 2 else rDeriv s0 - 2

theorem psiInv_mem_of_mem_image {s : ℝ} (hs : s ∈ psi '' Set.Icc 0 1) :
    psiInv s ∈ Set.Icc 0 1 :=
  Function.invFunOn_mem hs

theorem psi_psiInv_of_mem_image {s : ℝ} (hs : s ∈ psi '' Set.Icc 0 1) :
    psi (psiInv s) = s :=
  Function.invFunOn_eq hs

@[simp] theorem rDeriv_zero : rDeriv 0 = 2 := by simp [rDeriv]
@[simp] theorem rSecondDeriv_zero : rSecondDeriv 0 = 4 / 3 := by simp [rSecondDeriv]
@[simp] theorem K_zero : K 0 = 0 := by simp [K]
@[simp] theorem KDeriv_zero : KDeriv 0 = 0 := by simp [KDeriv]

theorem L_eq_zero_of_ell_le {x : ℝ} (hx : ell ≤ x) : L x = 0 := by
  simp [L, not_lt.mpr hx]

theorem L_eq_rGap {x : ℝ} (hx : x ∈ Set.Ioo 0 ell) :
    L x = rGap (ell - x) := by simp [L, hx.1, hx.2]

theorem K_eq_rGap {s : ℝ} (hs : 0 < s) (hs0 : s ≤ s0) : K s = rGap s := by
  simp [K, not_le.mpr hs, hs0]

theorem K_eq_tangent {s : ℝ} (hs : 0 < s) (hs0 : s0 ≤ s) :
    K s = rGap s0 + (rDeriv s0 - 2) * (s - s0) := by
  rcases hs0.eq_or_lt with rfl | hs0
  · simp [K, not_le.mpr hs]
  · simp [K, not_le.mpr hs, not_le.mpr hs0]

theorem image_psi_Icc : psi '' Icc 0 1 = Icc 0 ell := by
  simpa only [psi_zero, psi_one] using
    continuous_psi.continuousOn.image_Icc_of_monotoneOn
      (by norm_num : (0 : ℝ) ≤ 1) strictMonoOn_psi.monotoneOn

theorem psiInv_mem_Icc {s : ℝ} (hs : s ∈ Icc 0 ell) : psiInv s ∈ Icc 0 1 := by
  exact psiInv_mem_of_mem_image (image_psi_Icc.symm ▸ hs)

theorem psi_psiInv_Icc {s : ℝ} (hs : s ∈ Icc 0 ell) : psi (psiInv s) = s := by
  exact psi_psiInv_of_mem_image (image_psi_Icc.symm ▸ hs)

theorem psiInv_psi {u : ℝ} (hu : u ∈ Icc 0 1) : psiInv (psi u) = u :=
  strictMonoOn_psi.injOn.leftInvOn_invFunOn hu

@[simp] theorem psiInv_zero : psiInv 0 = 0 := by
  simpa only [psi_zero] using psiInv_psi (show (0 : ℝ) ∈ Icc 0 1 by norm_num)

@[simp] theorem psiInv_ell : psiInv ell = 1 := by
  simpa only [psi_one] using psiInv_psi (show (1 : ℝ) ∈ Icc 0 1 by norm_num)

@[simp] theorem r_zero : r 0 = 0 := by simp [r]
@[simp] theorem rGap_zero : rGap 0 = 0 := by simp [rGap]

theorem psi_psiInv {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) : psi (psiInv s) = s :=
  psi_psiInv_Icc ⟨hs, hsell.le⟩

theorem psiInv_mem_Ico {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) :
    psiInv s ∈ Ico 0 1 := by
  have hu := psiInv_mem_Icc ⟨hs, hsell.le⟩
  refine ⟨hu.1, ?_⟩
  by_contra h
  have he : psiInv s = 1 := le_antisymm hu.2 (le_of_not_gt h)
  have hv := psi_psiInv hs hsell
  rw [he, psi_one] at hv
  linarith

theorem psiInv_mem_Ioo {s : ℝ} (hs : s ∈ Ioo 0 ell) : psiInv s ∈ Ioo 0 1 := by
  have hu := psiInv_mem_Ico hs.1.le hs.2
  refine ⟨?_, hu.2⟩
  by_contra h
  have he : psiInv s = 0 := le_antisymm (le_of_not_gt h) hu.1
  have hv := psi_psiInv hs.1.le hs.2
  rw [he, psi_zero] at hv
  linarith [hs.1]

def psiOrderIso : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) ell where
  toFun u := ⟨psi u, image_psi_Icc ▸ mem_image_of_mem psi u.property⟩
  invFun s := ⟨psiInv s, psiInv_mem_Icc s.property⟩
  left_inv u := Subtype.ext (psiInv_psi u.property)
  right_inv s := Subtype.ext (psi_psiInv_Icc s.property)
  map_rel_iff' := by
    intro u v
    exact strictMonoOn_psi.le_iff_le u.property v.property

theorem continuousOn_psiInv : ContinuousOn psiInv (Icc 0 ell) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp psiOrderIso.symm.continuous

theorem continuousAt_psiInv {s : ℝ} (hs : s ∈ Ioo 0 ell) : ContinuousAt psiInv s :=
  (continuousOn_psiInv s ⟨hs.1.le, hs.2.le⟩).continuousAt (Icc_mem_nhds hs.1 hs.2)

theorem r_psi_nonneg {u : ℝ} (hu : u ∈ Icc 0 1) :
    r (psi u) = u * Real.artanh u := by rw [r, psiInv_psi hu]

theorem r_psi {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    r (psi u) = u * Real.artanh u := by
  by_cases h0 : 0 ≤ u
  · exact r_psi_nonneg ⟨h0, hu.2.le⟩
  · have hn : -u ∈ Ioo (-1) 1 := by constructor <;> linarith [hu.1, hu.2]
    have hodd : Real.artanh (-u) = -Real.artanh u := by
      rw [artanh_eq_log_sub hn, artanh_eq_log_sub hu]
      simp only [sub_eq_add_neg, neg_neg]
      ring
    calc
      r (psi u) = r (psi (-u)) := by rw [psi_neg]
      _ = (-u) * Real.artanh (-u) := r_psi_nonneg ⟨by linarith, hn.2.le⟩
      _ = u * Real.artanh u := by rw [hodd]; ring

theorem s0_pos : 0 < s0 := by
  change 0 < psi (1 / 5)
  rw [← psi_zero]
  exact strictMonoOn_psi (by norm_num) (by norm_num) (by norm_num)

theorem s0_lt_ell : s0 < ell := psi_lt_ell (by norm_num)

theorem hasDerivAt_psiInv {s : ℝ} (hs : s ∈ Ioo 0 ell) :
    HasDerivAt psiInv (Real.artanh (psiInv s))⁻¹ s := by
  have hu := psiInv_mem_Ioo hs
  apply HasDerivAt.of_local_left_inverse (continuousAt_psiInv hs)
    (hasDerivAt_psi ⟨by linarith [hu.1], hu.2⟩) (Real.artanh_pos hu).ne'
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  exact psi_psiInv ht.1.le ht.2

theorem continuousOn_r : ContinuousOn r (Ico 0 ell) := by
  have hi : ContinuousOn psiInv (Ico 0 ell) :=
    continuousOn_psiInv.mono (fun _ h => ⟨h.1, h.2.le⟩)
  intro s hs
  have hu := psiInv_mem_Ico hs.1 hs.2
  exact (hi s hs).mul
    ((hasDerivAt_artanh ⟨by linarith [hu.1], hu.2⟩).continuousAt.comp_continuousWithinAt
      (hi s hs))

theorem hasDerivAt_r {s : ℝ} (hs : s ∈ Ioo 0 ell) : HasDerivAt r (rDeriv s) s := by
  have hu := psiInv_mem_Ioo hs
  have hi := hasDerivAt_psiInv hs
  have ht := (hasDerivAt_artanh ⟨by linarith [hu.1], hu.2⟩).comp s hi
  have hn : Real.artanh (psiInv s) ≠ 0 := (Real.artanh_pos hu).ne'
  have hq : 1 - (psiInv s) ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
  convert! hi.mul ht using 1
  unfold rDeriv
  rw [ite_eq_right (not_le.mpr hs.1)]
  simp only [Function.comp_apply]
  field_simp

end LeanBlast.CourtadeKumar

end

end OAI
