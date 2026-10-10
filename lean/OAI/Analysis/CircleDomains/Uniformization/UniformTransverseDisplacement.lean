import OAI.Analysis.CircleDomains.Topology.CompactTransverseField
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-! Compactness gives a common displacement width for an actual smooth
transverse field, including retention in a prescribed open neighborhood. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma uniform_transverse_displacement
    {f : ℂ → ℝ} {V : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hV : ContDiff ℝ ∞ V)
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hpos : ∀ x ∈ K, 0 < fderiv ℝ f x (V x)) :
    ∃ δ > 0, ∀ x ∈ K, ∀ r ∈ Ioc (0 : ℝ) δ,
      f (x-r • V x) < f x ∧ f x < f (x+r • V x) ∧
        x-r • V x ∈ U ∧ x+r • V x ∈ U := by
  let D : ℝ × ℂ → ℝ := fun p => fderiv ℝ f (p.2+p.1 • V p.2) (V p.2)
  let W : Set (ℝ × ℂ) := {p | 0 < D p ∧ p.2+p.1 • V p.2 ∈ U}
  have hshift : Continuous (fun p : ℝ × ℂ => p.2+p.1 • V p.2) :=
    continuous_snd.add (continuous_fst.smul (hV.continuous.comp continuous_snd))
  have hD : Continuous D :=
    ((hf.continuous_fderiv (by simp)).comp hshift).clm_apply (hV.continuous.comp continuous_snd)
  have hW : IsOpen W := (isOpen_lt continuous_const hD).inter (hU.preimage hshift)
  have hCW : ({0} : Set ℝ) ×ˢ K ⊆ W := by
    rintro ⟨r, x⟩ ⟨hr, hx⟩
    simp only [mem_singleton_iff] at hr
    subst r
    simpa only [W, D, zero_smul, add_zero, mem_ofPred_eq] using And.intro (hpos x hx) (hKU hx)
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_singleton.prod hK).exists_cthickening_subset_open hW hCW
  have hbound (x : ℂ) (hx : x ∈ K) (r : ℝ) (hr : r ∈ Icc (-δ) δ) :
      0 < D (r,x) ∧ x+r • V x ∈ U := by
    apply hthick
    apply mem_cthickening_of_dist_le (r,x) (0,x) δ ({0} ×ˢ K) ⟨rfl, hx⟩
    rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, Real.dist_eq, sub_zero]
    exact abs_le.mpr hr
  have hmono (x : ℂ) (hx : x ∈ K) : StrictMonoOn (fun r : ℝ => f (x+r • V x)) (Icc (-δ) δ) := by
    apply strictMonoOn_of_deriv_pos (f := fun r : ℝ => f (x+r • V x)) (convex_Icc _ _) (hf.continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
    intro r hr
    have hd : HasDerivAt (fun s : ℝ => f (x+s • V x)) (D (r,x)) r := by
      have hi := ((hasDerivAt_id r).smul_const (V x)).const_add x
      have hh := (hf.differentiable (by simp) (x+r • V x)).hasFDerivAt.comp_hasDerivAt r hi
      convert! hh using 1
      simp only [D, one_smul]
    rw [hd.deriv]
    exact (hbound x hx r (interior_subset hr)).1
  refine ⟨δ, hδ, ?_⟩
  intro x hx r hr
  have hneg : -r ∈ Icc (-δ) δ := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hzero : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  have hposr : r ∈ Icc (-δ) δ := ⟨by linarith [hr.1], hr.2⟩
  have hlo := hmono x hx hneg hzero (by linarith [hr.1])
  have hhi := hmono x hx hzero hposr hr.1
  simpa only [zero_smul, add_zero, neg_smul, sub_eq_add_neg] using
    And.intro hlo (And.intro hhi (And.intro (hbound x hx (-r) hneg).2 (hbound x hx r hposr).2))

end CircleDomainRigidity

end

end OAI
