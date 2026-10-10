import Mathlib
import OAI.Geometry.IntegralFillings.Optimality.BallCoarea

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings.Optimality

lemma exists_le_of_integral_le_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (hμ : μ ≠ 0) {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hi : (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ) {P : α → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∃ x, P x ∧ f x ≤ g x := by
  classical
  by_contra h
  push Not at h
  have hlt : ∀ᵐ x ∂μ, g x < f x := hP.mono fun x hx => h x hx
  have hnonneg : 0 ≤ᵐ[μ] fun x => f x - g x := hlt.mono fun x hx => sub_nonneg.mpr hx.le
  have hzero : (∫ x, f x - g x ∂μ) = 0 := by
    apply le_antisymm
    · rw [integral_sub hf hg]
      linarith
    · exact integral_nonneg_of_ae hnonneg
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg (hf.sub hg)).mp hzero
  have : NeZero μ := ⟨hμ⟩
  obtain ⟨x,hx,he⟩ := (hlt.and hae).exists
  exact (sub_pos.mpr hx).ne' he

lemma integral_radial_area (n : ℕ) :
    (∫ t in Ioo (-1:ℝ) 0, ((n:ℝ)+1)*omega (n+1)*(-t)^n) = omega (n+1) := by
  let F : ℝ → ℝ := fun t => -omega (n+1)*(-t)^(n+1)
  let f : ℝ → ℝ := fun t => ((n:ℝ)+1)*omega (n+1)*(-t)^n
  have hc : Continuous f := by unfold f; fun_prop
  have hd (t : ℝ) : HasDerivAt F (f t) t := by
    have hh := (((hasDerivAt_id t).neg.pow (n+1)).const_mul (-omega (n+1)))
    convert hh using 1 <;> first | rfl | simp only [f, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.neg_apply, id_eq]; ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hc.intervalIntegrable (-1) 0)
  rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 0)] at hh
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  change (∫ t in Ioc (-1:ℝ) 0, f t) = _
  rw [hh]
  simp [F]

theorem exists_good_inner_ball (n : ℕ) :
    ∃ t ∈ Ioo (-1:ℝ) 0,
      IsIntegral (n+1) (innerBallCurrent (n+1) t) ∧
      mass (boundarySucc (innerBallCurrent (n+1) t)) ≤
        ((n:ℝ)+1)*omega (n+1)*(-t)^n := by
  obtain ⟨G,hG,hG0,hGI,hgood⟩ := innerBall_ae_integral n
  let μ := volume.restrict (Ioo (-1:ℝ) 0)
  let f : ℝ → ℝ := fun t => ((n:ℝ)+1)*omega (n+1)*(-t)^n
  have hμ : μ ≠ 0 := by
    intro h
    have hh := congrArg (fun m : Measure ℝ => m univ) h
    norm_num [μ] at hh
  have hf : Integrable f μ := by
    apply Continuous.integrableOn_Icc (a := (-1:ℝ)) (b := 0) (by unfold f; fun_prop) |>.mono_set
    exact Ioo_subset_Icc_self
  have hi : (∫ t, G t ∂μ) ≤ ∫ t, f t ∂μ := by
    calc (∫ t, G t ∂μ) ≤ ∫ t, G t :=
        setIntegral_le_integral hG (Eventually.of_forall hG0)
      _ ≤ omega (n+1) := hGI
      _ = ∫ t, f t ∂μ := (integral_radial_area n).symm
  obtain ⟨t,⟨ht,htI,htM⟩,hle⟩ := exists_le_of_integral_le_ae hμ hG.restrict hf hi
    ((ae_restrict_mem measurableSet_Ioo).and hgood)
  exact ⟨t,ht,htI,htM.trans hle⟩

end SharpIntegralFillings.Optimality

end

end OAI
