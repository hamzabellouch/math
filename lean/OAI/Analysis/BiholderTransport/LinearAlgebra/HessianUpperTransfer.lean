import Mathlib

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section HessianUpperTransfer
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bilinear_bound_abs (B:E →L[ℝ] E →L[ℝ] ℝ) (d:E) :
    |B d d| ≤ ‖B‖*‖d‖^2 := by
  calc
    _ = ‖B d d‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖B d‖*‖d‖ := (B d).le_opNorm d
    _ ≤ (‖B‖*‖d‖)*‖d‖ := mul_le_mul_of_nonneg_right (B.le_opNorm d) (norm_nonneg d)
    _ = _ := by ring

lemma quadratic_upper_transfer
    {A R:E →L[ℝ] E} (hR:∀w,A (R w)=w)
    {H B E0:E →L[ℝ] E →L[ℝ] ℝ} {Q:E →L[ℝ] E →L[ℝ] E} {p:E →L[ℝ] ℝ}
    (he:∀d,B d d=E0 d d+H (A d) (A d)+p (Q d d))
    {C:ℝ} (hC:0 ≤ C) (hB:∀d,B d d ≤ C*‖d‖^2) :
    ∀w,H w w ≤ (C+‖E0‖+‖p‖*‖Q‖)*‖R‖^2*‖w‖^2 := by
  intro w
  let d:=R w
  have hE:=bilinear_bound_abs E0 d
  have hQ:|p (Q d d)| ≤ ‖p‖*‖Q‖*‖d‖^2 := by
    calc
      _ = ‖p (Q d d)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖p‖*‖Q d d‖ := p.le_opNorm _
      _ ≤ ‖p‖*(‖Q d‖*‖d‖) := mul_le_mul_of_nonneg_left ((Q d).le_opNorm d) (norm_nonneg _)
      _ ≤ ‖p‖*((‖Q‖*‖d‖)*‖d‖) := by gcongr; exact Q.le_opNorm d
      _ = _ := by ring
  have HB:=hB d
  rw [he] at HB
  rw [show A d=w from hR w] at HB
  have hh:H w w ≤ (C+‖E0‖+‖p‖*‖Q‖)*‖d‖^2 := by
    nlinarith only [HB,(abs_le.mp hE).1,(abs_le.mp hQ).1]
  calc
    _ ≤ (C+‖E0‖+‖p‖*‖Q‖)*‖d‖^2 := hh
    _ ≤ (C+‖E0‖+‖p‖*‖Q‖)*(‖R‖*‖w‖)^2 := by
      gcongr
      exact R.le_opNorm w
    _ = _ := by ring

lemma eventually_bounded_right_inverse [CompleteSpace E] [FiniteDimensional ℝ E]
    {Aj:ℕ → E →L[ℝ] E} {A:E →L[ℝ] E}
    (hA:Function.Injective A) (hlim:Tendsto Aj atTop (𝓝 A)) :
    ∃K≥0,∀ᶠ i in atTop,∃R:E →L[ℝ] E,(∀w,Aj i (R w)=w) ∧ ‖R‖ ≤ K := by
  have hu:IsUnit A := ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hA,(LinearMap.injective_iff_surjective).mp hA⟩
  obtain ⟨u,hu⟩:=hu
  subst A
  have hi:Tendsto (fun i=>Ring.inverse (Aj i)) atTop (𝓝 (Ring.inverse (u:E →L[ℝ] E))) :=
    (NormedRing.inverse_continuousAt u).tendsto.comp hlim
  have hbound:=hi.norm.eventually (gt_mem_nhds (lt_add_one ‖Ring.inverse (u:E →L[ℝ] E)‖))
  have hunit:=hlim.eventually (Units.isOpen.mem_nhds u.isUnit)
  refine ⟨‖Ring.inverse (u:E →L[ℝ] E)‖+1,by positivity,?_⟩
  filter_upwards [hbound,hunit] with i hbi hui
  refine ⟨Ring.inverse (Aj i),?_,hbi.le⟩
  intro w
  exact congrArg (fun B:E →L[ℝ] E=>B w) (Ring.mul_inverse_cancel (Aj i) hui)

end HessianUpperTransfer
end WeakMTWTransport

end
end

end OAI
