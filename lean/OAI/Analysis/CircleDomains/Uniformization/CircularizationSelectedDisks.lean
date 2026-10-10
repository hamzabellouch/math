import OAI.Analysis.CircleDomains.Uniformization.JordanCircularizationCompactness

namespace OAI

/-! The actual disk selected at each circularization step stays in one
fixed bounded set. Its center and radius therefore have compact ranges. -/
open Set Function Metric Filter Asymptotics Bornology
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity

lemma closedBall_parameters_bounded {c : ℂ} {r L : ℝ} (hr : 0≤r)
    (hsub : closedBall c r ⊆ closedBall 0 L) : ‖c‖≤L ∧ r≤L := by
  have hc : ‖c‖≤L := by
    simpa only [mem_closedBall,dist_zero_right] using hsub (mem_closedBall_self hr)
  have hpoint (s : ℝ) (hs : |s|≤r) : ‖c+(s : ℂ)‖≤L := by
    apply (mem_closedBall_zero_iff).mp
    apply hsub
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,
      Complex.norm_real,Real.norm_eq_abs] using hs
  have hp := hpoint r (by rw [abs_of_nonneg hr])
  have hm := hpoint (-r) (by rw [abs_neg,abs_of_nonneg hr])
  have he : (c+(r : ℂ))-(c+((-r : ℝ) : ℂ))=((2*r : ℝ) : ℂ) := by
    push_cast
    ring
  have hn := norm_sub_le (c+(r : ℂ)) (c+((-r : ℝ) : ℂ))
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)] at hn
  exact ⟨hc,by linarith⟩

namespace FiniteJordanConfiguration
variable {I : Type*} [Finite I]

def selectedCenter (C : FiniteJordanConfiguration I) (schedule : ℕ → I) (n : ℕ) : ℂ :=
  (chosenStep (iterate C schedule n) (schedule n)).center

def selectedRadius (C : FiniteJordanConfiguration I) (schedule : ℕ → I) (n : ℕ) : ℝ :=
  (chosenStep (iterate C schedule n) (schedule n)).radius

lemma selectedRadius_pos (C : FiniteJordanConfiguration I) (schedule : ℕ → I) (n : ℕ) :
    0<selectedRadius C schedule n :=
  (chosenStep (iterate C schedule n) (schedule n)).radius_pos

lemma selected_cap_eq (C : FiniteJordanConfiguration I) (schedule : ℕ → I) (n : ℕ) :
    FiniteTransfer.closedTerminalCap ((iterate C schedule (n+1)).hole (schedule n))=
      ((↑) : ℂ → Sphere) '' closedBall (selectedCenter C schedule n) (selectedRadius C schedule n) := by
  change ((↑) : ℂ → Sphere) '' closure (jordanInterior
    ((chosenStep (iterate C schedule n) (schedule n)).target.hole (schedule n))) = _
  rw [(chosenStep (iterate C schedule n) (schedule n)).selected]
  change ((↑) : ℂ → Sphere) '' closure (ball (selectedCenter C schedule n)
    (selectedRadius C schedule n)) = _
  rw [closure_ball _ (selectedRadius_pos C schedule n).ne']

lemma selected_disk_bounded (C : FiniteJordanConfiguration I) (schedule : ℕ → I)
    {R : ℝ} (hR : 0<R)
    (hsource : ((((↑) : ℂ → Sphere) '' ball 0 R)ᶜ) ⊆ C.region) (n : ℕ) :
    ‖selectedCenter C schedule n‖≤3*R ∧
      selectedRadius C schedule n ∈ Icc 0 (3*R) := by
  have homit := (circularization_uniform_bounds C schedule hR hsource (n+1)).1
  have hsub : closedBall (selectedCenter C schedule n) (selectedRadius C schedule n) ⊆
      closedBall 0 (3*R) := by
    intro z hz
    have hzcap : (z : Sphere) ∈ FiniteTransfer.closedTerminalCap
        ((iterate C schedule (n+1)).hole (schedule n)) := by
      rw [selected_cap_eq]
      exact ⟨z,hz,rfl⟩
    have hout : (z : Sphere) ∈ (iterate C schedule (n+1)).regionᶜ := by
      simpa only [region,FiniteTransfer.openCompletedRegion,compl_compl] using
        (mem_iUnion.mpr ⟨schedule n,hzcap⟩)
    obtain ⟨w,hw,he⟩ := homit z hout
    exact OnePoint.coe_injective he ▸ hw
  obtain ⟨hc,hr⟩ := closedBall_parameters_bounded
    (selectedRadius_pos C schedule n).le hsub
  exact ⟨hc,(selectedRadius_pos C schedule n).le,hr⟩

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
