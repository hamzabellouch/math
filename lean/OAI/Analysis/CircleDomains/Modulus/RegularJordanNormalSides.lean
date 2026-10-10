import OAI.Analysis.CircleDomains.Modulus.NormalChartJordanSides
import OAI.Analysis.CircleDomains.Transfer.LevelChartBox

namespace OAI

/-! Uniform local rectangles of the actual normal strip have one inward
and one outward half; no orientation is assumed. -/
open Set Function Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def NormalSidePattern (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (t r : ℝ) (positive : Bool) : Prop :=
  ∀ s ∈ Ioo (t-r) (t+r), ∀ ρ ∈ Ioo (0 : ℝ) r,
    if positive then
      curveNormalStrip γ (s,ρ) ∈ jordanInterior H ∧
        curveNormalStrip γ (s,-ρ) ∈ (closure (jordanInterior H))ᶜ
    else
      curveNormalStrip γ (s,-ρ) ∈ jordanInterior H ∧
        curveNormalStrip γ (s,ρ) ∈ (closure (jordanInterior H))ᶜ

lemma exists_local_normal_side_pattern
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (t : ℝ) :
    ∃ r > 0, NormalSidePattern H γ t r true ∨ NormalSidePattern H γ t r false := by
  obtain ⟨e,U,ht,he,_,_,hU,htU,hUt,hstraight⟩ := exists_regular_jordan_boundary_chart hγ t
  have hval : e (t,0) = γ t := by simp [he,curveNormalStrip]
  have htE : γ t ∈ e.target := hval ▸ e.map_source ht
  obtain ⟨r,hr,hbox⟩ := exists_openPartialHomeomorph_box e.symm htE hU htU
  have heinv : e.symm (γ t) = (t,0) := by rw [← hval,e.left_inv ht]
  rw [heinv] at hbox
  simp only [zero_sub,zero_add,
    OpenPartialHomeomorph.symm_target,OpenPartialHomeomorph.symm_symm] at hbox
  have hB : Ioo (t-r) (t+r) ×ˢ Ioo (-r) r ⊆ e.source := hbox.trans inter_subset_left
  have hBU : e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r) ⊆ U := by
    rintro _ ⟨p,hp,rfl⟩
    exact (hbox hp).2
  have hside := normal_chart_jordan_sides H e U hstraight t r hr hB hBU
    (hval.symm ▸ hγ.mem_frontier t)
  refine ⟨r,hr,?_⟩
  rcases hside with h | h
  · left
    intro s hs ρ hρ
    exact ⟨he (s,ρ) ▸ h.1 ⟨(s,ρ),⟨hs,hρ⟩,rfl⟩,
      he (s,-ρ) ▸ h.2 ⟨(s,-ρ),⟨hs,by constructor <;> linarith [hρ.1,hρ.2]⟩,rfl⟩⟩
  · right
    intro s hs ρ hρ
    exact ⟨he (s,-ρ) ▸ h.1 ⟨(s,-ρ),⟨hs,by constructor <;> linarith [hρ.1,hρ.2]⟩,rfl⟩,
      he (s,ρ) ▸ h.2 ⟨(s,ρ),⟨hs,hρ⟩,rfl⟩⟩

end CircleDomainRigidity

end

end OAI
