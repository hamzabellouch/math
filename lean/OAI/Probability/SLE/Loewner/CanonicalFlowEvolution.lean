import OAI.Probability.SLE.Loewner.CanonicalSurvival
import OAI.Probability.SLE.Angle.TargetFlowEvolution

namespace OAI

/-! The geometric surviving domain is open in time. Its raw-flow
identification therefore supplies the local interval needed for the ODE. -/
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SLEExactGauge

lemma survivingDomain_exists_later (γ : C(ℝ≥0,ℂ)) (T : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ T) :
    ∃ S : ℝ≥0, T<S ∧ z ∈ survivingDomain γ S := by
  have hopen : IsOpen {S : ℝ≥0 | z ∈ survivingDomain γ S} :=
    source_survival_open.preimage ((continuous_const.prodMk continuous_id).prodMk continuous_const)
  have hn : ∀ᶠ S in 𝓝[>] T, z ∈ survivingDomain γ S :=
    (show ∀ᶠ S in 𝓝 T, z ∈ survivingDomain γ S from hopen.mem_nhds hz).filter_mono
      nhdsWithin_le_nhds
  have hgt : ∀ᶠ S in 𝓝[>] T, T<S := self_mem_nhdsWithin
  obtain ⟨S,hST,hS⟩ := (hgt.and hn).exists
  exact ⟨S,hST,hS⟩

lemma canonical_flow_time_derivative
    (κ : ℝ) (hκ : 0 < κ) (b : Target.Driver) (γ : C(ℝ≥0,ℂ))
    (hD : ∀ (T : ℝ≥0) (z : ℂ),
      Target.Surviving κ b z (κ*T) ↔ z ∈ survivingDomain γ T)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    HasDerivWithinAt (fun u : ℝ => Target.flow κ b z (κ*u.toNNReal))
      (2/(Target.flow κ b z (κ*T)-(b (κ.toNNReal*T):ℂ))) (Ici 0) T := by
  obtain ⟨S,hST,hS⟩ := survivingDomain_exists_later γ T z hz
  exact Target.physical_flow_hasDerivWithinAt κ hκ b z T S hST ((hD S z).mpr hS)

end SLEExactGauge

end

end OAI
