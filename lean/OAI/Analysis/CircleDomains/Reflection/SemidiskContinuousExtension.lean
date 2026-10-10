import OAI.Analysis.CircleDomains.Reflection.SemidiskDerivative

namespace OAI

/-! The derivative estimate supplies an actual continuous extension,
constructed by extending the two real Lipschitz coordinates. -/
open Set Function Filter Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_continuous_extension_of_lipschitz {S : Set ℂ} {f : ℂ → ℂ} {K : NNReal}
    (hf : LipschitzOnWith K f S) : ∃F:ℂ→ℂ,Continuous F ∧ EqOn F f S := by
  obtain ⟨u,hu,he_u⟩ := (reCLM.lipschitzWith.comp_lipschitzOnWith hf).extend_real
  obtain ⟨v,hv,he_v⟩ := (imCLM.lipschitzWith.comp_lipschitzOnWith hf).extend_real
  refine ⟨fun z => (u z : ℂ)+(v z : ℂ)*I,?_,?_⟩
  · exact (continuous_ofReal.comp hu.continuous).add
      ((continuous_ofReal.comp hv.continuous).mul_const I)
  · intro z hz
    have hu' : (f z).re=u z := he_u hz
    have hv' : (f z).im=v z := he_v hz
    change (u z : ℂ)+(v z : ℂ)*I=f z
    rw [←hu',←hv']
    exact re_add_im (f z)

lemma semidisk_continuous_extension {R M : ℝ} {f : ℂ → ℂ}
    (hR : 0<R) (hM : 0≤M) (hd : DifferentiableOn ℂ f (upperSemidisk R))
    (hpos : ∀z∈upperSemidisk R,0<(f z).im)
    (hbound : ∀z∈upperSemidisk R,(f z).im≤M)
    (hzero : ∀p:ℂ,‖p‖≤R → p.im=0 →
      Tendsto (fun z => (f z).im) (𝓝[upperSemidisk R] p) (𝓝 0)) :
    ∃F:ℂ→ℂ,Continuous F ∧ EqOn F f (upperSemidisk (R/4)) := by
  obtain ⟨K,hK⟩ := semidisk_lipschitz hR hM hd hpos hbound hzero
  exact exists_continuous_extension_of_lipschitz hK

end CircleDomainRigidity

end

end OAI
