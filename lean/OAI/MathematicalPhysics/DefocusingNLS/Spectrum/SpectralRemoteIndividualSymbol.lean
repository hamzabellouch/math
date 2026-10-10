import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSymbolProduct

namespace OAI

/-! Constant parameter families recover the individual tail symbol estimates.
This direction does not exchange the parameter and derivative quantifiers. -/

open Set Filter Topology
namespace DefocusingNLS

theorem HasUniformLogJetBound.to_single
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {L : ℕ → ℝ} {sigma : ℝ} {f : ℝ → A}
    (hf : HasUniformLogJetBound L sigma (fun _ => f)) : HasLogJetBound sigma f := by
  obtain ⟨n,hn⟩ := hf.smooth.exists
  refine ⟨⟨L n,hn⟩,?_⟩
  intro k
  obtain ⟨C,hC,hb⟩ := hf.bound k
  obtain ⟨j,hj⟩ := hb.exists
  exact ⟨C,hC,(eventually_gt_atTop (L j)).mono (fun t ht => hj t ht)⟩

end DefocusingNLS

end OAI
