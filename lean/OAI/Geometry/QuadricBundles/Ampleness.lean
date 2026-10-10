import OAI.Geometry.QuadricBundles.Embedding

namespace OAI

noncomputable section

namespace QuadricCounterexample
noncomputable section

theorem EqualizerData.powerTwist_ample (D : EqualizerData) (m : ℕ) (hm : 0 < m) :
    IsAmple (powerPullbackTwist D.bundle m hm) := by
  let t := 3*m+1
  let e := 2*t-1
  have he : 3*m≤e := by dsimp [e,t]; omega
  have hen : e+1=2*t := by dsimp [e,t]; omega
  have hn : 0<2*t := by dsimp [t]; omega
  let S := D.ampleSystem m hm e t he hen
  exact ⟨2*t,hn,_,S.sections,S.closedEmbedding hn⟩

end
end QuadricCounterexample

end

end OAI
