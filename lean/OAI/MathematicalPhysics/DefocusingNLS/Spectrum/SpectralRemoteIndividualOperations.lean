import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIndividualSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSymbolBilinear

namespace OAI

/-! Bilinear operations on the individual outgoing-tail symbols. -/

open Filter Topology
namespace DefocusingNLS
namespace HasLogJetBound

theorem bilinear {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {sigma tau : ℝ} {f : ℝ → A} {g : ℝ → B}
    (hf : HasLogJetBound sigma f) (hg : HasLogJetBound tau g)
    (T : A →L[ℝ] B →L[ℝ] C) :
    HasLogJetBound (sigma+tau) (fun t => T (f t) (g t)) := by
  have hL : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  exact ((HasUniformLogJetBound.of_single hf hL).bilinear
    (HasUniformLogJetBound.of_single hg hL) T).to_single

theorem apply {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {sigma tau : ℝ} {f : ℝ → A →L[ℝ] B} {g : ℝ → A}
    (hf : HasLogJetBound sigma f) (hg : HasLogJetBound tau g) :
    HasLogJetBound (sigma+tau) (fun t => f t (g t)) :=
  hf.bilinear hg (ContinuousLinearMap.id ℝ (A →L[ℝ] B))

end HasLogJetBound
end DefocusingNLS

end OAI
