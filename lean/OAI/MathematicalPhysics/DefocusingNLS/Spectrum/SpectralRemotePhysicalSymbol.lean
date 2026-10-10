import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteBoundedSymbol

namespace OAI

/-! Physical spectral parameters and odd-power coefficient symbols give the bounded Euler remainder. -/

open Set Filter Topology
namespace DefocusingNLS
namespace HasUniformLogJetBound

theorem const_family {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {L : ℕ → ℝ} {f : ℕ → A} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ᶠ n in atTop, ‖f n‖ ≤ C) :
    HasUniformLogJetBound L 0 (fun n _ => f n) := by
  refine ⟨Eventually.of_forall (fun _ => contDiffOn_const),?_⟩
  intro k
  refine ⟨C,hC,?_⟩
  filter_upwards [hf] with n hn
  intro t ht
  by_cases hk : k = 0
  · simpa [hk] using hn
  · simpa [iteratedDeriv_const,hk] using hC

end HasUniformLogJetBound

theorem spectralRemote_physical_bounded_symbol
    {L : ℕ → ℝ} {a b sigma : ℕ → ℝ} {D C : ℕ → ℝ → ℂ}
    {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ᶠ n in atTop, |a n| ≤ M) (hb : ∀ᶠ n in atTop, |b n| ≤ M)
    (hsigma : ∀ᶠ n in atTop, |sigma n| ≤ M)
    (hD : HasUniformLogJetBound L 0 D) (hC : HasUniformLogJetBound L 0 C) :
    HasUniformLogJetBound L 0
      (fun n t => spectralRemotePhysicalBounded (a n) (b n) (sigma n) (D n t) (C n t)) := by
  have ha' : HasUniformLogJetBound L 0 (fun n _ => (a n : ℂ)) :=
    (HasUniformLogJetBound.const_family hM ha).map Complex.ofRealCLM
  have hb' : HasUniformLogJetBound L 0 (fun n _ => (b n : ℂ)) :=
    (HasUniformLogJetBound.const_family hM hb).map Complex.ofRealCLM
  have hs' : HasUniformLogJetBound L 0 (fun n _ => (sigma n : ℂ)) :=
    (HasUniformLogJetBound.const_family hM hsigma).map Complex.ofRealCLM
  have hi : HasUniformLogJetBound L 0 (fun n _ => Complex.I*((a n : ℂ)+(sigma n : ℂ))) := by
    simpa only [add_zero] using (HasUniformLogJetBound.const (L := L) Complex.I).mul (ha'.add hs')
  have hDs : HasUniformLogJetBound L 0 (fun n t => star (D n t)) :=
    hD.map Complex.conjCLE.toContinuousLinearMap
  have hCs : HasUniformLogJetBound L 0 (fun n t => star (C n t)) :=
    hC.map Complex.conjCLE.toContinuousLinearMap
  exact spectralRemote_bounded_operator_symbol ((hb'.neg.sub hi).add hD)
    ((hb'.neg.add hi).add hDs) hC hCs

end DefocusingNLS

end OAI
