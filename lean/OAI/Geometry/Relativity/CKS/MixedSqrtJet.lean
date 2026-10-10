import OAI.Geometry.Relativity.CKS.MixedJetCalculus

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff

def sqrtJet (f : ScalarJet) : ScalarJet :=
  (Real.sqrt f.1, (fun a => f.2.1 a/(2*Real.sqrt f.1)), fun a b =>
    f.2.2 a b/(2*Real.sqrt f.1)-f.2.1 a*f.2.1 b/(4*Real.sqrt f.1^3))

lemma actualScalarJet_sqrt {f : Point → ℝ} {x : Point}
    (hf : ContDiffAt ℝ 2 f x) (h0 : 0 < f x) :
    actualScalarJet (fun y => Real.sqrt (f y)) x = sqrtJet (actualScalarJet f x) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · ext a
    exact D_sqrt _ (hf.differentiableAt (by norm_num)) h0
  · ext a b
    dsimp [actualScalarJet,sqrtJet]
    rw [D_D_sqrt (basis b) (basis a) hf h0]
    ring

lemma sqrtJet_smooth {j : ScalarJet} (h0 : 0 < j.1) : ContDiffAt ℝ ∞ sqrtJet j := by
  have hs : ContDiffAt ℝ ∞ (fun j : ScalarJet => Real.sqrt j.1) j :=
    (by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.1) j).sqrt h0.ne'
  unfold sqrtJet
  apply ContDiffAt.prodMk hs
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.mpr
    intro a
    exact (by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.2.1 a) j).div (hs.const_smul (2:ℝ)) (by positivity)
  · apply contDiffAt_pi.mpr
    intro a
    apply contDiffAt_pi.mpr
    intro b
    exact ((by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.2.2 a b) j).div (hs.const_smul (2:ℝ)) (by positivity)).sub
      ((by fun_prop : ContDiffAt ℝ ∞ (fun j : ScalarJet => j.2.1 a*j.2.1 b) j).div ((hs.pow 3).const_smul (4:ℝ)) (by positivity))

end
end CKSMixedGeometry

end

end OAI
