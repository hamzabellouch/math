import Mathlib
import OAI.Analysis.MatrixSigning.Potential.UnpackKkt

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private local instance : NormedAddCommGroup (H d) := inferInstance
private local instance : NormedSpace ℝ (H d) := inferInstance
private local instance : TopologicalSpace (H d) :=
  (inferInstance : NormedAddCommGroup (H d)).toUniformSpace.toTopologicalSpace

theorem exists_value_branch [NeZero d] (ε : ℝ) (S : E → H d) (η : E → H d →L[ℝ] H d) (b : E)
    (hS : ContDiffAt ℝ ∞ S b) (hη : ContDiffAt ℝ ∞ η b)
    (hηsym : ∀ᶠ a in 𝓝 b, SymmetricMap (η a)) (z : Vars d)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (hP : mCoord d z ∈ pd d) (hQ : nCoord d z ∈ pd d)
    (hzero : kktSystem ε (S b) (η b) z=0)
    (J : Vars d ≃L[ℝ] Vars d)
    (hJ : ∀ u, J u=CurrentKS.KKT.jacobian (identityPair d)
      (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) (η b)))
      (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) u) :
    ∃ g : E → Vars d, g b=z ∧ ContDiffAt ℝ ∞ g b ∧
      (∀ᶠ a in 𝓝 b,kktSystem ε (S a) (η a) (g a)=0) ∧
      (fun a => value ε (S a) (η a)) =ᶠ[𝓝 b] fun a => objective ε (unpack (g a)) := by
  obtain ⟨f,hf,hfc,hfe⟩ := exists_smooth_kkt_branch ε (S b,η b) z hX hY J hJ
  let g : E → Vars d := fun a => f (S a,η a)
  have hg : g b=z := hf
  have hgc : ContDiffAt ℝ ∞ g b := hfc.comp b (hS.prodMk hη)
  have hge : ∀ᶠ a in 𝓝 b,kktSystem ε (S a) (η a) (g a)=0 := by
    filter_upwards [(hS.continuousAt.prodMk hη.continuousAt).eventually hfe] with a ha
    exact ha.trans hzero
  have hXg : ∀ᶠ a in 𝓝 b,xCoord d (g a) ∈ pd d := by
    apply ((xCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change xCoord d (g b) ∈ pd d
    rw [hg]
    exact hX
  have hYg : ∀ᶠ a in 𝓝 b,yCoord d (g a) ∈ pd d := by
    apply ((yCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change yCoord d (g b) ∈ pd d
    rw [hg]
    exact hY
  have hPg : ∀ᶠ a in 𝓝 b,mCoord d (g a) ∈ pd d := by
    apply ((mCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change mCoord d (g b) ∈ pd d
    rw [hg]
    exact hP
  have hQg : ∀ᶠ a in 𝓝 b,nCoord d (g a) ∈ pd d := by
    apply ((nCoord d).continuous.continuousAt.comp hgc.continuousAt).eventually
    apply isOpen_pd.mem_nhds
    change nCoord d (g b) ∈ pd d
    rw [hg]
    exact hQ
  refine ⟨g,hg,hgc,hge,?_⟩
  filter_upwards [hηsym,hge,hXg,hYg,hPg,hQg] with a ha he hx hy hp hq
  exact value_eq_of_system ε (S a) (η a) ha (g a) hx hy hp.posSemidef hq.posSemidef he

end
end CurrentKS.Variational

end OAI
