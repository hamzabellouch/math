import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.NormalCoordinates3
import OAI.Analysis.BiholderTransport.Contact.CenterSupport

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def coordinateScalarSupport (a : M) (φ : ℝ → ℝ)
    (q : ((ℝ×ℝ)×(Model n×Model n))×Model n) : ℝ :=
  φ (q.1.1.1+cost ((extChartAt 𝓘(ℝ,Model n) a).symm q.1.2.1)
      (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))/q.1.1.2-
    cost ((extChartAt 𝓘(ℝ,Model n) a).symm q.2)
      (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))/q.1.1.2)

section
omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma coordinateScalarSupport_eq {a : M} {b : Model n}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (v s : ℝ) (p z : Model n) (φ : ℝ → ℝ) :
    coordinateScalarSupport a φ (((v,s),(b,p)),z)=
      scalarCostSupport φ v ((extChartAt 𝓘(ℝ,Model n) a).symm b)
        ((trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
          ((extChartAt 𝓘(ℝ,Model n) a).symm b) p) s
        ((extChartAt 𝓘(ℝ,Model n) a).symm z) := by
  simp only [coordinateScalarSupport,scalarCostSupport,movingNormal_eq hb,map_smul]

lemma coordinateScalarSupport_self (a : M) (v s : ℝ) (b p : Model n) (φ : ℝ → ℝ) :
    coordinateScalarSupport a φ (((v,s),(b,p)),b)=φ v := by
  simp only [coordinateScalarSupport,add_sub_cancel_right]

end

lemma coordinateScalarSupport_contDiffAt {a : M} {b p : Model n} {v s : ℝ} {φ : ℝ → ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hs : s≠0)
    (hp : s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hφ : ContDiffAt ℝ ∞ φ v) :
    ContDiffAt ℝ ∞ (coordinateScalarSupport a φ) (((v,s),(b,p)),b) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let Q := ((ℝ×ℝ)×(Model n×Model n))×Model n
  let q : Q := (((v,s),(b,p)),b)
  have hi : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ χ.symm b :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds hb)
  have hA : ContMDiffAt 𝓘(ℝ,Q) 𝓘(ℝ,Model n) ∞
      (fun q : Q => movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2)) q :=
    (movingNormal_contMDiffAt (q := (b,s • p)) hb).comp
      (f := fun q : Q => (q.1.2.1,q.1.1.2 • q.1.2.2)) q
      (contDiffAt_fst.snd.fst.prodMk (contDiffAt_fst.fst.snd.smul contDiffAt_fst.snd.snd)).contMDiffAt
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨χ.symm b,s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ (χ.symm b) p⟩ :
      TangentBundle 𝓘(ℝ,Model n) M) hp
  have he : movingNormal a (b,s • p)=riemannianExp (χ.symm b)
      (s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ (χ.symm b) p) := by
    rw [movingNormal_eq hb,map_smul]
  rw [←he] at hc
  have hC : ContDiffAt ℝ ∞ (fun q : Q => cost (χ.symm q.1.2.1)
      (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))) q :=
    (hc.comp (f := fun q : Q => (χ.symm q.1.2.1,
      movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))) q
      ((hi.comp (f := fun q : Q => q.1.2.1) q
        contDiffAt_fst.snd.fst.contMDiffAt).prodMk hA)).contDiffAt
  have hD : ContDiffAt ℝ ∞ (fun q : Q => cost (χ.symm q.2)
      (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))) q :=
    (hc.comp (f := fun q : Q => (χ.symm q.2,
      movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))) q
      ((hi.comp (f := fun q : Q => q.2) q contDiffAt_snd.contMDiffAt).prodMk hA)).contDiffAt
  have hF := (contDiffAt_fst.fst.fst.add (hC.div contDiffAt_fst.fst.snd hs)).sub
    (hD.div contDiffAt_fst.fst.snd hs)
  have hv : q.1.1.1+cost (χ.symm q.1.2.1) (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))/q.1.1.2-
      cost (χ.symm q.2) (movingNormal a (q.1.2.1,q.1.1.2 • q.1.2.2))/q.1.1.2=v := by
    dsimp only [q]; ring
  exact (show ContDiffAt ℝ ∞ φ _ from hv.symm ▸ hφ).comp q hF

end WeakMTWTransport

end

end OAI
