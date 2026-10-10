import Mathlib
import OAI.Analysis.BiholderTransport.Contact.ModifiedActiveLowerJet
import OAI.Analysis.BiholderTransport.Regularity.ActiveLimit

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.modified_active_lower_jet_nonneg (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v)
    {t s : ℝ} (ht : 0<t) (hts : t<s) (hs1 : s<1) {x:M}
    {ι : Type*} [Fintype ι]
    (pj : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
    (hw : ∀ j, 0≤w j) (hsum : ∑ j,w j=1) (i : ι) (hi : 0<w i)
    (hmin : ∀ j,pj j∈minimizingVectors x)
    (hactive : ∀ j,contactGap (cTransform v) v x (riemannianExp x (pj j))=0)
    (hleft : ∀ j,s • pj j∈injectivityDomain x)
    (hright : ∀ j,(1-s) • (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 ∈
      injectivityDomain (sprayFlow s (⟨x,pj j⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1)
    {a : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) x}
    {R : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x}
    (ha : HasFDerivAt a R (∑ j,w j • pj j)) (ha0 : a (∑ j,w j • pj j)=0)
    (harep : ∀ᶠ q in 𝓝 (∑ j,w j • pj j), riemannianExp x (a q)=
      hopfPole (n := n) t (cTransform v) (riemannianExp x (t • q))) :
    HasLowerSecondTaylor (fun d : TangentSpace 𝓘(ℝ,Model n) x =>
      v (riemannianExp x (pj i+d))+‖pj i+d‖^2/2) 0
      (w i • ((innerSL ℝ).comp R)) := by
  classical
  let κ := {j : ι // 0<w j}
  have H := positive_barycentric_restriction pj w hw hsum
  let : Nonempty κ := H.1
  have hs : (∑ j:κ,w j)=1 := H.2.1
  have hb : (∑ j:κ,w j • pj j)=∑ j,w j • pj j := H.2.2.1
  exact hmtw.modified_active_lower_jet hv ht hts hs1
    (fun j:κ=>pj j) (fun j:κ=>w j) (fun j=>j.2) hs (⟨i,hi⟩:κ)
    (fun j=>hmin j) (fun j=>hactive j) (fun j=>hleft j) (fun j=>hright j)
    (by simpa only [hb] using ha) (by simpa only [hb] using ha0)
    (by simpa only [hb] using harep)

end WeakMTWTransport

end

end OAI
