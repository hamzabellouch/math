import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCouplingEstimate
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice

namespace OAI

/-! A compact-shell maximum makes the small Green and Robin corrections absorbable.
No a priori bound on the size of a particular solution is required. -/

open Set
namespace DefocusingNLS

theorem spectralShellPairNorm_add_le (kp km : ℝ) (hp : 0≤ kp) (hm : 0≤ km)
    (u v : (ℂ × ℂ) × (ℂ × ℂ)) :
    spectralShellPairNorm kp km (u+v)≤ spectralShellPairNorm kp km u+spectralShellPairNorm kp km v := by
  apply max_le
  · exact (spectralShellNorm_add_le kp hp u.1 v.1).trans
      (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (spectralShellNorm_add_le km hm u.2 v.2).trans
      (add_le_add (le_max_right _ _) (le_max_right _ _))

theorem spectralShellPairNorm_continuousOn (R E : ℝ) (kp km : ℝ → ℝ)
    (u : ℝ → (ℂ × ℂ) × (ℂ × ℂ))
    (hkp : ContinuousOn kp (Icc R E)) (hkm : ContinuousOn km (Icc R E))
    (hp : ∀ r ∈ Icc R E, kp r≠0) (hm : ∀ r ∈ Icc R E, km r≠0)
    (hu : ContinuousOn u (Icc R E)) :
    ContinuousOn (fun r => spectralShellPairNorm (kp r) (km r) (u r)) (Icc R E) := by
  exact ((hkp.mul hu.fst.fst.norm).add ((hkp.inv₀ hp).mul hu.fst.snd.norm)).sup
    ((hkm.mul hu.snd.fst.norm).add ((hkm.inv₀ hm).mul hu.snd.snd.norm))

theorem spectralShellPairNorm_exists_max (R E : ℝ) (hRE : R≤ E)
    (kp km : ℝ → ℝ) (u : ℝ → (ℂ × ℂ) × (ℂ × ℂ))
    (hkp : ContinuousOn kp (Icc R E)) (hkm : ContinuousOn km (Icc R E))
    (hp : ∀ r ∈ Icc R E, 0<kp r) (hm : ∀ r ∈ Icc R E, 0<km r)
    (hu : ContinuousOn u (Icc R E)) :
    ∃ M : ℝ, 0≤ M ∧ (∀ r ∈ Icc R E, spectralShellPairNorm (kp r) (km r) (u r)≤ M) ∧
      ∃ r ∈ Icc R E, spectralShellPairNorm (kp r) (km r) (u r)=M := by
  obtain ⟨r,hr,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hRE)
    (spectralShellPairNorm_continuousOn R E kp km u hkp hkm
      (fun r hr => (hp r hr).ne') (fun r hr => (hm r hr).ne') hu)
  exact ⟨_,spectralShellPairNorm_nonneg _ _ (hp r hr).le _,hmax,r,hr,rfl⟩

theorem spectralShellPairNorm_absorb (R E B theta : ℝ) (hRE : R≤ E)
    (htheta : 0≤ theta) (htheta1 : theta≤ 1/2)
    (kp km : ℝ → ℝ) (u v : ℝ → (ℂ × ℂ) × (ℂ × ℂ))
    (hkp : ContinuousOn kp (Icc R E)) (hkm : ContinuousOn km (Icc R E))
    (hp : ∀ r ∈ Icc R E, 0<kp r) (hm : ∀ r ∈ Icc R E, 0<km r)
    (hu : ContinuousOn u (Icc R E))
    (hv : ∀ r ∈ Icc R E, spectralShellPairNorm (kp r) (km r) (v r)≤ B)
    (herror : ∀ M : ℝ, 0≤ M → (∀ r ∈ Icc R E, spectralShellPairNorm (kp r) (km r) (u r)≤ M) →
      ∀ r ∈ Icc R E, spectralShellPairNorm (kp r) (km r) (u r-v r)≤ theta*M) :
    ∀ r ∈ Icc R E, spectralShellPairNorm (kp r) (km r) (u r)≤ 2*B ∧
      spectralShellPairNorm (kp r) (km r) (u r-v r)≤ 2*theta*B := by
  obtain ⟨M,hM,hbound,s,hs,heq⟩ := spectralShellPairNorm_exists_max R E hRE kp km u
    hkp hkm hp hm hu
  have herr := herror M hM hbound
  have hmax : M≤ theta*M+B := by
    calc
      M = spectralShellPairNorm (kp s) (km s) (u s) := heq.symm
      _ = spectralShellPairNorm (kp s) (km s) ((u s-v s)+v s) := by rw [sub_add_cancel]
      _ ≤ spectralShellPairNorm (kp s) (km s) (u s-v s)+
          spectralShellPairNorm (kp s) (km s) (v s) :=
        spectralShellPairNorm_add_le _ _ (hp s hs).le (hm s hs).le _ _
      _ ≤ theta*M+B := add_le_add (herr s hs) (hv s hs)
  have hMB : M≤ 2*B := by nlinarith
  intro r hr
  refine ⟨(hbound r hr).trans hMB, (herr r hr).trans ?_⟩
  calc
    theta*M≤ theta*(2*B) := mul_le_mul_of_nonneg_left hMB htheta
    _ = _ := by ring

end DefocusingNLS

end OAI
