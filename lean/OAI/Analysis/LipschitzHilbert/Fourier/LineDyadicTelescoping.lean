import OAI.Analysis.LipschitzHilbert.Fourier.LineCommutatorLinearity
import OAI.Analysis.LipschitzHilbert.Trees.DyadicLineGrid

namespace OAI

/-! Exact inhomogeneous coefficient reconstruction: the low-frequency
part is retained, and the finite high-frequency tail telescopes. -/
noncomputable section
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

def lineDyadic (f : SchwartzMap ℝ ℂ) (k : ℤ) : SchwartzMap ℝ ℂ :=
  lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' f

def lineLowpass (f : SchwartzMap ℝ ℂ) (k : ℤ) : SchwartzMap ℝ ℂ :=
  lineSchwartzProjection reassemblyLow (scale k) (scale_pos k).ne' f

theorem lineDyadic_eq_lowpass_sub (f : SchwartzMap ℝ ℂ) (k : ℤ) :
    lineDyadic f (k+1)=lineLowpass f k-lineLowpass f (k+1) := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineDyadic f (k+1)) : SchwartzMap ℝ ℂ) eta=
    (𝓕 (lineLowpass f k-lineLowpass f (k+1)) : SchwartzMap ℝ ℂ) eta
  change (𝓕 (lineDyadic f (k+1)) : SchwartzMap ℝ ℂ) eta=
    (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ) (lineLowpass f k-lineLowpass f (k+1))) eta
  rw [map_sub,sub_apply,FourierTransform.fourierCLM_apply,FourierTransform.fourierCLM_apply]
  simp only [lineDyadic,lineLowpass,lineSchwartzProjection_fourier,dyadicDifference_apply]
  rw [scale_succ]
  have he : (2*scale k*eta)/2=scale k*eta := by ring
  rw [he]
  ring

theorem lineLowpass_telescope (f : SchwartzMap ℝ ℂ) (l u : ℤ) (hlu : l≤u) :
    lineLowpass f l=lineLowpass f u+∑ k∈Finset.Icc (l+1) u, lineDyadic f k := by
  classical
  induction u, hlu using Int.leInduction with
  | base => simp
  | succ u hlu ih =>
    have he : Finset.Icc (l+1) (u+1)=insert (u+1) (Finset.Icc (l+1) u) := by
      ext k
      simp only [Finset.mem_Icc,Finset.mem_insert]
      omega
    rw [he,Finset.sum_insert (by simp),lineDyadic_eq_lowpass_sub]
    rw [ih]
    abel

theorem lineLowpass_telescope_filtered (f : SchwartzMap ℝ ℂ) (l u v : ℤ)
    (hlu : l≤u) (huv : u≤v) :
    lineLowpass f l=lineLowpass f u+
      ∑ k∈Finset.Icc (l+1) v, if k≤u then lineDyadic f k else 0 := by
  classical
  rw [←Finset.sum_filter]
  have he : (Finset.Icc (l+1) v).filter (fun k => k≤u)=Finset.Icc (l+1) u := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_Icc]
    omega
  rw [he]
  exact lineLowpass_telescope f l u hlu

end LipschitzHilbert.PacketRepresentation

end

end OAI
