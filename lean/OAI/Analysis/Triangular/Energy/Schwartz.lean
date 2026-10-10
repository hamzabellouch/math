import OAI.Analysis.Triangular.Energy.Density
import OAI.Analysis.Triangular.Basic

namespace OAI

noncomputable section
open scoped FourierTransform SchwartzMap
open Complex MeasureTheory FourierTransform
namespace AtomicTriangular

def complexSchwartz (f : 𝓢(Plane,ℝ)) : 𝓢(Plane,ℂ) := f.postcompCLM Complex.ofRealCLM
lemma complexSchwartz_apply (f : 𝓢(Plane,ℝ)) (x : Plane) : complexSchwartz f x=(f x:ℂ) := by
  simp only [complexSchwartz,SchwartzMap.postcompCLM_apply,Complex.ofRealCLM_apply]
def schwartzLP (f : 𝓢(Plane,ℝ)) : TriangularUniversal.LPFunction where
  toFun := complexSchwartz f
  continuous := (complexSchwartz f).continuous
  integrable := (complexSchwartz f).integrable
  fourierIntegrable := (𝓕 (complexSchwartz f)).integrable
  momentIntegrable := by simpa only [pow_one] using (complexSchwartz f).integrable_pow_mul volume 1
  bound := SchwartzMap.seminorm ℝ 0 0 (complexSchwartz f)
  norm_bound := SchwartzMap.norm_le_seminorm ℝ (complexSchwartz f)
lemma schwartzLP_apply (f : 𝓢(Plane,ℝ)) (x : Plane) : schwartzLP f x=(f x:ℂ) :=
  complexSchwartz_apply f x
lemma schwartzLP_fourier (f : 𝓢(Plane,ℝ)) (w : Plane) :
    𝓕 (schwartzLP f : Plane → ℂ) w=realFourier f w := by
  congr 1
end AtomicTriangular
end

end OAI
