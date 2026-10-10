import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.PrincipalNormalize
import OAI.Geometry.TamingCompatibility.Functional.ChartNormalTest

namespace OAI


noncomputable section
namespace TamingCompatibility.LocalMatrixOperator
open EuclideanEnergy HilbertSobolev
open scoped RealInnerProductSpace SchwartzMap

lemma exists_scaled_normalize (g : MetricModel.Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (c k : ℝ) (hc : 0 < c) (hk : 0 < k) :
    ∃ (L : V ≃L[ℝ] V) (s : ℝ), c*(s*s)=k ∧ ∀ i, L (b i)=s • e i := by
  let s := Real.sqrt (k/c)
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos hk hc)
  refine ⟨(normalizeFrame g b hb).trans
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := V) (Units.mk0 s (ne_of_gt hs))),s,?_,?_⟩
  · have hh : s*s = k/c := by simpa only [← sq] using Real.sq_sqrt (le_of_lt (div_pos hk hc))
    rw [hh]
    field_simp
  · intro i
    change s • normalizeFrame g b hb (b i) = _
    rw [normalizeFrame_apply]

lemma exists_principal_normalization (g : MetricModel.Metric V) (b : Fin 4 → V)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
    (c k : ℝ) (hc : 0 < c) (hk : 0 < k)
    (G : Fin 4 → Fin 4 → 𝓢(V,ℂ)) (p : V)
    (hG : ∀ i j, G i j p = (c * ∑ t,b t i * b t j : ℝ)) :
    ∃ L : V ≃L[ℝ] V, ∀ a d,
      principalInBasis (stdOrthonormalBasis ℝ V) (fun i => L (e i))
        (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm (G i j)) a d (L p) =
        if a=d then (k : ℂ) else 0 := by
  obtain ⟨L,s,hcL,hL⟩ := exists_scaled_normalize g b hb c k hc hk
  let d := EuclideanSpace.basisFun (Fin 4) ℝ
  have hd (i : Fin 4) : d i = e i := by simp only [d,EuclideanSpace.basisFun_apply,e]
  refine ⟨L,fun a t => ?_⟩
  have hh := normalized_principal_center d (stdOrthonormalBasis ℝ V) L b s c k
    (by simpa only [hd] using hL) hcL G p (by
      intro i j
      rw [hG]
      congr 2
      apply Finset.sum_congr rfl
      intro t _
      simp only [d,EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_left,map_one,one_mul]) a t
  simpa only [hd] using hh

end TamingCompatibility.LocalMatrixOperator

end

end OAI
