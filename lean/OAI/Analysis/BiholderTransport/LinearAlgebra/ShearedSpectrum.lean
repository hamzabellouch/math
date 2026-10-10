import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ShearedOperator

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ShearedSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma uniform_sheared_radial_spectrum {a B : ℝ} (ha : 0<a) (hB : 0<B)
    (haB : a*B≤1/2) :
    ∃ l u b : ℝ, 0<l ∧ 0<u ∧ 0<b ∧
      ∀ x : M, ∀ p q : TangentSpace 𝓘(ℝ,Model n) x,
      0 < inner ℝ p q → ‖q‖^2/inner ℝ p q≤B →
      (∀ t∈Icc (-a) 1, p+t • q∈minimizingVectors x) →
      ∀ δ∈Ioc (0:ℝ) (1/2), ∀ t∈Icc (-a) 1,
      ∃ hF : (shearedRadialOperator x p q δ t).toLinearMap.IsSymmetric,
      ∀ i : Fin (Module.finrank ℝ (Model n)),
      l*δ/((endpointExpDifferential x (p+t • q)).toLinearMap.singularValues i.rev+δ)-b*δ ≤
        hF.eigenvalues rfl i ∧
      hF.eigenvalues rfl i ≤
        u*δ/((endpointExpDifferential x (p+t • q)).toLinearMap.singularValues i.rev+δ)+b*δ := by
  obtain ⟨l,u,b,hl,hu,hb,H⟩ := uniform_radial_inverse_profile (n := n) (M := M)
  refine ⟨l/4,(2+B)^2*u,b*(2+B)^2,by positivity,by positivity,by positivity,?_⟩
  intro x p q hpq hβ hline δ hd t ht
  have hPt := hline t ht
  have hPi := contracted_minimizer_mem_injectivityDomain hPt
    (show 0<1-δ by linarith [hd.2]) (show 1-δ<1 by linarith [hd.1])
  have hF := shearedRadialOperator_symmetric hPi
  refine ⟨hF,?_⟩
  intro i
  obtain ⟨K,hK,hKb,hBg,hSp⟩ := H x (p+t • q) hPt δ hd
  let L := spectralShear p q t
  have hLn := spectralShear_uniform_bounds p q ha hB haB hpq hβ ht
  have hLb := spectralShear_bijective p q ha hB haB hpq hβ ht
  have hbg : ∀ v, |inner ℝ (shearedRadialOperator x p q δ t v) v-
      δ*inner ℝ (K (L v)) (L v)|≤(b*(2+B)^2*δ)*‖v‖^2 := by
    intro v
    rw [inner_shearedRadialOperator]
    have hs2 : ‖L v‖^2≤(2+B)^2*‖v‖^2 := by
      simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hLn v).2
    have HH := mul_le_mul_of_nonneg_left hs2 (mul_nonneg hb.le hd.1.le)
    have HH2 := (hBg (L v)).trans HH
    convert HH2 using 1; first | rfl | ring
  have HG := ordered_sheared_background_spectrum hF hK L.toLinearMap hLb
    (show (0:ℝ)<1/2 by norm_num) (show 0≤2+B by positivity) hd.1.le hLn hbg rfl i
  have Hlo := mul_le_mul_of_nonneg_left (hSp i).1 (sq_nonneg (1/2:ℝ))
  have Hup := mul_le_mul_of_nonneg_left (hSp i).2 (sq_nonneg (2+B))
  constructor
  · have HH := le_trans (sub_le_sub_right Hlo (b*(2+B)^2*δ)) HG.1
    convert HH using 1; first | rfl | ring
  · have HH := HG.2.trans (add_le_add Hup le_rfl)
    convert HH using 1; first | rfl | ring
end ShearedSpectrum
end WeakMTWTransport

end

end

end

end OAI
