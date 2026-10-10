import Mathlib
import OAI.Analysis.BiholderTransport.Volume.ReversedRadial
import OAI.Analysis.BiholderTransport.Volume.OutwardSpectrum

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma three_determinants_close {σ σi σt σti V W K c C d c₀ c₁ C₀ : ℝ}
    (hσ : 0<σ) (hσi : 0<σi) (hσt : 0<σt) (hσti : 0<σti)
    (hK : 0<K) (hc : 0<c) (hC : 0<C) (hd : 0<d)
    (hc₀ : 0<c₀) (hc₁ : 0<c₁) (hC₀ : 0<C₀)
    (hr : c*σt ≤ C*σ) (hri : c*σi ≤ C*σti) (ha : d*σi ≤ σ)
    (hV : c₀*σ^2/σt ≤ V) (hW : W ≤ C₀*σi^2/σti) (hVW : c₁*K*V ≤ W) :
    K ≤ (C₀*C*C)/(c₁*c₀*c*c*d) := by
  have hV0 : 0 ≤ V := (div_nonneg (mul_nonneg hc₀.le (sq_nonneg σ)) hσt.le).trans hV
  have hlow : c₀*c*σ ≤ C*V := by
    have h0 := (div_le_iff₀ hσt).mp hV
    have h1 := mul_le_mul_of_nonneg_left h0 hc.le
    have h2 := mul_le_mul_of_nonneg_left hr hV0
    apply (mul_le_mul_iff_right₀ hσ).mp
    nlinarith only [h1,h2]
  have hupp : c*W ≤ C₀*C*σi := by
    have h0 := (le_div_iff₀ hσti).mp hW
    have h1 := mul_le_mul_of_nonneg_left h0 hc.le
    have h2 := mul_le_mul_of_nonneg_left hri (mul_nonneg hC₀.le hσi.le)
    apply (mul_le_mul_iff_right₀ hσti).mp
    nlinarith only [h1,h2]
  have h1 := mul_le_mul_of_nonneg_left hVW (mul_nonneg hc.le hC.le)
  have h2 := mul_le_mul_of_nonneg_left hlow (mul_nonneg (mul_nonneg hc.le hc₁.le) hK.le)
  have h3 := mul_le_mul_of_nonneg_left hupp hC.le
  have h4 := mul_le_mul_of_nonneg_left ha
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc₁.le hc₀.le) hc.le) hc.le) hK.le)
  apply (le_div_iff₀ (by positivity : 0<c₁*c₀*c*c*d)).mpr
  apply (mul_le_mul_iff_right₀ hσi).mp
  nlinarith only [h1,h2,h3,h4]

section DeterminantClosure
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [ConnectedSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance threeDeterminantsCloseFiniteDimensionalTangentSpace (x : M) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma WeakMTW.uniform_three_determinant_closure
    (hmtw : WeakMTW (n := n) (M := M)) {μ κ A c₀ c₁ C₀ : ℝ}
    (hμ : 0<μ) (hκ : 0<κ) (hA : 0<A) (hc₀ : 0<c₀) (hc₁ : 0<c₁) (hC₀ : 0<C₀) :
    ∃ B : ℝ, 0<B ∧ ∀ (ι : Type) [Fintype ι] (x : M)
      (v : ι → TangentSpace 𝓘(ℝ,Model n) x) (w : ι → ℝ)
      (p : TangentSpace 𝓘(ℝ,Model n) x),
      (∀ j,0 ≤ w j) → (∑ j,w j=1) → (∀ j,v j∈minimizingVectors x) →
      p=∑ j,w j • v j → ∀ (i : ι) (e : TangentSpace 𝓘(ℝ,Model n) x) (t D : ℝ),
      μ ≤ w i → ‖e‖=1 → 0<t → 0<D → 0 < inner ℝ p e →
      κ*D ≤ (inner ℝ p e)^2 → ‖v i‖^2-‖p‖^2 ≤ A*D → v i=p+t • e →
      ∀ l∈Icc (1/2:ℝ) 1, ∀ li∈Icc (1:ℝ) 2,
      let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,p⟩
      let zi : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,v i⟩
      let σ := expJacobian x p
      let σi := expJacobian x (v i)
      let σt := expJacobian (reverseRay z).1 (l⁻¹ • (reverseRay z).2)
      let σti := expJacobian (reverseRay zi).1 (li⁻¹ • (reverseRay zi).2)
      l⁻¹ • (reverseRay z).2∈minimizingVectors (reverseRay z).1 →
      0<σ → 0<σi → 0<σt → 0<σti → ∀ V W K : ℝ, 0<K →
      c₀*σ^2/σt ≤ V → W ≤ C₀*σi^2/σti → c₁*K*V ≤ W → K ≤ B := by
  obtain ⟨c,C,hc,hC,HR,HRi⟩ := uniform_reversed_radial_expJacobian_comparison (n := n) (M := M)
  obtain ⟨d,hd,HO⟩ := hmtw.uniform_outward_expJacobian_comparison hμ hκ hA
  refine ⟨(C₀*C*C)/(c₁*c₀*c*c*d),by positivity,?_⟩
  intro ι _ x v w p hw hs hv hp i e t D hi he ht hD hh hhD hgap hvi l hl li hli
  dsimp only
  intro hr hσ hσi hσt hσti V W K hK hV hW hVW
  have hpG : p∈minimizingVectors x := by
    rw [hp]
    exact (hmtw.convex_minimizingVectors x).sum_mem (fun j _ => hw j) hs (fun j _ => hv j)
  exact three_determinants_close hσ hσi hσt hσti hK hc hC hd hc₀ hc₁ hC₀
    (HR ⟨x,p⟩ hpG l hl hr) (HRi ⟨x,v i⟩ (hv i) li hli)
    (HO ι x v w p hw hs hv hp i e t D hi he ht hD hh hhD hgap hvi) hV hW hVW
end DeterminantClosure
end WeakMTWTransport

end

end

end

end OAI
