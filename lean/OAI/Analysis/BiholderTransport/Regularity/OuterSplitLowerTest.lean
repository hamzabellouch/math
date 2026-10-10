import Mathlib
import OAI.Analysis.BiholderTransport.Contact.CenterSupport
import OAI.Analysis.BiholderTransport.Calculus.ScalarInverseJet

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section OuterSplitLowerTest
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma outer_split_lower_test {v : M → ℝ} {a : M}
    {r : TangentSpace 𝓘(ℝ,Model n) a} (hr : r∈minimizingVectors a)
    {φ : ℝ → ℝ} (hmono : StrictMono φ) (hφ : ContDiffAt ℝ 2 φ (v a))
    {l : ℝ} (hd : HasDerivAt φ l (v a)) (hl : l≠0)
    (hmount : ∀ y : M,φ (v a)+cost a (riemannianExp a r)-cost y (riemannianExp a r)≤φ (v y))
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ f : TangentSpace 𝓘(ℝ,Model n) a → ℝ, ContDiffAt ℝ 2 f 0 ∧ f 0=v a ∧
      (∀ᶠ h in 𝓝 0,f h≤v (riemannianExp a h)) ∧
      fderiv ℝ f 0=innerSL ℝ (l⁻¹ • r) ∧
      ∀ ξ,fderiv ℝ (fderiv ℝ f) 0 ξ ξ=
        -(l*s)⁻¹*hessianValue a (s • r) ξ-
          (iteratedDeriv 2 φ (v a)/l^3)*(inner ℝ r ξ)^2 := by
  let : Nonempty M := ⟨a⟩
  let F : TangentSpace 𝓘(ℝ,Model n) a → ℝ := fun h =>
    scalarCostSupport id (φ (v a)) a r s (riemannianExp a h)
  have hsp := contracted_minimizer_mem_injectivityDomain hr hs hs1
  obtain ⟨hF,hDF,hHF⟩ := scalarCostSupport_normal_jet (φ := id) (v0 := φ (v a))
    (l := 1) hs.ne' hsp contDiffAt_id (by simp)
  have hD : fderiv ℝ F 0=innerSL ℝ r := by simpa only [one_smul] using hDF.fderiv
  have hFv : F 0=φ (v (riemannianExp a (0 : TangentSpace 𝓘(ℝ,Model n) a))) := by
    simp only [F,riemannianExp_zero,scalarCostSupport_self,id_eq]
  have hlo : ∀ᶠ h in 𝓝 0,F h≤φ (v (riemannianExp a h)) := by
    apply Filter.Eventually.of_forall
    intro h
    have H := hmount (riemannianExp a h)
    have Hs := minimizing_split_upper_support hr hs hs1 (riemannianExp a h)
    have He := minimizing_split_contact hr hs hs1
    dsimp only [F,scalarCostSupport,id_eq]
    linarith only [H,Hs,He]
  obtain ⟨f,hf,hfv,hfl,hfd,hfh⟩ := scalar_inverse_lower_test hmono
    (v := fun h => v (riemannianExp a h)) (x := 0)
    (by simpa only [riemannianExp_zero] using hφ)
    (by simpa only [riemannianExp_zero] using hd) hl hF hFv hlo
  refine ⟨f,hf,by simpa only [riemannianExp_zero] using hfv,hfl,?_,?_⟩
  · rw [hfd,hD,map_smul]
  · intro ξ
    rw [hfh,hD]
    have H := hHF ξ
    change fderiv ℝ (fderiv ℝ F) 0 ξ ξ=_ at H
    simp only [iteratedDeriv_succ,iteratedDeriv_zero,deriv_id',deriv_const,zero_mul,add_zero,one_div] at H
    rw [H,riemannianExp_zero,innerSL_apply_apply]
    ring

end OuterSplitLowerTest
end WeakMTWTransport

end

end

end

end OAI
