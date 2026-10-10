import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ContactDifferential
import OAI.Analysis.BiholderTransport.Coordinates.SplitLogInjective
import OAI.Analysis.BiholderTransport.LinearAlgebra.CompactQuadratic

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section JoinCoordinates
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_join_normal_coordinates {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {h : ℝ} (hh : h≠0) (hp : h • p∈injectivityDomain x) :
    ∃ q : TangentSpace 𝓘(ℝ,Model n) x →
        TangentSpace 𝓘(ℝ,Model n) (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1,
      q p=0 ∧ ContDiffAt ℝ ∞ q p ∧ Function.Injective (fderiv ℝ q p) ∧
      ∀ᶠ a in 𝓝 p, riemannianExp _ (q a)=riemannianExp x (h • a) := by
  let : Nonempty M := ⟨x⟩
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let z := sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let Z := TangentSpace 𝓘(ℝ,Model n) z.1
  obtain ⟨κ,hκ0,hκ,hκr⟩ := exists_normal_local_inverse_at (zero_mem_injectivityDomain (n := n) z.1)
  rw [riemannianExp_zero] at hκ0 hκ hκr
  let q : X → Z := fun a => κ (riemannianExp x (h • a))
  have heq : riemannianExp x (h • p)=z.1 := riemannianExp_smul x p h
  have hE : ContMDiffAt 𝓘(ℝ,X) 𝓘(ℝ,Model n) ∞
      (fun a : X => riemannianExp x (h • a)) p :=
    (contMDiff_riemannianExp_fiber x _).comp p
      (show ContDiffAt ℝ ∞ (fun a : X => h • a) p from by fun_prop).contMDiffAt
  have hq : ContDiffAt ℝ ∞ q p := by
    apply ContMDiffAt.contDiffAt
    apply ContMDiffAt.comp p _ hE
    rwa [heq]
  have hqp : q p=0 := by change κ _=0; rw [heq,hκ0]
  have hqr : ∀ᶠ a in 𝓝 p, riemannianExp z.1 (q a)=riemannianExp x (h • a) :=
    hE.continuousAt.eventually (by simpa only [heq] using hκr)
  exact ⟨q,hqp,hq,prefix_log_fderiv_injective hh hp (hq.differentiableAt (by simp)) hqr,hqr⟩

lemma middle_action_in_join_coordinates {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {h : ℝ} (hp : p∈minimizingVectors x) (hh : 0<h) (hh1 : h<1)
    {q : TangentSpace 𝓘(ℝ,Model n) x →
        TangentSpace 𝓘(ℝ,Model n) (sprayFlow h (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1}
    (hqr : ∀ᶠ a in 𝓝 p, riemannianExp _ (q a)=riemannianExp x (h • a)) :
    (middleCenteredAction (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) h ∘ q) =ᶠ[𝓝 p]
      (fun a => diagonalSplitAction x h (p,a)-cost x (riemannianExp x p)) := by
  filter_upwards [hqr] with a ha
  have hc := middle_action_contact (z := (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) hp hh hh1
  dsimp only [Function.comp_apply,middleCenteredAction]
  rw [middle_normal_prefix,middle_normal_suffix,ha]
  dsimp only [diagonalSplitAction,splitNormalAction,normalCost]
  simp only [normalCost,riemannianExp_zero,div_eq_mul_inv] at hc ⊢
  nlinarith only [hc]

end JoinCoordinates
end WeakMTWTransport

end

end

end

end OAI
