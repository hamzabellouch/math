import OAI.Geometry.SurfaceImmersion.Whitney.RegularPathCoverGerms

namespace OAI

/-! Away from finitely many corners, an embedded finite regular path is
an actual smooth immersion of the real parameter. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {x y : M} {γ : Path x y}

lemma affine_parameter_regular {a b : ℝ} (ha : a ≠ 0) (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ) (fun u : ℝ => a*u+b) t) := by
  have hA : HasDerivAt (fun u : ℝ => a*u+b) a t := by simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul a).add_const b
  have hD := hA.hasFDerivAt.hasMFDerivAt.mfderiv
  rw [hD]
  intro u v huv
  change ℝ at u v
  change u*a = v*a at huv
  exact (mul_right_cancel₀ ha huv : (u:ℝ) = (v:ℝ))

theorem FiniteRegularPath.smooth_outside_finite (hP : FiniteRegularPath J γ)
    (hi : Function.Injective γ) :
    ∃ S : Set ℝ, S.Finite ∧ ∀ t ∈ Ioo (0:ℝ) 1, t ∉ S →
      ContMDiffAt 𝓘(ℝ) J ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) J γ.extend t) := by
  obtain ⟨S,hS,hgerms⟩ := hP.cover.some.regular_germs_outside_finite hi
  refine ⟨S,hS,?_⟩
  intro t ht htS
  obtain ⟨A,a,b,ha,hab,he⟩ := hgerms t ht htS
  have hA := A.smooth.contMDiffAt (A.domain_open.mem_nhds hab)
  have hparam : ContDiff ℝ ∞ (fun u : ℝ => a*u+b) := by fun_prop
  have hC : ContMDiffAt 𝓘(ℝ) J ∞ (fun u : ℝ => A.curve (a*u+b)) t :=
    hA.comp t hparam.contMDiff.contMDiffAt
  refine ⟨hC.congr_of_eventuallyEq he,?_⟩
  have hreg : Function.Injective (mfderiv 𝓘(ℝ) J (fun u : ℝ => A.curve (a*u+b)) t) := by
    change Function.Injective (mfderiv 𝓘(ℝ) J (A.curve ∘ fun u : ℝ => a*u+b) t)
    rw [mfderiv_comp t (hA.mdifferentiableAt (by simp)) (hparam.contMDiff.mdifferentiable (by simp) t)]
    exact (A.regular _ hab).comp (affine_parameter_regular ha t)
  have hD := ((hC.mdifferentiableAt (by simp)).hasMFDerivAt.congr_of_eventuallyEq_abuse he).mfderiv
  exact hD.symm ▸ hreg

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
