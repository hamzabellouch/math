import SphereEversion.Local.HPrinciple
import SphereEversion.ToMathlib.LinearAlgebra.FiniteDimensional

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge
abbrev Plane := Fin 2 → ℝ
abbrev Vec := EuclideanSpace ℝ (Fin 3)

def localizedImmersionRel (K : Set Plane) : RelLoc Plane Vec :=
  {q | q.1 ∉ K ∨ Function.Injective q.2.2}

lemma localizedImmersionRel_open {K : Set Plane} (hK : IsClosed K) :
    IsOpen (localizedImmersionRel K) :=
  (hK.isOpen_compl.preimage continuous_fst).union
    (ContinuousLinearMap.isOpen_injective.preimage continuous_snd.snd)

lemma localizedImmersionRel_ample (K : Set Plane) :
    (localizedImmersionRel K).IsAmple := by
  apply RelLoc.isAmple_iff.mpr
  intro q p hq
  by_cases hx : q.1 ∈ K
  · have hi : Function.Injective q.2.2 := hq.resolve_left (not_not.mpr hx)
    have hs : (localizedImmersionRel K).slice p q =
        ((p.π.ker).map q.2.2.toLinearMap : Set Vec)ᶜ := by
      ext w
      simp only [RelLoc.mem_slice,localizedImmersionRel,mem_ofPred_eq,hx,not_true_eq_false,
        false_or,Set.mem_compl_iff,p.injective_update_iff hi]
      rfl
    rw [hs]
    apply AmpleSet.of_one_lt_codim
    exact one_lt_rank_of_rank_lt_rank p.ker_pi_ne_top (by simp [Plane,Vec]) q.2.2.toLinearMap
  · apply RelLoc.ample_slice_of_forall
    intro w
    exact Or.inl hx

end ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

namespace ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

/-- The local h-principle realizes an injective formal differential while
preserving the prescribed exterior germs. -/
theorem realize_relative_frame {f : Plane → Vec} {A : Plane → Plane →L[ℝ] Vec}
    (hf : ContDiff ℝ ∞ f) (hA : ContDiff ℝ ∞ A)
    (L : Landscape Plane) (hcover : L.K₀ ∪ L.C = Set.univ)
    (hAI : ∀ x ∈ L.K₁, Function.Injective (A x))
    (hhol : ∀ᶠ x in 𝓝ˢ L.C, fderiv ℝ f x = A x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Plane → Vec, ContDiff ℝ ∞ g ∧
      tsupport (g-f) ⊆ L.K₁ ∧ (∀ x, ‖g x-f x‖ < ε) ∧
      (∀ x ∈ L.K₁, Function.Injective (fderiv ℝ g x)) ∧
      ∀ x ∈ L.C, g =ᶠ[𝓝 x] f := by
  let S : (localizedImmersionRel L.K₁).FormalSol :=
    { f := f, f_diff := hf, φ := A, φ_diff := hA,
      is_sol := fun x => by
        by_cases hx : x ∈ L.K₁
        · exact Or.inr (hAI x hx)
        · exact Or.inl hx }
  have hShol : ∀ᶠ x in 𝓝ˢ L.C, S.IsHolonomicAt x := hhol
  obtain ⟨H,_hzero,_hone,hC,hout,hclose,hend⟩ :=
    RelLoc.FormalSol.improve_htpy' (localizedImmersionRel_open L.hK₁.isClosed)
      (localizedImmersionRel_ample L.K₁) L hε S hShol
  let g := (H 1).f
  have hg : ContDiff ℝ ∞ g := (H 1).f_diff
  have houtside : ∀ x ∉ L.K₁, g x = f x := by
    intro x hx
    exact congrArg Prod.fst (hout x hx 1)
  have hCgerm : ∀ x ∈ L.C, g =ᶠ[𝓝 x] f := by
    intro x hx
    have he : ∀ᶠ y in 𝓝 x, ∀ t, H t y = S y :=
      hC.filter_mono (nhds_le_nhdsSet hx)
    filter_upwards [he] with y hy
    exact congrArg Prod.fst (hy 1)
  refine ⟨g,hg,?_,fun x => hclose x 1,?_,hCgerm⟩
  · apply closure_minimal _ L.hK₁.isClosed
    intro x hx
    by_contra hn
    exact hx (sub_eq_zero.mpr (houtside x hn))
  · intro x hx
    have hsol : Function.Injective ((H 1).φ x) :=
      (H.is_sol 1 x).resolve_left (not_not.mpr hx)
    by_cases hx0 : x ∈ L.K₀
    · have hh := hend.self_of_nhdsSet x hx0
      change fderiv ℝ g x = (H 1).φ x at hh
      rwa [hh]
    · have hxC : x ∈ L.C := by
        have hxU : x ∈ L.K₀ ∪ L.C := hcover.symm ▸ Set.mem_univ x
        exact hxU.resolve_left hx0
      rw [(hCgerm x hxC).fderiv_eq, hhol.self_of_nhdsSet x hxC]
      exact hAI x hx

end ClosedSurfaceR4.FiniteOrderSmoothing.HPrincipleBridge

end

end OAI
