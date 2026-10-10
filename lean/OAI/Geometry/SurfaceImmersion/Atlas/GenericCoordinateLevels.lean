import OAI.Geometry.SurfaceImmersion.Geometry.IndependentRadiusProjections

namespace OAI

/-! Generic common levels for finitely many radius functions in countably
many surface charts. This is the radius-selection step of the global preparation. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PublishedInputs
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Countable α]

abbrev DistinctRadiusPairs (ι : Type*) := {p : ι × ι // p.1 ≠ p.2}
abbrev DistinctRadiusTriples (ι : Type*) :=
  {p : (ι × ι) × ι // p.1.1 ≠ p.1.2 ∧ p.1.1 ≠ p.2 ∧ p.1.2 ≠ p.2}

theorem exists_generic_coordinate_levels
    (ρ : α → ι → Plane → ℝ) (hρ : ∀ a i, ContDiff ℝ ∞ (ρ a i))
    (K : α → Set Plane) (hK : ∀ a, IsCompact (K a))
    (U : Set (ι → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ r ∈ U,
      (∀ a i j, i ≠ j → ∀ x ∈ K a,
        ρ a i x = r i → ρ a j x = r j →
        Function.Surjective (fderiv ℝ (fun y =>
          radiusPairProjection i j (fun k => ρ a k y)) x)) ∧
      (∀ a i j, i ≠ j → (K a ∩ {x | ρ a i x = r i ∧ ρ a j x = r j}).Finite) ∧
      ∀ a i j k, i ≠ j → i ≠ k → j ≠ k → ∀ x ∈ K a,
        ¬ (ρ a i x = r i ∧ ρ a j x = r j ∧ ρ a k x = r k) := by
  let p : α × DistinctRadiusPairs ι → (ι → ℝ) →L[ℝ] Plane :=
    fun a => radiusPairProjection a.2.1.1 a.2.1.2
  let q : α × DistinctRadiusTriples ι → (ι → ℝ) →L[ℝ] (Plane × ℝ) :=
    fun a => radiusTripleProjection a.2.1.1.1 a.2.1.1.2 a.2.1.2
  let f : α × DistinctRadiusPairs ι → Plane → Plane :=
    fun a x => p a (fun k => ρ a.1 k x)
  let g : α × DistinctRadiusTriples ι → Plane → Plane × ℝ :=
    fun a x => q a (fun k => ρ a.1 k x)
  have hf : ∀ a, ContDiff ℝ ∞ (f a) := fun a =>
    (p a).contDiff.comp (contDiff_pi.mpr (hρ a.1))
  have hg : ∀ a, ContDiff ℝ ∞ (g a) := fun a =>
    (q a).contDiff.comp (contDiff_pi.mpr (hρ a.1))
  obtain ⟨r,hr,hreg,hfinite,htriple⟩ := exists_generic_radius_parameters p
    (fun a => radiusPairProjection_surjective a.2.2) q
    (fun a => radiusTripleProjection_surjective a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    f hf (fun a => K a.1) (fun a => hK a.1)
    g hg (fun a => K a.1) (fun a => hK a.1) U hU hne
  have hpairEq (a : α) (i j : ι) (hij : i ≠ j) (x : Plane) :
      f (a,⟨(i,j),hij⟩) x = p (a,⟨(i,j),hij⟩) r ↔
        ρ a i x = r i ∧ ρ a j x = r j := by
    constructor
    · intro he
      exact ⟨congrArg (fun z : Plane => z 0) he,congrArg (fun z : Plane => z 1) he⟩
    · rintro ⟨hi,hj⟩
      apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).injective
      funext b
      fin_cases b
      · exact hi
      · exact hj
  refine ⟨r,hr,?_,?_,?_⟩
  · intro a i j hij x hx hi hj
    exact hreg (a,⟨(i,j),hij⟩) x hx ((hpairEq a i j hij x).mpr ⟨hi,hj⟩)
  · intro a i j hij
    exact (hfinite (a,⟨(i,j),hij⟩)).subset (fun x hx =>
      ⟨hx.1,(hpairEq a i j hij x).mpr hx.2⟩)
  · intro a i j k hij hik hjk x hx he
    apply htriple (a,⟨((i,j),k),hij,hik,hjk⟩) x hx
    apply Prod.ext
    · exact (hpairEq a i j hij x).mpr ⟨he.1,he.2.1⟩
    · exact he.2.2

end ClosedSurfaceR4.PublishedInputs

end

end OAI
