import Mathlib
import OAI.GroupTheory.BooneHigman.AlgebraPresentations
import OAI.GroupTheory.FiniteType.CWWhitehead
import OAI.GroupTheory.FiniteType.StageConstruction
import OAI.GroupTheory.FiniteType.StageGeometry
import OAI.GroupTheory.FiniteType.StageGeometryProperties
import OAI.GroupTheory.FiniteType.Steinberg
import OAI.GroupTheory.SimpleOvergroups.TwoEnlargements

namespace OAI

noncomputable section
namespace SimpleFInftyOvergroups
open StageConstruction SourceEnlargement
open scoped Classical

structure SourceRingData (G : Type) [Group G] where
  R : Type
  [ringR : Ring R]
  [nontrivialR : Nontrivial R]
  [algebraR : Algebra (ZMod 2) R]
  φ : R →ₙ+* R
  φ_injective : Function.Injective φ
  binary : CompressedSplittings.BinaryData φ
  e : R
  e_idempotent : IsIdempotentElem e
  e_nonzero : e ≠ 0
  S : Double.Y (Q := Q R) (X := X R) → e_idempotent.Corner
  T : Double.Y (Q := Q R) (X := X R) → e_idempotent.Corner
  TS : ∀ y z, T y * S z = if y = z then 1 else 0
  ρ : Double.W (Q R) →* e_idempotent.Cornerˣ
  ρ_injective : Function.Injective ρ
  ρS : ∀ w y, (ρ w).val * S y = S (w • y)
  Tρ : ∀ w y, T y * (ρ w).val = T (w⁻¹ • y)
  A : Type
  [finiteA : Finite A]
  π : FreeAlgebra (ZMod 2) A →ₐ[ZMod 2] R
  π_surjective : Function.Surjective π
  rel : Set (FreeAlgebra (ZMod 2) A)
  rel_finite : rel.Finite
  ker_π : TwoSidedIdeal.ker π.toRingHom = TwoSidedIdeal.span rel
  g : G →* e_idempotent.Cornerˣ
  g_injective : Function.Injective g

namespace SourceRingData
variable {G : Type} [Group G]

theorem realize (d : SourceRingData G) :
    ∃ (H : Type) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
      HasTypeFInfty H ∧ ∃ f : G →* H, Function.Injective f := by
  let _ := d.ringR
  let _ := d.nontrivialR
  let _ := d.algebraR
  let _ := d.finiteA
  exact StageGeometry.simple_geometric_overgroup_of_corner_ring_data
    d.φ d.binary d.e d.e_idempotent d.e_nonzero d.S d.T
    (by
      intro y z
      by_cases h : y = z
      · simpa only [ite_eq_left h] using d.TS y z
      · simpa only [ite_eq_right h] using d.TS y z) d.ρ
    (Double.iota (Q := Q d.R)) (Double.point (Q := Q d.R) (X := X d.R))
    d.ρS d.Tρ Double.iota_point d.φ_injective d.ρ_injective
    Double.iota_injective Double.point_injective Double.diagrams₂ Double.diagrams₃
    d.A d.π.toRingHom d.π_surjective d.rel d.rel_finite d.ker_π d.g d.g_injective

end SourceRingData

def SourceRingProducerObligation : Prop :=
  ∀ (G : Type) [Group G], HasDecidableWordProblem G → Nonempty (SourceRingData G)

universe u

theorem main_of_sourceRingProducer (produce : SourceRingProducerObligation)
    (G : Type u) [Group G] [Group.FG G] (hG : HasDecidableWordProblem G) :
    ∃ (H : Type u) (_ : Group H), Nontrivial H ∧ IsSimpleGroup H ∧
      HasTypeFInfty H ∧ ∃ f : G →* H, Function.Injective f := by
  obtain ⟨G₀, i₀, ⟨e⟩, h₀⟩ := small_model G hG
  let _ := i₀
  obtain ⟨d⟩ := produce G₀ h₀
  obtain ⟨H, iH, hnt, hsi, hf, f, hinj⟩ := d.realize
  let _ := iH
  exact ⟨ULift.{u} H, inferInstance, lift_explicit_overgroup e f hinj hnt hsi hf⟩

end SimpleFInftyOvergroups
end

end OAI
