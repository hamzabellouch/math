import OAI.Analysis.CircleDomains.Probability.CenteredSubtypeLaw
import OAI.Analysis.CircleDomains.Topology.QuotientLocalChart

namespace OAI

/-! The concrete centered disk data of a compact terminal-arc family. All
injectivity and unit bounds hold on the actual punctured Jordan interior. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

structure CenteredTerminalFamily (J : ℂ ≃ₜ ℂ) (b : Sphere)
    (A : Set C(PathTime, Sphere)) where
  map : C(Sphere, ℂ)
  map_eq : EqOn map (centeredJordanCoordinate J b)
    (closure (((↑) : ℂ → Sphere) '' jordanInterior J))
  diskArcs : Set C(PathTime, ℂ)
  compact : IsCompact diskArcs
  terminal : diskArcs ⊆ diskTerminalArcSet
  arcMap : A → diskArcs
  continuous_arcMap : Continuous arcMap
  arcMap_eq : ∀ γ : A, (arcMap γ).val = map.comp γ.val

 theorem exists_centered_terminal_family (J : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)
    (A : Set C(PathTime, Sphere)) (hA : IsCompact A)
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) b) :
    Nonempty (CenteredTerminalFamily J b A) := by
  obtain ⟨F, hF⟩ := exists_centeredJordanExtension J hb
  let K := F.comp '' A
  let f : A → K := fun γ => ⟨F.comp γ.val, mem_image_of_mem F.comp γ.property⟩
  refine ⟨⟨F, hF, K, hA.image F.continuous_postcomp, ?_, f,
    (F.continuous_postcomp.comp continuous_subtype_val).subtype_mk _, fun _ => rfl⟩⟩
  rintro _ ⟨γ, hγ, rfl⟩
  exact centeredJordanPath_mem J hb F hF (hAS hγ)

namespace CenteredTerminalFamily
variable {J : ℂ ≃ₜ ℂ} {b : Sphere} {A : Set C(PathTime, Sphere)}
    (P : CenteredTerminalFamily J b A)
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J)

 def punctured (_P : CenteredTerminalFamily J b A) : Set Sphere := (((↑) : ℂ → Sphere) '' jordanInterior J) \ {b}

 theorem punctured_open : IsOpen P.punctured :=
  (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen J)).sdiff isClosed_singleton

 include hb

 theorem nonzero : ∀ x ∈ P.punctured, P.map x ≠ 0 := by
  intro x hx he
  apply hx.2
  apply (centeredJordanCoordinate_injOn J hb (subset_closure hx.1) (subset_closure hb))
  rw [← P.map_eq (subset_closure hx.1), centeredJordanCoordinate_self]
  exact he

 theorem norm_lt : ∀ x ∈ ((↑) : ℂ → Sphere) '' jordanInterior J, ‖P.map x‖ < 1 := by
  intro x hx
  rw [P.map_eq (subset_closure hx)]
  exact diskCentering_norm_lt (sphereJordanCoordinate_norm_lt J hb)
    (sphereJordanCoordinate_norm_lt J hx)

 theorem norm_le : ∀ x ∈ P.punctured, ‖P.map x‖ ≤ 1 :=
  fun x hx => (P.norm_lt hb x hx.1).le

 theorem injective : InjOn P.map (closure (((↑) : ℂ → Sphere) '' jordanInterior J)) := by
  intro x hx y hy he
  apply centeredJordanCoordinate_injOn J hb hx hy
  rwa [← P.map_eq hx, ← P.map_eq hy]

 theorem injective_punctured : InjOn P.map P.punctured :=
  (P.injective hb).mono (fun _ hx => subset_closure hx.1)

 theorem injective_arcs
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) b) :
    ∀ γ : A, InjOn P.map (range γ.val ∪ P.punctured) := by
  intro γ
  apply (P.injective hb).mono
  rintro x (⟨t, rfl⟩ | hx)
  · exact terminalArcSet_mapsTo_closure (hAS γ.property) hb (mem_univ t)
  · exact subset_closure hx.1

 omit hb in
 theorem endpoint
    (hAS : A ⊆ terminalArcSet (((↑) : ℂ → Sphere) '' jordanInterior J) b) :
    ∀ γ : A, b ∈ range γ.val := fun γ => ⟨⊤, (hAS γ.property).2.2.1⟩

end CenteredTerminalFamily
end CircleDomainRigidity

end

end OAI
