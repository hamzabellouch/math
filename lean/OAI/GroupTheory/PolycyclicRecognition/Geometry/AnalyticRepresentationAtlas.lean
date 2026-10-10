import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Normed.Algebra.Exponential

namespace OAI

/-! # Analytic charts supplied by a local matrix representation

A local coordinate obtained by projecting a representation, with analytic
matrix entries in those coordinates, supplies analytic translated charts.
-/

noncomputable section
namespace PolycyclicRecognition
open Set
open scoped Manifold ContDiff

variable {G E A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]

/-- Only the concrete local chart data needed for the analytic atlas. -/
structure RepresentedLocalChart (ρ : G →* Aˣ) where
  chart : OpenPartialHomeomorph G E
  one_mem : (1 : G) ∈ chart.source
  at_one : chart 1 = 0
  coordinate : A →L[ℝ] E
  coordinate_eq : ∀ g ∈ chart.source, chart g = coordinate ((ρ g : A) - 1)
  realization : E → A
  realization_contDiff : ContDiffOn ℝ ω realization chart.target
  realization_eq : ∀ x ∈ chart.target, realization x = (ρ (chart.symm x) : A)
  inverseRealization : E → A
  inverseRealization_contDiff : ContDiffOn ℝ ω inverseRealization chart.target
  inverseRealization_eq : ∀ x ∈ chart.target,
    inverseRealization x = ((ρ (chart.symm x))⁻¹ : Aˣ)

namespace RepresentedLocalChart
variable {ρ : G →* Aˣ} (C : RepresentedLocalChart (E := E) ρ)

def translated (g : G) : OpenPartialHomeomorph G E :=
  (Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph.trans C.chart

@[simp] theorem translated_apply (g x : G) : C.translated g x = C.chart (g⁻¹ * x) := rfl

@[simp] theorem translated_symm_apply (g : G) (x : E) :
    (C.translated g).symm x = g * C.chart.symm x := by
  change g⁻¹⁻¹ * C.chart.symm x = _
  rw [inv_inv]

@[simp] theorem translated_target (g : G) : (C.translated g).target = C.chart.target := by
  ext x
  change x ∈ C.chart.target ∧ C.chart.symm x ∈ (Set.univ : Set G) ↔ _
  simp

@[instance_reducible]
def chartedSpace : ChartedSpace E G where
  atlas := Set.range C.translated
  chartAt := C.translated
  mem_chart_source g := by
    change g ∈ (Set.univ : Set G) ∧ g⁻¹ * g ∈ C.chart.source
    exact ⟨Set.mem_univ _, by simpa only [inv_mul_cancel] using C.one_mem⟩
  chart_mem_atlas g := ⟨g,rfl⟩

theorem transition_contDiff (a b : G) :
    ContDiffOn ℝ ω ((C.translated a).symm ≫ₕ C.translated b)
      ((C.translated a).symm ≫ₕ C.translated b).source := by
  let s := ((C.translated a).symm ≫ₕ C.translated b).source
  have hs : s ⊆ C.chart.target := by
    intro x hx
    exact (C.translated_target a) ▸ hx.1
  have hf : ContDiffOn ℝ ω
      (fun x => (((ρ b)⁻¹ : Aˣ) : A) * ((ρ a : A) * C.realization x) - 1) s :=
    (contDiffOn_const.mul (contDiffOn_const.mul
      (C.realization_contDiff.mono hs))).sub contDiffOn_const
  have hh := C.coordinate.contDiff.comp_contDiffOn hf
  apply hh.congr
  intro x hx
  simp only [OpenPartialHomeomorph.trans_apply, translated_apply,
    translated_symm_apply, Function.comp_apply]
  have hx' : (C.translated a).symm x ∈ (C.translated b).source := hx.2
  have hx'' : b⁻¹ * ((C.translated a).symm x) ∈ C.chart.source := hx'.2
  rw [translated_symm_apply] at hx''
  rw [C.coordinate_eq _ hx'']
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
    ← C.realization_eq x (hs hx)]

theorem isManifold : letI := C.chartedSpace; IsManifold (𝓘(ℝ,E)) ω G := by
  let cs : ChartedSpace E G := C.chartedSpace
  apply isManifold_of_contDiffOn
  rintro e e' ⟨a,rfl⟩ ⟨b,rfl⟩
  simpa only [mfld_simps] using C.transition_contDiff a b

end RepresentedLocalChart
end PolycyclicRecognition

end

end OAI
