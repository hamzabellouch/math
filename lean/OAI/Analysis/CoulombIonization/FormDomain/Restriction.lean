import Mathlib
import OAI.Analysis.CoulombIonization.Variational.Weighted

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
namespace CoulombAtom
section Restriction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def restrictWeakGraph (v : ι → E) (j : κ → ι) (F : weakGraph v) : weakGraph (v ∘ j) :=
  ⟨WithLp.toLp 2 (fun k => F.val (k.map j)), (mem_weakGraph _ _).mpr
    (fun k => (mem_weakGraph _ _).mp F.property (j k))⟩

def SmoothMultiplier.restrict {v : ι → E} (p : SmoothMultiplier v) (j : κ → ι) :
    SmoothMultiplier (v ∘ j) where
  value := p.value
  regular := p.regular
  bound := p.bound
  gradient_bound := fun k => p.gradient_bound (j k)

omit [Fintype ι] [Fintype κ] in
lemma SmoothMultiplier.restrict_apply {v : ι → E} (p : SmoothMultiplier v)
    (j : κ → ι) (F : weakGraph v) :
    (p.restrict j).apply (restrictWeakGraph v j F) = restrictWeakGraph v j (p.apply F) := by
  apply weakGraphValue_injective (v ∘ j)
  apply Lp.ext
  exact (p.restrict j).apply_value (restrictWeakGraph v j F) |>.trans (p.apply_value F).symm

omit [Fintype ι] in
lemma SmoothMultiplier.projected_kinetic_nonneg {v : ι → E}
    (P : E →L[ℝ] Space) (j : Fin 3 → ι)
    (hP : ∀ a, P (v (j a)) = EuclideanSpace.single a 1) (p : SmoothMultiplier v)
    (hp : ∀ x, (∑ a : Fin 3, (lineDeriv ℝ p.value x (v (j a))) ^ 2) ≤
      p.value x ^ 2 / (4 * ‖P x‖ ^ 2)) (F : weakGraph v) :
    0 ≤ ∑ a : Fin 3, (⟪(p.apply (p.apply F)).val (some (j a)), F.val (some (j a))⟫_ℂ).re := by
  have hh := (p.restrict j).weighted_kinetic_nonneg P (v ∘ j) hP hp
    (restrictWeakGraph v j F)
  rw [p.restrict_apply, p.restrict_apply] at hh
  exact hh

end Restriction

lemma lineDeriv_binding_coordinate {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (i j : Fin N) (a : Fin 3) (x : Configuration N) :
    lineDeriv ℝ (fun y : Configuration N => bindingRoot R ε (y i)) x (direction j a) =
      if j = i then fderiv ℝ (bindingRoot R ε) (x i) (EuclideanSpace.single a 1) else 0 := by
  classical
  have h := ((bindingRoot_smooth hR hε).differentiable (by simp) (x i)).hasFDerivAt.comp
    x (electronProjection i).hasFDerivAt
  change HasFDerivAt (fun y : Configuration N => bindingRoot R ε (y i)) _ x at h
  rw [h.differentiableAt.lineDeriv_eq_fderiv, h.fderiv]
  change fderiv ℝ (bindingRoot R ε) (x i) (direction j a i) = _
  by_cases hij : j = i
  · subst j
    simp [direction]
  · simp [direction, hij, Ne.symm hij]

def bindingMultiplier {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (i : Fin N) :
    SmoothMultiplier (sectorDirections N) where
  value := fun x => bindingRoot R ε (x i)
  regular := (bindingRoot_smooth hR hε).comp (electronProjection i).contDiff
  bound := ⟨Real.sqrt R, fun x => bindingRoot_bound hR hε (x i)⟩
  gradient_bound := fun j => ⟨Real.sqrt R / (2*ε), fun x => by
    rw [lineDeriv_binding_coordinate hR hε i j.1 j.2 x]
    split_ifs
    · exact bindingRoot_gradient_bound hR hε j.2 (x i)
    · simp only [abs_zero]; positivity⟩

lemma bindingMultiplier_kinetic_nonneg {N : ℕ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (i : Fin N) (F : weakGraph (sectorDirections N)) :
    0 ≤ ∑ a : Fin 3, (⟪((bindingMultiplier hR hε i).apply
      ((bindingMultiplier hR hε i).apply F)).val (some (i,a)), F.val (some (i,a))⟫_ℂ).re := by
  apply (bindingMultiplier hR hε i).projected_kinetic_nonneg (electronProjection i)
    (fun a => (i,a))
  · intro a
    simp [sectorDirections, direction, electronProjection]
  · intro x
    simpa [bindingMultiplier, sectorDirections, lineDeriv_binding_coordinate hR hε,
      electronProjection] using bindingRoot_hardy_control hR hε (x i)

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end

end OAI
