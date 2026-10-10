import OAI.Analysis.FreeEntropy.Signal

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace LabelHilbert
variable {α β : Type} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] in
 theorem orthogonal_embedding (f : α → β) (hf : Function.Injective f) :
    OrthogonalFamily ℂ (fun _ : α => ℂ) (fun a => coordinateIsometry (f a)) := by
  intro a b hab x y
  change inner ℂ (lp.single (E := fun _ : β => ℂ) 2 (f a) x)
    (lp.single (E := fun _ : β => ℂ) 2 (f b) y) = 0
  rw [lp.inner_single_left, lp.single_apply_ne (E := fun _ : β => ℂ) 2 (f b) y
    (fun h => hab (hf h))]
  simp

 def embedding (f : α → β) (hf : Function.Injective f) : Space α →ₗᵢ[ℂ] Space β :=
  (orthogonal_embedding f hf).linearIsometry

@[simp] theorem embedding_single (f : α → β) (hf : Function.Injective f) (a : α) (z : ℂ) :
    embedding f hf (lp.single 2 a z) = lp.single 2 (f a) z :=
  (orthogonal_embedding f hf).linearIsometry_apply_single z

end LabelHilbert
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

def signalSlice (g : G) : Fock.Space B →L[ℂ] Space B N G :=
  (LabelHilbert.embedding (fun w : List B => ((w,g), ([] : List (N × Atom B G))))
    (by intro v w h; exact congrArg (fun a => a.1.1) h)).toContinuousLinearMap

omit [Group G] in
@[simp] theorem signalSlice_single (g : G) (v : List B) (z : ℂ) :
    signalSlice (N := N) g (lp.single 2 v z) = lp.single 2 ((v,g),[]) z := by
  exact LabelHilbert.embedding_single
    (fun w : List B => ((w,g), ([] : List (N × Atom B G))))
    (by intro v w h; exact congrArg (fun a => a.1.1) h) v z

omit [Group G] in
@[simp] theorem signalSlice_basis [Group G] (g : G) (v : List B) :
    signalSlice (N := N) g (Fock.basisVector v) = basis ((v,g),[]) :=
  signalSlice_single g v 1

omit [Group G] in
theorem signalSlice_semicircular [Group G] (g : G) (b : B) :
    (semicircularB b).comp (signalSlice (N := N) g) =
      (signalSlice g).comp (Fock.semicircular b) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change semicircularB b (signalSlice g (lp.single 2 w z)) =
    signalSlice g (Fock.semicircular b (lp.single 2 w z))
  rw [signalSlice_single]
  cases w with
  | nil => simp [semicircularB, creationB_single, annihilationB_single, removeB, leftB]
  | cons c w =>
    simp only [semicircularB, add_apply, creationB_single, annihilationB_single, removeB,
      Fock.semicircular_single_cons, map_add, signalSlice_single, leftB]
    by_cases h : b = c <;> simp [h]

 theorem signalSlice_word (g : G) (w : List B) :
    ((w.map (semicircularB (N := N) (G := G))).prod).comp (signalSlice g) =
      (signalSlice g).comp ((w.map Fock.semicircular).prod) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    apply ContinuousLinearMap.ext
    intro x
    have hi := congrArg (fun T : Fock.Space B →L[ℂ] Space B N G => T x) ih
    have hc := congrArg (fun T : Fock.Space B →L[ℂ] Space B N G =>
      T ((w.map Fock.semicircular).prod x)) (signalSlice_semicircular (N := N) g b)
    simp only [ContinuousLinearMap.comp_apply] at hi hc
    simpa only [ContinuousLinearMap.comp_apply, List.map_cons, List.prod_cons,
      mul_apply_eq_comp, hi] using hc

 theorem signalSlice_vacuum_coefficient (g : G) (x : Fock.Space B) :
    inner ℂ (basis (empty : Word B N G)) (signalSlice g x) =
      if g = 1 then inner ℂ (Fock.basisVector []) x else 0 := by
  have h : (innerSL ℂ (basis (empty : Word B N G))).comp (signalSlice g) =
      if g = 1 then innerSL ℂ (Fock.basisVector ([] : List B)) else 0 := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro v
    apply ContinuousLinearMap.ext
    intro z
    by_cases hg : g = 1 <;> by_cases hv : v = [] <;>
      simp [hg, hv, basis, empty, Fock.basisVector, lp.inner_single_left, lp.single_apply, eq_comm]
  have hx := congrArg (fun f : Fock.Space B →L[ℂ] ℂ => f x) h
  by_cases hg : g = 1 <;> simpa [hg] using hx

theorem tensor_word_moment (w : List B) (g : G) :
    trace (tracialVector B N G) ((w.map semicircularB).prod * unitaryG g) =
      trace (Fock.tracialVector B) ((w.map Fock.semicircular).prod) *
        (if g = 1 then 1 else 0) := by
  change inner ℂ (basis (empty : Word B N G))
    (((w.map (semicircularB (N := N) (G := G))).prod * unitaryG (B := B) (N := N) g) (basis empty)) = _
  rw [mul_apply_eq_comp, unitaryG_basis]
  have hv : basis (leftG g (empty : Word B N G)) = signalSlice g (Fock.basisVector []) := by
    simp [leftG, empty]
  rw [hv, ← ContinuousLinearMap.comp_apply, signalSlice_word,
    ContinuousLinearMap.comp_apply, signalSlice_vacuum_coefficient]
  by_cases hg : g = 1 <;> simp [hg, trace, Fock.tracialVector]

 theorem trace_semicircularB_pow {p : ℕ} (b : Fin p) (k : ℕ) :
    trace (tracialVector (Fin p) N G) (semicircularB b ^ k) =
      if Even k then (catalan (k / 2) : ℂ) else 0 := by
  have h := tensor_word_moment (N := N) (List.replicate k b) (1 : G)
  simpa [Fock.semicircular_moments] using h

 theorem unitaryG_commutes_creationB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (creationB b) := by
  apply LabelHilbert.lift_commute
  intro w
  rfl

 theorem unitaryG_commutes_semicircularB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (semicircularB b) := by
  apply (unitaryG_commutes_creationB g b).add_right
  simpa using (unitaryG_commutes_creationB (N := N) g⁻¹ b).star_star

end FreeTensor
end FiniteEntropySeparation

end

end OAI
