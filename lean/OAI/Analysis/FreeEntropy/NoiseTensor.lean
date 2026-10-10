import OAI.Analysis.FreeEntropy.TensorLaw

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G]

def noiseWord : List N → Word B N G
  | [] => empty
  | i :: w => leftN i (noiseWord w)

@[simp] theorem noiseWord_nil : noiseWord ([] : List N) = (empty : Word B N G) := rfl
@[simp] theorem noiseWord_cons (i : N) (w : List N) :
    noiseWord (i :: w) = (leftN i (noiseWord w) : Word B N G) := rfl

 theorem noiseWord_formula (w : List N) :
    noiseWord (B := B) (G := G) w = (([],1), w.map (fun i => (i,([],1)))) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [noiseWord, ih, leftN, push]

 theorem noiseWord_injective : Function.Injective (noiseWord (B := B) (N := N) (G := G)) := by
  intro v w h
  have h' := congrArg (fun a : Word B N G => a.2.map Prod.fst) h
  simpa [noiseWord_formula, List.map_map, Function.comp_def] using h'

 theorem noiseWord_append (v w : List N) :
    noiseWord (B := B) (G := G) (v ++ w) =
      (([],1), (noiseWord (B := B) (G := G) v).2 ++ (noiseWord (B := B) (G := G) w).2) := by
  simp [noiseWord_formula]

@[simp] theorem rightN_noiseWord (i : N) (w : List N) :
    rightN i (noiseWord (B := B) (G := G) w) = noiseWord (w ++ [i]) := by
  simp [rightN_eq_append, append, noiseWord_formula]

variable [DecidableEq B] [DecidableEq N] [DecidableEq G]

def noiseSlice : Fock.Space N →L[ℂ] Space B N G :=
  (LabelHilbert.embedding noiseWord noiseWord_injective).toContinuousLinearMap

@[simp] theorem noiseSlice_single (w : List N) (z : ℂ) :
    noiseSlice (B := B) (G := G) (lp.single 2 w z) = lp.single 2 (noiseWord w) z :=
  LabelHilbert.embedding_single noiseWord noiseWord_injective w z

@[simp] theorem noiseSlice_basis (w : List N) :
    noiseSlice (B := B) (G := G) (Fock.basisVector w) = basis (noiseWord w) :=
  noiseSlice_single w 1

 theorem noiseSlice_semicircular (i : N) :
    (semicircularN i).comp (noiseSlice (B := B) (G := G)) =
      noiseSlice.comp (Fock.semicircular i) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change semicircularN i (noiseSlice (lp.single 2 w z)) =
    noiseSlice (Fock.semicircular i (lp.single 2 w z))
  rw [noiseSlice_single]
  cases w with
  | nil => simp [semicircularN, annihilationN_single, removeN, empty]
  | cons j w =>
    simp only [noiseWord_cons, semicircularN, add_apply, creationN_single,
      annihilationN_single, Fock.semicircular_single_cons, map_add, noiseSlice_single]
    by_cases hij : i = j <;> simp [removeN, leftN, push, hij]

 theorem noiseSlice_word (w : List N) :
    ((w.map (semicircularN (B := B) (G := G))).prod).comp noiseSlice =
      noiseSlice.comp ((w.map Fock.semicircular).prod) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    apply ContinuousLinearMap.ext
    intro x
    have hi := congrArg (fun T : Fock.Space N →L[ℂ] Space B N G => T x) ih
    have hc := congrArg (fun T : Fock.Space N →L[ℂ] Space B N G =>
      T ((w.map Fock.semicircular).prod x)) (noiseSlice_semicircular (B := B) (G := G) i)
    simp only [ContinuousLinearMap.comp_apply] at hi hc
    simpa only [ContinuousLinearMap.comp_apply, List.map_cons, List.prod_cons,
      mul_apply_eq_comp, hi] using hc

 theorem noiseSlice_vacuum_coefficient (x : Fock.Space N) :
    inner ℂ (basis (empty : Word B N G)) (noiseSlice x) =
      inner ℂ (Fock.basisVector []) x := by
  have h := (LabelHilbert.embedding (noiseWord (B := B) (G := G)) noiseWord_injective).inner_map_map
    (Fock.basisVector []) x
  change inner ℂ (noiseSlice (Fock.basisVector [])) (noiseSlice x) = _ at h
  simpa using h

 theorem noise_word_moment (w : List N) :
    trace (tracialVector B N G) ((w.map semicircularN).prod) =
      trace (Fock.tracialVector N) ((w.map Fock.semicircular).prod) := by
  change inner ℂ (basis (empty : Word B N G)) ((w.map semicircularN).prod (basis empty)) = _
  rw [← noiseWord_nil, ← noiseSlice_basis, ← ContinuousLinearMap.comp_apply,
    noiseSlice_word, ContinuousLinearMap.comp_apply, noiseSlice_basis, noiseWord_nil,
    noiseSlice_vacuum_coefficient]
  rfl

 theorem trace_semicircularN_pow {k : ℕ} (i : Fin k) (r : ℕ) :
    trace (tracialVector B (Fin k) G) (semicircularN i ^ r) =
      if Even r then (catalan (r / 2) : ℂ) else 0 := by
  have h := noise_word_moment (B := B) (G := G) (List.replicate r i)
  simpa [Fock.semicircular_moments] using h

 theorem noise_basis_orthonormal : Orthonormal ℂ (fun w : List N =>
    basis (noiseWord (B := B) (G := G) w)) := by
  rw [orthonormal_iff_ite]
  intro v w
  by_cases h : v = w
  · subst w
    simp [basis, ]
  · have h' : noiseWord (B := B) (G := G) v ≠ noiseWord w :=
      fun hh => h (noiseWord_injective hh)
    simp [basis, lp.inner_single_left, lp.single_apply, h, h']

end FreeTensor
end FiniteEntropySeparation

end

end OAI
