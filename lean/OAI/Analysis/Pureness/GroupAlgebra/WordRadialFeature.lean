import OAI.Analysis.Pureness.GroupAlgebra.FreeWordTreeDistance
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped InnerProductSpace
local instance wordRadialFeatureDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
variable {X V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def wordBranchFeature (e : List X → V) (r q : ℝ) : List X → V
  | [] => 0
  | a :: u => ((q * r ^ u.length : ℝ) : ℂ) • e [a] +
      wordBranchFeature (fun t => e (a :: t)) r q u

def wordRadialFeature (e : List X → V) (r q : ℝ) (u : List X) : V :=
  ((r ^ u.length : ℝ) : ℂ) • e [] + wordBranchFeature e r q u

lemma inner_wordBranchFeature_zero (e : List X → V) (r q : ℝ) (z : V)
    (h : ∀ t, ⟪z, e t⟫_ℂ = 0) (u : List X) :
    ⟪z, wordBranchFeature e r q u⟫_ℂ = 0 := by
  induction u generalizing e with
  | nil => simp [wordBranchFeature]
  | cons a u ih => simp [wordBranchFeature, inner_add_right, inner_smul_right, h,
      ih (fun t => e (a :: t)) (fun t => h (a :: t))]

lemma wordBranchFeature_inner_zero (e : List X → V) (r q : ℝ) (z : V)
    (h : ∀ t, ⟪e t, z⟫_ℂ = 0) (u : List X) :
    ⟪wordBranchFeature e r q u, z⟫_ℂ = 0 := by
  rw [← inner_conj_symm]
  have h' (t : List X) : ⟪z, e t⟫_ℂ = 0 := by rw [← inner_conj_symm, h]; simp
  rw [inner_wordBranchFeature_zero e r q z h']; simp

lemma wordBranchFeature_cross_zero (e f : List X → V) (r q : ℝ)
    (h : ∀ t s, ⟪e t, f s⟫_ℂ = 0) (u v : List X) :
    ⟪wordBranchFeature e r q u, wordBranchFeature f r q v⟫_ℂ = 0 := by
  induction u generalizing e with
  | nil => simp [wordBranchFeature]
  | cons a u ih =>
    simp [wordBranchFeature, inner_add_left, inner_smul_left,
      inner_wordBranchFeature_zero f r q (e [a]) (h [a]),
      ih (fun t => e (a :: t)) (fun t s => h (a :: t) s)]

lemma wordBranchFeature_root_inner (e : List X → V) (he : Orthonormal ℂ e)
    (r q : ℝ) (u : List X) : ⟪e [], wordBranchFeature e r q u⟫_ℂ = 0 := by
  cases u with
  | nil => simp [wordBranchFeature]
  | cons a u =>
    have hz (t : List X) : ⟪e [], e (a :: t)⟫_ℂ = 0 :=
      he.inner_eq_zero (by simp)
    simp [wordBranchFeature, inner_add_right, inner_smul_right, hz,
      inner_wordBranchFeature_zero (fun t => e (a :: t)) r q (e []) hz]

lemma wordBranchFeature_inner_root (e : List X → V) (he : Orthonormal ℂ e)
    (r q : ℝ) (u : List X) : ⟪wordBranchFeature e r q u, e []⟫_ℂ = 0 := by
  rw [← inner_conj_symm, wordBranchFeature_root_inner e he]; simp

lemma wordBranchFeature_inner_cons_same (e : List X → V) (he : Orthonormal ℂ e)
    (r q : ℝ) (a : X) (u v : List X) :
    ⟪wordBranchFeature e r q (a :: u), wordBranchFeature e r q (a :: v)⟫_ℂ =
      ((q ^ 2 * r ^ (u.length + v.length) : ℝ) : ℂ) +
        ⟪wordBranchFeature (fun t => e (a :: t)) r q u,
          wordBranchFeature (fun t => e (a :: t)) r q v⟫_ℂ := by
  have he' : Orthonormal ℂ (fun t => e (a :: t)) :=
    he.comp (List.cons a) List.cons_injective
  have h1 := wordBranchFeature_root_inner (fun t => e (a :: t)) he' r q v
  have h2 := wordBranchFeature_inner_root (fun t => e (a :: t)) he' r q u
  simp only [wordBranchFeature, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, h1, h2, mul_zero, add_zero, zero_add,
    inner_self_eq_norm_sq_to_K, he.norm_eq_one, Complex.conj_ofReal]
  push_cast
  rw [pow_add]
  ring

lemma wordBranchFeature_inner_cons_ne (e : List X → V) (he : Orthonormal ℂ e)
    (r q : ℝ) (a b : X) (hab : a ≠ b) (u v : List X) :
    ⟪wordBranchFeature e r q (a :: u), wordBranchFeature e r q (b :: v)⟫_ℂ = 0 := by
  have hz (t s : List X) : ⟪e (a :: t), e (b :: s)⟫_ℂ = 0 :=
    he.inner_eq_zero (by simp [hab])
  simp only [wordBranchFeature, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right]
  rw [hz, inner_wordBranchFeature_zero (fun t => e (b :: t)) r q (e [a]) (hz []),
    wordBranchFeature_inner_zero (fun t => e (a :: t)) r q (e [b]) (fun t => hz t []),
    wordBranchFeature_cross_zero (fun t => e (a :: t)) (fun t => e (b :: t)) r q hz]
  simp

lemma wordRadialFeature_inner (e : List X → V) (he : Orthonormal ℂ e)
    (r q : ℝ) (u v : List X) :
    ⟪wordRadialFeature e r q u, wordRadialFeature e r q v⟫_ℂ =
      ((r ^ (u.length + v.length) : ℝ) : ℂ) +
      ⟪wordBranchFeature e r q u, wordBranchFeature e r q v⟫_ℂ := by
  simp only [wordRadialFeature, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, wordBranchFeature_root_inner e he,
    wordBranchFeature_inner_root e he, mul_zero, add_zero, zero_add,
    inner_self_eq_norm_sq_to_K, he.norm_eq_one, Complex.conj_ofReal]
  rw [pow_add, Complex.ofReal_mul]
  push_cast
  ring

theorem wordRadialFeature_inner_eq (e : List X → V) (he : Orthonormal ℂ e)
    (r q : ℝ) (hq : q ^ 2 = 1 - r ^ 2) (u v : List X) :
    ⟪wordRadialFeature e r q u, wordRadialFeature e r q v⟫_ℂ =
      ((r ^ wordTreeDistance u v : ℝ) : ℂ) := by
  induction u generalizing v e with
  | nil => simp [wordRadialFeature_inner e he, wordBranchFeature, wordTreeDistance]
  | cons a u ih =>
    cases v with
    | nil => simp [wordRadialFeature_inner e he, wordBranchFeature, wordTreeDistance]
    | cons b v =>
      rw [wordRadialFeature_inner e he]
      by_cases hab : a = b
      · subst b
        rw [wordBranchFeature_inner_cons_same e he]
        have he' : Orthonormal ℂ (fun t => e (a :: t)) :=
          he.comp (List.cons a) List.cons_injective
        have hi := ih (fun t => e (a :: t)) he' v
        rw [wordRadialFeature_inner _ he'] at hi
        simp only [wordTreeDistance, ↓reduceIte, List.length_cons]
        rw [← hi, hq]
        push_cast
        simp only [pow_add, pow_succ]
        ring
      · rw [wordBranchFeature_inner_cons_ne e he r q a b hab, add_zero]
        simp only [wordTreeDistance, ite_eq_right hab, List.length_cons]
        congr 2
        omega
end CuntzPureness

end

end OAI
