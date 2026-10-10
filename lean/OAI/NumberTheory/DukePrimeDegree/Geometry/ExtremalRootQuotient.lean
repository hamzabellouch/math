import OAI.NumberTheory.DukePrimeDegree.Geometry.RootInductionStep
import OAI.NumberTheory.DukePrimeDegree.Geometry.PositiveRootCoordinates

namespace OAI

/-!
# The real quotient by the remaining roots

The extremal matrix entry is additive on its positive-root group.
Its kernel is precisely the remaining root group. Thus the subgroup
removed in the product induction is normal, as required by EK2003,
Proposition 8.3.
-/

noncomputable section
open Matrix Filter Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem neutral_root_entry_mul
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin (d + 1), (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2)
    {g h : G (d + 1)} (hg : PositiveRootPattern S g) (hh : PositiveRootPattern S h) :
    (g * h).val a b = g.val a b + h.val a b := by
  have hlim := (positiveRootPattern_isolated_limit d S hpos hab ell hell hneut hdecay g hg).mul
    (positiveRootPattern_isolated_limit d S hpos hab ell hell hneut hdecay h hh)
  have hfun (t : ℝ) :
      (diagonalOneParameter ell hell t * g * diagonalOneParameter ell hell (-t)) *
        (diagonalOneParameter ell hell t * h * diagonalOneParameter ell hell (-t)) =
      diagonalOneParameter ell hell t * (g * h) * diagonalOneParameter ell hell (-t) := by
    rw [diagonalOneParameter_neg]
    group
  simp_rw [hfun] at hlim
  have heq := tendsto_nhds_unique
    (positiveRootPattern_isolated_limit d S hpos hab ell hell hneut hdecay (g * h)
      (positiveRootPattern_mul S hcomp hg hh)) hlim
  rw [← Matrix.SpecialLinearGroup.transvection_add] at heq
  have he := congrArg (fun u : G (d + 1) => u.val a b) heq
  simpa [Matrix.SpecialLinearGroup.transvection_coe, hab] using he

def neutralRootEntryHom
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin (d + 1), (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2) :
    positiveRootGeneratedGroup S →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (g.val.val a b)
  map_one' := by
    change (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) a b = 0
    simp [hab]
  map_mul' g h := by
    change (g.val * h.val).val a b = g.val.val a b + h.val.val a b
    exact neutral_root_entry_mul d S hpos hcomp hab ell hell hneut hdecay
      (positiveRootGeneratedGroup_pattern S hcomp g.prop)
      (positiveRootGeneratedGroup_pattern S hcomp h.prop)

theorem neutralRootEntryHom_ker
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin (d + 1), (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2) :
    (neutralRootEntryHom d S hpos hcomp hab ell hell hneut hdecay).ker =
      (positiveRootGeneratedGroup (S.erase (a, b))).comap (positiveRootGeneratedGroup S).subtype := by
  ext g
  change g.val.val a b = 0 ↔ g.val ∈ positiveRootGeneratedGroup (S.erase (a, b))
  have herase := erase_neutral_root_closed S hcomp (a, b) ell hneut hdecay
  rw [positiveRootGeneratedGroup_iff (S.erase (a, b))
    (fun p hp => hpos p (Finset.mem_of_mem_erase hp)) herase]
  constructor
  · intro hz r s hrs
    by_cases h : (r, s) = (a, b)
    · obtain ⟨hr, hs⟩ := Prod.mk.inj h
      subst r
      subst s
      simpa only [Matrix.one_apply, hab, ite_false] using hz
    · exact positiveRootGeneratedGroup_pattern S hcomp g.prop r s
        (fun hS => hrs (Finset.mem_erase.mpr ⟨h, hS⟩))
  · intro hg
    simpa only [Matrix.one_apply, hab, ite_false] using hg a b (by simp)

theorem remaining_roots_normal
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin (d + 1), (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin (d + 1)} (hab : a ≠ b)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2) :
    ((positiveRootGeneratedGroup (S.erase (a, b))).comap
      (positiveRootGeneratedGroup S).subtype).Normal := by
  rw [← neutralRootEntryHom_ker d S hpos hcomp hab ell hell hneut hdecay]
  infer_instance

end DukePrimeDegree

end

end OAI
