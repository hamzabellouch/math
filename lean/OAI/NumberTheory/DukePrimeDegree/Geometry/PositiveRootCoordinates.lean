import OAI.NumberTheory.DukePrimeDegree.Geometry.PositiveRootFactorization

namespace OAI

/-!
# Coordinates separating an extremal root

Multiplication identifies a positive-root group with one real root
coordinate and the group of remaining roots. Both directions are
continuous, and the first coordinate is the corresponding matrix entry.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma transvection_mul_root_entry {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (t : ℝ) (g : G n) :
    (Matrix.SpecialLinearGroup.transvection hab t * g).val a b =
      g.val a b + t * g.val b b := by
  change ((1 + Matrix.single a b t) * g.val) a b = _
  simp [Matrix.add_mul]

lemma remaining_root_entry {n : ℕ} (S : Finset (Fin n × Fin n))
    (hpos : ∀ p ∈ S, p.1 < p.2) {a b : Fin n} (hab : a ≠ b)
    (hcomp : ∀ i j k : Fin n, (i, j) ∈ S.erase (a, b) →
      (j, k) ∈ S.erase (a, b) → (i, k) ∈ S.erase (a, b))
    (w : positiveRootGeneratedGroup (S.erase (a, b))) :
    w.val.val a b = 0 ∧ w.val.val b b = 1 := by
  have hw := positiveRootGeneratedGroup_pattern (S.erase (a, b)) hcomp w.prop
  constructor
  · simpa only [Matrix.one_apply, hab, ite_false] using hw a b (by simp)
  · have hbb : (b, b) ∉ S.erase (a, b) := by
      intro h
      exact lt_irrefl b (hpos (b, b) (Finset.mem_of_mem_erase h))
    simpa using hw b b hbb

/-- The explicit root-times-remainder coordinates used in the
positive-root product induction. -/
def positiveRootFactorHomeomorph {n : ℕ} (S : Finset (Fin n × Fin n))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin n, (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin n} (hab : a ≠ b) (habS : (a, b) ∈ S)
    (herase : ∀ i j k : Fin n, (i, j) ∈ S.erase (a, b) →
      (j, k) ∈ S.erase (a, b) → (i, k) ∈ S.erase (a, b)) :
    (ℝ × positiveRootGeneratedGroup (S.erase (a, b))) ≃ₜ positiveRootGeneratedGroup S where
  toFun z := ⟨Matrix.SpecialLinearGroup.transvection hab z.1 * z.2.val,
    (positiveRootGeneratedGroup S).mul_mem
      (transvection_mem_positiveRootGeneratedGroup S hab habS z.1)
      (positiveRootGeneratedGroup_mono (Finset.erase_subset (a, b) S) z.2.prop)⟩
  invFun g := (g.val.val a b,
    ⟨Matrix.SpecialLinearGroup.transvection hab (-g.val.val a b) * g.val,
      positiveRootPattern_mem_generated (S.erase (a, b))
        (fun p hp => hpos p (Finset.mem_of_mem_erase hp)) herase
        (positiveRootPattern_eliminate S hpos hcomp hab habS g.val
          (positiveRootGeneratedGroup_pattern S hcomp g.prop))⟩)
  left_inv := by
    rintro ⟨t, w⟩
    have hw := remaining_root_entry S hpos hab herase w
    have ht : (Matrix.SpecialLinearGroup.transvection hab t * w.val).val a b = t := by
      rw [transvection_mul_root_entry, hw.1, hw.2, mul_one, zero_add]
    apply Prod.ext
    · exact ht
    · apply Subtype.ext
      change Matrix.SpecialLinearGroup.transvection hab
          (-(Matrix.SpecialLinearGroup.transvection hab t * w.val).val a b) *
        (Matrix.SpecialLinearGroup.transvection hab t * w.val) = w.val
      rw [ht, ← mul_assoc, ← Matrix.SpecialLinearGroup.transvection_add, neg_add_cancel]
      simp only [Matrix.SpecialLinearGroup.transvection_coeff_zero, one_mul]
  right_inv := by
    intro g
    apply Subtype.ext
    change Matrix.SpecialLinearGroup.transvection hab (g.val.val a b) *
      (Matrix.SpecialLinearGroup.transvection hab (-g.val.val a b) * g.val) = g.val
    rw [← mul_assoc, Matrix.SpecialLinearGroup.transvection_mul_neg, one_mul]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_rootTransvection hab).comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have hc : Continuous (fun g : positiveRootGeneratedGroup S => g.val.val a b) := by
      fun_prop
    exact hc.prodMk (Continuous.subtype_mk
      (((continuous_rootTransvection hab).comp hc.neg).mul continuous_subtype_val) _)

lemma root_entry_mul_transvection {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (t : ℝ) (g : G n) :
    (g * Matrix.SpecialLinearGroup.transvection hab t).val a b =
      g.val a b + g.val a a * t := by
  change (g.val * (1 + Matrix.single a b t)) a b = _
  simp [Matrix.mul_add]

lemma positiveRootPattern_eliminate_right {n : ℕ} (S : Finset (Fin n × Fin n))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin n, (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin n} (hab : a ≠ b) (habS : (a, b) ∈ S)
    (g : G n) (hg : PositiveRootPattern S g) :
    PositiveRootPattern (S.erase (a, b))
      (g * Matrix.SpecialLinearGroup.transvection hab (-g.val a b)) := by
  have hw := positiveRootPattern_mul S hcomp hg
    (positiveRootPattern_transvection S hab habS (-g.val a b))
  have haa : g.val a a = 1 := by
    have ha : (a, a) ∉ S := fun h => lt_irrefl a (hpos (a, a) h)
    simpa using hg a a ha
  intro r s hrs
  by_cases he : (r, s) = (a, b)
  · have hr : r = a := congrArg Prod.fst he
    have hs : s = b := congrArg Prod.snd he
    subst r
    subst s
    simp only [root_entry_mul_transvection, haa, one_mul, add_neg_cancel,
      Matrix.one_apply, hab, ite_false]
  · exact hw r s (fun hS => hrs (Finset.mem_erase.mpr ⟨he, hS⟩))

/-- With the root factor last, its coordinate lines are actual right
root orbits. These are the coordinates used for disintegration. -/
def positiveRootRightFactorHomeomorph {n : ℕ} (S : Finset (Fin n × Fin n))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin n, (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b : Fin n} (hab : a ≠ b) (habS : (a, b) ∈ S)
    (herase : ∀ i j k : Fin n, (i, j) ∈ S.erase (a, b) →
      (j, k) ∈ S.erase (a, b) → (i, k) ∈ S.erase (a, b)) :
    (positiveRootGeneratedGroup (S.erase (a, b)) × ℝ) ≃ₜ positiveRootGeneratedGroup S where
  toFun z := ⟨z.1.val * Matrix.SpecialLinearGroup.transvection hab z.2,
    (positiveRootGeneratedGroup S).mul_mem
      (positiveRootGeneratedGroup_mono (Finset.erase_subset (a, b) S) z.1.prop)
      (transvection_mem_positiveRootGeneratedGroup S hab habS z.2)⟩
  invFun g := (⟨g.val * Matrix.SpecialLinearGroup.transvection hab (-g.val.val a b),
      positiveRootPattern_mem_generated (S.erase (a, b))
        (fun p hp => hpos p (Finset.mem_of_mem_erase hp)) herase
        (positiveRootPattern_eliminate_right S hpos hcomp hab habS g.val
          (positiveRootGeneratedGroup_pattern S hcomp g.prop))⟩, g.val.val a b)
  left_inv := by
    rintro ⟨w, t⟩
    have hp := positiveRootGeneratedGroup_pattern (S.erase (a, b)) herase w.prop
    have ha : w.val.val a a = 1 := by
      apply (show w.val.val a a = (1 : Matrix (Fin n) (Fin n) ℝ) a a from
        hp a a (fun h => lt_irrefl a (hpos (a, a) (Finset.mem_of_mem_erase h)))).trans
      simp
    have hw := (remaining_root_entry S hpos hab herase w).1
    have ht : (w.val * Matrix.SpecialLinearGroup.transvection hab t).val a b = t := by
      rw [root_entry_mul_transvection, ha, hw, one_mul, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change (w.val * Matrix.SpecialLinearGroup.transvection hab t) *
        Matrix.SpecialLinearGroup.transvection hab
          (-(w.val * Matrix.SpecialLinearGroup.transvection hab t).val a b) = w.val
      rw [ht, mul_assoc, Matrix.SpecialLinearGroup.transvection_mul_neg, mul_one]
    · exact ht
  right_inv := by
    intro g
    apply Subtype.ext
    change (g.val * Matrix.SpecialLinearGroup.transvection hab (-g.val.val a b)) *
      Matrix.SpecialLinearGroup.transvection hab (g.val.val a b) = g.val
    rw [mul_assoc, ← Matrix.SpecialLinearGroup.transvection_add, neg_add_cancel]
    simp only [Matrix.SpecialLinearGroup.transvection_coeff_zero, mul_one]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_rootTransvection hab).comp continuous_snd)
  continuous_invFun := by
    have hc : Continuous (fun g : positiveRootGeneratedGroup S => g.val.val a b) := by
      fun_prop
    exact (Continuous.subtype_mk
      (continuous_subtype_val.mul ((continuous_rootTransvection hab).comp hc.neg)) _).prodMk hc

end DukePrimeDegree

end

end OAI
