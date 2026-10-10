import OAI.NumberTheory.TwoPoint.Bounds.PatternHarmonicSum

namespace OAI

/-! Resample one prime per observed equality class, retaining arbitrary nonnegative events. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

variable {τ P : Type*} [Fintype τ] [DecidableEq P]

def patternClasses (template : τ → P) : Finset P := univ.image template

def patternCoordinate (template : τ → P) (t : τ) : patternClasses template :=
  ⟨template t, mem_image.mpr ⟨t, mem_univ _, rfl⟩⟩

noncomputable def patternRepresentative (template : τ → P) (c : patternClasses template) : τ :=
  Classical.choose (mem_image.mp c.property)

lemma patternRepresentative_value (template : τ → P) (c : patternClasses template) :
    template (patternRepresentative template c) = c.val :=
  (Classical.choose_spec (mem_image.mp c.property)).2

noncomputable def patternEncode (template w : τ → P) (c : patternClasses template) : P :=
  w (patternRepresentative template c)

def patternResample (template : τ → P) (a : patternClasses template → P) (t : τ) : P :=
  a (patternCoordinate template t)

lemma patternResample_encode (template w : τ → P)
    (hpattern : ∀ i j, w i = w j ↔ template i = template j) :
    patternResample template (patternEncode template w) = w := by
  funext t
  exact (hpattern _ _).mpr (patternRepresentative_value template (patternCoordinate template t))

lemma patternEncode_injOn (template : τ → P) (F : Finset (τ → P))
    (hpattern : ∀ w ∈ F, ∀ i j, w i = w j ↔ template i = template j) :
    Set.InjOn (patternEncode template) F := by
  intro w hw v hv he
  calc
    w = patternResample template (patternEncode template w) :=
      (patternResample_encode template w (hpattern w hw)).symm
    _ = patternResample template (patternEncode template v) := congrArg _ he
    _ = v := patternResample_encode template v (hpattern v hv)

lemma patternEncode_weight (template w : τ → P) (a : P → ℝ)
    (hpattern : ∀ i j, w i = w j ↔ template i = template j) :
    (∏ p ∈ univ.image w, a p) = ∏ c : patternClasses template, a (patternEncode template w c) := by
  have hc (t : τ) : w t = patternEncode template w (patternCoordinate template t) := by
    exact (congrFun (patternResample_encode template w hpattern) t).symm
  have he : univ.image (patternEncode template w) = univ.image w := by
    ext p
    constructor
    · rintro hp
      obtain ⟨c, _, rfl⟩ := mem_image.mp hp
      exact mem_image.mpr ⟨patternRepresentative template c, mem_univ _, rfl⟩
    · rintro hp
      obtain ⟨t, _, rfl⟩ := mem_image.mp hp
      exact mem_image.mpr ⟨patternCoordinate template t, mem_univ _, (hc t).symm⟩
  rw [← he, prod_image]
  intro c _ d _ hcd
  apply Subtype.ext
  exact (patternRepresentative_value template c).symm.trans
    (((hpattern _ _).mp hcd).trans (patternRepresentative_value template d))

/-- Numerical restrictions and outside weights are preserved by the
resampling map. They are not discarded before the high-rank estimate. -/
theorem same_pattern_resampled_sum [Fintype P]
    (template : τ → P) (F : Finset (τ → P)) (a : P → ℝ) (ha : ∀ p, 0 ≤ a p)
    (potential : (τ → P) → ℝ) (hpotential : ∀ w, 0 ≤ potential w)
    (hpattern : ∀ w ∈ F, ∀ i j, w i = w j ↔ template i = template j) :
    (∑ w ∈ F, (∏ p ∈ univ.image w, a p) * potential w) ≤
      ∑ x : patternClasses template → P,
        (∏ c, a (x c)) * potential (patternResample template x) := by
  calc
    _ = ∑ x ∈ F.image (patternEncode template),
        (∏ c, a (x c)) * potential (patternResample template x) := by
      rw [sum_image (patternEncode_injOn template F hpattern)]
      apply sum_congr rfl
      intro w hw
      rw [patternResample_encode template w (hpattern w hw),
        patternEncode_weight template w a (hpattern w hw)]
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro x _ _
      exact mul_nonneg (prod_nonneg (fun c _ => ha (x c))) (hpotential _)

end TwoPointCorrelations

end OAI
