import OAI.Analysis.CircleDomains.Selection.PuncturedHitProduct
import OAI.Analysis.CircleDomains.Selection.CountableMeetingBound

namespace OAI

/-! The quantitative dust meeting estimate for the actual two code laws. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
theorem code_dust_meeting_bound
    (d e : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d))
    (Q : ProbabilityMeasure (BasePathCode e)) (U D : Set X) (hD : D.Countable)
    (hcontacts : ∀ᵐ z ∂((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e))),
      range z.1.val.1 ∩ range z.2.val.1 ∩ d.dust ⊆ D)
    (p q : X) (hp : p ∈ D ∩ (U ∩ d.dust)) (hq : q ∈ D ∩ (U ∩ d.dust)) (hpq : p ≠ q)
    {δ : ℝ≥0∞}
    (hatail : countingSquareNorm (fun x : ↥(D ∩ (U ∩ d.dust)) =>
      if x.val ≠ p then codeHitProbability d P x.val else 0) ≤ δ)
    (hbtail : countingSquareNorm (fun x : ↥(D ∩ (U ∩ d.dust)) =>
      if x.val ≠ q then codeHitProbability e Q x.val else 0) ≤ δ) :
    ((P : Measure (BasePathCode d)).prod (Q : Measure (BasePathCode e)))
      {z | (range z.1.val.1 ∩ range z.2.val.1 ∩ (U ∩ d.dust)).Nonempty} ≤
        2 * δ + δ ^ 2 := by
  have hcount : (D ∩ (U ∩ d.dust)).Countable := hD.mono inter_subset_left
  let : Countable ↥(D ∩ (U ∩ d.dust)) := hcount.to_subtype
  apply (code_pair_meeting_bound d e P Q (U ∩ d.dust) D hD ?_).trans
  · let p' : ↥(D ∩ (U ∩ d.dust)) := ⟨p, hp⟩
    let q' : ↥(D ∩ (U ∩ d.dust)) := ⟨q, hq⟩
    have ha : codeHitProbability d P p ≤ 1 := prob_le_one
    have hb : codeHitProbability e Q q ≤ 1 := prob_le_one
    have hpa : countingSquareNorm (puncturedHit
        (fun x : ↥(D ∩ (U ∩ d.dust)) => codeHitProbability d P x.val) univ p') ≤ δ := by
      convert hatail using 1
      congr 1
      funext x
      simp [puncturedHit, p', Subtype.ext_iff]
    have hqb : countingSquareNorm (puncturedHit
        (fun x : ↥(D ∩ (U ∩ d.dust)) => codeHitProbability e Q x.val) univ q') ≤ δ := by
      convert hbtail using 1
      congr 1
      funext x
      simp [puncturedHit, q', Subtype.ext_iff]
    have h := punctured_hit_product_sum_le
      (fun x : ↥(D ∩ (U ∩ d.dust)) => codeHitProbability d P x.val)
      (fun x : ↥(D ∩ (U ∩ d.dust)) => codeHitProbability e Q x.val)
      univ p' q' (mem_univ _) (mem_univ _)
      (fun h => hpq (congrArg Subtype.val h)) ha hb
      hpa hqb
    simpa only [mem_univ, ite_true] using h
  · filter_upwards [hcontacts] with z hz
    rintro x ⟨hx, hxU, hxB⟩
    exact hz ⟨hx, hxB⟩

end CircleDomainRigidity

end

end OAI
