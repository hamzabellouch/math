import OAI.Analysis.CircleDomains.Probability.RecursiveCodeLaw
import OAI.Analysis.CircleDomains.Selection.DustBoundDiffuseIntersections

namespace OAI

/-! Every earlier law retained in a later stage has only countably many
dust contacts with it. All visit hypotheses are supplied by the candidates. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem RecursiveCodeLaw.countable_contacts
    {base : PathCodeData Sphere Sphere} {π : Sphere → Sphere}
    {flags : Set Sphere} {ω : TupleType → ℝ≥0∞} [SFinite (tupleReference ω)]
    (L M : RecursiveCodeLaw base π flags ω)
    (hB : IsClosed base.dust) (hflags : flags.Countable)
    (hH : ∀ i, IsClosed (base.levels i))
    (hweights : ∀ i, (∑' x, base.levelWeights i x ^ 2) < ∞)
    (hmarked : ∀ i, support (base.levelWeights i) ⊆ flags)
    (hcompat : OrderedLevelNullCompatibility base.levels (base.dust \ flags))
    (hunique : ∀ x ∈ base.dust \ flags, ∀ j a b,
      (a, x) ∈ base.levels j → (b, x) ∈ base.levels j → a = b)
    (i : ℕ) (hprior : M.data.priorLaws i = (codePathLaw L.data L.law : Measure C(PathTime, Sphere))) :
    ∃ D : Set Sphere, D.Countable ∧
      ∀ᵐ z ∂((L.law : Measure (BasePathCode L.data)).prod
        (M.law : Measure (BasePathCode M.data))),
        range z.1.val.1 ∩ range z.2.val.1 ∩ L.data.dust ⊆ D := by
  have hde : M.data.dust = L.data.dust := M.dust_eq.trans L.dust_eq.symm
  have heq : support (dustPriorHitMass M.data.dust (M.data.priorLaws i)) =
      {x | x ∈ L.data.dust ∧ 0 < codeHitProbability L.data L.law x} := by
    rw [hde, hprior, support_dustPriorHitMass]
    ext x
    simp only [mem_inter_iff, mem_support, priorHitMass_codePathLaw, mem_ofPred_eq,
      pos_iff_ne_zero]
  have hm : (support (dustPriorHitMass M.data.dust (M.data.priorLaws i))).Countable :=
    heq.symm ▸ L.countable_dust_hits
  have hw : countingSquareNorm (fun x : support
      (dustPriorHitMass M.data.dust (M.data.priorLaws i)) =>
        dustPriorHitMass M.data.dust (M.data.priorLaws i) x.val) < ∞ := by
    rw [M.dust_eq, hprior]
    exact dust_prior_weight_norm_finite L.data L.law base.dust L.hit_square_finite
  have hv : countingSquareNorm (fun x : support
      (dustPriorHitMass M.data.dust (M.data.priorLaws i)) =>
        meanVisitCount (codePathLaw M.data M.law) x.val) < ∞ := by
    rw [M.dust_eq]
    exact M.prior_visit_norm_finite i
  have hc : ∀ x ∈ support (dustPriorHitMass M.data.dust (M.data.priorLaws i)),
      ∀ᶠ n in atTop, x ∈ M.data.priorDeletions i n := by
    intro x hx
    rw [support_dustPriorHitMass] at hx
    simpa only [M.prior_deletions_eq] using M.presentation.prior_cover i x hx.2
  have hs : ∀ n, (M.data.priorDeletions i n : Set Sphere) ⊆
      support (priorHitMass (M.data.priorLaws i)) := by
    intro n
    simpa only [M.prior_deletions_eq] using M.presentation.prior_subset i n
  have hf : ∀ n, (L.data.flagDeletions n : Set Sphere) ⊆ flags := by
    intro n
    simpa only [L.flag_deletions_eq] using L.presentation.flag_subset n
  have hlcount (j : ℕ) : (support (L.data.levelWeights j)).Countable := by
    rw [L.weights_eq]
    exact hflags.mono (hmarked j)
  have hlweight (j : ℕ) : countingSquareNorm (fun x : support (L.data.levelWeights j) =>
      L.data.levelWeights j x.val) < ∞ := by
    rw [L.weights_eq]
    apply (countingSquareNorm_comp_injective (base.levelWeights j)
      (fun x : support (base.levelWeights j) => x.val) Subtype.val_injective).trans_lt
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (hweights j).ne
  have hlvisit (j : ℕ) : countingSquareNorm (fun x : support (L.data.levelWeights j) =>
      meanVisitCount (codePathLaw L.data L.law) x.val) < ∞ := by
    rw [L.weights_eq]
    exact L.flag_visit_norm_finite j (hmarked j)
  have hlcover : ∀ j x, x ∈ support (L.data.levelWeights j) →
      ∀ᶠ n in atTop, x ∈ L.data.flagDeletions n := by
    intro j x hx
    rw [L.weights_eq] at hx
    simpa only [L.flag_deletions_eq] using L.presentation.flag_cover x (hmarked j hx)
  have hraw := ae_diffuse_dust_intersections_of_dust_bounds L.data M.data
    (by simpa only [L.dust_eq] using hB) hde
    (by simpa only [L.levels_eq] using hH) (M.levels_eq.trans L.levels_eq.symm)
    L.law M.law i hprior hm hw hv hc hs flags hf hlcount hlweight hlvisit hlcover
    (by simpa only [L.levels_eq, L.dust_eq] using hcompat)
    (by simpa only [L.levels_eq, L.dust_eq] using hunique)
    ω L.tuple_absolutelyContinuous M.tuple_absolutelyContinuous
  refine ⟨flags ∪ support (dustPriorHitMass M.data.dust (M.data.priorLaws i)),
    hflags.union hm, ?_⟩
  filter_upwards [hraw] with z hz
  intro x hx
  rcases hz hx with hxf | hxp
  · exact Or.inl hxf
  · right
    rw [support_dustPriorHitMass]
    exact ⟨hde.symm ▸ hx.2, hxp⟩

end CircleDomainRigidity

end

end OAI
