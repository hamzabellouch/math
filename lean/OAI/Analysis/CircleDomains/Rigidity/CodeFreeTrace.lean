import OAI.Analysis.CircleDomains.Selection.CodeResidualAvoidance
import OAI.Analysis.CircleDomains.Rigidity.TaggedNullTrace

namespace OAI

/-! The residual constraints stored in a base code combine with the
open-tag trace theorem to exclude free incidences along the entire path.
-/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem ae_code_free_level_incidence_null
    (d : PathCodeData X Y) (P : ProbabilityMeasure (BasePathCode d)) (i : ℕ)
    (Free : Set X) (hFree : Free ⊆ d.dust) (w : X → UnitAddCircle)
    (htrace : ∀ x ∈ Free, ∀ t, (t, x) ∈ d.levels i ↔ w x = t)
    (hm : (support (d.levelWeights i)).Countable)
    (hweight : countingSquareNorm (fun x : support (d.levelWeights i) =>
      d.levelWeights i x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support (d.levelWeights i) =>
      meanVisitCount (codePathLaw d P) x.val) < ∞)
    (hcover : ∀ x ∈ support (d.levelWeights i), ∀ᶠ n in atTop, x ∈ d.flagDeletions n)
    (hdelete : ∀ n, Disjoint Free (d.flagDeletions n : Set X))
    (htags : ∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ∀ k,
      volume (w '' (Γ.val.1 '' Ioo (tagLeft (Γ.val.2 k)) (tagRight (Γ.val.2 k)) ∩ Free)) = 0) :
    ∀ᵐ Γ ∂(P : Measure (BasePathCode d)),
      volume {t | ∃ x ∈ range Γ.val.1 ∩ Free, (t, x) ∈ d.levels i} = 0 := by
  filter_upwards [ae_code_level_envelope_null d P i hm hweight hvisits hcover, htags]
    with Γ hres htag
  have hresidual : volume (w '' (Γ.val.1 '' residualTimes d.dust Γ.val ∩ Free)) = 0 := by
    apply measure_mono_null (t := ⋂ n, {t | (Γ.val, t) ∈
      residualIncidence d.dust univ (d.levels i) (d.flagDeletions n)}) _ hres
    rintro _ ⟨x, ⟨⟨s, hs, rfl⟩, hx⟩, rfl⟩
    exact mem_iInter.mpr fun n => ⟨s, hs, mem_univ _,
      (htrace _ hx _).mpr rfl, fun hp => disjoint_left.mp (hdelete n) hx hp⟩
  exact free_level_incidence_null_of_trace volume Γ.val.1 Free w (d.levels i)
    (fun x hx t ht => (htrace x hx t).mp ht)
    (tagged_free_trace_null d.dust Free hFree Γ.val w hresidual htag)

end CircleDomainRigidity

end

end OAI
