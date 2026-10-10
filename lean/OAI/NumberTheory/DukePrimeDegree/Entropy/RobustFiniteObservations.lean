import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafLusin
import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientLogTopology
import Mathlib.Topology.Order.Compact

namespace OAI

/-! # Finite measurable observations away from a small exceptional set -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem continuous_quotientLogDistance_pair (n : ℕ) :
    Continuous (fun p : X n × X n => quotientLogDistance p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε/2 := by positivity
  have hx : ∀ᶠ z : X n × X n in 𝓝 p, quotientLogDistance p.1 z.1 < ε/2 := by
    exact (((continuous_quotientLogDistance n p.1).comp continuous_fst).tendsto p).eventually
      (p := fun a : ℝ => a < ε/2)
      (gt_mem_nhds (by simpa only [Function.comp_apply,quotientLogDistance_self] using hhalf))
  have hy : ∀ᶠ z : X n × X n in 𝓝 p, quotientLogDistance p.2 z.2 < ε/2 := by
    exact (((continuous_quotientLogDistance n p.2).comp continuous_snd).tendsto p).eventually
      (p := fun a : ℝ => a < ε/2)
      (gt_mem_nhds (by simpa only [Function.comp_apply,quotientLogDistance_self] using hhalf))
  filter_upwards [hx,hy] with z hx hy
  have h₁ := quotientLogDistance_triangle z.1 p.1 z.2
  have h₂ := quotientLogDistance_triangle p.1 p.2 z.2
  have h₃ := quotientLogDistance_triangle p.1 z.1 p.2
  have h₄ := quotientLogDistance_triangle z.1 z.2 p.2
  rw [quotientLogDistance_symm z.1 p.1] at h₁
  rw [quotientLogDistance_symm z.2 p.2] at h₄
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

theorem compact_finite_observation_separation {n M : ℕ}
    (K : Set (X n)) (hK : IsCompact K) (P : X n → Fin M)
    (hP : ContinuousOn P K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ K,
      quotientLogDistance x y < δ → P x=P y := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Set (K × K) := {p | P p.1.val ≠ P p.2.val}
  have hp : Continuous (fun x : K => P x.val) := continuousOn_iff_continuous_domRestrict.mp hP
  have hS : IsClosed S :=
    (isClosed_discrete {q : Fin M × Fin M | q.1 ≠ q.2}).preimage
      ((hp.comp continuous_fst).prodMk (hp.comp continuous_snd))
  have hf : Continuous (fun p : K × K => quotientLogDistance p.1.val p.2.val) :=
    (continuous_quotientLogDistance_pair n).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  obtain ⟨δ,hδ,hlower⟩ := hS.isCompact.exists_forall_le' hf.continuousOn
    (a := (0 : ℝ)) (fun p hp => by
      apply lt_of_le_of_ne (quotientLogDistance_nonneg _ _)
      intro h
      exact hp (congrArg P ((quotientLogDistance_eq_zero_iff _ _).mp h.symm)))
  refine ⟨δ,hδ,?_⟩
  intro x hx y hy hxy
  by_contra hne
  exact (not_lt_of_ge (hlower (⟨x,hx⟩,⟨y,hy⟩) hne)) hxy

/-- A reference point can be assigned a robust label even when the
reference point itself lies outside the good compact set. -/
theorem compact_finite_reference_labels {n M : ℕ}
    (K : Set (X n)) (hK : IsCompact K) (P : X n → Fin M)
    (hP : ContinuousOn P K) :
    ∃ (δ : ℝ) (R : X n → Fin M), 0 < δ ∧
      ∀ z y, y ∈ K → quotientLogDistance z y < δ → P y=R z := by
  classical
  obtain ⟨ε,hε,hsep⟩ := compact_finite_observation_separation K hK P hP
  let δ := ε/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let E (z : X n) := ∃ y ∈ K, quotientLogDistance z y < δ
  let y₀ : X n := Quotient.mk _ (1 : G n)
  let R (z : X n) : Fin M := if h : E z then P h.choose else P y₀
  refine ⟨δ,R,hδ,?_⟩
  intro z y hy hzy
  have he : E z := ⟨y,hy,hzy⟩
  have hc := he.choose_spec
  have hnear : quotientLogDistance y he.choose < ε := by
    have ht := quotientLogDistance_triangle y z he.choose
    rw [quotientLogDistance_symm y z] at ht
    dsimp [δ] at hzy hc
    linarith [hc.2]
  simpa only [R,dite_eq_left he] using hsep y hy he.choose hc.1 hnear

theorem exists_robust_finite_observation {n M : ℕ}
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (P : X n → Fin M) (hP : Measurable P)
    (η : ℝ≥0∞) (hη : η ≠ 0) :
    ∃ (B : Set (X n)) (δ : ℝ) (R : X n → Fin M),
      MeasurableSet B ∧ μ B < η ∧ 0 < δ ∧
        ∀ z y, y ∉ B → quotientLogDistance z y < δ → P y=R z := by
  obtain ⟨K,hK,_,hsmall,hcont⟩ := exists_compact_continuousOn_metrizable
    μ P hP ∅ MeasurableSet.empty (by simp) η hη
  obtain ⟨δ,R,hδ,hr⟩ := compact_finite_reference_labels K hK P hcont
  exact ⟨Kᶜ,δ,R,hK.isClosed.measurableSet.compl,hsmall,hδ,
    fun z y hy hzy => hr z y (not_not.mp hy) hzy⟩

end DukePrimeDegree

end

end OAI
