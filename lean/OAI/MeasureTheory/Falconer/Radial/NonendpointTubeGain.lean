import OAI.MeasureTheory.Falconer.Angular.NonendpointAngularGain
import OAI.MeasureTheory.Falconer.Radial.PreparedTubeRelation

namespace OAI

/-! # Nonendpoint angular decay for arbitrary original finite fiber covers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem nonendpoint_dyadic_tube_gain
    (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q C : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    (hC : 0 ≤ C) :
    ∃ ε c δ₀ : ℝ, 0 < ε ∧ 0 < c ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν] (E : Set (Space (h+2) × Sphere (h+2))),
    1/(2:ℝ)^N < δ₀ → (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^q)) →
    MeasurableSet E → (∀ u ∈ E, ‖u.1‖ ≤ 1/4) →
    (∀ w : Sphere (h+2), ∃ S : Finset (Space (h+2)),
      (S.card : ℝ) ≤ (1/(2:ℝ)^N)^(-q-ε) ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S,
        ‖perpendicularPart (w:Space (h+2)) (x-a)‖ ≤ C*(1/(2:ℝ)^N)) →
    (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ε,c,δ₀,hε,hc,hδ₀,hgain⟩ := nonendpoint_dyadic_angular_gain hpublished hq hq' hqt ht
    (by linarith : 0 ≤ 2*C+1)
  refine ⟨ε,c,δ₀,hε,hc,hδ₀,?_⟩
  intro N μ ν _ _ E hδsmall hμ hμmass hνmass hμball hνball hE hEb hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨G,hG,J,F,hF,hFE,hJ,hcard,hzero,hcoverF⟩ :=
    prepare_original_tube_relation μ E hE hδ (Nat.floor (δ^(-q-ε))) hEb (by
      intro w
      obtain ⟨S,hS,hcoverS⟩ := hcover w
      exact ⟨S,Nat.le_floor hS,hcoverS⟩)
  have hmass : (μ.prod ν) F = (μ.prod ν) E := by
    have hh := product_inter_eq_of_null_original_fibers μ μ ν Measure.AbsolutelyContinuous.rfl
      E F hE hF hzero
    simpa only [inter_eq_right.mpr hFE] using hh
  rw [← hmass]
  refine hgain N {a // a ∈ G} μ ν F J (fun a => a.val) hδsmall hμ hμmass hνmass
    hμball hνball hF hJ ?_ (fun u hu => hEb u (hFE hu)) (fun _ i _ => hG i.val i.property) ?_
  · intro w
    have hh : ((J w).card : ℝ) ≤ (Nat.floor (δ^(-q-ε)) : ℝ) := by exact_mod_cast hcard w
    exact hh.trans (Nat.floor_le (Real.rpow_nonneg hδ.le _))
  · intro u hu
    obtain ⟨a,ha,hp⟩ := hcoverF u hu
    refine ⟨a,ha,?_⟩
    nlinarith

end Falconer

end OAI
