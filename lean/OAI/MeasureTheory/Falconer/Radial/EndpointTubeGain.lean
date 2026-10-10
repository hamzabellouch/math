import OAI.MeasureTheory.Falconer.Angular.EndpointAngularGain
import OAI.MeasureTheory.Falconer.Radial.PreparedTubeRelation

namespace OAI

/-! # Endpoint decay for arbitrary original finite fiber covers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem endpoint_dyadic_tube_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C : ℝ} (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
    (hζ : 0 < ζ) (hC : 0 ≤ C) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
        [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ E : Set (Space (h+3) × Sphere (h+3)),
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ)) →
      MeasurableSet E → (∀ u ∈ E, ‖u.1‖ ≤ 1/4) →
      (∀ w : Sphere (h+3), ∃ S : Finset (Space (h+3)),
        (S.card : ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-ε) ∧
        ∀ x, (x,w) ∈ E → ∃ a ∈ S,
          ‖perpendicularPart (w:Space (h+3)) (x-a)‖ ≤ C*(1/(2:ℝ)^N)) →
      (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ε,c,hε,hc,N₀,hgain⟩ := endpoint_dyadic_angular_gain hLW ht ht' hζ
    (by linarith : 0 ≤ 2*C+1)
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro N hN μ ν _ _ E hμ hμmass hνmass hμball hνball hslab hE hEb hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨G,hG,J,F,hF,hFE,hJ,hcard,hzero,hcoverF⟩ :=
    prepare_original_tube_relation μ E hE hδ (Nat.floor (δ^(-(h+1:ℝ)-ε))) hEb (by
      intro w
      obtain ⟨S,hS,hcoverS⟩ := hcover w
      exact ⟨S,Nat.le_floor hS,hcoverS⟩)
  have hmass : (μ.prod ν) F = (μ.prod ν) E := by
    have hh := product_inter_eq_of_null_original_fibers μ μ ν Measure.AbsolutelyContinuous.rfl
      E F hE hF hzero
    simpa only [inter_eq_right.mpr hFE] using hh
  rw [← hmass]
  refine hgain N hN {a // a ∈ G} μ ν F J (fun a => a.val)
    hμ hμmass hνmass hμball hνball hslab hF hJ ?_
    (fun u hu => hEb u (hFE hu)) (fun _ i _ => hG i.val i.property) ?_
  · intro w
    have hh : ((J w).card : ℝ) ≤ (Nat.floor (δ^(-(h+1:ℝ)-ε)) : ℝ) := by exact_mod_cast hcard w
    exact hh.trans (Nat.floor_le (Real.rpow_nonneg hδ.le _))
  · intro u hu
    obtain ⟨a,ha,hp⟩ := hcoverF u hu
    refine ⟨a,ha,?_⟩
    nlinarith

end Falconer

end OAI
