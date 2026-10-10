import OAI.MeasureTheory.Falconer.Geometry.SelectTransverseChartTriple
import OAI.MeasureTheory.Falconer.Slicing.EndpointSliceObstruction

namespace OAI

/-! # Exclusion of common chart incidence by the three-tube estimate -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem endpoint_chart_incidence_obstruction
    (α : Measure (Space (n+1))) (β : Measure (Space n))
    [IsFiniteMeasure α] [IsFiniteMeasure β]
    (V : Submodule ℝ (Space (n+1))) (e : V ≃ₗᵢ[ℝ] Space 3)
    (E : Set (Space (n+1) × Space n)) (hE : MeasurableSet E)
    (G : Set (Space n × Space n)) (hG : MeasurableSet G)
    (J : Space n → Finset (Space (n+1)))
    {δ η a κ C s R M b : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ a) (hC : 0 ≤ C) (hη : η < 1)
    (hM : 0 < M) (hb : 0 < b)
    (hα : α univ ≤ ENNReal.ofReal M) (hβ : β univ ≤ ENNReal.ofReal M)
    (hchart : ∀ u ∈ E, ‖u.2‖ ≤ 1)
    (hbounded : ∀ u ∈ E, ‖u.1‖ ≤ R)
    (hband : ∀ u ∈ E, gnomonicChart u.2 ∈ directionSliceBand V η)
    (hball : ∀ p : Space 3, α {x | dist (e (V.orthogonalProjectionOnto x)) p < 6*δ} ≤
      ENNReal.ofReal (δ^(-κ)*(6*δ)^s))
    (hcover : ∀ u ∈ E, ∃ v ∈ J u.2,
      ‖perpendicularPart (gnomonicChart u.2 : Space (n+1)) (u.1-v)‖ ≤ C*δ)
    (hcard : ∀ p, ((J p).card:ℝ) ≤ δ^(-1-κ))
    (hbad : (β.prod (β.prod β)) (badChartTriples G (2*δ^a))+
      2*β univ*(β.prod β) Gᶜ ≤ ENNReal.ofReal (b^3/(4*M^3)))
    (hmass : δ^κ ≤ b^3/(2*M^5))
    (herror : 72*η ≤ 3*(δ^a)^2)
    (hbudget : (δ^(-1-κ))^3*((6*C+35)/δ^a)^6*(δ^(-κ)*(6*δ)^s)^2 < (δ^κ)^2) :
    (α.prod β) E < ENNReal.ofReal b := by
  classical
  by_contra! hI
  obtain ⟨w,hvol,_,_,hcommon⟩ := exists_transverse_common_chart_triple α β E hE hchart
    G hG (2*δ^a) hM hb hα hβ hI hbad
  let Q : Set (Space (n+1)) := {x | (x,w) ∈ commonTripleRelation E}
  let v : Fin 3 → Sphere (n+1) := ![gnomonicChart w.1,gnomonicChart w.2.1,gnomonicChart w.2.2]
  let L : Fin 3 → Finset (Space (n+1)) := ![J w.1,J w.2.1,J w.2.2]
  have hQ (x : Space (n+1)) (hx : x ∈ Q) :
      (x,w.1) ∈ E ∧ (x,w.2.1) ∈ E ∧ (x,w.2.2) ∈ E := hx
  have hn : Q.Nonempty := by
    by_contra hn
    have he : Q = ∅ := not_nonempty_iff_eq_empty.mp hn
    change ENNReal.ofReal (b^3/(2*M^5)) < α Q at hcommon
    rw [he,measure_empty] at hcommon
    exact not_lt_of_ge (bot_le : (0 : ℝ≥0∞) ≤ _) hcommon
  obtain ⟨x,hx⟩ := hn
  have hvband : ∀ i, v i ∈ directionSliceBand V η := by
    intro i
    fin_cases i
    · exact hband (x,w.1) (hQ x hx).1
    · exact hband (x,w.2.1) (hQ x hx).2.1
    · exact hband (x,w.2.2) (hQ x hx).2.2
  have hvgram : 2*δ^a ≤ Real.sqrt ((Matrix.gram ℝ (fun i => (v i : Space (n+1)))).det) := hvol
  have hQbound : ∀ y ∈ Q, ‖y‖ ≤ R := fun y hy => hbounded (y,w.1) (hQ y hy).1
  have hQcover : ∀ i : Fin 3, ∀ y ∈ Q, ∃ c ∈ L i,
      ‖perpendicularPart (v i : Space (n+1)) (y-c)‖ ≤ C*δ := by
    intro i y hy
    fin_cases i
    · exact hcover (y,w.1) (hQ y hy).1
    · exact hcover (y,w.2.1) (hQ y hy).2.1
    · exact hcover (y,w.2.2) (hQ y hy).2.2
  have hLcard : ∀ i, ((L i).card:ℝ) ≤ δ^(-1-κ) := by
    intro i
    fin_cases i
    · exact hcard w.1
    · exact hcard w.2.1
    · exact hcard w.2.2
  have hQmass : δ^κ ≤ (α Q).toReal := hmass.trans (by
    have hh := ENNReal.toReal_mono (measure_ne_top α Q) hcommon.le
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ b^3/(2*M^5))] using hh)
  exact endpoint_slice_obstruction α V e v hδ hδ1 ha hC hη hvband hvgram herror hbudget
    Q L R hQbound hball hQcover hLcard hQmass

end Falconer

end OAI
