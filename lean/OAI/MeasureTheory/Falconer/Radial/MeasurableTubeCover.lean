import OAI.MeasureTheory.Falconer.Radial.TubeCoverEnumeration

namespace OAI

/-! # Measurable bounded-grid covers of the original direction fibers -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem original_tube_cover_choice (μ : Measure (Space d)) [SFinite μ]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {D ε δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (hbounded : ∀ t ∈ E, ‖t.1‖ ≤ D)
    (hcover : ∀ w : Sphere d, ∃ S : Finset (Space d), S.card ≤ N ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ G : Finset (Space d), (∀ a ∈ G, ‖a‖ ≤ D) ∧
      ∃ J : Sphere d → Finset (Space d),
        (∀ a, MeasurableSet {w | a ∈ J w}) ∧ (∀ w, J w ⊆ G ∧ (J w).card ≤ N) ∧
        ∀ w, μ {x | (x,w) ∈ E ∧ ∀ a ∈ J w,
          ¬‖perpendicularPart (w:Space d) (x-a)‖ ≤ 2*ε+δ} = 0 := by
  classical
  obtain ⟨G,hGb,hGn⟩ := exists_bounded_anchor_net (d := d) D hδ
  obtain ⟨C,hC,hCs⟩ := bounded_finset_enumeration G N
  let U : Space d → Sphere d → Set (Space d) := fun a w =>
    {x | ‖perpendicularPart (w:Space d) (x-a)‖ ≤ 2*ε+δ}
  have hU (a : Space d) : MeasurableSet {p : Sphere d × Space d | p.2 ∈ U a p.1} := by
    dsimp [U,perpendicularPart]
    exact measurableSet_le (by fun_prop) measurable_const
  have hc : ∀ w : Sphere d, ∃ n, μ {x | (x,w) ∈ E ∧ ∀ a ∈ C n, x ∉ U a w} = 0 := by
    intro w
    obtain ⟨S,hSN,hS⟩ := hcover w
    obtain ⟨J,hJG,hJS,hJ⟩ := rounded_tube_cover w {x | (x,w) ∈ E} S G
      (fun x hx => hGn x (hbounded (x,w) hx)) hS
    obtain ⟨n,hn⟩ := hCs J hJG (hJS.trans hSN)
    refine ⟨n,?_⟩
    apply measure_mono_null (t := ∅) _ (measure_empty)
    intro x hx
    obtain ⟨a,ha,hxa⟩ := hJ x hx.1
    exact (hx.2 a (hn.symm ▸ ha) hxa).elim
  obtain ⟨J,hJ,hzero,hJC⟩ := exists_measurable_tube_cover_choice μ E hE U hU C hc
  refine ⟨G,hGb,J,hJ,?_,hzero⟩
  intro w
  obtain ⟨n,hn⟩ := hJC w
  simpa only [hn] using hC n

theorem finite_tube_cover_relation_measurable
    (G : Finset (Space d)) (J : Sphere d → Finset (Space d))
    (hJ : ∀ a, MeasurableSet {w | a ∈ J w}) (hJG : ∀ w, J w ⊆ G) (ε : ℝ) :
    MeasurableSet {t : Space d × Sphere d |
      ∃ a ∈ J t.2, ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε} := by
  have hm : MeasurableSet {t : Space d × Sphere d |
      ∃ a ∈ G, a ∈ J t.2 ∧ ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε} := by
    have hu : MeasurableSet (⋃ a ∈ G, {t : Space d × Sphere d |
        a ∈ J t.2 ∧ ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε}) := by
      apply G.measurableSet_biUnion
      intro a _
      have hp : MeasurableSet {t : Space d × Sphere d |
          ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε} := by
        dsimp [perpendicularPart]
        exact measurableSet_le (by fun_prop) measurable_const
      exact ((hJ a).preimage measurable_snd).inter hp
    convert hu using 1
    ext t
    simp only [mem_ofPred_eq,mem_iUnion,exists_prop]
  convert hm using 1
  ext t
  constructor
  · rintro ⟨a,ha,hp⟩
    exact ⟨a,hJG t.2 ha,ha,hp⟩
  · rintro ⟨a,_,ha,hp⟩
    exact ⟨a,ha,hp⟩

end Falconer

end OAI
