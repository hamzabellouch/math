import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafLusin

namespace OAI

/-!
# A strictly invariant version of an almost-everywhere invariant observable

For a measurable group action, use the essential constant value of the
observable along the orbit with respect to a nonzero translation-invariant
measure on the acting group. Fubini gives agreement almost everywhere;
translation invariance makes the new version invariant at every point.
This supplies the pointwise neutral invariance needed for selecting
noncentral return pairs.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree

theorem exists_strictly_invariant_version
    {H X Y : Type*} [Group H] [MeasurableSpace H]
    [MeasurableSpace X] [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] [Inhabited Y]
    (σ : Measure H) [SigmaFinite σ] [NeZero σ]
    (μ : Measure X) [SigmaFinite μ]
    (R : H → X → X) (hR : Measurable (fun p : H × X => R p.1 p.2))
    (hone : ∀ x, R 1 x = x) (hmul : ∀ a b x, R a (R b x) = R (a * b) x)
    (hσ : ∀ b : H, MeasurePreserving (fun a => a * b) σ σ)
    (F : X → Y) (hF : Measurable F)
    (hinv : ∀ a : H, ∀ᵐ x ∂μ, F (R a x) = F x) :
    ∃ V : X → Y, V =ᵐ[μ] F ∧ AEMeasurable V μ ∧
      ∀ a x, V (R a x) = V x := by
  let E : X → Prop := fun x => ∃ y : Y, ∀ᵐ a ∂σ, F (R a x) = y
  let V : X → Y := fun x => if h : E x then h.choose else default
  have hvalue (x : X) (hx : E x) : ∀ᵐ a ∂σ, F (R a x) = V x := by
    simpa only [V, dite_eq_left hx] using hx.choose_spec
  have hpull (x : X) (b : H) (y : Y) (hy : ∀ᵐ a ∂σ, F (R a x) = y) :
      ∀ᵐ a ∂σ, F (R a (R b x)) = y := by
    have hmap : ∀ᵐ a ∂σ.map (fun a => a * b), F (R a x) = y := by
      simpa only [(hσ b).map_eq] using hy
    have h := ae_of_ae_map (hσ b).measurable.aemeasurable hmap
    simpa only [hmul] using h
  have hE (x : X) (b : H) : E (R b x) ↔ E x := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      have h := hpull (R b x) b⁻¹ y hy
      simpa only [hmul, inv_mul_cancel, hone] using h
    · rintro ⟨y, hy⟩
      exact ⟨y, hpull x b y hy⟩
  have hstrict (b : H) (x : X) : V (R b x) = V x := by
    by_cases hx : E x
    · have hy := (hE x b).mpr hx
      obtain ⟨a, ha, hb⟩ := ((hvalue (R b x) hy).and (hpull x b (V x) (hvalue x hx))).exists
      exact ha.symm.trans hb
    · have hy : ¬ E (R b x) := fun h => hx ((hE x b).mp h)
      simp only [V, dite_eq_right hx, dite_eq_right hy]
  have hmeas : MeasurableSet {p : H × X | F (R p.1 p.2) = F p.2} :=
    measurableSet_eq_fun (hF.comp hR) (hF.comp measurable_snd)
  have horbit : ∀ᵐ x ∂μ, ∀ᵐ a ∂σ, F (R a x) = F x :=
    (Measure.ae_ae_comm hmeas).mp (Eventually.of_forall hinv)
  have heq : V =ᵐ[μ] F := by
    filter_upwards [horbit] with x hx
    have hEx : E x := ⟨F x, hx⟩
    obtain ⟨a, ha, hb⟩ := ((hvalue x hEx).and hx).exists
    exact ha.symm.trans hb
  exact ⟨V, heq, hF.aemeasurable.congr heq.symm, hstrict⟩

end DukePrimeDegree

end

end OAI
