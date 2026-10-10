import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientMeasurableSection
import Mathlib.MeasureTheory.Measure.Sum

namespace OAI

/-! # Lifting an arbitrary finite measure through the arithmetic covering

The countable sum over deck transformations restricts on every injective
chart to the original quotient measure. In particular this construction
applies also to singular invariant measures.
-/

noncomputable section
open MeasureTheory Set Function TopologicalSpace
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

lemma quotient_left_integral (n : ℕ) (γ : integralGroup n) (g : G n) :
    Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (γ.val*g)=
      Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g := by
  apply Quotient.sound
  change QuotientGroup.rightRel (integralGroup n) (γ.val*g) g
  rw [QuotientGroup.rightRel_apply]
  simpa only [mul_inv_rev,←mul_assoc,mul_inv_cancel,one_mul] using
    (integralGroup n).inv_mem γ.prop

lemma quotient_fiber_representative (n : ℕ) (s : X n → G n)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (g : G n) : ∃ γ : integralGroup n,
      γ.val*s (Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g)=g := by
  let x : X n := Quotient.mk _ g
  have he : Quotient.mk (QuotientGroup.rightRel (integralGroup n)) g=
      Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x) := (hs x).symm
  have hmem := Quotient.exact he
  change QuotientGroup.rightRel (integralGroup n) g (s x) at hmem
  rw [QuotientGroup.rightRel_apply] at hmem
  have hmem' : g*(s x)⁻¹ ∈ integralGroup n := by
    simpa only [mul_inv_rev,inv_inv] using (integralGroup n).inv_mem hmem
  refine ⟨⟨g*(s x)⁻¹,hmem'⟩,?_⟩
  exact inv_mul_cancel_right _ _

def quotientLiftMeasure (n : ℕ) (μ : Measure (X n)) (s : X n → G n) : Measure (G n) :=
  Measure.sum (fun γ : integralGroup n => μ.map (fun x => γ.val*s x))

theorem quotientLiftMeasure_injective_chart (n : ℕ)
    (μ : Measure (X n)) (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (E : Set (G n)) (hE : MeasurableSet E)
    (hinj : Set.InjOn (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) E) :
    quotientLiftMeasure n μ s E =
      μ ((Quotient.mk (QuotientGroup.rightRel (integralGroup n))) '' E) := by
  let : Countable (integralGroup n) := separableSpace_iff_countable.mp inferInstance
  let q : G n → X n := Quotient.mk (QuotientGroup.rightRel (integralGroup n))
  let A : integralGroup n → Set (X n) := fun γ => (fun x => γ.val*s x) ⁻¹' E
  have hA (γ : integralGroup n) : MeasurableSet (A γ) :=
    hE.preimage (measurable_const.mul hsm)
  have hd : Pairwise (Disjoint on A) := by
    intro γ δ hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    have he : γ.val*s x=δ.val*s x := hinj hx hy (by
      change q (γ.val*s x)=q (δ.val*s x)
      dsimp only [q]
      rw [quotient_left_integral,quotient_left_integral])
    exact hne (Subtype.ext (mul_right_cancel he))
  have hu : (⋃ γ, A γ)=q '' E := by
    ext x
    constructor
    · intro hx
      obtain ⟨γ,hγ⟩ := mem_iUnion.mp hx
      refine ⟨γ.val*s x,hγ,?_⟩
      exact (quotient_left_integral n γ (s x)).trans (hs x)
    · rintro ⟨g,hg,rfl⟩
      obtain ⟨γ,hγ⟩ := quotient_fiber_representative n s hs g
      exact mem_iUnion.mpr ⟨γ,by change γ.val*s (q g) ∈ E; rwa [hγ]⟩
  rw [quotientLiftMeasure,Measure.sum_apply _ hE]
  calc
    _ = ∑' γ : integralGroup n, μ (A γ) := by
      apply tsum_congr
      intro γ
      exact Measure.map_apply (measurable_const.mul hsm) hE
    _ = _ := by rw [←measure_iUnion hd hA,hu]

theorem quotient_measure_ext_on_injective_charts (n : ℕ)
    (ν ν' : Measure (G n))
    (heq : ∀ E : Set (G n), MeasurableSet E →
      Set.InjOn (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) E → ν E=ν' E) :
    ν=ν' := by
  let q : G n → X n := Quotient.mk (QuotientGroup.rightRel (integralGroup n))
  choose e he hqe using (quotient_covering n).isLocalHomeomorph
  obtain ⟨S,hSuniv,hSc,hS⟩ := isOpen_biUnion_countable (univ : Set (G n))
    (fun g => (e g).source) (fun g _ => (e g).open_source)
  have hcover : (⋃ g ∈ S, (e g).source)=univ := by
    rw [hS]
    apply eq_univ_of_forall
    intro g
    exact mem_iUnion₂.mpr ⟨g,mem_univ _,he g⟩
  apply Measure.ext_of_biUnion_eq_univ hSc hcover
  intro g hg
  ext E hE
  rw [Measure.restrict_apply hE,Measure.restrict_apply hE]
  apply heq _ (hE.inter (e g).open_source.measurableSet)
  intro a ha b hb hab
  apply (e g).injOn ha.2 hb.2
  rwa [←hqe g]

theorem quotientLiftMeasure_section_independent (n : ℕ)
    (μ : Measure (X n)) (s t : X n → G n) (hsm : Measurable s) (htm : Measurable t)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x)
    (ht : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (t x)=x) :
    quotientLiftMeasure n μ s=quotientLiftMeasure n μ t := by
  apply quotient_measure_ext_on_injective_charts
  intro E hE hEinj
  rw [quotientLiftMeasure_injective_chart n μ s hsm hs E hE hEinj,
    quotientLiftMeasure_injective_chart n μ t htm ht E hE hEinj]

theorem quotientLiftMeasure_locallyFinite (n : ℕ)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x) :
    IsLocallyFiniteMeasure (quotientLiftMeasure n μ s) := by
  constructor
  intro g
  obtain ⟨e,hg,hqe⟩ := (quotient_covering n).isLocalHomeomorph g
  refine ⟨e.source,e.open_source.mem_nhds hg,?_⟩
  rw [quotientLiftMeasure_injective_chart n μ s hsm hs e.source e.open_source.measurableSet]
  · exact measure_lt_top μ _
  · intro a ha b hb hab
    apply e.injOn ha hb
    rwa [←hqe]

end DukePrimeDegree

end

end OAI
