import OAI.Probability.BenjaminiSchramm.FreshWhiteExposure
import OAI.Probability.BenjaminiSchramm.AvoidanceProduct

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def exteriorEscape (S : Set V) (f : V → ℝ) (x u : V) : Set (Set E) :=
  {η | ∃ y, y ≠ x ∧ f x ≤ f y ∧ y ∉ S ∧ Conn G (η \ internalEdges G S) u y}

lemma exteriorEscape_upper (S : Set V) (f : V → ℝ) (x u : V) :
    IsUpperSet (exteriorEscape G S f x u) := by
  rintro ω η hωη ⟨y,hy,hf,hyS,huy⟩
  exact ⟨y,hy,hf,hyS,conn_mono G (Set.sdiff_subset_sdiff_left hωη) huy⟩

lemma exteriorEscape_hasFiniteOpenWitness (S : Set V) (f : V → ℝ) (x u : V) :
    CriticalPercolation.BernoulliProduct.HasFiniteOpenWitness (exteriorEscape G S f x u) := by
  rintro ω ⟨y,hy,hf,hyS,huy⟩
  obtain ⟨F,hF,hconn⟩ := finiteWitness_conn G u y _ huy
  refine ⟨F,F.finite_toSet,fun e he => (hF he).1,y,hy,hf,hyS,conn_mono G ?_ hconn⟩
  intro e he
  exact ⟨he,(hF he).2⟩

lemma measurableSet_exteriorEscape [Countable E] (S : Set V) (f : V → ℝ) (x u : V) :
    MeasurableSet (exteriorEscape G S f x u) :=
  CriticalPercolation.BernoulliProduct.measurableSet_finiteWitness _
    (exteriorEscape_upper G S f x u) (exteriorEscape_hasFiniteOpenWitness G S f x u)

lemma conn_eq_of_incident_closed (η : Set E) (u y : V)
    (hclosed : ∀ e, u ∈ G e → e ∉ η) (hconn : Conn G η u y) : y=u := by
  induction hconn with
  | refl => rfl
  | @tail v w _ hstep ih =>
    subst v
    obtain ⟨e,he,heq⟩ := hstep
    exact False.elim (hclosed e (by rw [heq]; simp) he)

lemma finiteBondPattern_excludes_exteriorEscape (S : Set V) (f : V → ℝ) (x u : V)
    (hu : u ∈ S) (F : Finset E) (hF : ∀ e, u ∈ G e → e ∈ F) :
    finiteBondPattern F ∅ ⊆ (exteriorEscape G S f x u)ᶜ := by
  rintro η hη ⟨y,_hy,_hf,hyS,huy⟩
  have hclosed (e : E) (he : u ∈ G e) : e ∉ η := by
    have hh := hη e (hF e he)
    simpa only [Set.mem_empty_iff_false,eq_iff_iff,iff_false] using hh
  have heq := conn_eq_of_incident_closed G η u y hclosed
    (conn_mono G Set.sdiff_subset huy)
  exact hyS (heq ▸ hu)

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BernoulliProduct
open Percolation.BenjaminiSchramm
variable {E : Type*}

lemma finiteBondPattern_law_eq_of_parameters (r : E → unitInterval)
    (b : unitInterval) (F : Finset E) (hb : ∀ e ∈ F, r e=b) (σ : Set E) :
    law r (finiteBondPattern F σ)=law (fun _ => b) (finiteBondPattern F σ) := by
  let T : Set (F : Set E) := Subtype.val ⁻¹' σ
  have he : finiteBondPattern F σ=
      (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (F : Set E))) ⁻¹' {T} := by
    ext ω
    change (∀ e ∈ F, (e ∈ ω)=(e ∈ σ)) ↔ Subtype.val ⁻¹' ω=T
    constructor
    · intro h
      ext e
      exact Iff.of_eq (h e e.property)
    · intro h e he
      exact propext (show (⟨e,he⟩ : (F : Set E)) ∈ Subtype.val ⁻¹' ω ↔
        (⟨e,he⟩ : (F : Set E)) ∈ T from by rw [h])
  rw [he,←Measure.map_apply (Percolation.measurable_set_restrict _) (MeasurableSet.singleton T),
    ←Measure.map_apply (Percolation.measurable_set_restrict _) (MeasurableSet.singleton T),
    law_map_restrict,law_map_restrict]
  congr 1
  apply congrArg law
  funext e
  exact hb e e.property

lemma finiteBondPattern_inhomogeneous_lower (r : E → unitInterval)
    (b : unitInterval) (F : Finset E) (hb : ∀ e ∈ F, r e=b) (σ : Set E) :
    ENNReal.ofReal ((min (b : ℝ) (1-b))^F.card) ≤ law r (finiteBondPattern F σ) := by
  rw [finiteBondPattern_law_eq_of_parameters r b F hb σ,law_const]
  exact finiteBondPattern_probability_lower b F σ

end CriticalPercolation.BernoulliProduct

namespace Percolation.BenjaminiSchramm
open CriticalPercolation.BernoulliProduct
variable {V E : Type*} [Countable E] (G : BondGraph V E)

omit [Countable E] in
theorem exteriorEscape_avoidance_finite_energy (r : E → unitInterval)
    (b : unitInterval) (S : Set V) (f : V → ℝ) (x u : V) (hu : u ∈ S)
    (F : Finset E) (hF : ∀ e, u ∈ G e → e ∈ F) (hb : ∀ e ∈ F, r e=b) :
    (min (b : ℝ) (1-b))^F.card ≤ (CriticalPercolation.BernoulliProduct.law r).real (exteriorEscape G S f x u)ᶜ := by
  have hh := (finiteBondPattern_inhomogeneous_lower r b F hb ∅).trans
    (measure_mono (finiteBondPattern_excludes_exteriorEscape G S f x u hu F hF))
  have hr := ENNReal.toReal_mono (measure_ne_top _ _) hh
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_min b.2.1 (sub_nonneg.mpr b.2.2)) _)] at hr
  exact hr

theorem exteriorEscape_avoidance_product (r : E → unitInterval)
    (S : Finset V) (f : V → ℝ) (x : V) (g : V → ℝ)
    (hbound : ∀ u ∈ S, Real.exp (-g u) ≤
      (CriticalPercolation.BernoulliProduct.law r).real (exteriorEscape G (S : Set V) f x u)ᶜ) :
    ENNReal.ofReal (Real.exp (-(∑ u ∈ S, g u))) ≤
      CriticalPercolation.BernoulliProduct.law r {η | ∀ u ∈ S, η ∉ exteriorEscape G (S : Set V) f x u} := by
  have he : (finiteBadUnion S (fun u => exteriorEscape G (S : Set V) f x u))ᶜ=
      {η | ∀ u ∈ S, η ∉ exteriorEscape G (S : Set V) f x u} := by
    ext η
    simp [finiteBadUnion]
  rw [←he]
  exact exponential_finite_avoidance r S _
    (fun u _ => exteriorEscape_upper G _ f x u)
    (fun u _ => exteriorEscape_hasFiniteOpenWitness G _ f x u) g hbound

end Percolation.BenjaminiSchramm

end

end OAI
