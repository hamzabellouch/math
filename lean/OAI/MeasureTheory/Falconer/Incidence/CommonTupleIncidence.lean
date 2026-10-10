import OAI.MeasureTheory.Falconer.Incidence.IncidenceMoment
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # Common incidence of an arbitrary finite tuple of original pins -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]

def commonTupleRelation (k : ℕ) (E : Set (X × W)) : Set (X × (Fin k → W)) :=
  {p | ∀ i, (p.1,p.2 i) ∈ E}

theorem commonTupleRelation_measurable (k : ℕ) (E : Set (X × W)) (hE : MeasurableSet E) :
    MeasurableSet (commonTupleRelation k E) := by
  simp only [commonTupleRelation, ofPred_forall]
  exact MeasurableSet.iInter (fun i => hE.preimage (by fun_prop))

omit [MeasurableSpace X] in
theorem commonTupleRelation_fiber (k : ℕ) (ν : Measure W) [SigmaFinite ν]
    (E : Set (X × W)) (x : X) :
    (Measure.pi (fun _ : Fin k => ν)) (Prod.mk x ⁻¹' commonTupleRelation k E) =
      (ν (Prod.mk x ⁻¹' E))^k := by
  have he : Prod.mk x ⁻¹' commonTupleRelation k E = Set.pi univ (fun _ => Prod.mk x ⁻¹' E) := by
    ext w
    simp only [commonTupleRelation,mem_preimage,mem_ofPred_eq,mem_pi,mem_univ,true_implies]
  rw [he,Measure.pi_pi]
  simp

theorem common_tuple_incidence_moment (μ : Measure X) (ν : Measure W)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {k : ℕ} (hk : 2 ≤ k)
    (E : Set (X × W)) (hE : MeasurableSet E) :
    ((μ.prod ν) E)^k ≤
      (μ.prod (Measure.pi (fun _ : Fin k => ν))) (commonTupleRelation k E)*(μ univ)^(k-1) := by
  have hf : Measurable (fun x : X => ν (Prod.mk x ⁻¹' E)) := measurable_measure_prodMk_left hE
  have hh := incidence_moment μ (fun x : X => ν (Prod.mk x ⁻¹' E)) hf.aemeasurable hk
  rw [Measure.prod_apply hE,Measure.prod_apply (commonTupleRelation_measurable k E hE)]
  simpa only [commonTupleRelation_fiber] using hh

theorem exists_good_common_tuple (μ : Measure X) (ν : Measure W)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {k : ℕ} (hk : 2 ≤ k)
    (E : Set (X × W)) (hE : MeasurableSet E)
    (B : Set (Fin k → W)) (hB : MeasurableSet B) (t : ℝ≥0∞)
    (hgap : (μ univ)^(k-1)*(t*(ν univ)^k + μ univ*(Measure.pi (fun _ : Fin k => ν)) B) <
      ((μ.prod ν) E)^k) :
    ∃ w ∉ B, t < μ {x | (x,w) ∈ commonTupleRelation k E} := by
  classical
  let ξ := Measure.pi (fun _ : Fin k => ν)
  let F := commonTupleRelation k E ∩ (univ ×ˢ Bᶜ)
  have hF : MeasurableSet F := (commonTupleRelation_measurable k E hE).inter
    (MeasurableSet.univ.prod hB.compl)
  have hξ : ξ univ = (ν univ)^k := by
    have he : (univ : Set (Fin k → W)) = Set.pi univ (fun _ => (univ : Set W)) := by ext; simp
    rw [he,Measure.pi_pi]
    simp
  by_contra! hn
  have hfiber (w : Fin k → W) : μ ((fun x => (x,w)) ⁻¹' F) ≤ t := by
    by_cases hw : w ∈ B
    · have he : (fun x => (x,w)) ⁻¹' F = ∅ := by
        ext x
        simp only [F,mem_preimage,mem_inter_iff,mem_prod,mem_univ,mem_compl_iff,hw,
          not_true_eq_false,and_false,mem_empty_iff_false]
      simp only [he,measure_empty,zero_le]
    · exact (measure_mono (fun _ hx => hx.1)).trans (hn w hw)
  have hgood : (μ.prod ξ) F ≤ t*(ν univ)^k := by
    rw [Measure.prod_apply_symm hF]
    calc
      _ ≤ ∫⁻ _w, t ∂ξ := lintegral_mono hfiber
      _ = _ := by rw [lintegral_const,hξ,mul_comm]
  have hsub : commonTupleRelation k E ⊆ F ∪ (univ ×ˢ B) := by
    intro p hp
    by_cases hb : p.2 ∈ B
    · exact Or.inr ⟨mem_univ _,hb⟩
    · exact Or.inl ⟨hp,mem_univ _,hb⟩
  have hu : (μ.prod ξ) (commonTupleRelation k E) ≤ t*(ν univ)^k+μ univ*ξ B := by
    apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
    exact add_le_add hgood (by rw [Measure.prod_prod])
  have hm := common_tuple_incidence_moment μ ν hk E hE
  have hle := hm.trans (mul_le_mul' hu le_rfl)
  rw [mul_comm] at hle
  exact (not_lt_of_ge hle) hgap

end Falconer

end OAI
