import Mathlib
import OAI.Analysis.HardSphere.Geometry.SmoothSiteWeight
import OAI.Analysis.HardSphere.Geometry.ScalarNormSqIntegral
import OAI.Analysis.HardSphere.Geometry.BoxWeight
import OAI.Analysis.HardSphere.Conditioning.BathPhase

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace HardSphere

lemma cons_measurableEmbedding {n : ℕ} (L : Length) :
    MeasurableEmbedding (fun p : Configuration n L × Torus L ↦ Fin.cons (α:=fun _ ↦ Torus L) p.2 p.1) := by
  have h := ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm.measurableEmbedding).comp
    (MeasurableEquiv.prodComm : Configuration n L × Torus L ≃ᵐ Torus L × Configuration n L).measurableEmbedding
  convert h using 1
  funext pair
  change Fin.cons pair.2 pair.1 = Fin.insertNth (α:=fun _ : Fin (n+1) ↦ Torus L) 0 pair.2 pair.1
  exact (Fin.insertNth_zero' _ _).symm

lemma ground_bath_integral {n : ℕ} {L : Length} {u : Jet (n+1) L} (hu : ‖u.1‖=1)
    (F : Configuration n L → ℝ) (hF : Measurable F) {B : ℝ} (hB : ∀Y,|F Y|≤B) :
    (∫Y,F Y*(∫x,‖u.1 (Fin.cons x Y)‖^2)) =
      ∫Y,F Y ∂(groundPositionLaw (n+1) L u).map (fun X ↦ fun i : Fin n ↦ X i.succ) := by
  let μ := groundPositionLaw (n+1) L u
  let := groundPositionLaw_probability u hu
  have hm : Measurable (fun X : Configuration (n+1) L ↦ fun i : Fin n ↦ X i.succ) := by fun_prop
  rw [integral_map hm.aemeasurable hF.aestronglyMeasurable,groundPositionLaw_integral]
  let f : Configuration n L × Torus L → ℝ := fun p ↦ F p.1*‖u.1 (Fin.cons p.2 p.1)‖^2
  have hf : Integrable f (volume.prod volume) := by
    have hu' := (Lp.memLp u.1).comp_measurePreserving (cons_preserving (n:=n) L)
    apply ((hu'.integrable_norm_pow (by norm_num : (2:ℕ)≠0)).const_mul B).mono'
    · exact (hF.comp measurable_fst).aestronglyMeasurable.mul (hu'.aestronglyMeasurable.norm.pow 2)
    · exact Eventually.of_forall fun p ↦ by
        change ‖F p.1*‖u.1 (Fin.cons p.2 p.1)‖^2‖ ≤ B*‖u.1 (Fin.cons p.2 p.1)‖^2
        simp only [Real.norm_eq_abs,abs_mul,abs_sq]
        exact mul_le_mul_of_nonneg_right (hB _) (sq_nonneg _)
  calc
    _ = ∫p,f p ∂volume.prod volume := by rw [integral_prod _ hf]; simp only [f,integral_const_mul]
    _ = _ := by
      have he := (cons_preserving (n:=n) L).integral_comp (cons_measurableEmbedding (n:=n) L)
        (fun X ↦ F (fun i : Fin n ↦ X i.succ)*‖u.1 X‖^2)
      simpa only [Fin.cons_succ] using he

lemma ground_physical_phase_transfer {n : ℕ} {L : Length} {r h : ℝ}
    {u : Jet (n+1) L} (hu : IsGroundVector (n+1) L r u) (hh : 0<h) :
    Phase.modulusOccupation (fun p : Configuration n L × Torus L ↦ u.1 (Fin.cons p.2 p.1)) volume volume -
      4*Real.sqrt ((∫Y,(volume : Measure (Torus L)).real (BathSlice.omitted h r Y)
        ∂(groundPositionLaw (n+1) L u).map (fun X ↦ fun i : Fin n ↦ X i.succ))/L.val^3) ≤
    Phase.occupation (fun p : Configuration n L × Torus L ↦ u.1 (Fin.cons p.2 p.1)) volume volume := by
  have hLp := L.property
  let f : Configuration n L × Torus L → ℂ := fun p ↦ u.1 (Fin.cons p.2 p.1)
  have hf : MemLp f 2 (volume.prod volume) :=
    (Lp.memLp u.1).comp_measurePreserving (cons_preserving (n:=n) L)
  have hn : ∫p,‖f p‖^2 ∂volume.prod volume=1 := by
    rw [(cons_preserving (n:=n) L).integral_comp (cons_measurableEmbedding (n:=n) L)
      (fun X ↦ ‖u.1 X‖^2),←scalar_norm_sq_integral,hu.2.2.1]
    norm_num
  have hV : (volume : Measure (Torus L)).real univ=L.val^3 := by
    rw [Measure.real,BathSlice.volume_torus,ENNReal.toReal_ofReal (by positivity)]
  have hU : MeasurableSet {p : Configuration n L × Torus L | p.2∈BathSlice.retained h r p.1} :=
    (BathSlice.measurableSet_omitted_graph L h r).compl
  have ht := Phase.phase_transfer hf hn (by rw [hV]; positivity) hU (hu.ae_retained_commonPhase hh)
  have hl : Phase.geometricLoss f {p | p.2∈BathSlice.retained h r p.1} volume volume =
      (∫Y,(volume : Measure (Torus L)).real (BathSlice.omitted h r Y)
        ∂(groundPositionLaw (n+1) L u).map (fun X ↦ fun i : Fin n ↦ X i.succ))/L.val^3 := by
    unfold Phase.geometricLoss
    simp only [hV]
    congr 1
    convert ground_bath_integral hu.2.2.1 (fun Y ↦ (volume : Measure (Torus L)).real (BathSlice.omitted h r Y))
      (BathSlice.measurable_omitted_volume L h r).ennreal_toReal (B:=L.val^3) (fun Y ↦ by
        rw [abs_of_nonneg measureReal_nonneg,←hV]
        exact measureReal_mono (subset_univ _)) using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun Y ↦ by
      have he : Prod.mk Y ⁻¹' {p : Configuration n L × Torus L | p.2∈BathSlice.retained h r p.1}ᶜ = BathSlice.omitted h r Y := by
        ext x
        simp [BathSlice.retained]
      dsimp only
      rw [he]
  simpa only [hl] using ht

end HardSphere

end
end

end

end OAI
