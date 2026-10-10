import Mathlib
import OAI.Analysis.Conductivity.Geometry.ControlledCorrectionBoxes
import OAI.Analysis.Conductivity.Variational.QuantitativePhysicalMoments

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma ControlledCorrectionBox.bounded_transfer
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {U : Set Coord3}
    (hD : ∀ p∈U,Function.Surjective (fderiv ℝ u p))
    (B C : ControlledCorrectionBox u U) (hBC : (B.region∩C.region).Nonempty) :
    ∃ L : ℝ,0<L ∧ ∀ r : PhysicalSourcePair,CompactSmoothPair r → PairSupported r B.region →
      ∀ M : ℝ,0≤M → (∀ j,UniformC1Bound (r j) M) →
      ∃ q : PhysicalSourcePair,CompactSmoothPair q ∧ PairSupported q C.region ∧
        physicalSourceMoment u q=physicalSourceMoment u r ∧
        (∀ j,UniformC1Bound (q j) (L*M)) ∧ BoundedPhysicallyCorrectable u U (r-q) (L*M) := by
  obtain ⟨Q,P,hP,hQ,hQs,hQm,hQb⟩ := bounded_physical_moments_in_open hu
    (B.region_open.inter C.region_open) hBC (inter_subset_left.trans B.region_subset) hD
  obtain ⟨Z,hZ,hZb⟩ := physical_source_moment_bound hu.continuous B.region_bounded
  obtain ⟨D,hDpos,solve⟩ := B.bounded_solver hu
  let L := (D+1)*(1+P*Z)
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨L,hL,?_⟩
  intro r hr hs M hM hb
  let q := Q (physicalSourceMoment u r)
  have hq : CompactSmoothPair q := hQ _
  have hqm : physicalSourceMoment u q=physicalSourceMoment u r := hQm _
  have hqb (j) : UniformC1Bound (q j) ((P*Z)*M) := (hQb _ j).mono
    ((mul_le_mul_of_nonneg_left (hZb r hs M hM (fun j x => (hb j x).1)) hP.le).trans_eq (by ring))
  have hsmall : (P*Z)*M≤L*M := by
    dsimp [L]
    nlinarith [mul_nonneg hP.le hZ.le,mul_nonneg hDpos.le (mul_nonneg hP.le hZ.le)]
  have hrq : CompactSmoothPair (r-q) := hr.sub hq
  have hsrc : physicalSourceMoment u (r-q)=0 := by
    rw [physicalSourceMoment_sub hu.continuous hr hq,hqm,sub_self]
  have hdif (j) : UniformC1Bound ((r-q) j) ((1+P*Z)*M) := by
    change UniformC1Bound (fun x => r j x-q j x) ((1+P*Z)*M)
    convert (hb j).sub ((hr j).1.differentiable (by simp)) ((hq j).1.differentiable (by simp)) (hqb j) using 1
    ring
  have hc := solve (r-q) hrq (hs.sub ((hQs _).mono inter_subset_left)) hsrc
    ((1+P*Z)*M) (by positivity) hdif
  refine ⟨q,hq,(hQs _).mono inter_subset_right,hqm,fun j => (hqb j).mono hsmall,hc.mono ?_⟩
  dsimp [L]
  nlinarith [mul_nonneg hP.le hZ.le,mul_nonneg (add_nonneg zero_le_one (mul_nonneg hP.le hZ.le)) hM]

lemma controlled_correction_boxes_cover
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {U : Set Coord3}
    (hU : IsOpen U) (hD : ∀ p∈U,Function.Surjective (fderiv ℝ u p)) :
    (⋃ B : ControlledCorrectionBox u U,B.region)=U := by
  apply Subset.antisymm
  · exact iUnion_subset fun B => B.region_subset
  · intro p hp
    obtain ⟨B,hB⟩ := exists_controlled_correction_box hu hU hp (hD p hp)
    exact mem_iUnion.mpr ⟨B,hB⟩

lemma controlled_correction_boxes_chain
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {U : Set Coord3}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hD : ∀ p∈U,Function.Surjective (fderiv ℝ u p)) (B C : ControlledCorrectionBox u U) :
    Relation.TransGen (fun P Q : ControlledCorrectionBox u U => (P.region∩Q.region).Nonempty) B C := by
  have hc : IsPreconnected (⋃ B : ControlledCorrectionBox u U,B.region) := by
    rwa [controlled_correction_boxes_cover hu hU hD]
  exact hc.transGen_of_iUnion (fun B => B.region_open) B C B.region_nonempty C.region_nonempty

theorem controlled_source_transport
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {U : Set Coord3}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hD : ∀ p∈U,Function.Surjective (fderiv ℝ u p)) (B C : ControlledCorrectionBox u U) :
    ∃ L : ℝ,0<L ∧ ∀ r : PhysicalSourcePair,CompactSmoothPair r → PairSupported r B.region →
      ∀ M : ℝ,0≤M → (∀ j,UniformC1Bound (r j) M) →
      ∃ q : PhysicalSourcePair,CompactSmoothPair q ∧ PairSupported q C.region ∧
        physicalSourceMoment u q=physicalSourceMoment u r ∧
        (∀ j,UniformC1Bound (q j) (L*M)) ∧ BoundedPhysicallyCorrectable u U (r-q) (L*M) := by
  have hp := controlled_correction_boxes_chain hu hU hUc hD B C
  induction hp with
  | single h => exact B.bounded_transfer hu hD _ h
  | @tail C D hpath hCD ih =>
    obtain ⟨L,hL,solve⟩ := ih
    obtain ⟨P,hP,step⟩ := C.bounded_transfer hu hD D hCD
    refine ⟨L+P*L,by positivity,?_⟩
    intro r hr hs M hM hb
    obtain ⟨q,hq,hqs,hqm,hqb,hqc⟩ := solve r hr hs M hM hb
    obtain ⟨s,hss,hssup,hsm,hsb,hsc⟩ := step q hq hqs (L*M) (mul_nonneg hL.le hM) hqb
    refine ⟨s,hss,hssup,hsm.trans hqm,fun j => (hsb j).mono ?_,?_⟩
    · nlinarith [mul_nonneg hL.le hM]
    · have he := hqc.add hu hsc
      rw [sub_add_sub_cancel] at he
      exact he.mono (by ring_nf; rfl)

end ScalarConductivity

end

end OAI
