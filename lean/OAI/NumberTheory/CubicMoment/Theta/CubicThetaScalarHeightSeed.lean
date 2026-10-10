import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRankinConvergence

namespace OAI

/-! The sharp scalar height cutoff has an actual half-open strip seed. -/
noncomputable section
open Set
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaScalarHeightWeight (s v : ℝ) : ℝ := if v≤1 then v^s else 0

def cubicThetaScalarHeightSeed (s : ℝ) (p : CubicThetaPoint) : ℝ :=
  if p.val.1∈cubicThetaHorizontalCell then cubicThetaScalarHeightWeight s p.val.2 else 0

lemma cubicThetaScalarHeightWeight_nonneg {s v : ℝ} (hv : 0<v) :
    0≤cubicThetaScalarHeightWeight s v := by
  unfold cubicThetaScalarHeightWeight
  split_ifs
  · exact Real.rpow_nonneg hv.le _
  · exact le_rfl

lemma cubicThetaScalarHeightSeed_nonneg (s : ℝ) (p : CubicThetaPoint) :
    0≤cubicThetaScalarHeightSeed s p := by
  unfold cubicThetaScalarHeightSeed
  split_ifs
  · exact cubicThetaScalarHeightWeight_nonneg p.property
  · exact le_rfl

lemma cubicThetaScalarHeightSeed_translate (s : ℝ) (w : Eisenstein) (p : CubicThetaPoint) :
    cubicThetaScalarHeightSeed s (cubicThetaPrincipalTranslation w • p)=
      if p.val.1+3*(w:ℂ)∈cubicThetaHorizontalCell then cubicThetaScalarHeightWeight s p.val.2 else 0 := by
  unfold cubicThetaScalarHeightSeed
  have h := cubicThetaPrincipalTranslation_coordinates w p
  change (cubicThetaPrincipalTranslation w • p).val=(p.val.1+3*(w:ℂ),p.val.2) at h
  rw [h]

lemma cubicThetaScalarHeightSeed_translation_hasSum (s : ℝ) (p : CubicThetaPoint) :
    HasSum (fun w : Eisenstein => cubicThetaScalarHeightSeed s (cubicThetaPrincipalTranslation w • p))
      (cubicThetaScalarHeightWeight s p.val.2) := by
  obtain ⟨w,hw,huniq⟩ := cubicThetaHorizontalCell_unique_eisenstein p.val.1
  have hzero : ∀ v≠w,cubicThetaScalarHeightSeed s (cubicThetaPrincipalTranslation v • p)=0 := by
    intro v hv
    rw [cubicThetaScalarHeightSeed_translate]
    exact ite_eq_right (fun hm => hv (huniq v hm))
  have h := hasSum_single w hzero
  rw [cubicThetaScalarHeightSeed_translate,ite_eq_left hw] at h
  exact h

lemma cubicThetaScalarHeightSeed_group_summable {s : ℝ} (hs : 2<s) (p : CubicThetaPoint) :
    Summable (fun g : cubicThetaPrincipalGroup => cubicThetaScalarHeightSeed s (g • p)) := by
  let e : (CubicThetaBottomRow × Eisenstein) ≃ cubicThetaPrincipalGroup :=
    (Equiv.prodComm _ _).trans cubicThetaRowTranslationEquiv
  apply e.summable_iff.mp
  apply (summable_prod_of_nonneg (fun rw => cubicThetaScalarHeightSeed_nonneg s (e rw • p))).mpr
  constructor
  · intro r
    change Summable (fun w : Eisenstein => cubicThetaScalarHeightSeed s
      ((cubicThetaPrincipalTranslation w*r.completion) • p))
    simp_rw [mul_smul]
    exact (cubicThetaScalarHeightSeed_translation_hasSum s (r.completion • p)).summable
  · have hh (r : CubicThetaBottomRow) : (r.completion • p).val.2=r.height p.val := by
      change (cubicThetaBottomRow r.completion).height p.val=_
      rw [r.completion_row]
    change Summable (fun r : CubicThetaBottomRow => ∑' w : Eisenstein,
      cubicThetaScalarHeightSeed s ((cubicThetaPrincipalTranslation w*r.completion) • p))
    simp_rw [mul_smul,(cubicThetaScalarHeightSeed_translation_hasSum s _).tsum_eq,hh]
    exact cubicThetaScalarHeightCutoff_summable p.property hs

theorem cubicThetaScalarHeightSeed_group_sum {s : ℝ} (hs : 2<s) (p : CubicThetaPoint) :
    (∑' g : cubicThetaPrincipalGroup,cubicThetaScalarHeightSeed s (g • p))=
      cubicThetaScalarHeightCutoff p.val s := by
  let e : (CubicThetaBottomRow × Eisenstein) ≃ cubicThetaPrincipalGroup :=
    (Equiv.prodComm _ _).trans cubicThetaRowTranslationEquiv
  let f : cubicThetaPrincipalGroup → ℝ := fun g => cubicThetaScalarHeightSeed s (g • p)
  have hsum := e.summable_iff.mpr (cubicThetaScalarHeightSeed_group_summable hs p)
  calc
    _ = ∑' rw : CubicThetaBottomRow × Eisenstein,f (e rw) := (e.tsum_eq f).symm
    _ = ∑' r : CubicThetaBottomRow,∑' w : Eisenstein,f (e (r,w)) := hsum.tsum_prod
    _ = ∑' r : CubicThetaBottomRow,cubicThetaScalarHeightWeight s (r.height p.val) := by
      apply tsum_congr
      intro r
      change (∑' w : Eisenstein,cubicThetaScalarHeightSeed s
        ((cubicThetaPrincipalTranslation w*r.completion) • p))=_
      simp_rw [mul_smul]
      rw [(cubicThetaScalarHeightSeed_translation_hasSum s _).tsum_eq]
      have hh : (r.completion • p).val.2=r.height p.val := by
        change (cubicThetaBottomRow r.completion).height p.val=_
        rw [r.completion_row]
      rw [hh]
    _ = _ := rfl

end CubicFirstMoment

end

end OAI
