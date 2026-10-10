import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteCuspEnergy

namespace OAI

/-! The global exterior inequality for actual compact smooth cubic
sections. The only remainder is mass on two explicit arithmetic compact
cores; no analytic estimate is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaFiniteCusps_cover :
    ∃ S T : Finset SL(2,Eisenstein),
      (∀ H : ℝ, cubicThetaQuotientCore S H∪(⋃ δ∈T,cubicThetaCuspNeighborhood δ H)=univ) ∧
      ∀ H : ℝ, 1≤H → (T : Set SL(2,Eisenstein)).PairwiseDisjoint
        (fun δ => cubicThetaCuspNeighborhood δ H) := by
  classical
  obtain ⟨S,hS⟩ := cubicThetaCuspNeighborhood_cover
  obtain ⟨T,_,hT,hdis⟩ := cubicThetaFiniteCusps_disjoint (S.image (fun δ => δ⁻¹))
  refine ⟨S,T,?_,hdis⟩
  intro H
  rw [← hT H]
  have he : (⋃ δ∈S,cubicThetaCuspNeighborhood δ⁻¹ H)=
      ⋃ δ∈S.image (fun δ => δ⁻¹),cubicThetaCuspNeighborhood δ H := by
    ext q
    constructor
    · intro hq
      obtain ⟨δ,hδ,hqδ⟩ := mem_iUnion₂.mp hq
      exact mem_iUnion₂.mpr ⟨δ⁻¹,Finset.mem_image.mpr ⟨δ,hδ,rfl⟩,hqδ⟩
    · intro hq
      obtain ⟨δ,hδ,hqδ⟩ := mem_iUnion₂.mp hq
      obtain ⟨σ,hσ,rfl⟩ := Finset.mem_image.mp hδ
      exact mem_iUnion₂.mpr ⟨σ,hσ,hqδ⟩
  rw [← he]
  exact hS H

theorem cubicThetaExterior_integral {ε : ℝ} (hε : 0<ε) :
    ∃ (S R : Finset SL(2,Eisenstein)) (B : ℝ), 0≤B ∧
      ∀ F : cubicThetaSmoothTests,
    (∫ q, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure)≤
      (1+ε)*(∫ q, cubicThetaQuotientEnergy F q ∂cubicThetaQuotientMeasure)+
      (∫ q in cubicThetaQuotientCore S 2, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure)+
      B*(∫ q in cubicThetaQuotientCore R 2, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure) := by
  classical
  obtain ⟨S,T,hcover,hdis⟩ := cubicThetaFiniteCusps_cover
  obtain ⟨R,B,hB,hcusp⟩ := cubicThetaCusp_exterior_mass hε
  refine ⟨S,R,T.card*B,mul_nonneg (Nat.cast_nonneg _) hB,?_⟩
  intro F
  have hm := cubicThetaFiniteCusps_mass_le S T (hcover 2) (hdis 2 (by norm_num)) F
  have he := cubicThetaFiniteCusps_energy_le T (hdis 1 (le_refl 1)) F
  have hs := Finset.sum_le_sum (s:=T) (fun δ hδ => hcusp δ F)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] at hs
  have hg := mul_le_mul_of_nonneg_left he (by positivity : 0≤1+ε)
  calc
    _ ≤ (∫ q in cubicThetaQuotientCore S 2, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure)+
        ((1+ε)*(∑ δ∈T,∫ q in cubicThetaCuspNeighborhood δ 1,
          cubicThetaQuotientEnergy F q ∂cubicThetaQuotientMeasure)+
        T.card*(B*(∫ q in cubicThetaQuotientCore R 2,
          cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure))) :=
      hm.trans (add_le_add le_rfl hs)
    _ ≤ (∫ q in cubicThetaQuotientCore S 2, cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure)+
        ((1+ε)*(∫ q, cubicThetaQuotientEnergy F q ∂cubicThetaQuotientMeasure)+
        T.card*(B*(∫ q in cubicThetaQuotientCore R 2,
          cubicThetaSectionNorm F q^2 ∂cubicThetaQuotientMeasure))) :=
      add_le_add le_rfl (add_le_add hg le_rfl)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
