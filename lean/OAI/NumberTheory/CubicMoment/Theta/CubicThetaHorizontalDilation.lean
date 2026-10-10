import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalCover

namespace OAI

/-! Exact integration over a finite horizontal lattice cover and its dilated
fundamental cell. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalCover_integral {a : Eisenstein} (ha : a≠0)
    (f : ℂ → ℂ) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    (hi : IntegrableOn f cubicThetaHorizontalCell) :
    (∫ z in cubicThetaHorizontalCover a,f z)=
      (Nat.card (Residues a):ℂ)*(∫ z in cubicThetaHorizontalCell,f z) := by
  let : Finite (Residues a) := finite_residues ha
  let : Fintype (Residues a) := Fintype.ofFinite _
  have hmeas (r : Residues a) :
      MeasurableSet ((fun z : ℂ => z-3*(residueRepresentative a r:ℂ)) '' cubicThetaHorizontalCell) :=
    (Homeomorph.subRight _).measurableEmbedding.measurableSet_image' cubicThetaHorizontalCell_measurable
  have hint (r : Residues a) :
      IntegrableOn f ((fun z : ℂ => z-3*(residueRepresentative a r:ℂ)) '' cubicThetaHorizontalCell) := by
    have hp (g : CubicThetaPeriodGroup) (z : ℂ) : f (g • z)=f z := hf (Multiplicative.toAdd g) z
    have hh := ((cubicThetaHorizontalCell_fundamental volume).integrableOn_iff
      (cubicThetaHorizontalTranslated_fundamental (-3*(residueRepresentative a r:ℂ))) hp).mp hi
    simpa only [sub_eq_add_neg,neg_mul] using hh
  unfold cubicThetaHorizontalCover
  rw [integral_iUnion_fintype hmeas (cubicThetaHorizontalCover_disjoint a) hint]
  have he (r : Residues a) :
      (∫ z in (fun z : ℂ => z-3*(residueRepresentative a r:ℂ)) '' cubicThetaHorizontalCell,f z)=
        ∫ z in cubicThetaHorizontalCell,f z := by
    have ht := (cubicThetaHorizontalCell_fundamental volume).setIntegral_eq
      (cubicThetaHorizontalTranslated_fundamental (-3*(residueRepresentative a r:ℂ)))
      (fun g z => hf (Multiplicative.toAdd g) z)
    simpa only [sub_eq_add_neg,neg_mul] using ht.symm
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul]

lemma cubicThetaHorizontalScaledCell_integral {a : Eisenstein} (ha : a≠0)
    (f : ℂ → ℂ) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    (hi : IntegrableOn f cubicThetaHorizontalCell) :
    (∫ z in cubicThetaHorizontalScaledCell a,f z)=
      (Nat.card (Residues a):ℂ)*(∫ z in cubicThetaHorizontalCell,f z) := by
  have hp (g : CubicThetaScaledPeriodGroup a) (z : ℂ) : f (g • z)=f z := by
    change f (z+3*(a:ℂ)*((Multiplicative.toAdd g:Eisenstein):ℂ))=f z
    simpa only [Subalgebra.coe_mul,mul_assoc] using hf (a*Multiplicative.toAdd g) z
  exact ((cubicThetaHorizontalScaledCell_fundamental ha).setIntegral_eq
    (cubicThetaHorizontalCover_fundamental ha) hp).trans
    (cubicThetaHorizontalCover_integral ha f hf hi)

lemma cubicThetaHorizontal_mul_integral {a : Eisenstein} (ha : a≠0)
    (f : ℂ → ℂ) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    (hi : IntegrableOn f cubicThetaHorizontalCell) :
    (∫ z in cubicThetaHorizontalCell,f ((a:ℂ)*z))=∫ z in cubicThetaHorizontalCell,f z := by
  have haC : (a:ℂ)≠0 := fun he => ha (Subtype.ext he)
  have he := setIntegral_map_equiv (μ:=volume)
    (complexMulEquiv (a:ℂ) haC).toHomeomorph.toMeasurableEquiv f (cubicThetaHorizontalScaledCell a)
  have hpre : (complexMulEquiv (a:ℂ) haC) ⁻¹' cubicThetaHorizontalScaledCell a=
      cubicThetaHorizontalCell := by
    exact (complexMulEquiv (a:ℂ) haC).injective.preimage_image _
  change (∫ z in cubicThetaHorizontalScaledCell a,f z
    ∂Measure.map (fun z : ℂ => (a:ℂ)*z) volume)=
    ∫ z in (complexMulEquiv (a:ℂ) haC) ⁻¹' cubicThetaHorizontalScaledCell a,f ((a:ℂ)*z) at he
  rw [hpre,complexMul_map_volume _ haC,Measure.restrict_smul,integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (Complex.normSq_nonneg _)),
    cubicThetaHorizontalScaledCell_integral ha f hf hi,residues_card ha] at he
  have hn : (normNat a:ℝ)=Complex.normSq (a:ℂ) := normNat_cast a
  have hnC : (normNat a:ℂ)=((Complex.normSq (a:ℂ):ℝ):ℂ) := by exact_mod_cast hn
  rw [Complex.real_smul,hnC,←mul_assoc,←Complex.ofReal_mul,
    inv_mul_cancel₀ (Complex.normSq_pos.mpr haC).ne',Complex.ofReal_one,one_mul] at he
  exact he.symm

end CubicFirstMoment

end

end OAI
