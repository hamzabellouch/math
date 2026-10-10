import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalTranslation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueCount

namespace OAI

/-! The finite residue coordinates for the sublattice used by a horizontal
Hecke dilation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalLattice_bijective {a : Eisenstein} (ha : a≠0) :
    Function.Bijective (fun mr : Eisenstein × Residues a =>
      a*mr.1+residueRepresentative a mr.2) := by
  constructor
  · rintro ⟨m,r⟩ ⟨n,s⟩ he
    have hr : r=s := by
      have hd : a∣residueRepresentative a r-residueRepresentative a s := by
        refine ⟨n-m,?_⟩
        linear_combination he
      simpa only [residueRepresentative_spec] using residue_eq_of_dvd_sub hd
    subst s
    have hm : m=n := mul_left_cancel₀ ha (add_right_cancel he)
    subst n
    rfl
  · intro b
    let r := Ideal.Quotient.mk (modulus a) b
    have hd : a∣b-residueRepresentative a r := by
      apply dvd_sub_comm.mp
      exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (residueRepresentative_spec a r))
    obtain ⟨m,hm⟩ := hd
    refine ⟨(m,r),?_⟩
    dsimp
    linear_combination -hm

def cubicThetaHorizontalLatticeEquiv {a : Eisenstein} (ha : a≠0) :
    (Eisenstein × Residues a) ≃ Eisenstein :=
  Equiv.ofBijective _ (cubicThetaHorizontalLattice_bijective ha)

def CubicThetaScaledPeriodGroup (_a : Eisenstein) := Multiplicative Eisenstein
instance (_a : Eisenstein) : CommGroup (CubicThetaScaledPeriodGroup _a) :=
  inferInstanceAs (CommGroup (Multiplicative Eisenstein))
instance (_a : Eisenstein) : Countable (CubicThetaScaledPeriodGroup _a) := by
  change Countable Eisenstein
  exact coordinatesEquiv.symm.injective.countable

instance cubicThetaScaledPeriodGroup_action (a : Eisenstein) :
    MulAction (CubicThetaScaledPeriodGroup a) ℂ where
  smul g z := z+3*(a:ℂ)*((Multiplicative.toAdd g:Eisenstein):ℂ)
  one_smul z := by change z+3*(a:ℂ)*((0:Eisenstein):ℂ)=z; simp
  mul_smul g h z := by
    change z+3*(a:ℂ)*((Multiplicative.toAdd g+Multiplicative.toAdd h:Eisenstein):ℂ)=
      (z+3*(a:ℂ)*((Multiplicative.toAdd h:Eisenstein):ℂ))+
        3*(a:ℂ)*((Multiplicative.toAdd g:Eisenstein):ℂ)
    push_cast
    ring

instance cubicThetaScaledPeriodGroup_continuous (a : Eisenstein) :
    ContinuousConstSMul (CubicThetaScaledPeriodGroup a) ℂ where
  continuous_const_smul g := by
    change Continuous (fun z : ℂ => z+3*(a:ℂ)*((Multiplicative.toAdd g:Eisenstein):ℂ))
    fun_prop

instance cubicThetaScaledPeriodGroup_measure (a : Eisenstein) :
    SMulInvariantMeasure (CubicThetaScaledPeriodGroup a) ℂ volume where
  measure_preimage_smul g A _ := by
    change volume ((fun z : ℂ => z+(3*(a:ℂ)*((Multiplicative.toAdd g:Eisenstein):ℂ))) ⁻¹' A)=volume A
    exact measure_preimage_add_right volume _ A

def cubicThetaHorizontalScaledCell (a : Eisenstein) : Set ℂ :=
  (fun z : ℂ => (a:ℂ)*z) '' cubicThetaHorizontalCell

lemma cubicThetaHorizontalScaledCell_fundamental {a : Eisenstein} (ha : a≠0) :
    IsFundamentalDomain (CubicThetaScaledPeriodGroup a) (cubicThetaHorizontalScaledCell a) volume := by
  have haC : (a:ℂ)≠0 := fun he => ha (Subtype.ext he)
  have hqmp : Measure.QuasiMeasurePreserving (fun z : ℂ => (a:ℂ)⁻¹*z) volume volume := by
    refine ⟨by fun_prop,?_⟩
    rw [complexMul_map_volume _ (inv_ne_zero haC)]
    exact Measure.smul_absolutelyContinuous
  apply IsFundamentalDomain.image_of_equiv (H := CubicThetaScaledPeriodGroup a)
    (cubicThetaHorizontalCell_fundamental volume)
    (complexMulEquiv (a:ℂ) haC).toEquiv
    hqmp
    (show CubicThetaScaledPeriodGroup a ≃ CubicThetaPeriodGroup from Equiv.refl _)
  intro g z
  change (a:ℂ)*(z+3*((Multiplicative.toAdd g:Eisenstein):ℂ))=
    (a:ℂ)*z+3*(a:ℂ)*((Multiplicative.toAdd g:Eisenstein):ℂ)
  ring

end CubicFirstMoment

end

end OAI
