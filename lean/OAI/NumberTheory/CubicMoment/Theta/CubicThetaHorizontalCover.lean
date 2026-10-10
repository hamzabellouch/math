import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalLattice

namespace OAI

/-! A disjoint finite union of period cells for the scaled horizontal lattice. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaHorizontalCover (a : Eisenstein) : Set ℂ :=
  ⋃ r : Residues a, (fun z : ℂ => z-3*(residueRepresentative a r:ℂ)) '' cubicThetaHorizontalCell

lemma cubicThetaHorizontalCover_measurable {a : Eisenstein} (ha : a≠0) :
    MeasurableSet (cubicThetaHorizontalCover a) := by
  let : Finite (Residues a) := finite_residues ha
  apply MeasurableSet.iUnion
  intro r
  exact (Homeomorph.subRight (3*(residueRepresentative a r:ℂ))).measurableEmbedding.measurableSet_image'
    cubicThetaHorizontalCell_measurable

lemma cubicThetaHorizontalCover_unique {a : Eisenstein} (ha : a≠0) (z : ℂ) :
    ∃! g : CubicThetaScaledPeriodGroup a,g • z∈cubicThetaHorizontalCover a := by
  obtain ⟨w,hw,hwu⟩ := cubicThetaHorizontalCell_unique z
  let mr := (cubicThetaHorizontalLatticeEquiv ha).symm (Multiplicative.toAdd w)
  have he : a*mr.1+residueRepresentative a mr.2=Multiplicative.toAdd w :=
    (cubicThetaHorizontalLatticeEquiv ha).apply_symm_apply _
  refine ⟨Multiplicative.ofAdd mr.1,?_,?_⟩
  · refine mem_iUnion.mpr ⟨mr.2, z+3*((Multiplicative.toAdd w:Eisenstein):ℂ), hw, ?_⟩
    change z+3*((Multiplicative.toAdd w:Eisenstein):ℂ)-3*(residueRepresentative a mr.2:ℂ)=
      z+3*(a:ℂ)*(mr.1:ℂ)
    rw [←he]
    push_cast
    ring
  · intro g hg
    obtain ⟨r,y,hy,hyg⟩ := mem_iUnion.mp hg
    have hwy : Multiplicative.ofAdd (a*Multiplicative.toAdd g+residueRepresentative a r)=w := by
      apply hwu
      convert hy using 1
      change z+3*((a*Multiplicative.toAdd g+residueRepresentative a r:Eisenstein):ℂ)=y
      change y-3*(residueRepresentative a r:ℂ)=z+3*(a:ℂ)*((Multiplicative.toAdd g:Eisenstein):ℂ) at hyg
      push_cast
      linear_combination -hyg
    have hpair : (Multiplicative.toAdd g,r)=mr := by
      apply (cubicThetaHorizontalLatticeEquiv ha).injective
      exact (congrArg (fun v : CubicThetaPeriodGroup => (Multiplicative.toAdd v:Eisenstein)) hwy).trans he.symm
    exact congrArg (fun v : Eisenstein × Residues a => Multiplicative.ofAdd v.1) hpair

lemma cubicThetaHorizontalCover_fundamental {a : Eisenstein} (ha : a≠0) :
    IsFundamentalDomain (CubicThetaScaledPeriodGroup a) (cubicThetaHorizontalCover a) volume :=
  IsFundamentalDomain.mk' (cubicThetaHorizontalCover_measurable ha).nullMeasurableSet
    (cubicThetaHorizontalCover_unique ha)

lemma cubicThetaHorizontalCover_disjoint (a : Eisenstein) :
    Pairwise (fun r s : Residues a =>
      Disjoint ((fun z : ℂ => z-3*(residueRepresentative a r:ℂ)) '' cubicThetaHorizontalCell)
        ((fun z : ℂ => z-3*(residueRepresentative a s:ℂ)) '' cubicThetaHorizontalCell)) := by
  intro r s hrs
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
  have hw : (Multiplicative.ofAdd (residueRepresentative a s) : CubicThetaPeriodGroup)=
      Multiplicative.ofAdd (residueRepresentative a r) := by
    apply (cubicThetaHorizontalCell_unique z).unique
    · change z+3*(residueRepresentative a s:ℂ)∈cubicThetaHorizontalCell
      have h : z+3*(residueRepresentative a s:ℂ)=y := by linear_combination -hyz
      rwa [h]
    · change z+3*(residueRepresentative a r:ℂ)∈cubicThetaHorizontalCell
      have h : z+3*(residueRepresentative a r:ℂ)=x := by linear_combination -hxz
      rwa [h]
  have he : residueRepresentative a s=residueRepresentative a r :=
    congrArg (fun v : CubicThetaPeriodGroup => (Multiplicative.toAdd v:Eisenstein)) hw
  apply hrs
  simpa only [residueRepresentative_spec] using
    (congrArg (Ideal.Quotient.mk (modulus a)) he).symm

end CubicFirstMoment

end

end OAI
