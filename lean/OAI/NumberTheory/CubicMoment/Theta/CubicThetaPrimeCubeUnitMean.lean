import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalAffine
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeZeroMode

namespace OAI

/-! The second nontrivial character branch has zero constant mode for
any actual continuous periodic horizontal slice. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeUnitFourier_zero_eq {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) : cubicThetaPrimeCubeUnitFourier hp k 0=
      ∑' u : (Residues (p^(3-k.val)))ˣ,
        (cubicSymbol p (3*residueRepresentative (p^(3-k.val))
          (u:Residues (p^(3-k.val)))))^k.val := by
  unfold cubicThetaPrimeCubeUnitFourier
  apply tsum_congr
  intro u
  rw [map_zero,zero_mul,AddChar.map_zero_eq_one,mul_one]

lemma cubicThetaPrimeCubeSquareCharacter_sum {p : Eisenstein} (hp : primaryPrime p) :
    (∑' u : (Residues p)ˣ,(cubicSymbol p (3*residueRepresentative p (u:Residues p)))^2)=0 := by
  have he := cubicThetaPrimeCubeUnitFourier_zeroFrequency hp (⟨2,by decide⟩:Fin 3) (by decide)
  rw [cubicThetaPrimeCubeUnitFourier_zero_eq] at he
  have hd : 3-(⟨2,by decide⟩:Fin 3).val=1 := rfl
  rw [hd,pow_one] at he
  exact he

theorem cubicThetaPrimeCubeSquareCharacter_mean {p : Eisenstein} (hp : primaryPrime p)
    (f : C(ℂ,ℂ)) (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    (b : (Residues p)ˣ → ℂ) :
    (∫ z in cubicThetaHorizontalCell,
      ∑' u : (Residues p)ˣ,(cubicSymbol p (3*residueRepresentative p (u:Residues p)))^2*
        f ((p:ℂ)*z+b u))=0 := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Fintype (Residues p)ˣ := Fintype.ofFinite _
  simp_rw [tsum_fintype]
  rw [integral_finsetSum Finset.univ (fun u _ =>
    (cubicThetaHorizontal_affine_integrable f (p:ℂ) (b u)).const_mul _)]
  simp_rw [integral_const_mul,cubicThetaHorizontal_affine_integral f hf hp.2.ne_zero]
  have hc : (∑ u : (Residues p)ˣ,
      (cubicSymbol p (3*residueRepresentative p (u:Residues p)))^2)=0 := by
    simpa only [tsum_fintype] using cubicThetaPrimeCubeSquareCharacter_sum hp
  rw [←Finset.sum_mul,hc,zero_mul]

theorem cubicThetaPrimeCubeSquareCharacter_mean_of_eq {p q : Eisenstein}
    (hp : primaryPrime p) (hq : q=p) (f : C(ℂ,ℂ))
    (hf : ∀ (w : Eisenstein) z,f (z+3*(w:ℂ))=f z)
    (b : (Residues q)ˣ → ℂ) :
    (∫ z in cubicThetaHorizontalCell,
      ∑' u : (Residues q)ˣ,(cubicSymbol p (3*residueRepresentative q (u:Residues q)))^2*
        f ((p:ℂ)*z+b u))=0 := by
  subst q
  exact cubicThetaPrimeCubeSquareCharacter_mean hp f hf b

end CubicFirstMoment

end

end OAI
