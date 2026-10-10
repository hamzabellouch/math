import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeDilationNorm
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteEnergySum
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1Energy

namespace OAI

/-! First differentiability of the literal cubed-prime Hecke trace.
Every summand is the actual Mobius pullback, including its cubic phase. -/
noncomputable section
open Set
namespace CubicFirstMoment

def cubicThetaPrimeCubeHeckeMatrix {p : Eisenstein} (hp : primaryPrime p)
    (t : cubicThetaPrimeCubeTransversal p) :=
  cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)*cubicThetaPrincipalComplex t.val

def cubicThetaPrimeCubeHeckeCoordinate {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (t : cubicThetaPrimeCubeTransversal p) (y : ℂ × ℝ) : ℂ :=
  star (cubicThetaKubotaValue t.val)*
    cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaPrimeCubeHeckeMatrix hp t) y)

lemma cubicThetaPrimeCubeHecke_function {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaSectionFunction (cubicThetaPrimeCubeHecke hp F) y=
      ∑' t : cubicThetaPrimeCubeTransversal p,cubicThetaPrimeCubeHeckeCoordinate hp F t y := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  rw [cubicThetaSectionFunction_apply _ hy]
  rw [cubicThetaPrimeCubeHecke_apply hp F (⟨y,hy⟩ : CubicThetaPoint)]
  apply tsum_congr
  intro t
  unfold cubicThetaPrimeCubeHeckeCoordinate
  rw [cubicThetaSectionFunction_apply _ (cubicThetaMobius_height_pos _ hy)]
  exact congrArg (fun x : CubicThetaPoint => star (cubicThetaKubotaValue t.val)*F.val x)
    (mul_smul (β:=CubicThetaPoint) (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))
      (cubicThetaPrincipalComplex t.val) (⟨y,hy⟩ : CubicThetaPoint)).symm

lemma cubicThetaPrimeCubeHeckeCoordinate_c1 {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (t : cubicThetaPrimeCubeTransversal p) :
    ContDiffOn ℝ 1 (cubicThetaPrimeCubeHeckeCoordinate hp F t) {y : ℂ × ℝ | 0<y.2} := by
  have hm : ContDiffOn ℝ 1 (cubicThetaMobius (cubicThetaPrimeCubeHeckeMatrix hp t))
      {y : ℂ × ℝ | 0<y.2} := fun _ hy =>
    ((cubicThetaMobius_contDiffAt _ hy).of_le (by simp)).contDiffWithinAt
  exact contDiffOn_const.mul (hF.comp hm (fun _ hy => cubicThetaMobius_height_pos _ hy))

theorem cubicThetaPrimeCubeHecke_c1 {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ 1 (cubicThetaSectionFunction (cubicThetaPrimeCubeHecke hp F))
      {y : ℂ × ℝ | 0<y.2} := by
  let : Finite (cubicThetaPrimeCubeTransversal p) := cubicThetaPrimeCubeTransversal_finite hp
  let : Fintype (cubicThetaPrimeCubeTransversal p) := Fintype.ofFinite _
  have hs := ContDiffOn.sum (s:=Finset.univ)
    (fun t _ => cubicThetaPrimeCubeHeckeCoordinate_c1 hp F hF t)
  apply hs.congr
  intro y hy
  simpa only [tsum_fintype] using cubicThetaPrimeCubeHecke_function hp F hy

end CubicFirstMoment

end

end OAI
