import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularUniqueness
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace OAI

/-! Regular normalization at the origin forces independence at every positive matching radius. -/

open Set Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralRegularField_add (d : ℕ) (A B cp cm : ℂ) (r : ℝ) (Z W : E₄) :
    spectralRegularField d A B cp cm r (Z+W)=
      spectralRegularField d A B cp cm r Z+spectralRegularField d A B cp cm r W := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [spectralRegularField,Prod.fst_add,Prod.snd_add]
  all_goals ring

theorem spectralRegularField_smul (d : ℕ) (A B cp cm : ℂ) (r : ℝ) (a : ℂ) (Z : E₄) :
    spectralRegularField d A B cp cm r (a • Z)=a • spectralRegularField d A B cp cm r Z := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [spectralRegularField,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  all_goals ring

theorem spectralRegular_zero_at_origin (d : ℕ) (A B : ℝ →ᵇ ℂ) (cp cm : ℂ)
    (Z : ℝ → E₄) (R : ℝ) (hR : 0 < R) (hZ : Continuous Z)
    (hD : ∀ r ∈ Ioc 0 R, HasDerivAt Z (spectralRegularField d (A r) (B r) cp cm r (Z r)) r)
    (hz : Z R=0) : Z 0=0 := by
  have hzero (r : ℝ) (hr : r ∈ Ioc 0 R) : Z r=0 :=
    spectralRegular_zero_on_annulus d A B cp cm Z r R hr.1 hZ.continuousOn
      (fun s hs => hD s ⟨hr.1.trans_le hs.1,hs.2⟩) hz r ⟨le_rfl,hr.2⟩
  have ht : Tendsto Z (nhdsWithin 0 (Ioi 0)) (nhds (0 : E₄)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hR)] with r hr hrR
    exact (hzero r ⟨hr,hrR.le⟩).symm
  exact tendsto_nhds_unique (hZ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ht

theorem spectralRegular_coefficients_at_point (d : ℕ) (A B : ℝ →ᵇ ℂ) (cp cm : ℂ)
    (Yp Ym : ℝ → E₄) (R : ℝ) (hR : 0 < R) (hYp : Continuous Yp) (hYm : Continuous Ym)
    (hDp : ∀ r ∈ Ioc 0 R, HasDerivAt Yp (spectralRegularField d (A r) (B r) cp cm r (Yp r)) r)
    (hDm : ∀ r ∈ Ioc 0 R, HasDerivAt Ym (spectralRegularField d (A r) (B r) cp cm r (Ym r)) r)
    (hp : Yp 0=((1,0),(0,0))) (hm : Ym 0=((0,0),(1,0)))
    (a b : ℂ) (hz : a • Yp R+b • Ym R=0) : a=0 ∧ b=0 := by
  let Z := fun r => a • Yp r+b • Ym r
  have hDZ : ∀ r ∈ Ioc 0 R, HasDerivAt Z (spectralRegularField d (A r) (B r) cp cm r (Z r)) r := by
    intro r hr
    apply (((hDp r hr).const_smul a).add ((hDm r hr).const_smul b)).congr_deriv
    dsimp only [Z]
    rw [spectralRegularField_add,spectralRegularField_smul,spectralRegularField_smul]
  have hzero := spectralRegular_zero_at_origin d A B cp cm Z R hR
    ((hYp.const_smul a).add (hYm.const_smul b)) hDZ hz
  have he : a • ((1,0),(0,0)) + b • ((0,0),(1,0))=(0 : E₄) := by
    simpa only [Z,hp,hm] using hzero
  exact ⟨by simpa using congrArg (fun z : E₄ => z.1.1) he,
    by simpa using congrArg (fun z : E₄ => z.2.1) he⟩

theorem spectralRegular_at_linearIndependent (d : ℕ) (A B : ℝ →ᵇ ℂ) (cp cm : ℂ)
    (Yp Ym : ℝ → E₄) (R : ℝ) (hR : 0 < R) (hYp : Continuous Yp) (hYm : Continuous Ym)
    (hDp : ∀ r ∈ Ioc 0 R, HasDerivAt Yp (spectralRegularField d (A r) (B r) cp cm r (Yp r)) r)
    (hDm : ∀ r ∈ Ioc 0 R, HasDerivAt Ym (spectralRegularField d (A r) (B r) cp cm r (Ym r)) r)
    (hp : Yp 0=((1,0),(0,0))) (hm : Ym 0=((0,0),(1,0))) :
    LinearIndependent ℂ ![Yp R,Ym R] := by
  rw [linearIndependent_fin2]
  constructor
  · change Ym R ≠ 0
    intro hz
    have he := spectralRegular_coefficients_at_point d A B cp cm Yp Ym R hR hYp hYm hDp hDm hp hm
      0 1 (by simp [hz])
    exact one_ne_zero he.2
  · intro a ha
    change a • Ym R=Yp R at ha
    have he := spectralRegular_coefficients_at_point d A B cp cm Yp Ym R hR hYp hYm hDp hDm hp hm
      (-1) a (by rw [ha]; simp)
    exact (neg_ne_zero.mpr one_ne_zero) he.1

end DefocusingNLS

end OAI
