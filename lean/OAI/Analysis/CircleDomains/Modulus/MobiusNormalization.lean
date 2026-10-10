import OAI.Analysis.CircleDomains.Uniformization.ConformalComposition

namespace OAI

/-!
# Concrete Möbius normalizations

Affine changes and inversion are homeomorphisms of the concrete sphere.
Their matrix actions agree with the projective-line action used in the
definition of round disks.
-/

open Set Filter Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

def affineHomeomorph (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ where
  toFun z := a * z + b
  invFun z := (z - b) / a
  left_inv z := by dsimp; field_simp; ring
  right_inv z := by dsimp; field_simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def affineSphere (a b : ℂ) (ha : a ≠ 0) : Sphere ≃ₜ Sphere :=
  (affineHomeomorph a b ha).onePointCongr

def affineMobius (a b : ℂ) (ha : a ≠ 0) : Mobius :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, 1] (by simpa using ha)

def inversionMobius : Mobius :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by norm_num)

theorem affineSphere_eq_smul (a b : ℂ) (ha : a ≠ 0) (p : Sphere) :
    affineSphere a b ha p = affineMobius a b ha • p := by
  cases p using OnePoint.rec with
  | infty => simp [affineSphere, OnePoint.smul_infty_eq_ite, affineMobius]
  | coe z => simp [affineSphere, affineHomeomorph, OnePoint.smul_some_eq_ite, affineMobius]

theorem inversion_eq_smul (p : Sphere) : CannonMobius.inversion p = inversionMobius • p := by
  change CannonMobius.inv p = inversionMobius • p
  cases p using OnePoint.rec with
  | infty => simp [OnePoint.smul_infty_eq_ite, inversionMobius]
  | coe z =>
    by_cases hz : z = 0
    · simp [hz, OnePoint.smul_some_eq_ite, inversionMobius]
    · simp [hz, OnePoint.smul_some_eq_ite, inversionMobius,
        CannonMobius.inv, div_eq_mul_inv]

theorem isRoundClosedDisk_image_mobius {K : Set Sphere} (hK : IsRoundClosedDisk K)
    (M : Mobius) : IsRoundClosedDisk ((fun p : Sphere => M • p) '' K) := by
  obtain ⟨N, rfl⟩ := hK
  refine ⟨M * N, ?_⟩
  rw [Set.image_image]
  congr 1
  funext p
  exact (mul_smul M N p).symm

end CircleDomainRigidity

end

end OAI
