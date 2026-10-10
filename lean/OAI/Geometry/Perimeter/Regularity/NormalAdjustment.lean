import OAI.Geometry.Perimeter.Regularity.NormalCoordinates

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary
variable {n : ℕ}

theorem normalPlane_finrank {v : Euc n} (hv : ‖v‖=1) :
    Module.finrank ℝ (normalPlane v)=n-1 := by
  have hn : v≠0 := by intro hzero; simp [hzero] at hv
  have h := (ℝ ∙ v).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hn,finrank_euclideanSpace,Fintype.card_fin] at h
  dsimp [normalPlane]
  omega

def normalPlaneEuclideanChart {v : Euc n} (hv : ‖v‖=1) : Euc (n-1) ≃ₗᵢ[ℝ] normalPlane v :=
  ((stdOrthonormalBasis ℝ (normalPlane v)).reindex (finCongr (normalPlane_finrank hv))).repr.symm

theorem exists_normal_rotation {v w : Euc n} (h : ‖v‖=‖w‖) :
    ∃ e : Euc n ≃ₗᵢ[ℝ] Euc n, e v=w :=
  ⟨(ℝ ∙ (v-w))ᗮ.reflection,Submodule.reflection_sub h⟩

theorem dual_of_normal_linear {v : Euc n} {L : Euc n →L[ℝ] ℝ} (hL : L v=0) :
    let u := (InnerProductSpace.toDual ℝ (Euc n)).symm L
    ‖u‖=‖L‖ ∧ inner ℝ v u=0 ∧ ∀ x, inner ℝ u x=L x := by
  constructor
  · exact (InnerProductSpace.toDual ℝ (Euc n)).symm.norm_map L
  constructor
  · rw [real_inner_comm,InnerProductSpace.toDual_symm_apply,hL]
  · intro x; exact InnerProductSpace.toDual_symm_apply

theorem exists_adjusted_unit_normal {v : Euc n} (hv : ‖v‖=1)
    (L : Euc n →L[ℝ] ℝ) (hLv : L v=0) {a : ℝ} (ha : 0≤a) :
    ∃ w : Euc n, ‖w‖=1 ∧ ‖w-v‖≤2*a*‖L‖ ∧
      ∀ x, |inner ℝ w x|≤|inner ℝ v x-a*L x| := by
  let u := (InnerProductSpace.toDual ℝ (Euc n)).symm L
  have hu := dual_of_normal_linear hLv
  change ‖u‖=‖L‖ ∧ inner ℝ v u=0 ∧ ∀ x, inner ℝ u x=L x at hu
  let z := v-a•u
  have hzsq : ‖z‖^2=1+a^2*‖u‖^2 := by
    dsimp [z]
    rw [norm_sub_sq_real,hv,real_inner_smul_right,hu.2.1,mul_zero,mul_zero,sub_zero,
      norm_smul,Real.norm_of_nonneg ha]
    ring
  have hzn : 1≤‖z‖ := by nlinarith [norm_nonneg z,sq_nonneg a,sq_nonneg ‖u‖]
  have hz : 0<‖z‖ := lt_of_lt_of_le zero_lt_one hzn
  let w := ‖z‖⁻¹•z
  have hwn : ‖w‖=1 := by rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hz.le),inv_mul_cancel₀ hz.ne']
  have hdist : ‖w-z‖=‖z‖-1 := by
    have he : w-z=(‖z‖⁻¹-1)•z := by dsimp [w]; rw [sub_smul,one_smul]
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr ((inv_le_one₀ hz).mpr hzn))]
    field_simp
    ring
  have hzv : ‖z-v‖=a*‖L‖ := by
    have he : z-v=-(a•u) := by dsimp [z]; abel
    rw [he,norm_neg,norm_smul,Real.norm_of_nonneg ha,hu.1]
  refine ⟨w,hwn,?_,?_⟩
  · have hrev := norm_sub_norm_le z v
    rw [hv,hzv] at hrev
    have htri := norm_sub_le w z
    have hh := norm_sub_le w v
    calc
      ‖w-v‖ ≤ ‖w-z‖+‖z-v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖z‖-1+a*‖L‖ := by rw [hdist,hzv]
      _ ≤ 2*a*‖L‖ := by linarith
  · intro x
    have he : inner ℝ w x=‖z‖⁻¹*(inner ℝ v x-a*L x) := by
      dsimp [w,z]
      rw [real_inner_smul_left,inner_sub_left,real_inner_smul_left,hu.2.2]
    rw [he,abs_mul,abs_of_nonneg (inv_nonneg.mpr hz.le)]
    exact mul_le_of_le_one_left (abs_nonneg _) ((inv_le_one₀ hz).mpr hzn)

end RPISingularHarnack

end

end OAI
