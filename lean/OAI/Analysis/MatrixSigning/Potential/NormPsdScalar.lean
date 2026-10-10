import Mathlib
import OAI.Analysis.MatrixSigning.Potential.NormTCoord

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}
private local instance : NormedAddCommGroup (Vars d) := inferInstance
private local instance : NormedSpace ℝ (Vars d) := inferInstance
private local instance : TopologicalSpace (Vars d) :=
  (inferInstance : NormedAddCommGroup (Vars d)).toUniformSpace.toTopologicalSpace

lemma norm_psd_le_scalar (U : H d) (hU : U ∈ psdCone d) {r : ℝ} (hr : 0 ≤ r)
    (hUr : U ≤ r • Hermitian.one) : ‖U‖ ≤ r*((d:ℝ)+1) := by
  have ht := realTrace_mono hUr
  rw [Hermitian.realTrace_smul,Hermitian.realTrace_one] at ht
  have hh := inner_nonneg_of_psd U (r • Hermitian.one-U) hU
    ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hUr))
  rw [inner_sub_right,real_inner_smul_right U (Hermitian.one : H d) r,inner_one',real_inner_self_eq_norm_sq] at hh
  have hnt : ‖U‖^2 ≤ r^2*d := by nlinarith [mul_le_mul_of_nonneg_left ht hr]
  have hd : (0:ℝ)≤d := Nat.cast_nonneg d
  have hd' : (d:ℝ)≤(d+1)^2 := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hd' (sq_nonneg r)
  have hn : 0 ≤ r*((d:ℝ)+1) := by positivity
  nlinarith [norm_nonneg U]

lemma norm_pair_le_two (X Y : H d) {r : ℝ} (hX : ‖X‖ ≤ r) (hY : ‖Y‖ ≤ r) :
    ‖(pairEquiv d).symm (X,Y)‖ ≤ 2*r := by
  exact ((pairEquiv d).symm.toContinuousLinearMap.le_opNorm (X,Y)).trans
    (mul_le_mul norm_pairEquiv_symm_le (by simpa only [Prod.norm_def,max_le_iff] using And.intro hX hY)
      (norm_nonneg _) (by norm_num))

lemma norm_pack_bounds (z : Point d) (P Q : H d) {ε : ℝ} (hε : 0 < ε)
    (ht : z.1 ∈ Icc 0 100)
    (hX : z.2.1 ∈ pd d) (hY : z.2.2 ∈ pd d)
    (hXhi : z.2.1 ≤ (100/ε) • (Hermitian.one : H d))
    (hYhi : z.2.2 ≤ (100/ε) • (Hermitian.one : H d))
    (hP : P ∈ pd d) (hQ : Q ∈ pd d) (htr : realTrace P+realTrace Q=1) :
    ‖pack z P Q‖ ≤ 200+(200/ε)*((d:ℝ)+1) := by
  have hx := norm_psd_le_scalar z.2.1 hX.posSemidef (by positivity) hXhi
  have hy := norm_psd_le_scalar z.2.2 hY.posSemidef (by positivity) hYhi
  have hu := norm_pair_le_two z.2.1 z.2.2 hx hy
  have hp := (trace_pair_norm P Q hP.posSemidef hQ.posSemidef htr).2.2.1
  have hr : 0 ≤ (200/ε)*((d:ℝ)+1) := by positivity
  change max |z.1| (max ‖(pairEquiv d).symm z.2‖ ‖(pairEquiv d).symm (P,Q)‖) ≤ _
  rw [max_le_iff,max_le_iff,abs_of_nonneg ht.1]
  constructor
  · linarith [ht.2]
  constructor
  · have he : 2*((100/ε)*((d:ℝ)+1)) = (200/ε)*((d:ℝ)+1) := by ring
    rw [he] at hu
    linarith
  · linarith

theorem bounded_optimizer_data [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hηpos : ∀ X ∈ psdCone d,η X ∈ psdCone d) (hηsym : SymmetricMap η)
    {ε : ℝ} (hε : 0 < ε) (hSlo : -(100:ℝ) • (Hermitian.one : H d) ≤ S)
    (hShi : S ≤ (100:ℝ) • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible S η) (hz100 : objective ε z ≤ 100)
    (hmin : ∀ w ∈ feasible S η,objective ε z ≤ objective ε w) :
    ∃ P Q : H d, ∃ J : Vars d ≃L[ℝ] Vars d,
      P ∈ pd d ∧ Q ∈ pd d ∧ ‖P‖ ≤ 1 ∧ ‖Q‖ ≤ 1 ∧
      kktSystem ε S η (pack z P Q)=0 ∧
      (∀ u,J u=CurrentKS.KKT.jacobian (identityPair d)
        (onPairHilbert (linConstraint z.2.1 z.2.2 η)) (hessian z.2.1 z.2.2 P Q) u) ∧
      ‖J.symm.toContinuousLinearMap‖ ≤ 10^18*((d:ℝ)+1)*(1+ε⁻¹)^4 ∧
      ‖pack z P Q‖ ≤ 200+(200/ε)*((d:ℝ)+1) ∧
      ‖invH z.2.1‖ ≤ 200*((d:ℝ)+1) ∧ ‖invH z.2.2‖ ≤ 200*((d:ℝ)+1) := by
  obtain ⟨P,Q,hP,hQ,hPle,hQle,htr,hPX,hQY,ht,hx,hy⟩ :=
    kkt S η hηpos hηsym hε hSlo hShi z hz hmin
  have hb := sublevel_box S η hηpos hε (by norm_num : (0:ℝ)<100) hSlo hShi hz hz100
  have hhX : (200:ℝ)⁻¹ • (Hermitian.one : H d) ≤ z.2.1 := by convert hb.2.1.1 using 1; norm_num
  have hhY : (200:ℝ)⁻¹ • (Hermitian.one : H d) ≤ z.2.2 := by convert hb.2.2.1 using 1; norm_num
  obtain ⟨J,hJ,hJi⟩ := full_jacobian_inverse_bound z.2.1 z.2.2 P Q η hηpos hηsym
    hz.1.1 hz.1.2 hP hQ hε htr hx hy hhX hhY hb.2.1.2 hb.2.2.2
  have hPn := norm_sq_le_trace_of_psd_le_one P hP.posSemidef hPle
  have hQn := norm_sq_le_trace_of_psd_le_one Q hQ.posSemidef hQle
  have hnP : ‖P‖ ≤ 1 := by nlinarith [realTrace_nonneg hQ.posSemidef,norm_nonneg P]
  have hnQ : ‖Q‖ ≤ 1 := by nlinarith [realTrace_nonneg hP.posSemidef,norm_nonneg Q]
  refine ⟨P,Q,J,hP,hQ,hnP,hnQ,pack_kkt ε S η z P Q htr ht hx hy,hJ,hJi,
    norm_pack_bounds z P Q hε hb.1 hz.1.1 hz.1.2 hb.2.1.2 hb.2.2.2 hP hQ htr,?_,?_⟩
  · apply norm_psd_le_scalar _ hz.1.1.inv.posSemidef (by norm_num)
    simpa only [inv_inv] using inverse_upper_of_lower z.2.1 hz.1.1
      (by norm_num : (0:ℝ)<(200:ℝ)⁻¹) hhX
  · apply norm_psd_le_scalar _ hz.1.2.inv.posSemidef (by norm_num)
    simpa only [inv_inv] using inverse_upper_of_lower z.2.2 hz.1.2
      (by norm_num : (0:ℝ)<(200:ℝ)⁻¹) hhY
end
end CurrentKS.Variational

end OAI
