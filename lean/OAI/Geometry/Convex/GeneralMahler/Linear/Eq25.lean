import OAI.Geometry.Convex.GeneralMahler.Linear.Powers

namespace OAI
/-! Linear field: normalization substitution. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open Profile
variable {m:ℕ}
lemma pj_outer (A W C:Mat m): Pj W A C=Pj A W C := by
  have h (A B C:Mat m) : trN (A*(B*C))=trN (B*(C*A)) := by
    rw [trN_cyclic A,mul_assoc]
  unfold Pj jprod
  simp_rw [mul_smul_comm,trN_smul,mul_add,trN_add]
  rw [h W A C,← h A W C]; ring

lemma Eq_replace (C K S T:Mat m) (he:updEq C K T=0) :
    Pj 1 (S-1) K + Pj T (S-1) C-ar*trN (T*K) =
      -lam*trN (S*(T*T))-
        trN (((-ar)•C-(ar*lam)•T-scalar m lam)*(T*T)) := by
  have he' : K+jprod T C= -(lam • (T*T)) := by
    unfold updEq jprod at *
    rw [add_comm (T*C),add_comm]
    exact eq_neg_of_add_eq_zero_left (by rw [add_assoc] at he; rw [add_comm]; exact he)
  have hi : Pj 1 (S-1) K + Pj T (S-1) C= -lam*trN ((S-1)*(T*T)) := by
    rw [Pj,one_mul,trN_j,pj_outer,Pj,← trN_add,← mul_add,he',mul_neg]
    have hh (A:Mat m):trN (-A)= -trN A := by unfold trN; rw [trace_neg]; ring
    rw [hh,mul_smul_comm,trN_smul]; ring
  have hh : trN (T*K)= -lam*trN (T*(T*T))-trN (C*(T*T)) := by
    have heJ : trN (T*jprod T C)=trN (C*(T*T)) := by
      rw [← show Pj T T C=trN (T*jprod T C) from rfl,pj_sym,pj_outer,Pj,j_same]
    have h : K = ((-lam) • (T*T))- jprod T C := by simp only [neg_smul]; rw [← he']; abel
    rw [h,mul_sub,trN_sub,mul_smul_comm,trN_smul,heJ]
  rw [hi,hh]
  simp only [sub_mul,trN_sub,smul_mul_assoc,trN_smul,scalar,one_mul]
  ring
lemma pairGap (T C:Mat m) (hc:C ≤ scalar m cupper) (hH:scalar m mstar≤updGap C T) :
    scalar m (194/100) ≤ (-ar) • C - (ar*lam) • T -scalar m lam := by
  have hu : scalar m (ar*(mstar-cupper)/2-lam) ≤ (-ar) • C-(ar*lam) • T-scalar m lam := by
    have he := smul_le_smul_of_nonneg_left (sub_le_sub hH hc) (show (0:ℝ)≤ar/2 by norm_num [ar])
    have hh := sub_le_sub_right he (scalar m lam)
    apply le_trans _ (le_trans hh _)
    · apply le_of_eq; simp only [scalar]; module
    apply le_of_eq; simp only [scalar,updGap]; module
  apply le_trans _ hu
  apply scalar_le'
  norm_num [mstar,cupper,lam,ar]

namespace ProjField
variable [NeZero m] (q:ProjField m) (T:Mat m)
lemma eq25 (he:updEq (q.expL Cp) (q.expL Kp) T=0)
    (ht:T.IsHermitian) (hH: scalar m mstar≤updGap (q.expL Cp) T)
    (hc:q.expL Cp ≤ scalar m cupper) :
    q.DelP T ≤ q.RM 1 Kp+ q.RM T Cp -
      lam * trN (q.sumS*(T*T)) - (194/100)* trN (T*T) := by
  rw [q.DelP_form]
  have hi := Eq_replace _ _ q.sumS T he
  have hu := trN_mul_mono (pairGap T _ hc hH) (sqPSD ht)
  have he : trN (scalar m (194/100)*(T*T))=(194/100)*trN (T*T) := by
    simp only [scalar,smul_mul_assoc,one_mul,trN_smul]
  rw [he] at hu
  linarith
end ProjField
end GeneralMahler

end

end OAI
