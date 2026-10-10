import OAI.Geometry.Convex.GeneralMahler.Linear.SpectralIBP

namespace OAI
/-! §06. Commuting normalization controls weighted norm. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open HMode Profile Layers
variable {m:ℕ}

lemma sum_hsn (X Y:Mat m) : hsN (X+Y)≤125/100*hsN X+5*hsN Y := by
  simp only [hsN_eq]
  rw [mats_s2,mats_s2,← mats_add]
  apply mats_le; intro i
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro j _
  rw [Matrix.add_apply]
  nlinarith [sq_nonneg (X i j-4*Y i j)]

lemma H_J_frame {X W:Mat m} (u:Frm m) (l:Fin m→ℝ) (h:u.loc W=diagonal l):
    hsN (jprod W X)=mats (fun i=>∑ j,((l i+l j)/2)^2*(u.loc X i j)^2) := by
  rw [← hsN_loc (jprod W X) u,hsN_eq]; unfold jprod
  rw [u.loc_smul,u.loc_add,u.loc_mul,u.loc_mul,h]
  congr 1; ext i; apply Finset.sum_congr rfl; intro j _
  simp only [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul,Matrix.diagonal_mul,Matrix.mul_diagonal]
  ring

lemma Jgap_lower {W:Mat m} (hw:W.IsHermitian) (hu: scalar m mstar ≤ W) (X:Mat m) :
    mstar^2*hsN X≤ hsN (jprod W X) := by
  let u := Frm.eu hw
  let f := u.eig W
  have hi : u.loc W=diagonal f := Frm.eu_d hw
  have hp (i:Fin m) : mstar≤f i := by
    have he : f i∈ spectrum ℝ W := by
      unfold f u; rw [hw.spectrum_real_eq_range_eigenvalues,Frm.eu_eig]; exact ⟨_,rfl⟩
    exact (spectrum_order W hw (l:=mstar) (r:=mstar)).1.mp hu _ he
  rw [H_J_frame u f hi,← hsN_loc X u,hsN_eq,mats_s2]
  apply mats_le; intro i; apply Finset.sum_le_sum; intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hv := hp i; have hf := hp j; unfold mstar at *
  nlinarith

lemma Jdev_upper {W:Mat m} (hW:W∈specBox m tmin tmax) (X:Mat m) :
    hsN (jprod (W-scalar m tc) X) ≤ Profile.tr^2*hsN X := by
  let u := Frm.eu hW.1
  let f := u.eig W
  have hi : u.loc W=diagonal f := Frm.eu_d hW.1
  have hh : u.loc (W-scalar m tc)=diagonal (fun i=>f i-tc) := by
    rw [u.loc_sub,hi,u.loc_s]
    ext i j; by_cases he:i=j
    · subst j; simp [scalar]
    simp [scalar,he]
  have hp (i:Fin m) : tmin≤f i ∧ f i≤tmax := by
    have he : f i∈ spectrum ℝ W := by
      unfold f u; rw [hW.1.spectrum_real_eq_range_eigenvalues,Frm.eu_eig]; exact ⟨_,rfl⟩
    have h := spectrum_order W hW.1 (l:=tmin) (r:=tmax)
    exact ⟨h.1.mp hW.2.1 _ he,h.2.mp hW.2.2 _ he⟩
  rw [H_J_frame u _ hh,← hsN_loc X u,hsN_eq,mats_s2]
  apply mats_le; intro i; apply Finset.sum_le_sum; intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hv := hp i; have hf := hp j
  unfold tmin tmax tc Profile.tr at *; nlinarith [hv.1,hv.2,hf.1,hf.2]

lemma commute_update {C K T:Mat m} (h:updEq C K T=0) (M:Mat m):
    jprod (updGap C T) (cmu M T)=cmu M (K+tc • C)+jprod (T-scalar m tc) (cmu M C) := by
  have he : K= -(lam • (T*T)+jprod C T) := by
    unfold updEq at h
    apply eq_neg_of_add_eq_zero_left
    rwa [add_comm]
  rw [he]
  dsimp only [jprod,updGap,cmu]
  simp only [add_mul,mul_add, mul_sub,sub_mul,neg_mul,mul_neg,
    smul_mul_assoc,mul_smul_comm,scalar,one_mul,mul_one,mul_assoc]
  module

theorem Comm_bound {C K T:Mat m} (hc:C.IsHermitian)
    (hT:T∈specBox m tmin tmax)
    (he:updEq C K T=0) (hH:scalar m mstar ≤ updGap C T) (M:Mat m) :
    mstar^2*hsN (cmu M T) ≤
      (125/100)*hsN (cmu M (K+tc • C))+ (5*Profile.tr^2)*hsN (cmu M C) := by
  have hh : (updGap C T).IsHermitian :=
    hc.neg.sub (hT.1.smul (by simp [IsSelfAdjoint]))
  have hi := Jgap_lower hh hH (cmu M T)
  rw [commute_update he] at hi
  apply (hi.trans (sum_hsn _ _)).trans
  apply add_le_add le_rfl; rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (Jdev_upper hT _) (by norm_num)
end GeneralMahler

end

end OAI
