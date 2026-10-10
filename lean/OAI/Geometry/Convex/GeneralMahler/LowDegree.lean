import OAI.Geometry.Convex.GeneralMahler.FormSquare

namespace OAI
/-! Linear chaos coefficients for balance. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open Profile Layers HMode
variable {m:ℕ} [NeZero m]

namespace ProjField
variable (q:ProjField m)
omit [NeZero m] in
lemma Mzero (x:Rn m) : MM 0 x=1 := by simp only [MM]; simp [H]
omit [NeZero m] in
lemma Mi1 (i:Fin m) (x:Rn m) : MM (inc 0 i) x=x i := by
  rw [inc,factor_upd]; simp [H,sn]

omit [NeZero m] in
lemma cof_subm {f g:Rn m→Mat m} (hf:regular f) (hg:regular g) (a:MI m) :
    cof (fun x=>f x-g x) a=cof f a-cof g a := by
  unfold cof; simp_rw [smul_sub]; rw [integral_sub (i_cof hf.p hf.meas a) (i_cof hg.p hg.meas a)]

omit [NeZero m] in
lemma l_reg : regular q.Lmat := ⟨q.L_poly,q.L_cont.aestronglyMeasurable⟩
lemma a_reg : regular q.Amat := ⟨q.A_poly,q.A_SM.aestronglyMeasurable⟩
omit [NeZero m] in
lemma coL (a:MI m) :
    cof q.Lmat a=∑ i:Fin m,(if a=inc 0 i then (1:ℝ) else 0) • q.M i := by
  classical
  have hi (i:Fin m) : Integrable (fun x:Rn m=> (MM a x*x i) • q.M i) (normal m) := by
    have h := ((M_poly a).mul (PolyBound.clm (coord i)))
    exact ((h.gaussian_integrable (μ:=normal m)
      ((M_cont a).mul (coord i).continuous).aestronglyMeasurable).smul_const _)
  have he (x:Rn m) : MM a x • q.Lmat x=∑ i:Fin m,(MM a x*x i) • q.M i := by
    unfold Lmat; rw [Finset.smul_sum]; simp only [smul_smul]
  unfold cof; simp_rw [he]; rw [integral_finsetSum]
  · simp_rw [integral_smul_const, ← Mi1, M_inner]
  exact fun i _=>hi i

omit [NeZero m] in
lemma coL_o {a:MI m} (h:deg a ≠ 1) : cof q.Lmat a=0 := by
  have he (i:Fin m):a≠ inc 0 i := by
    intro h'; rw [h',deg_inc,dz _ |>.mpr rfl] at h; exact h rfl
  rw [q.coL]; simp [he]
lemma k_l (W:Mat m) {f:Rn m→Mat m} (hf:regular f) :
    2*KP W q.Lmat f=Pt W q.Lmat f := by
  have h := pt_sum (B:=W) q.l_reg hf
  unfold KP
  rw [← tsum_mul_left, ← h.tsum_eq]
  apply tsum_congr; intro a
  by_cases hh:deg a=1
  · rw [kMode,hh]; push_cast; ring
  unfold CpPair; rw [q.coL_o hh]
  simp [Pj,jprod,trN]

lemma kpR (W:Mat m) {f:Rn m→Mat m} (hf:regular f) :
    KP W q.Amat f= KP W q.Lmat f + KP W q.RR f := by
  have he : KP W q.RR f = KP W q.Amat f-KP W q.Lmat f := by
    unfold KP
    rw [← Summable.tsum_sub (K_sum q.a_reg hf) (K_sum q.l_reg hf)]
    apply tsum_congr; intro a
    unfold CpPair RR; rw [cof_subm q.a_reg q.l_reg]
    simp_rw [← pJ_eq]
    simp only [_root_.map_sub,_root_.sub_apply,sub_mul]
  linarith
omit [NeZero m] in
lemma pt_sym (W:Mat m) (f g:Rn m→Mat m) : Pt W f g=Pt W g f := by
  unfold Pt; congr 1; funext x; exact pj_sym ..
lemma MB_id :
    q.MB q.FL (fun x=>x)=q.RR := by
  ext x
  unfold MB RR; rw [q.evId,Profile.id_ga]; simp [scalar,Amat]; rfl

end ProjField
end GeneralMahler

end

end OAI
