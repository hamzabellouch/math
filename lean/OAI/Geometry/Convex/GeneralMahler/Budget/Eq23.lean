import OAI.Geometry.Convex.GeneralMahler.Budget.FinalR

namespace OAI
/-! §05 reduction to matrix functionals on linear field. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Interval
namespace GeneralMahler
open HMode Profile Layers Seg Roots
variable {m:ℕ} [NeZero m]
namespace ProjField
variable (q:ProjField m) (T:Mat m)

lemma P0_layer (h:LayerOK) :
    q.LLw q.FL 1 P0 =
      (2*ap+2*e₀*(2*tr)^2)*q.LLw q.FL 1 (fun _=>1) +
      (2*bm)*q.LLw q.FL 1 (fun u=> N2 qu u.1*N2 qu u.2) := by
  let g := fun u:Plane=> N2 qu u.1*N2 qu u.2
  let K := (2*ap+2*e₀*(2*tr)^2)
  have H : P0=fun x=> (K*1)+(2*bm)*g x := by funext x; unfold K P0 g; ring
  rw [H, q.Lbar_add q.FL 1 (Bwt.const _) ((Bwt.const _).mul
    ((Bwt.fst (N2_test h.q_test)).mul (Bwt.snd (N2_test h.q_test))))]
  rw [q.Lbar_scale,q.Lbar_scale]

lemma H0_layer (h:LayerOK) :
    q.LLw q.FL T (fun u=> HH u+deriv (deriv v) u.2)=2*kar*q.LLw q.FL T (fun _=>1)+
      q.LLw q.FL T Hh := by
  have H : (fun u:Plane=>HH u+deriv (deriv v) u.2)=fun u=>2*kar*1+Hh u :=
    by funext x; unfold Hh; ring
  rw [H,q.Lbar_add q.FL T (Bwt.const _) (bhj h)]
  rw [show q.LLw q.FL T (fun _=>2*kar*1)=2*kar*q.LLw q.FL T (fun _=>1) from
    q.Lbar_scale _ _ (fun _=>1) _]

lemma P_R_bd (ht:T∈specBox m tmin tmax) (he:1+T=q.covMat) :
    (bb+eta)*Pt q.covMat q.RR q.RR-kar*Pt T q.RR q.RR ≤ ap*Pt 1 q.RR q.RR := by
  let P := fun W=>Pt W q.RR q.RR
  let f := fun W (x:Rn m)=> Pj W (q.RR x) (q.RR x)
  have hs (W) : Integrable (f W) (normal m) := pj_poly_part q.R_reg _
  have hi : P q.covMat= P 1+P T := by
    unfold P Pt; rw [← he]; simp_rw [Pj,add_mul,trN_add]; exact integral_add (hs _) (hs _)
  have ht : P T ≥ tmin * P 1 := by
    unfold P Pt
    rw [← integral_const_mul]
    apply integral_mono ((hs _).const_mul _) (hs _)
    intro x
    have h := p_le_p ht.2.1 (q.r_sym x)
    simpa only [f,Pj,scalar,smul_mul_assoc,trN_smul] using h
  unfold ap
  change _*P _-_*P _≤_*P _
  unfold bb eta kar tmin at *; linarith

def scoreE := q.delt d-etw T (q.Hmat v)+(trN T-logD q.covMat)-q.NK 1/8

lemma reserve (ht:T∈specBox m tmin tmax) (he:1+T=q.covMat) (hh:q.avgA=0) :
    (bb+eta)*Pt q.covMat q.RR q.RR -(2*kar)*q.LLw q.FL T (fun _=>1)-q.NK 1/8 ≤
      (2*ap+2*e₀*(2*tr)^2)*q.LLw q.FL 1 (fun _=>1)+e₀*Hcomm q.Lmat T := by
  have h := q.P_R_bd T ht he
  have h₁ := q.NZ_L T
  have h₂ := q.NZ_L 1
  have hp := q.NKpos
  have hi := q.const_limit T ht
  rw [q.comm_split T ht.1 hh] at hi
  have hk := q.comm_bound T ht
  unfold ap lm bb eta tmin tmax e₀ Profile.tr kar at *
  linarith

theorem budget (ht:T∈specBox m tmin tmax) (he:1+T=q.covMat)
    (hs:LayerOK) (hh:q.avgA=0) :
    q.scoreE T ≤ q.DelP T-q.JVec q.covMat+(80/100)*Hcomm q.Lmat T+
      (18/10)*trN (T*T)-q.BB q.FL (fun u=> ww u-ww0 u) := by
  have h := q.entropy_decomp he hs
  have h₁ := q.degree19 hs hh ht he
  have h₂ := q.NTpos19 hs
  have hu := q.end_cost T ht he hs hh
  have hv := q.reserve T ht he hh
  have hx := q.limitB T ht hs
  rw [q.Lbar_sub q.FL 1 (H_ok hs) (P0_wt hs),q.P0_layer hs] at hx
  rw [q.H0_layer T hs] at h
  have hsum : e₀+alpha*(Real.log 2+1/4)/4 ≤ 80/100 := by
    unfold e₀ alpha; linarith [Real.log_two_lt_d9]
  have he' : 0 ≤ Hcomm q.Lmat T := integral_nonneg fun _=>hsN_pos _
  have he := mul_le_mul_of_nonneg_left h₂ GeneralMahler.bm_pos.le
  unfold scoreE
  linarith [mul_le_mul_of_nonneg_right hsum he']
end ProjField
end GeneralMahler

end

end OAI
