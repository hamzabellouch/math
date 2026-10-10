import OAI.Geometry.Convex.GeneralMahler.Linear.Eq25
import OAI.Geometry.Convex.GeneralMahler.Linear.Eq26
import OAI.Geometry.Convex.GeneralMahler.Linear.Eq27

namespace OAI
/-! §06 final inequalities before rigidity. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open HMode Profile Segment Layers
variable {m:ℕ} [NeZero m]

lemma hsn_eq_zero (A:Mat m) (h:hsN A=0) : A=0 := by
  rw [hsN_eq] at h
  unfold mats at h
  have hm : (m:ℝ)≠0:= (ProjField.m_pos (m:=m)).ne'
  have hi := (div_eq_zero_iff.mp h).resolve_right hm
  have hh (i:Fin m) : (∑ j,A i j^2)=0 := by
    have he : 0≤∑ j,A i j^2 := by positivity
    refine le_antisymm ?_ he
    have hv := Finset.single_le_sum (f:=fun i=>∑ j,A i j^2) (s:=Finset.univ)
      (fun j _=> by positivity) (Finset.mem_univ i)
    rwa [hi] at hv
  ext i j
  have hv := Finset.single_le_sum (f:=fun j=>A i j^2) (s:=Finset.univ)
    (fun j _=> by positivity) (Finset.mem_univ j)
  rw [hh] at hv; change _=0; nlinarith

namespace ProjField
variable (q:ProjField m) (T:Mat m)

lemma nuR (h:LayerOK) :
    q.nu symR=q.nu (rest Kp)+q.nu sgamma+(1/(4*lam))*q.nu (fun u=>bstar u^2) +
      tmax*q.nu dsum-q.nu vsum := by
  unfold symR
  have hh := Wres h
  rw [q.nu_s,q.nu_add hh (Wflip hh),q.nu_flip,show (1/2:ℝ)*(q.nu resid+q.nu resid)=q.nu resid from by ring]
  unfold resid
  have he := (Wr testK).add Wg
  have hu := (Bwt.const (1/(4*lam))).mul (Wsq (Wb h))
  have hv := (Bwt.const tmax).mul (Wd h)
  rw [q.nu_sub ((he.add hu).add hv) (Wvs h),q.nu_add (he.add hu) hv,
    q.nu_add he hu,q.nu_add (Wr testK) Wg,q.nu_s,q.nu_s]
lemma nupt_neg (i:Fin m) (x) (h:SegmentOK) :
    q.nupt i x symR ≤ 0 := by
  unfold nupt LPt.npt mats
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  apply Finset.sum_nonpos; intro i _
  apply Finset.sum_nonpos; intro j _
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (Rle h _)
lemma nuR_neg (h:SegmentOK) : q.nu symR ≤ 0 := by
  unfold nu
  apply Finset.sum_nonpos
  intro i _; exact integral_nonpos fun x=> q.nupt_neg i x h

def Bgap (u:Plane) := ww u-ww0 u
lemma Bpositive (h:LayerOK) (x): 0<Bgap x := sub_pos.mpr (wpos h x).1
lemma Btest (h:LayerOK): Bwt Bgap := (wwt h).sub (w0t h)
lemma Bgap_pos (h:LayerOK) :
    0 ≤ q.BB q.FL Bgap :=
  integral_nonneg fun x=> integral_nonneg fun z=> q.bm_pos q.FL x z Bgap fun u=>(Bpositive h u).le

-- normal form after covariance updates
structure Balanced : Prop where
  ht:T∈specBox m tmin tmax
  cov : 1+T=q.covMat
  eqn : updEq (q.expL Cp) (q.expL Kp) T=0
  avg : q.avgA=0
  gap : scalar m mstar ≤ updGap (q.expL Cp) T

lemma E_last (h:Balanced q T) (hc:UpdatesOK Cp Kp) (hh:LayerOK) :
    q.scoreE T ≤ q.nu symR - (14/100)*trN (T*T)- q.BB q.FL Bgap := by
  have ha := q.budget T h.ht h.cov hh h.avg
  have he := q.eq25 T h.eqn h.ht.1 h.gap (q.expL_bounds hc).1
  have hu := q.eq26 T hh h.ht
  have hv := q.eq27 T h.eqn h.ht h.gap
  rw [← h.cov,q.J_vec T hh] at ha
  rw [q.R_nu testK] at he
  rw [q.nuR hh]; unfold Bgap
  linarith
lemma entropy_pt (h:1+T=q.covMat):
    -q.scoreE T ≤ Real.log (chi q.C q.V*chi q.D q.U)/(m:ℝ) := by
  unfold scoreE
  have hh := q.entropy10 h
  rw [q.nn_eq]
  linarith
omit [NeZero m] in
lemma PairPos : 0 < chi q.C q.V*chi q.D q.U := by
  apply mul_pos
  · apply chi_pos (C:=q.C) ⟨q.U,q.U_in⟩ q.V_in
  have hq : q.U ∈ interior ((posDual q.D):Set (Rn m)) := by
    rw [show posDual q.D=q.C from ProperCone.innerDual_innerDual _]; exact q.U_in
  exact chi_pos (C:=q.D) ⟨q.V,q.V_in⟩ hq

lemma E_sign (h:Balanced q T) (hc:UpdatesOK Cp Kp) (hh:LayerOK) (hi:SegmentOK):
    q.scoreE T≤0 ∧ (q.scoreE T=0 → T=0∧q.nu symR=0 ∧ q.BB q.FL Bgap=0) := by
  have hz := q.E_last T h hc hh
  have hT : hsN T = trN (T*T) := by unfold hsN; rw [show star T=T from h.ht.1]
  rw [← hT] at hz
  have he := q.nuR_neg hi
  have hx := q.Bgap_pos hh
  have hm := hsN_pos T
  constructor
  · linarith
  intro hH
  refine ⟨hsn_eq_zero _ ?_,?_,?_⟩ <;> linarith

theorem Bound_pt (h:Balanced q T) (hc:UpdatesOK Cp Kp) (hh:LayerOK) (hi:SegmentOK):
    (1≤chi q.C q.V*chi q.D q.U) ∧ (chi q.C q.V*chi q.D q.U=1 →
      T=0∧q.nu symR=0 ∧ q.BB q.FL Bgap=0) := by
  have hl := q.entropy_pt T h.cov
  obtain ⟨hj,hk⟩:= q.E_sign T h hc hh hi
  constructor
  · have he : 0 ≤ Real.log (chi q.C q.V*chi q.D q.U)/(m:ℝ) := by linarith
    have hv := (le_div_iff₀ m_pos).mp he
    rw [← Real.log_le_log_iff zero_lt_one q.PairPos, Real.log_one]
    linarith
  intro he; rw [he,Real.log_one,zero_div] at hl
  apply hk; linarith
end ProjField
end GeneralMahler

end

end OAI
