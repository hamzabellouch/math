import OAI.Geometry.Convex.GeneralMahler.Linear.Final

namespace OAI
/-! §06 equality from strict signs, support of two layer functionals. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
open LPt Profile Segment Layers
variable {m:ℕ}
private lemma sZeroPt {f:Fin m→ℝ} (h:∀ i,0≤f i) (hh:∑ i,f i=0) (i:Fin m) : f i=0 := by
  refine le_antisymm ?_ (h i)
  have hi := Finset.single_le_sum (s:=Finset.univ) (fun j _=>h j) (Finset.mem_univ i)
  rwa [hh] at hi
private lemma s0n {f:Fin m→ℝ} (h:∀ i,f i≤0) (hh:∑ i,f i=0) (i:Fin m) : f i=0 := by
  have he : ∀ i,0 ≤ -f i := fun j=> neg_nonneg.mpr (h j)
  have hi : (∑ i,-f i)=0 := by rw [Finset.sum_neg_distrib,hh,neg_zero]
  exact neg_eq_zero.mp (sZeroPt he hi i)
variable [NeZero m]

private lemma m0 {f:Fin m→ℝ} (hh:mats f=0): ∑ i, f i=0 := by
  unfold mats at hh
  exact (div_eq_zero_iff.mp hh).resolve_right (show (m:ℝ)≠0 from (ProjField.m_pos (m:=m)).ne')

namespace ProjField
variable (q:ProjField m)
lemma pt_czero (i:Fin m) (x:Rn m) (h:SegmentOK) (hz:q.nupt i x symR=0) :
    hsN (cmu (q.Lmat x) (q.M i))=0 := by
  let l:=q.FL.ev x
  let u:=q.FL.Fr x
  let M:=u.loc (q.M i)
  let f := fun j k:Fin m=>M j k^2*symR (l j,l k)
  have hh (j k) : f j k≤0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (Rle h _)
  have hp (j) : ∑ k,f j k=0 :=
    s0n (fun j=> Finset.sum_nonpos (s:=Finset.univ) (f:=f j) (fun k _=>hh j k))
      (m0 (show mats (fun i=>∑ k,f i k)=0 from hz)) j
  have he (j k) : (l j-l k)^2*M j k^2 =0 := by
    have hi := s0n (hh j) (hp j) k
    unfold f at hi
    by_cases h': l j=l k
    · simp [h']
    have h : symR (l j,l k)<0 := negR h _ h'
    rw [(mul_eq_zero.mp hi).resolve_right h.ne,mul_zero]
  rw [cmu_eig (q.Lmat x) (q.M i) u (q.FL.Fr_D x)]
  change mats (fun j=>∑ k,(l j-l k)^2*M j k^2)=0
  simp [he,mats]

lemma nu_comm (h:LayerOK) (hs:SegmentOK) (hz:q.nu symR=0) (i j:Fin m):
    cmu (q.M j) (q.M i)=0 := by
  let f:= fun k x=> q.nupt k x symR
  have hh (i:Fin m) : (∫ x,f i x ∂normal m)=0 :=
    s0n (f:=fun i=> ∫ x,f i x ∂normal m)
      (fun j=> integral_nonpos fun x=>q.nupt_neg j x hs) hz i
  have hp : ∀ᵐ x∂normal m,f i x=0 := by
    have hi : (∫ x,-f i x ∂normal m)=0 := by rw [integral_neg,hh,neg_zero]
    have hv : (0: Rn m→ℝ)≤ fun x=> -f i x :=
      fun x=> neg_nonneg.mpr (q.nupt_neg i _ hs)
    filter_upwards [(integral_eq_zero_iff_of_nonneg hv (show Integrable _ _ from
      (q.nu_i (WR h) i).neg)).mp hi] with x hx
    exact neg_eq_zero.mp hx
  have he : (∑ j,hsN (cmu (q.M j) (q.M i)))=0 := by
    rw [← q.Comm_L,Hcomm]
    apply integral_eq_zero_of_ae
    exact hp.mono fun x hx=> q.pt_czero i x hs hx
  exact hsn_eq_zero _ (sZeroPt (fun i=> hsN_pos _) he j)

lemma BLzero (h:LayerOK) (x z)
    (hd:∀ i,q.FL.ev x i≠z) (he:q.bmZ q.FL Bgap z x=0): q.EZ q.FL z x=0 := by
  let b:= q.BL q.FL x z
  have hi (i:Fin m) : b.S i i=0 := by
    have hp := q.bm_trace q.FL x z Bgap
    rw [hp] at he
    have h₀ : ∑ i,b.S i i*Bgap (z,b.x i)=0 := m0 he
    have hi (i:Fin m): 0 ≤ b.S i i*Bgap (z,b.x i) :=
      mul_nonneg (b.Spar.posSemidef.diag_nonneg) (Bpositive h _).le
    exact (mul_eq_zero.mp (sZeroPt hi h₀ i)).resolve_right (Bpositive h _).ne'
  have hE : b.E=0 := by
    ext i j
    have he := b.Ed2 i
    have hz := hi i
    have hp : b.a i≠0 := abs_ne_zero.mpr (sub_ne_zero.mpr (hd i))
    rw [b.Sdiag,mul_assoc] at hz
    have hv : b.L i*b.E i i=0 := (mul_eq_zero.mp hz).resolve_left hp
    rw [hv] at he
    have hi := Finset.single_le_sum (f:=fun j=>b.E i j^2) (s:=Finset.univ)
      (fun j _ => by positivity) (Finset.mem_univ j)
    change _ = 0; nlinarith
  apply (q.FL.Fr x).loc_inj
  rw [Frm.loc_zero,← q.BLe]
  exact hE

lemma B_layer (h:LayerOK) (hz:q.BB q.FL Bgap=0):
    ∃ z:ℝ,∀ᵐ x∂normal m,q.Pmat z x=q.FL.Θ z x := by
  let F:=q.bmZ q.FL Bgap
  have hp (z x) : 0≤F z x := q.bm_pos q.FL x z Bgap fun u=> (Bpositive h u).le
  have he : ∀ᵐ x∂normal m, (∫ z,F z x)=0 :=
    (integral_eq_zero_iff_of_nonneg (show (0:Rn m→ℝ)≤ fun x=>∫ z,F z x from
      fun x=>integral_nonneg fun z=>hp z x) (q.bmah q.FL (Btest h))).mp hz
  let p := fun (x:Rn m) (z:ℝ)=>q.EZ q.FL z x=0
  have hm : MeasurableSet {x:Rn m × ℝ| p x.1 x.2} :=

    ((q.eSM q.FL).measurable.comp measurable_swap) measurableSet_eq
  have hh : ∀ᵐ z:ℝ,∀ᵐ x∂normal m,p x z := by
    apply (Measure.ae_ae_comm hm).mp
    filter_upwards [he] with x hx
    have hj : ∀ᵐ z:ℝ,F z x=0 := (integral_eq_zero_iff_of_nonneg
      (show (0:ℝ→ℝ)≤ fun z=> F z x from fun z=>hp z x)
      (q.bmh q.FL (Btest h) x)).mp hx
    have ha (i:Fin m): ∀ᵐ z:ℝ, z≠ q.FL.ev x i := by
      apply Measure.ae_ne
    filter_upwards [hj, ae_all_iff.mpr ha] with z hz he
    exact q.BLzero h x z (fun i=> Ne.symm (he i)) hz
  obtain ⟨z,hz⟩:= hh.exists
  exact ⟨z,hz.mono fun x hx=> sub_eq_zero.mp hx⟩
end ProjField
end GeneralMahler

end

end OAI
