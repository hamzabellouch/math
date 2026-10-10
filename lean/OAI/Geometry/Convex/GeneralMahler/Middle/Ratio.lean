import OAI.Geometry.Convex.GeneralMahler.Middle.Traversal

namespace OAI
/-! log-bound profiles and Guard induction. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology Interval
namespace GeneralMahler.SCal.Mid
open Tag Grid Jet Profile Segment SE
variable {f:ℝ→ℝ} {P:Cap}
lemma trav_guard (h:Guard f P)(a:ℝ):Guard (trav a f) (Cap.av P):= by
  let R := ment (Rg a f)
  let d:=ment (G1 a (f₀:=f))
  let e:=ment (G2 a (f₀:=f))
  let o:=fun _:ℝ=>(1:ℝ)
  let s:=denom a
  let D:=ment (G1 a (f₀:=o))
  let E:=ment (G2 a (f₀:=o))
  let v:=trav a f
  let j:=fun x=> (d x-v x*D x)/s x
  let k:=fun x=> (e x-2*j x*D x-v x*E x)/s x
  obtain ⟨⟨hr,hc,he⟩,hw⟩:= grTrav a h
  change Continuous R at hr;change Continuous d at hc;change Continuous e at he
  have h1 := grTrav a (Guard.const 1 1 (by norm_num))
  change (Continuous _∧Continuous D∧Continuous E)∧_ at h1
  have hh : ment (Rg a o)=s := by unfold o Rg; simp only [mul_one];rfl
  rw [hh] at h1
  obtain ⟨⟨hs,hD,hE⟩,hp⟩:=h1
  have hP(x):0 < s x:=dp a x
  have ha:Continuous v:= hr.div hs (fun x=> (hP _).ne')
  have hb:Continuous j:= (hc.sub (ha.mul hD)).div hs (fun x=>(hP _).ne')
  have hk:Continuous k:= ((he.sub ((continuous_const.mul hb).mul hD)).sub
    (ha.mul hE)).div hs fun x=>(hP _).ne'
  have hd (x:ℝ): HasDerivAt v (j x) x:=by
    obtain ⟨ht,h',_⟩:=hw x; obtain ⟨hs,h,_⟩:=hp x
    have hu: HasDerivAt R (d x) x:=ht
    have hv: HasDerivAt s (D x) x:=hs
    have hh:0 < s x:=hP x
    convert hu.div hv hh.ne' using 1
    all_goals first| rfl| skip
    change (d x-R x/s x*D x)/s x=_
    field_simp
  have hl(x:ℝ): HasDerivAt j (k x) x:=by
    obtain ⟨_,hh,_⟩:=hw x; obtain ⟨hs,h,_⟩:=hp x
    have hr:HasDerivAt d (e x) x:=hh
    have hv:HasDerivAt s (D x) x:=hs
    have hu:HasDerivAt D (E x) x:=h
    have hi:0 < s x:=hP x
    convert ((hr.sub ((hd x).mul hu)).div hv hi.ne') using 1
    unfold k
    change _ = ((_ - _)*s x-(d x-v x*D x)*D x)/_
    unfold j
    field_simp; ring
  have hI(x:ℝ) :
      |s x|=s x ∧ |D x| ≤ s x∧ |E x|≤ s x:= by
    obtain ⟨_,_,_,ha,hb⟩:=hp x
    exact ⟨abs_of_pos (hP _),by simpa [Cap.fl] using ha,by simpa [Cap.fl] using hb⟩
  have heV(x:ℝ): |v x| ≤ P.a := by
    change |R x / s x|≤ _
    rw [abs_div,(hI x).1,div_le_iff₀ (hP _),mul_comm];exact (hw x).2.2.1
  have hj(x:ℝ):|j x|≤ (Cap.av P).b:=by
    obtain ⟨ha,hb,hc⟩:= hI x
    unfold j; rw [abs_div,ha,div_le_iff₀ (hP x)]
    apply (abs_sub _ _).trans
    have hp:|d x|≤ s x*(P.b+P.a):= (hw x).2.2.2.1
    have hi:=Guard.absMul (heV x) hb
    dsimp [Cap.av]; linarith
  apply mkGuard (A:=Cap.av P) hd hl hk heV hj
  intro x; obtain ⟨ha,hb,hc⟩:=hI x
  unfold k; rw [abs_div,ha,div_le_iff₀ (hP x)]
  apply (abs_sub _ _).trans
  have he: |e x| ≤ s x*(P.c+2*P.b+P.a):=(hw x).2.2.2.2
  have hi:=Guard.absMul (Guard.absMul (show |(2:ℝ)|≤2 by norm_num) (hj x)) hb
  have hz:=Guard.absMul (heV x) hc
  have HH:=abs_sub (e x) (2*j x*D x)
  dsimp [Cap.av] at *
  linarith
lemma trav_bav (a x:ℝ){f:ℝ→ℝ}(hf:Continuous f):
    trav a (liftF f) x=bav f (xs a,xs x):=by
  rw [trav_eq,← bav_norm ((a+x)/2) ((x-a)/2) f hf]
  congr 1
  unfold seg left right
  rw [show (a+x)/2-(x-a)/2=a from by ring, show (a+x)/2+(x-a)/2=x from by ring]
end GeneralMahler.SCal.Mid

end

end OAI
