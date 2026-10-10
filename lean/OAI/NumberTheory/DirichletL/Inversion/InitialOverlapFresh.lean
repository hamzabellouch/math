import OAI.NumberTheory.DirichletL.Inversion.SecondChildWindows

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialOverlapFresh
variable {σ : Type*} [DecidableEq σ]

omit [DecidableEq σ] in
theorem overlap_column_interval (I : Finset σ) (lo hi y : σ→ℝ)
    (a b jlo jhi yj yc : ℝ) (ha : 0<a) (hab : a≤b)
    (hlo : ∀i∈I,0<lo i) (hy : ∀i∈I,y i∈Set.Icc (lo i) (hi i))
    (hjlo : 0<jlo) (hj : yj∈Set.Icc jlo jhi) (hc : 0<yc)
    (hsource : yj*yc/(∏i∈I,y i)∈Set.Icc a b) :
    yc∈Set.Icc (a*(∏i∈I,lo i)/jhi) (b*(∏i∈I,hi i)/jlo) := by
  have hyp : ∀i∈I,0<y i := fun i hi=>(hlo i hi).trans_le (hy i hi).1
  have hip : ∀i∈I,0<hi i := fun i hi=>(hyp i hi).trans_le (hy i hi).2
  have hprod : 0<∏i∈I,y i := Finset.prod_pos hyp
  have hloP : (∏i∈I,lo i)≤∏i∈I,y i :=
    Finset.prod_le_prod₀ (fun i hi=>(hlo i hi).le) (fun i hi=>(hy i hi).1)
  have hhiP : (∏i∈I,y i)≤∏i∈I,hi i :=
    Finset.prod_le_prod₀ (fun i hi=>(hyp i hi).le) (fun i hi=>(hy i hi).2)
  have hyj : 0<yj := hjlo.trans_le hj.1
  have hjhip : 0<jhi := hyj.trans_le hj.2
  have hsourceLo := (le_div_iff₀ hprod).mp hsource.1
  have hsourceHi := (div_le_iff₀ hprod).mp hsource.2
  constructor
  · apply (div_le_iff₀ hjhip).mpr
    calc
      a*(∏i∈I,lo i)≤a*(∏i∈I,y i) := mul_le_mul_of_nonneg_left hloP ha.le
      _≤yj*yc := hsourceLo
      _≤jhi*yc := mul_le_mul_of_nonneg_right hj.2 hc.le
      _=yc*jhi := mul_comm _ _
  · apply (le_div_iff₀ hjlo).mpr
    calc
      yc*jlo=jlo*yc := mul_comm _ _
      _≤yj*yc := mul_le_mul_of_nonneg_right hj.1 hc.le
      _≤b*(∏i∈I,y i) := hsourceHi
      _≤b*(∏i∈I,hi i) := mul_le_mul_of_nonneg_left hhiP (ha.le.trans hab)

omit [DecidableEq σ] in
theorem exists_overlap_fresh (I : Finset σ) (lo hi : σ→ℝ)
    (a b jlo jhi : ℝ) (ha : 0<a) (hab : a≤b)
    (hlo : ∀i∈I,0<lo i) (hhi : ∀i∈I,lo i≤hi i)
    (hjlo : 0<jlo) (hjhi : jlo≤jhi) :
    ∃(wFresh : 𝓢(ℝ,ℂ))(A B:ℝ),0<A ∧ A≤B ∧
      HasCompactSupport (wFresh:ℝ→ℂ) ∧ tsupport (wFresh:ℝ→ℂ)⊆Set.Icc A B ∧
      ∀(W:ℝ→ℂ),(Function.support W⊆Set.Icc a b)→
      ∀(y:σ→ℝ)(yj yc:ℝ),
      (∀i∈I,y i∈Set.Icc (lo i) (hi i))→yj∈Set.Icc jlo jhi→0<yc→
      W (yj*yc/(∏i∈I,y i))≠0→wFresh yc=1 := by
  let lower := a*(∏i∈I,lo i)/jhi
  let upper := b*(∏i∈I,hi i)/jlo
  have hl : 0<lower := div_pos (mul_pos ha (Finset.prod_pos hlo)) (hjlo.trans_le hjhi)
  have hu : 0<upper := div_pos (mul_pos (ha.trans_le hab)
    (Finset.prod_pos (fun i hi=>(hlo i hi).trans_le (hhi i hi)))) hjlo
  obtain ⟨w,hwc,hwone,hws⟩ := InverseSecondChildWindows.positive_cutoff
    lower (lower+upper+1) hl (by linarith)
  refine ⟨w,lower/2,lower+upper+2,half_pos hl,by linarith,hwc,?_,?_⟩
  · convert hws using 1 ; ring_nf
  · intro W hW y yj yc hy hj hc hn
    have hb := overlap_column_interval I lo hi y a b jlo jhi yj yc ha hab hlo hy hjlo hj hc (hW hn)
    apply hwone
    exact ⟨hb.1,by change yc≤lower+upper+1;have := hb.2;change yc≤upper at this;linarith⟩

end SevenEighths.InverseInitialOverlapFresh

end

end OAI
