import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.TemplateRightWeight

namespace OAI

section
section
noncomputable section
open Set
open scoped BigOperators

namespace WeakMTWTransport
section ActiveDifference
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup E] [Module ℝ E]

omit [DecidableEq ι] in
lemma active_difference_ne_bot {pj : ι → E} {p : E} {m : ι → ℝ}
    {level : E → ℝ} {Bc Bo : ℝ → ℝ} (hsum : ∑ i,m i=1)
    (hprofiles : Bc (level p) ≤ Bo (level p))
    (hparameter : 0 < Bc (level p)-∑ i,m i*Bo (level (pj i))) :
    Submodule.span ℝ (range (fun i => pj i-p))≠⊥ := by
  intro H
  have hpj : ∀ i,pj i=p := by
    intro i
    have HH := (Submodule.subset_span (mem_range_self i) :
      pj i-p∈Submodule.span ℝ (range (fun i => pj i-p)))
    rw [H] at HH
    exact sub_eq_zero.mp HH
  simp_rw [hpj] at hparameter
  rw [←Finset.sum_mul,hsum,one_mul] at hparameter
  linarith

omit [DecidableEq ι] in
lemma line_active_displacements {pj : ι → E} {p e : E} {m : ι → ℝ}
    (hline : Submodule.span ℝ (range (fun i => pj i-p))=Submodule.span ℝ {e})
    (he : e≠0) (hsum : ∑ i,m i=1) (hbar : ∑ i,m i • pj i=p) :
    ∃ d : ι → ℝ, (∀ i,pj i=p+d i • e) ∧ ∑ i,m i*d i=0 := by
  have H : ∀ i,∃ r:ℝ,r • e=pj i-p := by
    intro i
    apply Submodule.mem_span_singleton.mp
    rw [←hline]
    exact Submodule.subset_span (mem_range_self i)
  choose d hd using H
  have hd' : ∀ i,pj i=p+d i • e := by
    intro i
    rw [hd i,add_sub_cancel]
  refine ⟨d,hd',?_⟩
  have Hbar : (∑ i,m i*d i) • e=0 := by
    rw [Finset.sum_smul]
    simp_rw [mul_smul,hd,smul_sub]
    rw [Finset.sum_sub_distrib,←Finset.sum_smul,hsum,one_smul,hbar,sub_self]
  exact (smul_eq_zero.mp Hbar).resolve_right he

end ActiveDifference
end WeakMTWTransport

end

end

section

noncomputable section
open Set
open scoped BigOperators

namespace WeakMTWTransport
section OutwardGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma norm_increment_unit_line {p e : E} (he : ‖e‖=1) (d : ℝ) :
    ‖p+d • e‖^2-‖p‖^2=2*(inner ℝ p e)*d+d^2 := by
  have hee : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he]; norm_num
  rw [←real_inner_self_eq_norm_sq]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,inner_smul_right,
    real_inner_comm e p,hee,real_inner_self_eq_norm_sq]
  ring

lemma outward_active_endpoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : Fintype.card ι ≤ n+1) {pj : ι → E} {p e : E}
    {m B si : ι → ℝ} {D c eta delta zeta s center a0 : ℝ}
    (hm : ∀ i,0 < m i) (hsum : ∑ i,m i=1) (hbar : ∑ i,m i • pj i=p)
    (he : ‖e‖=1) (hq : 0 < inner ℝ p e)
    (hline : Submodule.span ℝ (range (fun i => pj i-p))=Submodule.span ℝ {e})
    (hD : 0 < D) (hc : 0 < c) (ha0 : 0 < a0) (hqa : a0*D ≤ (inner ℝ p e)^2)
    (heta : eta ≤ 1/128) (hdelta : delta ≤ zeta) (hzeta : zeta ≤ 1/16)
    (hs : s < 3/4) (hlow : ∀ i,-2*eta ≤ si i)
    (hrange : ∀ i,|si i-s| ≤ 1+delta)
    (hnorm : ∀ i,|‖pj i‖^2-‖p‖^2+2*D*(si i-s)| ≤ zeta*D)
    (hB : ∀ i,0 ≤ B i) (hleft : ∀ i,si i < 1-eta → 1 ≤ B i)
    (hcenter : center ≤ 1) (hparameter : c ≤ center-∑ i,m i*B i) :
    let mstar := c/(12*(n+1:ℝ))
    let theta0 := min (mstar/2) (a0/3)
    ∃ i d, 0 < d ∧ pj i=p+d • e ∧ mstar ≤ m i ∧
      c*D/(8*(n+1:ℝ)*(inner ℝ p e)) ≤ m i*d ∧
      d ≤ 3*D/(2*(inner ℝ p e)) ∧ -2*eta ≤ si i ∧ si i < 1-eta ∧
      B i ≤ 12*(n+1:ℝ)/c ∧ 0 < theta0 ∧
      ∀ theta∈Icc (-theta0) 1,
        p+theta • (pj i-p)∈convexHull ℝ (range pj) ∧
        (inner ℝ p e)/2 ≤ inner ℝ (p+theta • (pj i-p)) e ∧
        ‖pj i-p‖^2/(inner ℝ (p+theta • (pj i-p)) (pj i-p)) ≤ 3/a0 := by
  intro mstar theta0
  have he0 : e≠0 := by intro H; rw [H,norm_zero] at he; norm_num at he
  obtain ⟨d,hd,hbard⟩ := line_active_displacements hline he0 hsum hbar
  have hnorm' : ∀ i,|2*(inner ℝ p e)*d i+d i^2+2*D*(si i-s)| ≤ zeta*D := by
    intro i
    have H := hnorm i
    rwa [hd i,norm_increment_unit_line he (d i)] at H
  obtain ⟨i,hdi,hmi,hprod,hdub,hli,hri,hBi⟩ := outward_from_levels hn hm hsum hbard hq hD hc
    heta hdelta hzeta hs hlow hrange hnorm' hB hleft hcenter hparameter
  have hmstar : 0 < mstar := by dsimp [mstar]; positivity
  have ht0 : 0 < theta0 := lt_min (half_pos hmstar) (by positivity)
  refine ⟨i,d i,hdi,hd i,hmi,hprod,hdub,hli,hri,hBi,ht0,?_⟩
  intro theta htheta
  have hlowtheta : -m i/2 ≤ theta := by
    have HH : theta0 ≤ mstar/2 := min_le_left _ _
    linarith only [htheta.1,HH,hmi]
  have hthetaa : -a0/3 ≤ theta := by
    have HH : theta0 ≤ a0/3 := min_le_right _ _
    linarith only [htheta.1,HH]
  have Hconv := barycenter_opposite_extension pj m (fun j => (hm j).le) hsum i hlowtheta htheta.2
  rw [hbar] at Hconv
  have hpie : pj i-p=d i • e := by rw [hd i]; module
  have hee : inner ℝ e e=1 := by rw [real_inner_self_eq_norm_sq,he]; norm_num
  have Hrad := outward_radial_ratio hq ha0 hdi hqa hdub hthetaa
  refine ⟨Hconv,?_,?_⟩
  · simpa only [hpie,inner_add_left,real_inner_smul_left,hee,mul_one] using Hrad.1
  · have Hn : ‖pj i-p‖^2=d i^2 := by
      rw [hpie,norm_smul,he,mul_one,Real.norm_eq_abs,sq_abs]
    have Hi : inner ℝ (p+theta • (pj i-p)) (pj i-p)=
        (inner ℝ p e+theta*d i)*d i := by
      rw [hpie]
      simp only [inner_add_left,inner_smul_right,real_inner_smul_left,hee]
      ring
    rw [Hn,Hi]
    exact Hrad.2

end OutwardGeometry
end WeakMTWTransport

end

end

end

end OAI
