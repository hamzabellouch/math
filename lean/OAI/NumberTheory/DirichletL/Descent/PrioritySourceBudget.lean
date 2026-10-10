import OAI.NumberTheory.DirichletL.Descent.PriorityCellBudget

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
local notation "O"=>ActualEisensteinCubic.O

def priorityCellScalar (Z Y L X ell Ractive j t eta eps epsmass B:ℝ) (ray:ℂ) (d:BlockIndex):ℝ :=
  (Real.exp (6*L)*‖(Y:ℂ)*ray*((scales d 1*scales d 2*Z^(secondCellColumnExponent Z X d):ℝ):ℂ)⁻¹‖)*
    Z^((secondCount ell Ractive j t (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)*(1+epsmass))*
    Z^(2*(max 0 (secondCellColumnExponent Z X d)+
      (secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta))+eps)

theorem source_cell_joint_bound {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn)) (hk:∀x∈source,x.second.frequency≠0)
    (b X:ℝ) (hgeom:∀x∈source,primeProductNorm p x.second.sourceCommon*
      primeProductNorm p x.second.overlap≤b*X) (d:BlockIndex) (hd:d∈keys p source):
    scales d 0*scales d 2≤b*X := by
  obtain ⟨x,hx⟩:=(mem_keys_iff p source d).mp hd
  have h0:scales d 0≤primeProductNorm p x.second.sourceCommon:=by
    simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 0).1
  have h2:scales d 2≤primeProductNorm p x.second.overlap:=by
    simpa [outerNorms,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx 2).1
  exact (mul_le_mul h0 h2 (dyadScale_pos _).le (primeProductNorm_pos p hp _).le).trans
    (hgeom x (cell_subset p source d hx))

theorem priority_source_scalar_budget (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) :
    ∃ Cbin:ℝ,0≤Cbin ∧ ∀ {ι:Type*} [DecidableEq ι]
    (p:ι→O) (_hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B Ractive j t eta tau pi eps epsmass b C:ℝ)
    (ray:ℂ), 2≤Z → 0≤C → 1≤b → b≤Z^(6*eta) →
    (∀x∈source,x.second.frequency≠0) →
    (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
    (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*Z^(r-A-B-t)) →
    (∀d∈keys p source,epsmass*(secondCount ell Ractive j t (secondCellExponent Z d 0)
      (secondCellExponent Z d 1)+11*eta/2)≤pi) →
    C*Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))*
      (∑d∈keys p source,priorityCellScalar Z (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
        (eta*Real.log Z) (Z^(r-A-B-t)) ell Ractive j t eta eps epsmass B ray d) ≤
    C*‖ray‖*(1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+eps) := by
  refine ⟨capConstant caps,capConstant_nonneg caps hcaps,?_⟩
  intro ι _ p hp _ Jo Jn source Z M r ell V delta A B Ractive j t eta tau pi eps epsmass b C
    ray hZ hC hb hthreshold hk hnorm hgeom hmass
  have hZ':1<Z:=lt_of_lt_of_le (by norm_num) hZ
  have hz:0<Z:=zero_lt_one.trans hZ'
  have hcard:((keys p source).card:ℝ)≤(1+capConstant caps*Real.log Z)^4:=by
    have h:=keys_card_le_product p hp source hk caps Z hnorm
    have hr:((keys p source).card:ℝ)≤∏i:Fin 4,((dyadIndex (Z^(caps i)):ℝ)+1):=by exact_mod_cast h
    apply hr.trans
    calc
      _≤∏_i:Fin 4,(1+capConstant caps*Real.log Z):=
        Finset.prod_le_prod₀ (fun _ _=>by positivity) (fun i _=>cap_bin_bound caps hcaps Z hZ i)
      _= _:=by simp
  rw [Finset.mul_sum]
  calc
    _≤∑_d∈keys p source,C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps):=by
      apply Finset.sum_le_sum
      intro d hd
      have he:=priority_cell_physical_budget Z hZ' d M r ell V delta A B Ractive j t eta tau pi eps epsmass b C
        ray hC hb (source_cell_joint_bound p hp source hk b _ hgeom d hd) hthreshold (hmass d hd)
      convert he using 1 ; dsimp only [priorityCellScalar] ; ring
    _= ((keys p source).card:ℝ)*(C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps)):=by simp
    _≤ (1+capConstant caps*Real.log Z)^4*(C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps)):=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _= _:=by ring

end SevenEighths.InverseMoment

end

end OAI
