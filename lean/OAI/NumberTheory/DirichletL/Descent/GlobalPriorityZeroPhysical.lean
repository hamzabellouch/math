import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityZero

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion FirstCauchyArithmetic
open InverseSecondPrincipalCaller InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass
local notation "O"=>ActualEisensteinCubic.O

theorem global_priority_zero_physical (ε:ℝ)(hε:0<ε)(Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall):
    ∃(s:Finset (ℕ×ℕ))(Czero:ℝ),0<Czero ∧
    ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (Jo:ℕ),Jo≤Jmax→∀(extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)
      (original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)(negative:Bool)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→(∀u,‖Ψ u‖≤1)→
      (∀x∈original,‖w x‖≤1)→
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (Z M r ell V delta A B Ractive j t eta tau window pi height:ℝ)(R:Finset ι→Finset ι→ℝ),
      1≤Z→0≤ell+eta→0≤B→0≤j→
      ε*(r-A-B-t)+7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*ε*(2*ell+B+t+4*eta)≤pi+eta/2→
      (∀x∈original,SourceValid p x)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^(B+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^(t+eta))→
      (∀x∈original,extra x.cube⊆x.cube.support)→
      hi≤Real.exp window→1≤Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)→(∀G E,0≤R G E)→
      (Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityZeroAggregate p hg extra pool original w negative Ψ m slots lists a
        (principalWindow om lo hi hlo hs negative height) (Z^(r-A-B-t))
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) R≤
      Czero*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Real.exp (window*(1+ε))*
        Z^(r+3*ell+V+17*eta+tau+pi):=by
  obtain ⟨s,Cp,hCp,hprincipal⟩:=global_priority_zero_aggregate ε hε
  obtain ⟨Cm,hCm,hmass⟩:=original_physical_weighted_source Jmax dsmall hdsmall
  refine ⟨s,Cp*Cm,mul_pos hCp hCm,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop Jo hJo extra pool original w negative Ψ m slots lists a
    hslots ha hΨ hw om lo hi hlo hs Z M r ell V delta A B Ractive j t eta tau window pi height R
    hZ hell hB hj hcost hsource hc₁ hc₂ hactive hcommon hquot hextra hhi hY hR
  have hz:0<Z:=zero_lt_one.trans_le hZ
  let P:=Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let Q:=Cp*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
    (SchwartzMap.seminorm ℝ 0 0 om)^2
  have hP:0≤P:=by dsimp [P];positivity
  have hQ:0≤Q:=by dsimp [Q];positivity
  have he:=mul_le_mul_of_nonneg_left (hprincipal p hp hg hinj hcop extra pool original w negative Ψ m slots lists a
    hslots ha hΨ hw om lo hi hlo hs (Z^(r-A-B-t)) window
    (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) height R (by positivity) hhi hY hR) hP
  have hm:=hmass p hp hinj Jo hJo original Z M r ell V delta A B Ractive j t eta tau ε window pi
    hZ hell hε.le hB hj hcost hsource hc₁ hc₂ hactive hcommon hquot extra negative hextra
  have hsupp(x:Source ι Jo):wholeExtractedSupport (fun x=>extra x.cube) negative x=principalSupport extra negative x:=by
    simp only [wholeExtractedSupport,extractedSupport,principalSupport,Finset.union_assoc]
  simp_rw [hsupp] at he
  apply he.trans
  calc
    _=Q*(physicalPrincipalFactor Z M r ell V delta A B Ractive j t eta tau ε window*
      ∑x∈original,(primeProductNorm p (principalSupport extra negative x))^(2*ε)):=by
      dsimp [Q,P,physicalPrincipalFactor];ring
    _≤Q*(Cm*Real.exp (window*(1+ε))*Z^(r+3*ell+V+17*eta+tau+pi)):=mul_le_mul_of_nonneg_left hm hQ
    _= _:=by dsimp [Q];ring
end SevenEighths.InverseMoment

end

end OAI
