import OAI.NumberTheory.DirichletL.Descent.FirstDyadicTail
import OAI.NumberTheory.DirichletL.Descent.OriginalZeroPhysical

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
open CompletedHeight SecondPassIntegration FourierBridge
local notation "O"=>ActualEisensteinCubic.O

theorem original_dyadic_zero_tail
    (om:𝓢(ℝ,ℂ))(b Mmax Fmax eta tau saving eps:ℝ)
    (hs:∀y,om y≠0→y≤b)(hMm:0≤Mmax)(hFm:0≤Fmax)(heta:0≤eta)(htau:0<tau)(heps:0<eps):
    ∃Czero Ctail:ℝ,0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta:ℝ),
      1<Z→2≤Z^eta→0≤M→M≤Mmax→0≤ell→0≤V→ (-eta≤r) → (r+3*ell+V≤Fmax)→0≤Γ→b≤Z^eta→
      (∀u,‖Ψ u‖≤1)→(∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))→
      (∀I∈labels,I≠0)→(∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))→
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ)→
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖weights i q‖≤1)→
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let mark:=fun (v:ι→₀ℕ) U=>primeMark slots lists weights (v.support∪U);
      Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun q C I=>
        canonicalCubeDualZero p hp hcop hg pool q C Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M))‖≤
          Czero*Γ^2*Z^(M-ell+3*eta+eps*(5*ell+2*r+7*eta)) ∧
      ‖reopenedPhysicalSourceSum pool Q labels β (fun q C I=>
        canonicalCubeDualTail p hp hcop hg pool q C Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M)
          (firstDyadicPhysicalCutoff p q C I Z M r ell V eta tau))‖≤Ctail*Γ^2*Z^(-saving):=by
  obtain ⟨Cz,hCz,hzero⟩:=original_first_zero_physical eps heps
  obtain ⟨s,Ct,hCt,htail⟩:=full_first_dyadic_marked_rapid_tail Mmax Fmax eta tau saving hMm hFm heta htau
  let G:=SchwartzMap.seminorm ℝ 0 0 om
  let Cz':=Cz*G^2*‖paperRadialFourier rowMajorant 0‖
  let Ct':=Ct*G^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)
  refine ⟨Cz',Ct',by dsimp [Cz'];positivity,by dsimp [Ct'];positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta
    hZ hbin hM hMmax hell hV hr hF hΓ hb hΨ hQ hn hlabels hβ hslots hw W mark
  have hz:0<Z:=zero_lt_one.trans hZ
  have hG:0≤G:=apply_nonneg _ _
  have hW:∀U,‖W (primeProductNorm p U)‖≤G:=by
    intro U
    simp only [W,normTwistedSource,norm_mul,logPhase_norm,one_mul]
    exact om.norm_le_seminorm ℝ _
  have hsupport:∀U,W (primeProductNorm p U)≠0→primeProductNorm p U≤Z^(r+eta):=by
    intro U hU
    have hnon:om (primeProductNorm p U/Z^r)≠0:=by
      intro hh
      exact hU (by simp [W,normTwistedSource,hh])
    have hle:primeProductNorm p U≤b*Z^r:=(div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mp (hs _ hnon)
    apply hle.trans
    calc
      b*Z^r≤Z^eta*Z^r:=mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hz.le _)
      _=Z^(r+eta):=by rw [←Real.rpow_add hz];congr 1;ring
  have hzero':=hzero p hp hcop hg hinj hc pool Q labels β Ψ m slots lists weights W rowMajorant
    Z M r ell V eta Γ G hZ (by linarith) (by linarith) hΓ hG hΨ hQ hn hlabels hβ hslots hw hW hsupport
  have hcb:=reopenedCubeFamily_cube_norms p Q _ hQ
  have htail':=htail p hp hinj hcop hg hc pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
    Ψ Ψ m m slots lists weights (fun q=>q.rightExponent.support) (fun q=>q.leftExponent.support)
    (fun _ U=>W (primeProductNorm p U)) (fun _ U=>W (primeProductNorm p U)) rowMajorant Z M r ell V
    (Γ^2) G G hZ hbin hM hMmax hell hV hr hF (sq_nonneg _) hG hG hΨ hΨ
    (reopenedCubeFamily_admissible Q) (fun q hq=>(hcb q hq).1) (fun q hq=>(hcb q hq).2)
    hn hlabels (fun q hq C _ I hI=>reopenedPairCoefficient_bound Q labels β Γ hΓ hβ q hq C I hI)
    hslots hw (fun _ _=>Finset.subset_union_right) (fun _ _=>Finset.subset_union_left)
    (fun _ _=>hW) (fun _ _=>hW) (fun _ _=>hsupport) (fun _ _=>hsupport)
  constructor
  · simpa only [mark,Finset.union_comm,Cz',G,mul_assoc,mul_left_comm,mul_comm] using hzero'
  · simpa only [mark,reopenedPhysicalSourceSum,Ct',pow_two,mul_assoc,mul_left_comm,mul_comm] using htail'

end SevenEighths.InverseMoment

end

end OAI
