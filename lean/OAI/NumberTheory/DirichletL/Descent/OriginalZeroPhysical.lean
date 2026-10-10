import OAI.NumberTheory.DirichletL.Descent.ReopenedZeroEnergy
import OAI.NumberTheory.DirichletL.Descent.PhysicalExponents

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_first_zero_physical (ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
      (Z M r ell V eta Γ G:ℝ),1<Z→0≤ell+eta→0≤V+eta→0≤Γ→0≤G→
      (∀u,‖Ψ u‖≤1)→
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))→
      (∀I∈labels,I≠0)→(∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))→
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ)→
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→
      (∀U,‖W (primeProductNorm p U)‖≤G)→
      (∀U,W (primeProductNorm p U)≠0→primeProductNorm p U≤Z^(r+eta))→
      Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
        canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists a (U∪b.rightExponent.support)*W (primeProductNorm p U))
          (fun U=>primeMark slots lists a (U∪b.leftExponent.support)*W (primeProductNorm p U)) Φ (Z^M))‖≤
        C*Γ^2*G^2*‖paperRadialFourier Φ 0‖*Z^(M-ell+3*eta+ε*(5*ell+2*r+7*eta)):=by
  obtain ⟨C,hC,he⟩:=original_reopened_marked_zero_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool Q labels β Ψ m slots lists a W Φ Z M r ell V eta Γ G
    hZ hell hV hΓ hG hΨ hQ hn hlabels hβ hslots ha hW hs
  have hz:0<Z:=zero_lt_one.trans hZ
  have hb:=he p hp hcop hg hinj hc pool Q labels β Ψ m slots lists a W Φ Γ G
    (Z^(r+eta)) (Z^M) (Z^(ell+eta)) (Z^(V+eta)) hΓ hG
    (Real.rpow_pos_of_pos hz _) (Real.one_le_rpow hZ.le hell) (Real.one_le_rpow hZ.le hV)
    hΨ hQ hn hlabels hβ hslots ha hW hs
  apply (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hz.le _)).trans
  apply le_of_eq
  rw [abs_of_pos (Real.rpow_pos_of_pos hz M)]
  have hp2 (x:ℝ):(Z^x)^2=Z^(2*x):=by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le];congr 1;ring
  rw [hp2,←Real.rpow_add hz,←Real.rpow_mul hz.le,←Real.rpow_mul hz.le,hp2]
  calc
    _=(C*Γ^2*G^2*‖paperRadialFourier Φ 0‖)*
      (Z^(-r-2*ell-V)*Z^((ell+eta)*(1+ε))*Z^(r+eta)*Z^(V+eta)*
        Z^(2*((2*(ell+eta)+(r+eta))*ε))*Z^M):=by ring
    _=_:=by
      rw [←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
      congr 2
      ring

end SevenEighths.InverseMoment

end

end OAI
