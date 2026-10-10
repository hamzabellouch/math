import OAI.NumberTheory.DirichletL.Descent.FirstDyadicLiveRadius
import OAI.NumberTheory.DirichletL.Descent.FirstLiveNorms

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

lemma actual_dyadic_exponent_cap (Z eta x A:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hx:1≤x)(hcap:x≤Z^A):
    0≤dyadicExponent Z (dyadIndex x) ∧ dyadicExponent Z (dyadIndex x)≤A:=by
  have h:=first_dyadic_bounds Z eta x hZ hbin hx
  exact ⟨h.1,(Real.rpow_le_rpow_left_iff hZ).mp (h.2.1.trans hcap)⟩

theorem original_live_exponent_caps {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(om:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (K Z r ell F eta tau theta b:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)
    (hF:0≤F)(hr:r≤F)(hell:ell≤F)(heta:0≤eta)(htau:0≤tau)(hb:b≤Z^eta)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hlabels:∀I∈labels,I≠0)(hs:∀y,om y≠0→y≤b):
    let Y:=Z^(2*F+15*eta+tau);
    let W:=fun y=>normTwistedSource om theta (y/Z^r);
    let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
    ∀k∈liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K),
      (∀i,0≤dyadicExponent Z (k.1 i) ∧ dyadicExponent Z (k.1 i)≤3*F+15*eta+tau) ∧
      (0≤dyadicExponent Z k.2.1 ∧ dyadicExponent Z k.2.1≤3*F+15*eta+tau) ∧
      (0≤dyadicExponent Z k.2.2 ∧ dyadicExponent Z k.2.2≤3*F+15*eta+tau):=by
  intro Y W source k hk
  have hz:0<Z:=zero_lt_one.trans hZ
  have hW:∀y,W y≠0→y≤Z^(r+eta):=by
    intro y hy
    have hh:om (y/Z^r)≠0:=by intro hh;exact hy (by simp [W,normTwistedSource,hh])
    calc
      y≤b*Z^r:=(div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mp (hs _ hh)
      _≤Z^eta*Z^r:=mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hz.le _)
      _=Z^(r+eta):=by rw [←Real.rpow_add hz];congr 1;ring
  obtain ⟨⟨x,j⟩,hmem,rfl⟩:=Finset.mem_image.mp hk
  obtain ⟨hm,hnon⟩:=Finset.mem_filter.mp hmem
  obtain ⟨hx,hj⟩:=Finset.mem_product.mp hm
  obtain ⟨h₁,h₂,h₃⟩:=InverseMomentFirstLiveCaps.original_live_norm_caps p hp hcop hg pool Q labels Y β cutoff Ψ m mark W Φ K
    (Z^(r+eta)) (Z^(ell+eta)) (Real.rpow_nonneg hz.le _) hQ hlabels hW x hx j hnon
  have hlow:=original_source_norms_ge_one p hp pool Q labels Y x hx
  have hsq:(Z^(ell+eta))^2=Z^(2*ell+2*eta):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le];congr 1;norm_num;ring
  have hA:Z^(r+eta)≤Z^(3*F+15*eta+tau):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hB:(Z^(ell+eta))^2≤Z^(3*F+15*eta+tau):=by
    rw [hsq]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  have hAB:Z^(r+eta)*(Z^(ell+eta))^2≤Z^(3*F+15*eta+tau):=by
    rw [hsq,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  have hY:Y≤Z^(3*F+15*eta+tau):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  refine ⟨?_,?_,?_⟩
  · intro i
    apply actual_dyadic_exponent_cap Z eta _ _ hZ hbin (hlow i)
    apply (h₁ i).trans
    fin_cases i <;> first | exact hA | exact hAB | exact hB | exact hY
  · exact actual_dyadic_exponent_cap Z eta _ _ hZ hbin (primeProductNorm_ge_one p hp _) (h₂.trans hA)
  · exact actual_dyadic_exponent_cap Z eta _ _ hZ hbin
      (EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)) (h₃.trans hB)

end SevenEighths.InverseMoment

end

end OAI
