import OAI.NumberTheory.DirichletL.Descent.FirstLiveCaps
import OAI.NumberTheory.DirichletL.Inversion.FirstGlobalCaps

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentFirstLiveCaps
open InverseMoment InverseMomentFirstOriginalProfile ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_live_norm_caps
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L B:ℝ)
    (hB:0≤B)(hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B)
    (hlabels:∀I∈labels,I≠0)(hW:∀y,W y≠0→y≤L)(x:OriginalIndex ι)
    (hx:x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y)
    (j:FirstCommonIndex ι)
    (hn:sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K x j≠0):
    (∀i:Fin 6,originalNorms p x i≤(![L,L,L,L*B^2,B^2,Y]:Fin 6→ℝ) i) ∧
      primeProductNorm p j.2.1≤L ∧ InverseFirstGlobalCaps.jNorm p x.1≤B^2:=by
  obtain ⟨ha₁,ha₂,hcommon,hquot⟩:=original_live_profile_caps p hp hcop hg pool Q labels Y β cutoff Ψ m mark W Φ K L hW x hx j hn
  obtain ⟨ho,hfreq⟩:=Finset.mem_sigma.mp hx
  obtain ⟨hb,hC,hD⟩:=(mem_firstOriginalOuter pool Q x.1).mp ho
  obtain ⟨hf,hrow⟩:=(mem_firstRetainedSource p labels x.1.1 Y x.2).mp hfreq
  have hcube:=reopenedCubeFamily_cube_norms p Q B hQ x.1.1 hb
  have hsup:=cube_whole_support_dyad p hp x.1.1 B hB hcube.1 hcube.2
  have hdiv:primeProductNorm p x.1.2.2≤L*B^2:=by
    calc
      _≤primeProductNorm p (x.1.2.1∪cubePrincipalSupport x.1.1.support x.1.1.leftExponent
          x.1.1.rightExponent x.1.1.leftBit x.1.1.rightBit):=
        primeProductNorm_mono p hp (Finset.mem_powerset.mp hD)
      _≤primeProductNorm p x.1.2.1*primeProductNorm p x.1.1.support:=by
        apply (primeProductNorm_union_le_mul p hp _ _).trans
        exact mul_le_mul_of_nonneg_left (primeProductNorm_mono p hp (Finset.filter_subset _ _))
          (primeProductNorm_pos p hp _).le
      _≤L*B^2:=mul_le_mul hcommon hsup (primeProductNorm_pos p hp _).le
        ((primeProductNorm_pos p hp _).le.trans hcommon)
  have hactive:activeNorm p x≤B^2:=
    (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans hsup
  have hE:=firstPhysicalMultiplier_ne_zero p hp x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
    x.1.1.leftBit x.1.1.rightBit x.2.1 (hlabels _ hf)
  have hh0:x.2.2≠0:=(Finset.mem_erase.mp hrow).1
  have hh:=((mem_nonzeroChildFrequencyBall _ hE Y x.2.2).mp hrow).2
  have hfreqnorm:‖eisEmbedding x.2.2‖^2≤Y:=
    (element_norm_le_of_dvd (mul_ne_zero hE hh0) (dvd_mul_left x.2.2 _)).trans hh
  have hj:InverseFirstGlobalCaps.jNorm p x.1≤B^2:=by
    have hd:=jLabel_dvd_cube_product p x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
      x.1.1.leftBit x.1.1.rightBit x.1.1.support_pos
    have hnorm:=element_norm_le_of_dvd
      (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _)) hd
    simp only [map_mul,norm_mul,mul_pow] at hnorm
    exact hnorm.trans ((mul_le_mul hcube.1 hcube.2 (sq_nonneg _) hB).trans_eq (pow_two B).symm)
  refine ⟨?_,hquot,hj⟩
  intro i
  fin_cases i
  · exact ha₁
  · exact ha₂
  · exact hcommon
  · simpa [originalNorms,InverseMomentFirstChildWindows.sourceNorms,divisorElement,
      primeSubsetGenerator_norm_eq_productNorm] using hdiv
  · exact hactive
  · exact hfreqnorm

end SevenEighths.InverseMomentFirstLiveCaps

end

end OAI
