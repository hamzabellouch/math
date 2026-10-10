import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileAssembly
import OAI.NumberTheory.DirichletL.Descent.CubeSupportNorm

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentFirstLiveCaps
open InverseMoment InverseMomentFirstOriginalProfile ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

lemma factor_four_bound (a b c d L:ℝ)(ha:1≤a)(hb:1≤b)(hc:1≤c)(hd:1≤d)
    (h:a*b*c*d≤L): a≤L ∧ b≤L ∧ c≤L ∧ d≤L:=by
  have ha0:0≤a:=zero_le_one.trans ha
  have hb0:0≤b:=zero_le_one.trans hb
  have hc0:0≤c:=zero_le_one.trans hc
  have hd0:0≤d:=zero_le_one.trans hd
  have hab:1≤a*b:=ha.trans (le_mul_of_one_le_right ha0 hb)
  have habc:1≤a*b*c:=hab.trans (le_mul_of_one_le_right (mul_nonneg ha0 hb0) hc)
  have habd:1≤a*b*d:=hab.trans (le_mul_of_one_le_right (mul_nonneg ha0 hb0) hd)
  have ha':a≤a*b*c*d:=by
    calc
      a≤a*b:=le_mul_of_one_le_right ha0 hb
      _≤a*b*c:=le_mul_of_one_le_right (mul_nonneg ha0 hb0) hc
      _≤a*b*c*d:=le_mul_of_one_le_right (mul_nonneg (mul_nonneg ha0 hb0) hc0) hd
  have hb':b≤a*b*c*d:=by
    calc
      b≤a*b:=le_mul_of_one_le_left hb0 ha
      _≤a*b*c:=le_mul_of_one_le_right (mul_nonneg ha0 hb0) hc
      _≤a*b*c*d:=le_mul_of_one_le_right (mul_nonneg (mul_nonneg ha0 hb0) hc0) hd
  have hc':c≤a*b*c*d:=by
    calc
      c≤a*b*c:=le_mul_of_one_le_left hc0 hab
      _≤a*b*c*d:=le_mul_of_one_le_right (mul_nonneg (mul_nonneg ha0 hb0) hc0) hd
  exact ⟨ha'.trans h,hb'.trans h,hc'.trans h,(le_mul_of_one_le_left hd0 habc).trans h⟩

theorem first_profile_live_factors (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L:ℝ)(q:Fin 9→ℝ)
    (hq:∀i,1≤q i)(hW:∀x,W x≠0→x≤L)
    (hn:firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K q≠0):
    q 0≤L ∧ q 1≤L ∧ q 2≤L ∧ q 5≤L:=by
  have h₁:W (q 0*q 2*q 5*q 7)≠0:=by
    intro h
    apply hn
    simp [firstNormProfile,h]
  have h₂:W (q 1*q 2*q 5*q 8)≠0:=by
    intro h
    apply hn
    simp [firstNormProfile,h]
  have hb₁:=factor_four_bound (q 0) (q 2) (q 5) (q 7) L (hq _) (hq _) (hq _) (hq _) (hW _ h₁)
  have hb₂:=factor_four_bound (q 1) (q 2) (q 5) (q 8) L (hq _) (hq _) (hq _) (hq _) (hW _ h₂)
  exact ⟨hb₁.1,hb₂.1,hb₁.2.1,hb₁.2.2.1⟩

variable {ι:Type*}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_live_profile_caps
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L:ℝ)
    (hW:∀y,W y≠0→y≤L)(x:OriginalIndex ι)
    (hx:x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y)
    (j:FirstCommonIndex ι)
    (hn:sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K x j≠0):
    leftNorm p x≤L ∧ rightNorm p x≤L ∧ commonNorm p x≤L ∧ primeProductNorm p j.2.1≤L:=by
  have hq:∀i,1≤firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
      (divisorElement p x.1) x.2.2 j i:=by
    have hs:=original_source_norms_ge_one p hp pool Q labels Y x hx
    intro i
    fin_cases i
    · exact hs 0
    · exact hs 1
    · exact hs 2
    · exact hs 3
    · exact hs 4
    · exact primeProductNorm_ge_one p hp _
    · exact hs 5
    · exact primeProductNorm_ge_one p hp _
    · exact primeProductNorm_ge_one p hp _
  have hprof:firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K
      (firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
        (divisorElement p x.1) x.2.2 j)≠0:=by
    intro hz
    exact hn (by unfold sourceSummand;rw [hz,mul_zero])
  exact first_profile_live_factors W Φ K L _ hq hW hprof

end SevenEighths.InverseMomentFirstLiveCaps

end

end OAI
