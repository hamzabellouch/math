import OAI.NumberTheory.DirichletL.Descent.FirstDyadicLiveRadius

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem first_live_cell_radius_one {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y Z M r ell V eta tau:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K:ℝ)
    (hlabels:∀I∈labels,I≠0):
    let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
    ∀k∈liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool
      (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K),1≤firstCellRadius Z M r ell V eta tau k.1 k.2.2:=by
  intro cutoff k hk
  obtain ⟨⟨x,j⟩,hm,rfl⟩:=Finset.mem_image.mp hk
  obtain ⟨hm,hnon⟩:=Finset.mem_filter.mp hm
  have hx:=(Finset.mem_product.mp hm).1
  have hweight:firstOriginalWeight p β cutoff x.1 x.2≠0:=by
    intro hh
    exact hnon (sourceSummand_zero_of_weight p hp hcop hg β cutoff Ψ m mark W Φ K x j hh)
  have hrow:=original_weight_frequency p β cutoff x hweight
  obtain ⟨ho,hf⟩:=Finset.mem_sigma.mp hx
  obtain ⟨hI,hfreq⟩:=(mem_firstRetainedSource p labels x.1.1 Y x.2).mp hf
  have hfreq0:x.2.2≠0:=(Finset.mem_erase.mp hfreq).1
  have hE:=firstPhysicalMultiplier_ne_zero p hp x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
    x.1.1.leftBit x.1.1.rightBit x.2.1 (hlabels _ hI)
  have hn:= (mem_childFrequencyBall _ hE _ _).mp hrow
  have hone:=EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (mul_ne_zero hE hfreq0)
  have href:x.1∈refinedOuter p pool Q (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
      (labelGate p (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))):=by
    rw [refinedOuter_label]
    refine Finset.mem_filter.mpr ⟨?_,rfl⟩
    exact InverseFirstGlobalCaps.sourceCell_outer p pool Q labels Y _ _ (Finset.mem_filter.mpr ⟨hx,rfl⟩)
  change 1≤firstCellRadius Z M r ell V eta tau (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
    (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))
  rw [←first_dyadic_radius_cell p pool Q _ _ x.1 href]
  exact hone.trans hn

end SevenEighths.InverseMoment

end

end OAI
