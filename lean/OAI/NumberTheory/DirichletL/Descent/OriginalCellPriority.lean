import OAI.NumberTheory.DirichletL.Descent.GlobalCanonicalEnergy
import OAI.NumberTheory.DirichletL.Inversion.FirstGlobalCaps

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic
open InverseFirstPriorityParents InverseFirstGlobalParents
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]

def originalSubsetSource (outer:Finset (FirstOriginalOuter ι)):Finset (Source ι 0):=
  outer.image ofOriginal

theorem original_subset_canonical_priority
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (outer:Finset (FirstOriginalOuter ι))(pool:Finset ι)
    (selector:FirstOriginalOuter ι→Finset ι→ℂ)(extra:CubeCoordinates ι→Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj pool k.1 k.2.1
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) k.2.2)
      (fun U=>primeMark slots lists a (extra k.1∪U)) (selector k) om X t Y) ≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool
      (globalParentSource (originalSubsetSource outer) pool (originalSelector selector))
      (fun x=>(‖selector (toOriginal x) x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y:=by
  have hempty:∀x∈originalSubsetSource outer,x.quotientSupport=∅:=by
    intro x hx
    obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hx
    rfl
  have he:=global_canonical_to_original_priority p hp hg hinj hc
    (originalSubsetSource outer) pool (originalSelector selector) hempty extra
    negative Ψ m slots lists a om X t Y hY
  rw [show originalSubsetSource outer=outer.image ofOriginal from rfl,
    Finset.sum_image (fun _ _ _ _ h=>ofOriginal_injective h)] at he
  have hs (k:FirstOriginalOuter ι): originalSelector selector (ofOriginal k)=selector k :=
    originalSelector_ofOriginal_fun selector k
  simp_rw [hs] at he
  simpa only [originalSubsetSource,ofOriginal,originalSelector,toOriginal,eraseFirstQuotient] using he

theorem original_cell_parent_source
    (p:ι→O)(pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (selector:FirstOriginalOuter ι→Finset ι→ℂ)
    (k:InverseMomentFirstChildWindows.SourceIndex)(l:ℕ):
    globalParentSource (originalSubsetSource (InverseFirstGlobalCaps.outerCell p pool Q k))
      pool (originalSelector (fun x=>InverseMomentFirstChildWindows.commonSelector p (selector x) l))=
      InverseFirstGlobalCaps.parentCell p pool Q selector k l:=by
  ext x
  rw [InverseFirstGlobalCaps.mem_parentCell]
  simp only [globalParentSource,Finset.mem_biUnion,originalSubsetSource,Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨y,⟨o,ho,rfl⟩,D,⟨hD,hs⟩,he⟩
    exact ⟨o,ho,D,hD,by simpa using hs,he⟩
  · rintro ⟨o,ho,D,hD,hs,he⟩
    exact ⟨ofOriginal o,⟨o,ho,rfl⟩,D,⟨hD,by simpa using hs⟩,he⟩

theorem original_cell_canonical_priority
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(selector:FirstOriginalOuter ι→Finset ι→ℂ)
    (k:InverseMomentFirstChildWindows.SourceIndex)(l:ℕ)
    (extra:CubeCoordinates ι→Finset ι)(negative:Bool)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑o∈InverseFirstGlobalCaps.outerCell p pool Q k,
      firstCanonicalSecondEnergy p hp hg hinj pool o.1 o.2.1 negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) o.2.2)
        (fun U=>primeMark slots lists a (extra o.1∪U))
        (InverseMomentFirstChildWindows.commonSelector p (selector o) l) om X t Y)≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool
      (InverseFirstGlobalCaps.parentCell p pool Q selector k l)
      (fun x=>(‖InverseMomentFirstChildWindows.commonSelector p (selector (toOriginal x)) l x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y:=by
  have he:=original_subset_canonical_priority p hp hg hinj hc
    (InverseFirstGlobalCaps.outerCell p pool Q k) pool
    (fun x=>InverseMomentFirstChildWindows.commonSelector p (selector x) l) extra negative Ψ m slots lists a om X t Y hY
  rwa [original_cell_parent_source] at he

end SevenEighths.InverseMoment

end

end OAI
