import OAI.NumberTheory.DirichletL.Descent.FirstDyadicCell
import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLivePartition

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem first_dyadic_original_cap (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (Z M r ell V eta tau Fmax:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hM:0≤M)
    (hF:r+3*ell+V≤Fmax)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)):
    ∀x∈firstOriginalOuter pool Q,firstDyadicRadius p x.1 x.2.1 x.2.2 Z M r ell V eta tau≤Z^(2*Fmax+15*eta+tau):=by
  intro x hx
  have hm:=(mem_firstOriginalOuter pool Q x).mp hx
  have hb:=reopenedCubeFamily_cube_norms p Q _ hQ x.1 hm.1
  exact first_dyadic_radius_global_cap p hp x.1 x.2.1 x.2.2 (Finset.mem_powerset.mp hm.2.2)
    Z M r ell V eta tau Fmax hZ hbin hM hF hb.1 hb.2

include hp in
theorem first_live_cell_radius_cap (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (labels:Finset (Ideal O))(Y:ℝ)(term:OriginalIndex ι→FirstCommonIndex ι→ℂ)
    (Z M r ell V eta tau Fmax:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hM:0≤M)
    (hF:r+3*ell+V≤Fmax)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (k:JointKey)(hk:k∈liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool term):
    firstCellRadius Z M r ell V eta tau k.1 k.2.2≤Z^(2*Fmax+15*eta+tau):=by
  obtain ⟨⟨x,j⟩,hx,rfl⟩:=Finset.mem_image.mp hk
  have hm:=Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have ho: x.1∈firstOriginalOuter pool Q:=(Finset.mem_sigma.mp hm.1).1
  have href:x.1∈refinedOuter p pool Q (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
      (labelGate p (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))):=by
    rw [refinedOuter_label]
    apply Finset.mem_filter.mpr
    refine ⟨?_,rfl⟩
    apply InverseFirstGlobalCaps.sourceCell_outer p pool Q labels Y
    exact Finset.mem_filter.mpr ⟨hm.1,rfl⟩
  change firstCellRadius Z M r ell V eta tau (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
    (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))≤_
  rw [←first_dyadic_radius_cell p pool Q _ _ x.1 href]
  exact first_dyadic_original_cap p hp pool Q Z M r ell V eta tau Fmax hZ hbin hM hF hQ x.1 ho

end SevenEighths.InverseMoment

end

end OAI
