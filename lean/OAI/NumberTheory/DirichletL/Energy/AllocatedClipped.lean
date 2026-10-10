import OAI.NumberTheory.DirichletL.Energy.AllocatedPaid
import OAI.NumberTheory.DirichletL.Energy.AllocatedZero

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyAllocatedClipped
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

def pair (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    {a b:ℝ}(ha:0<a)(p:Profiles a b)(v X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    Profiles (a/max 1 b) b :=
  retainedPair a b ha p ![rawScale D alloc X₁ 0,rawScale D alloc X₂ 1]
    (by intro i;fin_cases i;exact rawScale_pos D alloc X₁ hX₁ 0;exact rawScale_pos D alloc X₂ hX₂ 1) v

def scale (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (X:ℝ)(j:Fin 2)(F:Finset (Ideal O)):ℝ:=
  clippedScale (rawScale D alloc X j)/((∏I∈F,I).absNorm:ℝ)

lemma scale_pos (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (X:ℝ)(j:Fin 2)(F:Finset (Ideal O))(hF:∀I∈F,I≠0):0<scale D alloc X j F:=by
  have hn:0<((∏I∈F,I).absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hF))
  exact div_pos (by unfold clippedScale;positivity) hn

lemma scale_cap (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (Z L X:ℝ)(hZ:1≤Z)(hL:0≤L)(hX:0<X)(hc:X≤Z^L)
    (j:Fin 2)(F:Finset (Ideal O))(hF:∀I∈F,I≠0):scale D alloc X j F≤Z^L:=
  (allocatedScale_le D alloc X hX j F hF).trans (max_le (Real.one_le_rpow hZ hL) hc)

lemma allocated_pair {Z Bmask bΦ a b:ℝ}(st:NaturalState Z Bmask bΦ)(hunit:st.puncture=1)
    (D:Ideal O)(alloc:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (ha:0<a)(p:Profiles a b)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (v X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(F₁ F₂:Finset (Ideal O))(J:Finset α):
    allocatedEnergy st.character st.radial D alloc
      (sourcePlain a b ha (p.profile 0) (p.support 0))
      (sourcePlain a b ha (p.profile 1) (p.support 1)) pool β P v X₁ X₂ hX₁ hX₂ F₁ F₂ J =
    energy st.character st.mask 1 0
      ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).profile 0)
      ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).profile 1)
      (fun i:↥(liveIndices D alloc\J)=>pool i)
      (fun i:↥(liveIndices D alloc\J)=>CenteredMomentCommonMaskEnergy.heightCoefficient (β i) v)
      (fun i:↥(liveIndices D alloc\J)=>P i)
      (scale D alloc X₁ 0 F₁) (scale D alloc X₂ 1 F₂)
      st.radial.keep st.radial.profile st.radial.scale:=by
  simp only [allocatedEnergy,pair,retainedPair,scale,NaturalState.mask,hunit,
    Matrix.cons_val_zero,Matrix.cons_val_one]

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_clipped_paid_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hbΦ:0≤bΦ)(hLs:0≤Lslot)(hε:0<εremove)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀(a b Bmask L εchild:ℝ)(ha:0<a),0≤L → ∀Q:Ideal O,Q≤M →
    ∀(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ),0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀st:NaturalState Z Bmask bΦ,st.puncture=1 → st.fixedModulus=internalQ Q η₀ → st.width≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src st.character v) C R B
    allocatedEnergy st.character st.radial D alloc
      (sourcePlain a b ha (p.profile 0) (p.support 0))
      (sourcePlain a b ha (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl st.radial.profile*
        ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).control S)^2*
        (1+(|v|+height))^(dc+degree)*
        Z^(st.width+εchild+εremove+
          CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hbound⟩:=actual_allocated_paid_bands (α:=α) M H hH W aslot bslot Mcap bΦ Lslot
    εremove lo hi κ ha hWs hW hMcap hbΦ hLs hε hbeta hκ
  refine ⟨dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ a b Bmask L εchild ha hL Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only
  rw [allocated_pair st hunit]
  exact hbound Z hZ (a/max 1 b) b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs (pair D alloc ha p v X₁ X₂ hX₁ hX₂)
    (scale D alloc X₁ 0 F₁) (scale D alloc X₂ 1 F₂)
    (scale_pos D alloc X₁ 0 F₁ hF₁) (scale_pos D alloc X₂ 1 F₂ hF₂)
    (scale_cap D alloc Z L X₁ st.base_ge_one hL hX₁ hc₁ 0 F₁ hF₁)
    (scale_cap D alloc Z L X₂ st.base_ge_one hL hX₂ hc₂ 1 F₂ hF₂)

end SevenEighths.CenteredMomentEnergyAllocatedClipped

end

end OAI
