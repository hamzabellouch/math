import OAI.NumberTheory.DirichletL.Energy.AllocatedBound
import OAI.NumberTheory.DirichletL.Energy.AllocatedProfiles
import OAI.NumberTheory.DirichletL.Energy.Bands

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedZero
open HeckeFamily CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedProfiles
open CenteredMomentAllocatedNaturalSource CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentRetainedProfile CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

lemma allocatedScale_le (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(X:ℝ)(hX:0<X)
    (j:Fin 2)(F:Finset (Ideal O))(hF:∀I∈F,I≠0):
    clippedScale (rawScale D a X j)/(Ideal.absNorm (∏I∈F,I):ℝ)≤max 1 X:=by
  have hn:1≤(Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a j):ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (CenteredMomentDivisorExtraction.selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  have hf:1≤(Ideal.absNorm (∏I∈F,I):ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr hF))
  have hx:rawScale D a X j≤X:=div_le_self hX.le hn
  exact (div_le_self (by unfold clippedScale;positivity) hf).trans
    (max_le_max_left 1 hx)

lemma allocated_empty (η:Character)(r:Radial)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O)):
    allocatedEnergy η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ (liveIndices D a)=
      CenteredMomentCoreFloor.zeroEnergy η
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
        (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
        (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
        (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
        (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) r:=by
  let : IsEmpty ↥(liveIndices D a\liveIndices D a):=⟨fun i=>by
    have hi:=Finset.mem_sdiff.mp i.property
    exact hi.2 hi.1⟩
  simp only [allocatedEnergy,energy,CenteredMomentCoreFloor.zeroEnergy,
    CenteredMomentCoreFloor.zeroRow,positiveSlotRow,Fintype.prod_empty,mul_one]

theorem empty_from_zeroAt (lo hi Z Bmask bΦ L Mcap ε:ℝ)(hlo:0<lo)(hL:0≤L)
    (Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hz:ZeroAt Q (lo/max 1 hi) hi bΦ Bmask L Mcap ε Z degree S C)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)(hwidth:s.width≤Mcap)
    (hunit:s.puncture=1)(p:Profiles lo hi)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O))
    (hD₁:∀I∈D₁,I≠0)(hD₂:∀I∈D₂,I≠0)
    (hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L):
    let V₁:=sourcePlain lo hi hlo (p.profile 0) (p.support 0)
    let V₂:=sourcePlain lo hi hlo (p.profile 1) (p.support 1)
    let U:Fin 2→ℝ:=![rawScale D a X₁ 0,rawScale D a X₂ 1]
    let hU:∀i,0<U i:=by intro i;fin_cases i;exact rawScale_pos D a X₁ hX₁ 0;exact rawScale_pos D a X₂ hX₂ 1
    allocatedEnergy s.character s.radial D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ (liveIndices D a)≤
      C*diagonalControl s.radial.profile*((retainedPair lo hi hlo p U hU t).control S)^2*
        Z^(s.width+ε):=by
  dsimp only
  rw [allocated_empty]
  have hd₁:0<(Ideal.absNorm (∏I∈D₁,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₁))
  have hd₂:0<(Ideal.absNorm (∏I∈D₂,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₂))
  let U:Fin 2→ℝ:=![rawScale D a X₁ 0,rawScale D a X₂ 1]
  have hU:∀i,0<U i:=by
    intro i;fin_cases i
    · exact rawScale_pos D a X₁ hX₁ 0
    · exact rawScale_pos D a X₂ hX₂ 1
  have hh:=hz s hQ hwidth (retainedPair lo hi hlo p U hU t) 0
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    (div_pos (by unfold clippedScale;positivity) hd₁)
    (div_pos (by unfold clippedScale;positivity) hd₂)
    ((allocatedScale_le D a X₁ hX₁ 0 D₁ hD₁).trans
      (max_le (Real.one_le_rpow s.base_ge_one hL) hc₁))
    ((allocatedScale_le D a X₂ hX₂ 1 D₂ hD₂).trans
      (max_le (Real.one_le_rpow s.base_ge_one hL) hc₂))
  rw [NaturalState.plainEnergy_eq_zero] at hh
  simpa only [NaturalState.mask,hunit,retainedPair,U,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons,norm_zero,zero_add,abs_zero,add_zero,one_pow,mul_one] using hh

end SevenEighths.CenteredMomentEnergyAllocatedZero

end

end OAI
