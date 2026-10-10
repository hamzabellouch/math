import OAI.NumberTheory.DirichletL.Moments.FirstAnnularActiveInput
import OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary
import OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary
open HeckeFamily CenteredMomentSecondHeightFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedRayDictionary
open CenteredMomentFirstAnnularInput CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentEligibleEnergy CenteredMomentCommonHeightEnvelope
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq β := Classical.decEq _

lemma active_pools_subset (s : Input α) (j : α⊕Fin 2) :
    (activeInput s).pools j⊆s.pools j := by
  cases j with
  | inl i => exact Finset.filter_subset _ _
  | inr j => exact Finset.Subset.refl _

lemma actualAllocations_mono {β : Type*} [Fintype β]
    (S T : β→Finset (Ideal O)) (h : ∀i,S i⊆T i) (C : Ideal O) :
    actualAllocations S C⊆actualAllocations T C := by
  intro B hB
  obtain ⟨hlabel,hprod⟩ := Finset.mem_filter.mp hB
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp hlabel
  refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v,?_,hvB⟩,hprod⟩
  exact Fintype.mem_piFinset.mpr (fun i=>h i (Fintype.mem_piFinset.mp hv i))

abbrev restoreAllocation (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) : actualAllocations s.pools C :=
  ⟨B.val,actualAllocations_mono _ _ (active_pools_subset s) C B.property⟩

@[simp] lemma restoreAllocation_val (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput s).pools C) : (restoreAllocation s C B).val=B.val := rfl

lemma restoreAllocation_injective (s : Input α) (C : Ideal O) :
    Function.Injective (restoreAllocation s C) := by
  intro B D h
  exact Subtype.ext (congrArg (fun x : actualAllocations s.pools C=>x.val) h)

lemma child_active (s : Input α) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (τ : Character) (t : ℝ) :
    child (activeInput s) C R B τ t=
      activeInput (child s C R (restoreAllocation s C B) τ t) := rfl

lemma active_coefficient (s : Input α) (i : α) :
    (activeInput s).toData.coefficient i=s.toData.coefficient i := rfl

lemma rowSlot_active (s : Input α) (i : α) (η : Character) (m A z : O) (t v : ℝ) :
    rowSlot η m A z ((activeInput s).slots i)
      (heightCoefficient ((activeInput s).toData.coefficient i) v) t=
    rowSlot η m A z (s.slots i) (heightCoefficient (s.toData.coefficient i) v) t := by
  unfold rowSlot
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro I hI hn
  have hz : s.W i ((I.absNorm:ℝ)/s.P i)=0 := by
    by_contra hh
    exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
  simp only [heightCoefficient,Data.coefficient,activeInput,hz,mul_zero,zero_mul]

lemma positive_active (s : Input α) (η : Character) (m A z : O)
    (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ) :
    positiveSlotRow η m A z W₁ W₂ (activeInput s).slots
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient i) v)
      (activeInput s).P t X₁ X₂=
    positiveSlotRow η m A z W₁ W₂ s.slots
      (fun i=>heightCoefficient (s.toData.coefficient i) v) s.P t X₁ X₂ := by
  unfold positiveSlotRow
  congr 2
  exact Finset.prod_congr rfl (fun i _=>rowSlot_active s i η m A z t v)

theorem energy_active (s : Input α) (η : Character) (m A : O)
    (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ (activeInput s).slots
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient i) v)
      (activeInput s).P X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ s.slots
      (fun i=>heightCoefficient (s.toData.coefficient i) v) s.P X₁ X₂ keep Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_active]

theorem positive_active_restrict {κ : Type*} [Fintype κ] (s : Input α) (f : κ→α)
    (η : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ) :
    positiveSlotRow η m A z W₁ W₂ (fun i=>(activeInput s).slots (f i))
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient (f i)) v)
      (fun i=>(activeInput s).P (f i)) t X₁ X₂=
    positiveSlotRow η m A z W₁ W₂ (fun i=>s.slots (f i))
      (fun i=>heightCoefficient (s.toData.coefficient (f i)) v)
      (fun i=>s.P (f i)) t X₁ X₂ := by
  unfold positiveSlotRow
  congr 2
  exact Finset.prod_congr rfl (fun i _=>rowSlot_active s (f i) η m A z t v)

theorem energy_active_restrict {κ : Type*} [Fintype κ] (s : Input α) (f : κ→α)
    (η : Character) (m A : O) (W₁ W₂ : ℝ→ℂ) (t v X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ (fun i=>(activeInput s).slots (f i))
      (fun i=>heightCoefficient ((activeInput s).toData.coefficient (f i)) v)
      (fun i=>(activeInput s).P (f i)) X₁ X₂ keep Φ K=
    energy η m A t W₁ W₂ (fun i=>s.slots (f i))
      (fun i=>heightCoefficient (s.toData.coefficient (f i)) v)
      (fun i=>s.P (f i)) X₁ X₂ keep Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_active_restrict]

theorem common_energy_active (s : Input α) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (τ : Character) (v : ℝ)
    (L : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)))
    (J : Finset (liveIndices B.val)) (m A : O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d : CenteredMomentEligibleEnergy.Data (liveIndices B.val) :=
      commonData (withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools] using B.property⟩
    let e : CenteredMomentEligibleEnergy.Data (liveIndices B.val) :=
      commonData (withHeight s τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools, restoreAllocation_val]
          using (restoreAllocation s C B).property⟩
    energy τ m A 0 W₁ W₂
      (fun i:remaining (activeInput s) C B L a J=>d.slots i.val)
      (fun i:remaining (activeInput s) C B L a J=>heightCoefficient (d.coefficient i.val) v)
      (fun i:remaining (activeInput s) C B L a J=>d.P i.val) X₁ X₂ keep Φ K=
    energy τ m A 0 W₁ W₂
      (fun i:remaining s C (restoreAllocation s C B) L a J=>e.slots i.val)
      (fun i:remaining s C (restoreAllocation s C B) L a J=>heightCoefficient (e.coefficient i.val) v)
      (fun i:remaining s C (restoreAllocation s C B) L a J=>e.P i.val) X₁ X₂ keep Φ K := by
  exact energy_active_restrict s
    (fun i:remaining (activeInput s) C B L a J=>i.val.val) τ m A W₁ W₂ 0 v X₁ X₂ keep Φ K

def restoredError (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) : Input (liveIndices Bp.val) :=
  twiceChild s C R B τ t Q k (restoreAllocation (child s C R B τ t) (Q^k) Bp) υ v

lemma error_source_active (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v=
      activeInput (restoredError s C R B τ t Q k Bp υ v) := rfl

theorem restoredError_data (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    let d:=restoredError s C R B τ t Q k Bp υ v
    d.η=υ ∧ d.t=v ∧ d.m=fixedBadMask*ConcretePrimeRowBridge.idealGenerator ((R*C)*(Q^k)) ∧
    d.X₁=s.X₁/(B.val (Sum.inr 0)).absNorm/(Bp.val (Sum.inr 0)).absNorm ∧
    d.X₂=s.X₂/(B.val (Sum.inr 1)).absNorm/(Bp.val (Sum.inr 1)).absNorm ∧
    d.Y₁=s.Y₁/(B.val (Sum.inr 0)).absNorm/(Bp.val (Sum.inr 0)).absNorm ∧
    d.Y₂=s.Y₂/(B.val (Sum.inr 1)).absNorm/(Bp.val (Sum.inr 1)).absNorm :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem error_live_slots (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k)) :
    liveIndices Bp.val=Finset.univ :=
  prime_slots_live (activeInput (child s C R B τ t)) Q hQ k hslot Bp

theorem restoredError_volume (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    volume (restoredError s C R B τ t Q k Bp υ v)=
      volume s/(CenteredMomentCommonRawScale.rawReduction B.val s.P*(Q.absNorm:ℝ)^k) := by
  have hh:=child_volume (activeInput (child s C R B τ t)) Q hQ k hslot (R*C) Bp υ v
  rw [error_source_active,active_volume,active_volume,common_volume,div_div] at hh
  exact hh

theorem error_normalized_source (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    childNormalizedGaussSource (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp υ v Φ K=
      normalizedGaussSource (restoredError s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed Φ K := by
  unfold childNormalizedGaussSource
  rw [error_source_active,active_normalized]

theorem error_normalized_sum (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (υ : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k)→Character)
    (v : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k)→ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k),
      childNormalizedGaussSource (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp (υ Bp) (v Bp) Φ K)=
    ∑Bp:actualAllocations (activeInput (child s C R B τ t)).pools (Q^k),
      normalizedGaussSource (restoredError s C R B τ t Q k Bp (υ Bp) (v Bp)) ((R*C)*(Q^k)) seed Φ K :=
  Finset.sum_congr rfl (fun Bp _=>error_normalized_source s C R seed B τ t Q k Bp (υ Bp) (v Bp) Φ K)

theorem error_energy (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let e:=child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v
    let d:=restoredError s C R B τ t Q k Bp υ v
    energy e.η e.m 1 0 W₁ W₂ e.slots
      (fun i=>heightCoefficient (e.toData.coefficient i) e.t) e.P X₁ X₂ keep Φ K=
    energy d.η d.m 1 0 W₁ W₂ d.slots
      (fun i=>heightCoefficient (d.toData.coefficient i) d.t) d.P X₁ X₂ keep Φ K := by
  dsimp only
  rw [error_source_active]
  exact energy_active (restoredError s C R B τ t Q k Bp υ v) υ
    (fixedBadMask*ConcretePrimeRowBridge.idealGenerator ((R*C)*(Q^k))) 1 W₁ W₂ 0 v X₁ X₂ keep Φ K

section Ray
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable {s : Input α} {η₀ : Character} {θ : α→RayQuotient.Characters M H}
  {w σ freq : α→ℝ} {W : ℝ→ℂ} {bslot Z : ℝ}

theorem matches_child (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    Matches M H hH (child s C R B τ t) η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val)
      (fun i=>freq i.val) W bslot Z := by
  constructor
  · intro i I;exact h.character i.val I
  · intro i y;exact h.profile i.val y
  · intro i;exact h.pool i.val
  · intro i;exact h.scale i.val

theorem matches_twiceChild (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    Matches M H hH (twiceChild s C R B τ t Q k Bp υ v) η₀
      (fun i=>θ i.val.val) (fun i=>w i.val.val) (fun i=>σ i.val.val)
      (fun i=>freq i.val.val) W bslot Z :=
  matches_child M H hH (matches_child M H hH h C R B τ t) (Q^k) (R*C) Bp υ v

theorem active_common_ray_energy (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations (activeInput s).pools C) (L : Ideal O)
    (a : CenteredMomentDivisorAllocation.Allocation L (Finset.univ : Finset (liveIndices B.val⊕Fin 2)))
    (J : Finset (liveIndices B.val)) (m A : O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d : CenteredMomentEligibleEnergy.Data (liveIndices B.val) :=
      commonData (withHeight (activeInput s) τ v) C R
        ⟨B.val, by simpa only [withHeight, Input.pools] using B.property⟩
    energy τ m A 0 W₁ W₂
      (fun i:remaining (activeInput s) C B L a J=>d.slots i.val)
      (fun i:remaining (activeInput s) C B L a J=>heightCoefficient (d.coefficient i.val) v)
      (fun i:remaining (activeInput s) C B L a J=>d.P i.val) X₁ X₂ keep Φ K=
    energy τ m A 0 W₁ W₂
      (fun i:originalImage s C (restoreAllocation s C B) L a J=>primePool M H bslot (Z^(w i)))
      (fun i:originalImage s C (restoreAllocation s C B) L a J=>fun I=>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i:originalImage s C (restoreAllocation s C B) L a J=>Z^(w i)) X₁ X₂ keep Φ K :=
  (common_energy_active s C R B τ v L a J m A W₁ W₂ X₁ X₂ keep Φ K).trans
    (common_energy h τ v C R (restoreAllocation s C B) L a J m A W₁ W₂ X₁ X₂ keep Φ K)

theorem restoredError_matches (h : Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    Matches M H hH (restoredError s C R B τ t Q k Bp υ v) η₀
      (fun i=>θ i.val.val) (fun i=>w i.val.val) (fun i=>σ i.val.val)
      (fun i=>freq i.val.val) W bslot Z :=
  matches_twiceChild M H hH h C R B τ t Q k (restoreAllocation (child s C R B τ t) (Q^k) Bp) υ v

end Ray
end SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

end

end OAI
