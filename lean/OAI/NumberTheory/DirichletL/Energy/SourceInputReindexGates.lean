import OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
import OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary
import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates
import OAI.NumberTheory.DirichletL.Moments.FirstAnnularActiveInput
import OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergySourceInputReindexGates
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSourceInputReindex CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentFirstSecondInputGates CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstChildProfileControl CenteredMomentFirstAnnularInput
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentOriginalChildEnergy
local notation "O" => HeckeFamily.O
variable {α β : Type*} [Fintype α] [Fintype β]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma mass_map (e : α≃β) (s : Input α) : mass (reindex e s)=mass s :=
  (controls_map e s).1

lemma nominal_map (e : α≃β) (s : Input α) (K : ℝ) :
    nominal (reindex e s) K=nominal s K := by
  unfold nominal
  rw [volume_map]

theorem ready_map (e : α≃β) (s : Input α) (R : Ideal O) (K Z ξ B : ℝ)
    (h : Ready s R K Z ξ B) : Ready (reindex e s) R K Z ξ B := by
  rcases h with ⟨hR0,hK,hV,hs0,hs,hq,hr,hn0,hn,hf0,hf⟩
  exact ⟨hR0,hK,by simpa only [volume_map] using hV,
    by simpa only [sourceRadius_map] using hs0,
    by simpa only [sourceRadius_map] using hs,hq,hr,
    by simpa only [nominal_map] using hn0,
    by simpa only [nominal_map] using hn,
    by simpa only [nominal_map] using hf0,
    by simpa only [nominal_map] using hf⟩

section Dictionary
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem matches_map (e : α≃β) (s : Input α) (η₀ : Character)
    (θ : α→RayQuotient.Characters M H) (w σ freq : α→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (reindex e s) η₀
      (θ ∘ e.symm) (w ∘ e.symm) (σ ∘ e.symm) (freq ∘ e.symm) W bslot Z :=
  ⟨fun i I=>h.character (e.symm i) I,fun i y=>h.profile (e.symm i) y,
    fun i=>h.pool (e.symm i),fun i=>h.scale (e.symm i)⟩

theorem matches_child (s : Input α) (η₀ : Character)
    (θ : α→RayQuotient.Characters M H) (w σ freq : α→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (child s C R B τ t) η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val) W bslot Z :=
  ⟨fun i I=>h.character i.val I,fun i y=>h.profile i.val y,
    fun i=>h.pool i.val,fun i=>h.scale i.val⟩

omit [Fintype α] [Fintype β] in
theorem imageInput_matches (e : α↪β) (T : Finset α) (s : Input T) (η₀ : Character)
    (θ : T→RayQuotient.Characters M H) (w σ freq : T→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (imageInput e T s) η₀
      (θ ∘ (Finset.equivMap e T).symm) (w ∘ (Finset.equivMap e T).symm)
      (σ ∘ (Finset.equivMap e T).symm) (freq ∘ (Finset.equivMap e T).symm) W bslot Z :=
  matches_map M H hH (Finset.equivMap e T) s η₀ θ w σ freq W bslot Z h

omit [Fintype β] in
theorem allocatedImage_matches (e : α↪β) (s : Input α) (η₀ : Character)
    (θ : α→RayQuotient.Characters M H) (w σ freq : α→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (allocatedImage e s C R B τ t) η₀
      (fun i=>θ ((Finset.equivMap e (liveIndices B.val)).symm i).val)
      (fun i=>w ((Finset.equivMap e (liveIndices B.val)).symm i).val)
      (fun i=>σ ((Finset.equivMap e (liveIndices B.val)).symm i).val)
      (fun i=>freq ((Finset.equivMap e (liveIndices B.val)).symm i).val) W bslot Z :=
  imageInput_matches M H hH e (liveIndices B.val) (child s C R B τ t) η₀
    _ _ _ _ W bslot Z (matches_child M H hH s η₀ θ w σ freq W bslot Z h C R B τ t)
end Dictionary

theorem active_map (e : α≃β) (s : Input α) :
    activeInput (reindex e s)=reindex e (activeInput s) := rfl

lemma allocationLabels_map (e : α≃β) (s : Input α) (C : Ideal O) :
    (allocationLabels s.pools C).image (tupleMap e)=
      allocationLabels (reindex e s).pools C := by
  unfold allocationLabels
  rw [←pools_map,Finset.image_image,Finset.image_image]
  congr 1

lemma actualAllocations_map (e : α≃β) (s : Input α) (C : Ideal O) :
    (actualAllocations s.pools C).image (tupleMap e)=
      actualAllocations (reindex e s).pools C := by
  change ((allocationLabels s.pools C).filter (fun B=>finiteTupleProduct B=C)).image (tupleMap e)=
    (allocationLabels (reindex e s).pools C).filter (fun B=>finiteTupleProduct B=C)
  rw [←allocationLabels_map e s C,Finset.filter_image]
  simp only [tupleMap_product]

def allocationEquiv (e : α≃β) (s : Input α) (C : Ideal O) :
    actualAllocations s.pools C ≃ actualAllocations (reindex e s).pools C where
  toFun B := ⟨tupleMap e B.val,by
    rw [←actualAllocations_map]
    exact Finset.mem_image.mpr ⟨B.val,B.property,rfl⟩⟩
  invFun B := ⟨(tupleMap e).symm B.val,by
    have hh : B.val∈(actualAllocations s.pools C).image (tupleMap e) := by
      simpa only [actualAllocations_map e s C] using B.property
    obtain ⟨v,hv,hvB⟩:=Finset.mem_image.mp hh
    simpa only [←hvB,Equiv.symm_apply_apply] using hv⟩
  left_inv B := Subtype.ext ((tupleMap e).symm_apply_apply B.val)
  right_inv B := Subtype.ext ((tupleMap e).apply_symm_apply B.val)

@[simp] lemma allocationEquiv_val (e : α≃β) (s : Input α) (C : Ideal O)
    (B : actualAllocations s.pools C) :
    (allocationEquiv e s C B).val=tupleMap e B.val := rfl

def liveEquiv (e : α≃β) (B : Tuple α) : liveIndices B ≃ liveIndices (tupleMap e B) where
  toFun i := ⟨e i.val,by
    simpa only [liveIndices,Finset.mem_filter,Finset.mem_univ,true_and,
      tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Sum.map_inl,
      Equiv.symm_apply_apply] using (Finset.mem_filter.mp i.property).2⟩
  invFun j := ⟨e.symm j.val,by
    simpa only [liveIndices,Finset.mem_filter,Finset.mem_univ,true_and,
      tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Sum.map_inl]
      using (Finset.mem_filter.mp j.property).2⟩
  left_inv i := Subtype.ext (e.symm_apply_apply i.val)
  right_inv j := Subtype.ext (e.apply_symm_apply j.val)

@[simp] lemma liveEquiv_val (e : α≃β) (B : Tuple α) (i : liveIndices B) :
    (liveEquiv e B i).val=e i.val := rfl

@[simp] lemma liveEquiv_symm_val (e : α≃β) (B : Tuple α)
    (j : liveIndices (tupleMap e B)) : ((liveEquiv e B).symm j).val=e.symm j.val := rfl

theorem child_map (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    reindex (liveEquiv e B.val) (child s C R B τ t)=
      child (reindex e s) C R (allocationEquiv e s C B) τ t := rfl

theorem child_mass_map (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    mass (child (reindex e s) C R (allocationEquiv e s C B) τ t)=
      mass (child s C R B τ t) := by
  exact mass_map (liveEquiv e B.val) (child s C R B τ t)

theorem child_volume_map (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    volume (child (reindex e s) C R (allocationEquiv e s C B) τ t)=
      volume (child s C R B τ t) := by
  exact volume_map (liveEquiv e B.val) (child s C R B τ t)

theorem child_normalized_map (e : α≃β) (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    childNormalizedGaussSource (reindex e s) C R seed (allocationEquiv e s C B) τ t W K=
      childNormalizedGaussSource s C R seed B τ t W K := by
  exact normalizedGaussSource_map (liveEquiv e B.val) (child s C R B τ t) (R*C) seed W K

theorem active_allocation_pullback (e : α≃β) (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput (reindex e s)).pools C) :
    ∃A : actualAllocations (activeInput s).pools C,
      (allocationEquiv e (activeInput s) C A).val=B.val := by
  exact ⟨(allocationEquiv e (activeInput s) C).symm B,
    congrArg Subtype.val ((allocationEquiv e (activeInput s) C).apply_symm_apply B)⟩

omit [Fintype α] [Fintype β] in
theorem imageInput_ready (e : α↪β) (T : Finset α) (s : Input T)
    (R : Ideal O) (K Z ξ B : ℝ) (h : Ready s R K Z ξ B) :
    Ready (imageInput e T s) R K Z ξ B :=
  ready_map (Finset.equivMap e T) s R K Z ξ B h

omit [Fintype β] in
theorem allocatedImage_ready (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t K Z ξ bound : ℝ)
    (h : Ready (child s C R B τ t) (R*C) K Z ξ bound) :
    Ready (allocatedImage e s C R B τ t) (R*C) K Z ξ bound :=
  imageInput_ready e (liveIndices B.val) (child s C R B τ t) (R*C) K Z ξ bound h

omit [Fintype α] [Fintype β] in
lemma imageInput_mass (e : α↪β) (T : Finset α) (s : Input T) :
    mass (imageInput e T s)=mass s := mass_map (Finset.equivMap e T) s

omit [Fintype β] in
lemma allocatedImage_mass (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    mass (allocatedImage e s C R B τ t)=mass (child s C R B τ t) :=
  imageInput_mass e (liveIndices B.val) (child s C R B τ t)

omit [Fintype β] in
lemma allocatedImage_volume (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    volume (allocatedImage e s C R B τ t)=volume (child s C R B τ t) :=
  volume_map (Finset.equivMap e (liveIndices B.val)) (child s C R B τ t)

lemma source_fields_map (e : α≃β) (s : Input α) :
    (reindex e s).η=s.η ∧ (reindex e s).m=s.m ∧ (reindex e s).A=s.A ∧
    (reindex e s).t=s.t ∧ (reindex e s).W₁=s.W₁ ∧ (reindex e s).W₂=s.W₂ ∧
    (reindex e s).X₁=s.X₁ ∧ (reindex e s).X₂=s.X₂ ∧
    (reindex e s).Y₁=s.Y₁ ∧ (reindex e s).Y₂=s.Y₂ ∧
    (reindex e s).lower=s.lower ∧ (reindex e s).upper=s.upper ∧
    (reindex e s).plain₁=s.plain₁ ∧ (reindex e s).plain₂=s.plain₂ ∧
    (reindex e s).rows=s.rows ∧ (reindex e s).weight=s.weight := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem active_child_pullback (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations (activeInput (reindex e s)).pools C) (τ : Character) (t : ℝ) :
    ∃A : actualAllocations (activeInput s).pools C,
      (allocationEquiv e (activeInput s) C A).val=B.val ∧
      mass (child (activeInput (reindex e s)) C R B τ t)=
        mass (child (activeInput s) C R A τ t) ∧
      volume (child (activeInput (reindex e s)) C R B τ t)=
        volume (child (activeInput s) C R A τ t) ∧
      ∀(seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
        childNormalizedGaussSource (activeInput (reindex e s)) C R seed B τ t W K=
          childNormalizedGaussSource (activeInput s) C R seed A τ t W K := by
  obtain ⟨A,hA⟩:=(allocationEquiv e (activeInput s) C).surjective B
  subst B
  exact ⟨A,rfl,child_mass_map e (activeInput s) C R A τ t,
    child_volume_map e (activeInput s) C R A τ t,
    fun seed W K=>child_normalized_map e (activeInput s) C R seed A τ t W K⟩

end SevenEighths.CenteredMomentEnergySourceInputReindexGates

end

end OAI
