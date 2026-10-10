import OAI.NumberTheory.DirichletL.Energy.SlotHeight
import OAI.NumberTheory.DirichletL.Energy.Reindex
import OAI.NumberTheory.DirichletL.Moments.SlotClassTransport

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentAllocatedRayDictionary
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentHeckeTwist CenteredMomentHeckeCancellation
local notation "O" => HeckeFamily.O

variable {α : Type*} [Fintype α] [DecidableEq α]

def originalEmbedding (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C) :
    CenteredMomentCommonProfile.liveIndices B.val ↪ α :=
  ⟨Subtype.val, Subtype.val_injective⟩

def remaining (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    Finset (CenteredMomentCommonProfile.liveIndices B.val) :=
  CenteredMomentDivisorRaw.liveIndices (ι := CenteredMomentCommonProfile.liveIndices B.val) L a \ J

def originalImage (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) : Finset α :=
  (remaining s C B L a J).map (originalEmbedding s C B)

lemma projection_injective (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    Function.Injective (fun i : remaining s C B L a J => i.val.val) := by
  intro i j h
  exact Subtype.ext (Subtype.ext h)

lemma mem_originalImage (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) (i : α) :
    i ∈ originalImage s C B L a J ↔
      ∃ j ∈ remaining s C B L a J, j.val = i := by
  simp only [originalImage, Finset.mem_map, originalEmbedding, Function.Embedding.coeFn_mk]

lemma originalImage_card (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C)
    (L : Ideal O) (a : Allocation L (Finset.univ : Finset
      (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) :
    (originalImage s C B L a J).card = (remaining s C B L a J).card := Finset.card_map _

def commonFirst (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : ℝ :=
  if left then (commonData s C R B).X₁ else (commonData s C R B).Y₁

def commonSecond (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : ℝ :=
  if left then (commonData s C R B).X₂ else (commonData s C R B).Y₂

omit [DecidableEq α] in
lemma commonFirst_pos (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : 0 < commonFirst s C R B left := by
  unfold commonFirst
  split
  · exact (commonData s C R B).X₁_pos
  · exact (commonData s C R B).Y₁_pos

omit [DecidableEq α] in
lemma commonSecond_pos (s : Input α) (C R : Ideal O) (B : actualAllocations s.pools C)
    (left : Bool) : 0 < commonSecond s C R B left := by
  unfold commonSecond
  split
  · exact (commonData s C R B).X₂_pos
  · exact (commonData s C R B).Y₂_pos

section RayData
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

structure Matches (s : Input α) (η₀ : Character)
    (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ)
    (W : ℝ → ℂ) (bslot Z : ℝ) : Prop where
  character : ∀ i I, s.ν i I = idealCoeff (relativeCharacter M H hH η₀ (θ i)) I
  profile : ∀ i y, s.W i y = W y * (y : ℂ)^(-HeckeDyadic.shift (σ i) (freq i))
  pool : ∀ i, s.slots i = primePool M H bslot (Z^(w i))
  scale : ∀ i, s.P i = Z^(w i)

variable {M H hH}
variable {s : Input α} {η₀ : Character} {θ : α → RayQuotient.Characters M H}
  {w σ freq : α → ℝ} {W : ℝ → ℂ} {bslot Z : ℝ}
  (h : Matches M H hH s η₀ θ w σ freq W bslot Z)

include h

omit [DecidableEq α] in
lemma common_coefficient (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (i : CenteredMomentCommonProfile.liveIndices B.val)
    (I : Ideal O) :
    (commonData (withHeight s τ v) C R B).coefficient i I =
      idealCoeff (relativeCharacter M H hH η₀ (θ i.val)) I *
        annularWeight W (Z^(w i.val)) (σ i.val) (freq i.val) I := by
  change s.ν i.val I * s.W i.val ((I.absNorm : ℝ) / s.P i.val) = _
  rw [h.character, h.profile, h.scale]
  rfl

omit [DecidableEq α] in
lemma common_height_coefficient (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (i : CenteredMomentCommonProfile.liveIndices B.val)
    (I : Ideal O) (hI : I ≠ 0) :
    heightCoefficient ((commonData (withHeight s τ v) C R B).coefficient i) v I =
      ((Z^(w i.val) : ℝ) : ℂ)^(Complex.I*v) *
        (idealCoeff (relativeCharacter M H hH η₀ (θ i.val)) I *
          annularWeight W (Z^(w i.val)) (σ i.val) (v+freq i.val) I) := by
  have he : (commonData (withHeight s τ v) C R B).coefficient i =
      fun I => idealCoeff (relativeCharacter M H hH η₀ (θ i.val)) I *
        annularWeight W (Z^(w i.val)) (σ i.val) (freq i.val) I :=
    funext (common_coefficient h τ v C R B i)
  rw [he]
  exact CenteredMomentEnergySlotHeight.height_coefficient _ W _ _ _ v
    (h.scale i.val ▸ s.P_pos i.val) I hI

omit [DecidableEq α] in
lemma scale_phase_norm (i : α) (v : ℝ) :
    ‖((Z^(w i) : ℝ) : ℂ)^(Complex.I*v)‖ = 1 := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos (h.scale i ▸ s.P_pos i) (Complex.I*v)

theorem common_energy (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (m A : O) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d := commonData (withHeight s τ v) C R B
    energy τ m A 0 W₁ W₂
      (fun i : remaining s C B L a J => d.slots i.val)
      (fun i : remaining s C B L a J => heightCoefficient (d.coefficient i.val) v)
      (fun i : remaining s C B L a J => d.P i.val) X₁ X₂ keep Φ K =
    energy τ m A 0 W₁ W₂
      (fun i : originalImage s C B L a J => primePool M H bslot (Z^(w i)))
      (fun i : originalImage s C B L a J => fun I =>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i : originalImage s C B L a J => Z^(w i)) X₁ X₂ keep Φ K := by
  dsimp only
  have hc : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).coefficient i.val) =
      fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i.val.val)) I *
        annularWeight W (Z^(w i.val.val)) (σ i.val.val) (freq i.val.val) I := by
    funext i I
    exact common_coefficient h τ v C R B i.val I
  have hp : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).P i.val) = fun i => Z^(w i.val.val) := by
    funext i
    exact h.scale i.val.val
  have hs : (fun i : remaining s C B L a J =>
      (commonData (withHeight s τ v) C R B).slots i.val) =
      fun i => primePool M H bslot (Z^(w i.val.val)) := by
    funext i
    exact h.pool i.val.val
  have hhc := congrArg (fun f => fun i : remaining s C B L a J => heightCoefficient (f i) v) hc
  rw [hhc, hp, hs]
  rw [CenteredMomentEnergySlotHeight.inherited_height_energy τ m A W₁ W₂ _ _ _ _ _ _
    (fun i => h.scale i.val.val ▸ s.P_pos i.val.val)
    (fun i I hI => (s.prime i.val.val I (by rw [h.pool]; exact hI)).ne_zero)
    v 0 X₁ X₂ keep Φ K]
  exact CenteredMomentEnergyReindex.energy_subset_map (originalEmbedding s C B)
    (remaining s C B L a J) τ m A W₁ W₂
    (fun i => primePool M H bslot (Z^(w i)))
    (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
      annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
    (fun i => Z^(w i)) 0 X₁ X₂ keep Φ K

theorem common_clipped_energy (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (V₁ V₂ : Plain) (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (D₁ D₂ : Finset (Ideal O)) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let d := commonData (withHeight s τ v) C R B
    let W₁ := V₁.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ hX₁ 0) v
    let W₂ := V₂.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ hX₂ 1) v
    let Y₁ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)
    let Y₂ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
      W₁ W₂ (fun i : remaining s C B L a J => d.slots i.val)
      (fun i : remaining s C B L a J => heightCoefficient (d.coefficient i.val) v)
      (fun i : remaining s C B L a J => d.P i.val) Y₁ Y₂ keep Φ K =
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
      W₁ W₂ (fun i : originalImage s C B L a J => primePool M H bslot (Z^(w i)))
      (fun i : originalImage s C B L a J => fun I =>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i : originalImage s C B L a J => Z^(w i)) Y₁ Y₂ keep Φ K :=
  common_energy h τ v C R B L a J _ 1 _ _ _ _ keep Φ K

theorem both_common_rectangles (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (V₁ V₂ : Plain) (left : Bool)
    (D₁ D₂ : Finset (Ideal O)) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let X₁ := commonFirst s C R B left
    let X₂ := commonSecond s C R B left
    let hX₁ := commonFirst_pos s C R B left
    let hX₂ := commonSecond_pos s C R B left
    let d := commonData (withHeight s τ v) C R B
    let W₁ := V₁.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ hX₁ 0) v
    let W₂ := V₂.profile (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1) (rawScale_pos (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ hX₂ 1) v
    let Y₁ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)
    let Y₂ := clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
      W₁ W₂ (fun i : remaining s C B L a J => d.slots i.val)
      (fun i : remaining s C B L a J => heightCoefficient (d.coefficient i.val) v)
      (fun i : remaining s C B L a J => d.P i.val) Y₁ Y₂ keep Φ K =
    energy τ (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
      W₁ W₂ (fun i : originalImage s C B L a J => primePool M H bslot (Z^(w i)))
      (fun i : originalImage s C B L a J => fun I =>
        idealCoeff (relativeCharacter M H hH η₀ (θ i)) I *
          annularWeight W (Z^(w i)) (σ i) (v+freq i) I)
      (fun i : originalImage s C B L a J => Z^(w i)) Y₁ Y₂ keep Φ K :=
  common_clipped_energy h τ v C R B L a J V₁ V₂
    (commonFirst s C R B left) (commonSecond s C R B left)
    (commonFirst_pos s C R B left) (commonSecond_pos s C R B left) D₁ D₂ keep Φ K

omit h

lemma deleted_clipped_scale_pos (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (X : ℝ) (j : Fin 2) (D : Finset (Ideal O)) (hD : ∀I∈D,I≠0) :
    0 < clippedScale (rawScale (α := CenteredMomentCommonProfile.liveIndices B.val) L a X j)/(Ideal.absNorm (∏I∈D,I):ℝ) := by
  apply div_pos (zero_lt_one.trans_le (clippedScale_ge_one _))
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Finset.prod_ne_zero_iff.mpr hD))

lemma originalImage_fixedQ (Q : Ideal O) (hQM : Q ≤ M) (hQη : Q ≤ η₀.modulus)
    (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (i : originalImage s C B L a J) :
    Q ≤ (relativeCharacter M H hH η₀ (θ i)).modulus :=
  relativeCharacter_fixedQ M H hH η₀ (θ i) Q hQM hQη

lemma originalImage_bounds (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (Lslot lo hi height heightShift v : ℝ)
    (hw : ∀i,0 ≤ w i) (hwL : ∀i,w i ≤ Lslot)
    (hσlo : ∀i,lo ≤ σ i) (hσhi : ∀i,σ i ≤ hi)
    (hf : ∀i,|freq i| ≤ height) (hv : |v| ≤ heightShift) :
    ∀i : originalImage s C B L a J,
      0 ≤ w i ∧ w i ≤ Lslot ∧ lo ≤ σ i ∧ σ i ≤ hi ∧ |v+freq i| ≤ height+heightShift := by
  intro i
  refine ⟨hw i, hwL i, hσlo i, hσhi i, ?_⟩
  exact (abs_add_le v (freq i)).trans (by linarith [hf i])

lemma originalImage_scale_bounds (C : Ideal O) (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val ⊕ Fin 2)))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (hZ : 1<Z) (Lslot : ℝ) (hw : ∀i,0 ≤ w i) (hwL : ∀i,w i ≤ Lslot) :
    ∀i : originalImage s C B L a J, 1 ≤ Z^(w i) ∧ Z^(w i) ≤ Z^Lslot := by
  intro i
  exact ⟨Real.one_le_rpow hZ.le (hw i), Real.rpow_le_rpow_of_exponent_le hZ.le (hwL i)⟩

end RayData
end SevenEighths.CenteredMomentAllocatedRayDictionary

end

end OAI
