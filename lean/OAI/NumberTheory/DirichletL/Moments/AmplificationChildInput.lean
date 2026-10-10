import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
import OAI.NumberTheory.DirichletL.Moments.CommonRadialData

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationChildInput
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceRectangle CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentRemainingBox
open CenteredMomentAmplificationAllocationCost CenteredMomentAmplificationAllocationScale
open CenteredMomentHeckeColumnWindow CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationShortening
open CenteredMomentAmplificationLiveMask CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectors CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

def original (s : Input ι) (R seed : Ideal O) : OriginalData ι where
  S := s.pools
  R := R
  s := seed
  nu := s.ν
  slot := s.W
  lengths := s.P
  W₁ := s.W₁
  W₂ := s.W₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  B₁ := 1
  B₂ := 1

def volume (s : Input ι) : ℝ := s.X₁*s.X₂*∏i,s.P i

theorem volume_pos (s : Input ι) : 0<volume s :=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

theorem residual_ne (S : Finset (Ideal O)) (hS : ∀I∈S,I≠0)
    (B : Ideal O) (hB : B≠0) : ∀I∈residualPool B hB S,I≠0 := by
  intro I hI
  exact right_ne_zero_of_mul (hS (B*I) ((mem_residualPool B hB S I).mp hI))

theorem residual_one (S : Finset (Ideal O)) (h : (1:Ideal O)≠0) :
    residualPool 1 h S=S := by
  ext I
  simp only [mem_residualPool,one_mul]

theorem residual_coverage (S : Finset (Ideal O)) (W : ℝ→ℂ)
    (B : Ideal O) (hB : B≠0) (X Y : ℝ) (h : PlainCoverage S W 1 X Y) :
    PlainCoverage (residualPool B hB S) W 1 (X/B.absNorm) (Y/B.absNorm) := by
  have he := plainCoverage_residualPool S W 1 B hB X Y h
  intro I hi
  apply he I
  simpa only [one_mul,map_mul,map_one,Nat.cast_mul,Nat.cast_one,mul_one,div_div_eq_mul_div,mul_comm] using hi

def child (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : Input (liveIndices B.val) where
  toData := {commonData s C R B with η:=τ,t:=t}
  plain₁ := residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) s.plain₁
  plain₂ := residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) s.plain₂
  plain₁_ne := residual_ne s.plain₁ s.plain₁_ne _ _
  plain₂_ne := residual_ne s.plain₂ s.plain₂_ne _ _
  coverage₁ := residual_coverage s.plain₁ s.W₁ _ _ _ _ s.coverage₁
  coverage₂ := residual_coverage s.plain₂ s.W₂ _ _ _ _ s.coverage₂
  ν_bound := fun i=>s.ν_bound i.val
  W_bound := fun i=>s.W_bound i.val
  lower := s.lower
  upper := s.upper
  lower_pos := s.lower_pos
  lower_le := fun i=>s.lower_le i.val
  upper_ge := fun i=>s.upper_ge i.val

@[simp] theorem child_modulus (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : (child s C R B τ t).m=fixedBadMask*idealGenerator (R*C) := rfl

@[simp] theorem child_character (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : (child s C R B τ t).η=τ := rfl

@[simp] theorem child_height (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : (child s C R B τ t).t=t := rfl

theorem live_slot_one (B : Tuple ι) (i : liveIndices B) : B (Sum.inl i.val)=1 :=
  (Finset.mem_filter.mp i.property).2

theorem child_tuplePool (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1 =
      Fintype.piFinset (child s C R B τ t).pools := by
  ext v
  simp only [liveBox,Fintype.mem_piFinset]
  constructor <;> intro h j
  all_goals
    cases j with
    | inl i =>
      have hi:=h (Sum.inl i)
      simpa only [remainingSets,child,commonData,Input.pools,Sum.elim_inl,live_slot_one B.val i,
        residual_one] using hi
    | inr j =>
      fin_cases j
      · simpa [remainingSets,child,commonData,Input.pools] using h (Sum.inr 0)
      · simpa [remainingSets,child,commonData,Input.pools] using h (Sum.inr 1)

theorem child_profile (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂
      s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 = (original (child s C R B τ t) (R*C) seed).profile := by
  funext v
  simp only [maskedLiveProfile,OriginalData.profile,original,child,commonData,
    profileCoefficient,one_mul,idealRectangle_extract]
  rfl

theorem prime_slot_one (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) (i : ι) : B.val (Sum.inl i)=1 :=
  allocation_slot_one s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B i

theorem prime_slots_live (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) : liveIndices B.val=Finset.univ :=
  all_slots_live s.pools Q hQ k (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B

theorem prime_plain_norm_product (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) :
    (B.val (Sum.inr 0)).absNorm*(B.val (Sum.inr 1)).absNorm=Q.absNorm^k := by
  rw [←map_mul,allocation_plain_product s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B,map_pow]

theorem child_products (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : Character) (t : ℝ) :
    (child s (Q^k) R B τ t).X₁*(child s (Q^k) R B τ t).X₂=
      (s.X₁*s.X₂)/(Q.absNorm:ℝ)^k ∧
    (child s (Q^k) R B τ t).Y₁*(child s (Q^k) R B τ t).Y₂=
      (s.X₁*s.X₂)/(Q.absNorm:ℝ)^k := by
  have hnorm : ((B.val (Sum.inr 0)).absNorm:ℝ)*(B.val (Sum.inr 1)).absNorm=(Q.absNorm:ℝ)^k := by
    exact_mod_cast prime_plain_norm_product s Q hQ k hslot B
  change (s.X₁/_)*(s.X₂/_)=_ ∧ (s.Y₁/_)*(s.Y₂/_)=_
  rw [div_mul_div_comm,div_mul_div_comm,hnorm,s.same_product]
  exact ⟨rfl,rfl⟩

theorem child_volume (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : Character) (t : ℝ) :
    volume (child s (Q^k) R B τ t)=volume s/(Q.absNorm:ℝ)^k := by
  change (s.X₁/(B.val (Sum.inr 0)).absNorm)*(s.X₂/(B.val (Sum.inr 1)).absNorm)*
    (∏i:liveIndices B.val,s.P i.val)=_
  rw [div_mul_div_comm]
  exact remainingRaw_exact s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B s.P (s.X₁*s.X₂)

theorem child_slot_card (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) : Fintype.card (liveIndices B.val)=Fintype.card ι :=
  live_slot_card s.pools Q hQ k (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B

theorem child_slot_scale_ge_one (s : Input ι) (hs : ∀i,1≤s.P i)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    ∀i,1≤(child s C R B τ t).P i := fun i=>hs i.val

theorem child_plain_annuli (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t a₁ a₂ b₁ b₂ : ℝ)
    (h₁ : Function.support s.W₁⊆Set.Icc a₁ b₁)
    (h₂ : Function.support s.W₂⊆Set.Icc a₂ b₂) :
    Function.support (child s C R B τ t).W₁⊆Set.Icc a₁ b₁ ∧
    Function.support (child s C R B τ t).W₂⊆Set.Icc a₂ b₂ := ⟨h₁,h₂⟩

theorem child_columns (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    finiteColumns (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)=
      (original (child s C R B τ t) (R*C) seed).columns ∧
    finiteColumnCoefficient
      (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
      (maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1)=
      (original (child s C R B τ t) (R*C) seed).beta := by
  dsimp only [OriginalData.columns, OriginalData.beta, original]
  rw [child_tuplePool s C R B τ t,child_profile s C R seed B τ t]
  dsimp only [original]
  constructor
  · apply congrArg finiteColumns
    ext v
    simp only [Fintype.mem_piFinset]
  · apply congrArg (fun S => finiteColumnCoefficient S _)
    ext v
    simp only [Fintype.mem_piFinset]

theorem child_gauss_source (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy
      (finiteColumns (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1))
      (finiteColumnCoefficient
        (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
        (maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1))
      (heightCoeff τ t) W K=
    sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (original (child s C R B τ t) (R*C) seed).beta
      (heightCoeff (child s C R B τ t).η (child s C R B τ t).t) W K := by
  obtain ⟨hcols,hcoeff⟩ := child_columns s C R seed B τ t
  rw [hcols,hcoeff]
  rfl

def normalizedGaussSource (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  (sourceGaussEnergy (original s R seed).columns (original s R seed).beta
    (heightCoeff s.η s.t) W K).re / volume s

def childNormalizedGaussSource (s : Input ι) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  normalizedGaussSource (child s C R B τ t) (R*C) seed W K

theorem original_childEnergy_eq_inputs (s : Input ι) (R seed : Ideal O)
    (τ : RayCharacter→Character) (p : O) (hp : p≠0)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime (Ideal.span {p}) I)
    (n : ℕ) (t K : ℝ) :
    (original s R seed).childEnergy τ p n t (volume s) K=
      (16*(n+2:ℝ)*localErrorCost p n)*
        ∑χ:RayCharacter,∑B:actualAllocations s.pools ((Ideal.span {p})^(n+1)),
          childNormalizedGaussSource s ((Ideal.span {p})^(n+1)) R seed B (τ χ) t ballProfile K := by
  have hQ : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp
  unfold OriginalData.childEnergy
  simp only [original,Finset.sum_div]
  apply congrArg (fun x : ℝ => (16*(n+2:ℝ)*localErrorCost p n)*x)
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro B hB
  unfold childNormalizedGaussSource normalizedGaussSource
  rw [child_volume s (Ideal.span {p}) hQ (n+1) hslot R B (τ χ) t,
    child_gauss_source s ((Ideal.span {p})^(n+1)) R seed B (τ χ) t ballProfile K]

end SevenEighths.CenteredMomentAmplificationChildInput

end

end OAI
