import Mathlib.RingTheory.Radical.Basic
import OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy
import OAI.NumberTheory.DirichletL.Moments.RadialEligibleEnergy
import OAI.NumberTheory.DirichletL.Moments.CommonRadialData

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentAllocatedNaturalSource
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentHeckeTwist CenteredMomentHeckeVolume CenteredMomentHeckeCancellation
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained
local notation "O" => HeckeFamily.O

structure Plain where
  W : ℝ→ℂ
  a : ℝ
  b : ℝ
  a_pos : 0<a
  support : Function.support W⊆Set.Icc a b
  smooth : ContDiff ℝ ∞ W

def Plain.profile (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  if h : 1≤U*V.b then retainedProfile V.W V.a V.b V.a_pos V.support V.smooth U hU h t else 0

lemma Plain.profile_retained (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) (h : 1≤U*V.b) :
    V.profile U hU t=retainedProfile V.W V.a V.b V.a_pos V.support V.smooth U hU h t := by
  simp [Plain.profile,h]

lemma Plain.profile_zero (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) (h : U*V.b<1) :
    V.profile U hU t=0 := by simp [Plain.profile,not_le.mpr h]

lemma polynomial_zero (χ : Character) (X : ℝ) :
    HeckeDyadic.polynomial χ false (0 : 𝓢(ℝ,ℂ)) X 0 0=0 := by
  simp [HeckeDyadic.polynomial,HeckeDyadic.summand]

theorem retained_normalized (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    {α : Type*} [Fintype α] [DecidableEq α] (V₁ V₂ : Plain)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t U₁ U₂ : ℝ) (hU₁ : 0<U₁) (hU₂ : 0<U₂) :
    retainedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z V₁.W V₂.W pool β P t U₁ U₂=
      (((clippedScale U₁):ℂ)^(Complex.I*t)*((clippedScale U₂):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₁.profile U₁ hU₁ t) (clippedScale U₁) 0 0 *
         HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₂.profile U₂ hU₂ t) (clippedScale U₂) 0 0 *
         ∏i,naturalSlot (excluded (naturalRow η z hz).character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  by_cases h₁ : 1≤U₁*V₁.b
  · by_cases h₂ : 1≤U₂*V₂.b
    · rw [V₁.profile_retained U₁ hU₁ t h₁,V₂.profile_retained U₂ hU₂ t h₂]
      exact original_retained_normalized (naturalRow η z hz) R hR _ _ _ _ _ _ V₁.a_pos V₂.a_pos
        V₁.support V₂.support V₁.smooth V₂.smooth pool β P hP t U₁ U₂ hU₁ hU₂ h₁ h₂
    · rw [original_retained_zero η _ 1 z V₁.W V₂.W V₁.b V₂.b
        (fun _ h=>(V₁.support h).2) (fun _ h=>(V₂.support h).2) pool β P t U₁ U₂ hU₁ hU₂
        (Or.inr (lt_of_not_ge h₂)),V₂.profile_zero U₂ hU₂ t (lt_of_not_ge h₂),polynomial_zero]
      simp
  · rw [original_retained_zero η _ 1 z V₁.W V₂.W V₁.b V₂.b
      (fun _ h=>(V₁.support h).2) (fun _ h=>(V₂.support h).2) pool β P t U₁ U₂ hU₁ hU₂
      (Or.inl (lt_of_not_ge h₁)),V₁.profile_zero U₁ hU₁ t (lt_of_not_ge h₁),polynomial_zero]
    simp

variable {α : Type*} [Fintype α] [DecidableEq α]

def rawScale (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) (X : ℝ) (j : Fin 2) : ℝ :=
  X/Ideal.absNorm (selectedPlain D a j)

lemma rawScale_pos (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (X : ℝ) (hX : 0<X) (j : Fin 2) : 0<rawScale D a X j := by
  apply div_pos hX
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (selectedDivisor_ne_zero D Finset.univ a _))

lemma raw_same_product (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (X₁ X₂ Y₁ Y₂ : ℝ) (h : X₁*X₂=Y₁*Y₂) :
    rawScale D a X₁ 0*rawScale D a X₂ 1=rawScale D a Y₁ 0*rawScale D a Y₂ 1 := by
  simp only [rawScale,div_mul_div_comm,h]

theorem allocated_normalized (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    allocatedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z t pool β P D a V₁.W V₂.W X₁ X₂=
      (((clippedScale (rawScale D a X₁ 0)):ℂ)^(Complex.I*t)*
       ((clippedScale (rawScale D a X₂ 1)):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t) (clippedScale (rawScale D a X₁ 0)) 0 0 *
         HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t) (clippedScale (rawScale D a X₂ 1)) 0 0 *
         ∏i∈liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
           (pool i) (heightCoefficient (β i) t) (P i)) := by
  have h:=retained_normalized η z hz R hR V₁ V₂
    (fun i : liveIndices D a=>pool i) (fun i : liveIndices D a=>β i) (fun i : liveIndices D a=>P i)
    (fun i=>hP i) t _ _ (rawScale_pos D a X₁ hX₁ 0) (rawScale_pos D a X₂ hX₂ 1)
  have hp': (∏i : liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
      (pool i) (heightCoefficient (β i) t) (P i))=
      ∏i∈liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
      (pool i) (heightCoefficient (β i) t) (P i) := Finset.prod_coe_sort (liveIndices D a) (fun i : α=>naturalSlot (excluded (naturalRow η z hz).character R) (pool i) (heightCoefficient (β i) t) (P i))
  rw [hp'] at h
  exact h

omit [Fintype α] [DecidableEq α] in

theorem slot_controls (ν : α→Ideal O→ℂ) (W : α→ℝ→ℂ) (P b M : α→ℝ)
    (hP : ∀i,0<P i) (hν : ∀i I,‖ν i I‖≤1)
    (hW : ∀i x,‖W i x‖≤M i) (hs : ∀i,Function.support (W i)⊆Set.Iic (b i)) :
    (∀i I,‖ν i I*W i ((I.absNorm:ℝ)/P i)‖≤M i) ∧
    (∀i I,ν i I*W i ((I.absNorm:ℝ)/P i)≠0 → (I.absNorm:ℝ)≤b i*P i) := by
  constructor
  · intro i I
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hν i I) (norm_nonneg _)).trans (by simpa using hW i _)
  · intro i I hn
    exact (div_le_iff₀ (hP i)).mp (hs i (right_ne_zero_of_mul hn))

def SharedBound (F : Finset α) (b M : α→ℝ) (C ε : ℝ) : Prop :=
    ∀{ι : Type*} [Fintype ι],
      ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)(χ : ι→Character)
        (W₁ W₂ : ι→𝓢(ℝ,ℂ))(X₁ X₂ : ι→ℝ)
        (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ),
      (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      (∀i j,j∈F → ∀I∈pool i j,Prime I) → (∀i j,j∈F → 0<P i j) →
      (∀i j,j∈F → ∀I∈pool i j,‖β i j I‖≤M j) →
      (∀i j,j∈F → ∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
      ∀E : ℝ,0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        (∑i,‖HeckeDyadic.polynomial (χ i) false (W₁ i)
          (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ i) false (W₂ i)
          (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ i) (pool i j) (β i j) (P i j)‖^2)≤E) →
      (∑i,‖HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
        HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
        ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j)‖^2)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E

theorem uniform_shared (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀F : Finset α,SharedBound F b M C ε := by
  have he (F : Finset α) : ∃C : ℝ,0<C ∧ SharedBound F b M C ε :=
    actual_shared_energy F b M (fun i _=>hM i) ε hε
  choose C hC hb using he
  let B : ℝ:=1+∑F : Finset α,C F
  have hsum : 0≤∑F : Finset α,C F:=Finset.sum_nonneg (fun F _=>(hC F).le)
  refine ⟨B,by dsimp [B];linarith,?_⟩
  intro F ι _ R hR χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE hchild
  have hCB : C F≤B := by
    have hh:=Finset.single_le_sum (fun G _=>(hC G).le) (Finset.mem_univ F)
    dsimp [B]
    linarith
  exact (hb F R hR χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE hchild).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE)

lemma primeSupport_product_radical (R : Ideal O) (hR : R≠0) :
    (∏I∈CompletedGauss.primeSupport R,I)=R.radical := by
  ext x
  change x∈(∏I∈CompletedGauss.primeSupport R,I) ↔ ∃n : ℕ,x^n∈R
  simp_rw [←Ideal.span_singleton_le_iff_mem,←Ideal.dvd_iff_le,←Ideal.span_singleton_pow]
  exact (UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd hR).symm

def child (χ : Character) (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (D₁ D₂ : Finset (Ideal O)) (J : Finset α) : ℂ :=
  HeckeDyadic.polynomial χ false (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
  HeckeDyadic.polynomial χ false (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
  ∏i∈liveIndices D a\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)

def AllocatedBound (b M : α→ℝ) (C ε : ℝ) : Prop :=
  ∀(D : Ideal O)(a : Allocation D (Finset.univ : Finset (α⊕Fin 2))),
  ∀{ι : Type*} [Fintype ι],∀(η : ι→Character)(z : ι→O)(hz : ∀i,z i≠0)
    (R : Ideal O),R≠0 → ∀(V₁ V₂ : ι→Plain)
    (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ)(t X₁ X₂ : ι→ℝ)
    (hX₁ : ∀i,0<X₁ i)(hX₂ : ∀i,0<X₂ i),
    (∀i j,∀I∈pool i j,Prime I) → (∀i j,0<P i j) →
    (∀i j,∀I∈pool i j,‖β i j I‖≤M j) →
    (∀i j,∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
    ∀E : ℝ,0≤E →
    (∀D₁∈(CompletedGauss.primeSupport R).powerset,
     ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
       (∑i,‖child (naturalRow (η i) (z i) (hz i)).character D a (V₁ i) (V₂ i)
         (pool i) (β i) (P i) (t i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i) D₁ D₂ J‖^2)≤E) →
    (∑i,‖allocatedPositiveRow (η i)
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 (z i) (t i) (pool i) (β i) (P i) D a (V₁ i).W (V₂ i).W (X₁ i) (X₂ i)‖^2)≤
      C*(Ideal.absNorm R.radical:ℝ)^ε*E

theorem allocated_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ AllocatedBound b M C ε := by
  obtain ⟨C,hC,hbound⟩:=uniform_shared b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro D a ι _ η z hz R hR V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ hp hP hβ hs E hE hchild
  have hh:=hbound (liveIndices D a) (CompletedGauss.primeSupport R) (support_prime R)
    (fun i=>(naturalRow (η i) (z i) (hz i)).character)
    (fun i=>(V₁ i).profile _ (rawScale_pos D a (X₁ i) (hX₁ i) 0) (t i))
    (fun i=>(V₂ i).profile _ (rawScale_pos D a (X₂ i) (hX₂ i) 1) (t i))
    (fun i=>clippedScale (rawScale D a (X₁ i) 0)) (fun i=>clippedScale (rawScale D a (X₂ i) 1))
    pool (fun i j=>heightCoefficient (β i j) (t i)) P
    (fun _=>by unfold clippedScale;positivity) (fun _=>by unfold clippedScale;positivity)
    (fun i j _=>hp i j) (fun i j _=>hP i j)
    (fun i j _ I hi=>by rw [heightCoefficient_norm _ _ _ (hp i j I hi).ne_zero];exact hβ i j I hi)
    (fun i j _ I hi hn=>hs i j I hi (left_ne_zero_of_mul hn)) E hE hchild
  have he (i : ι):=allocated_normalized (η i) (z i) (hz i) R hR D a (V₁ i) (V₂ i)
    (pool i) (β i) (P i) (hP i) (t i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i)
  have hphase (U t : ℝ) : ‖((clippedScale U):ℂ)^(Complex.I*t)‖=1 :=
    positive_height_phase_norm _ _ (by unfold clippedScale;positivity)
  simp_rw [he,norm_mul,hphase,one_mul]
  rw [←primeSupport_product_radical R hR]
  simpa only [SharedBound,excluded,norm_mul] using hh

theorem uniform_allocated_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀T : Finset α,
      AllocatedBound (fun i : T=>b i) (fun i : T=>M i) C ε := by
  have he (T : Finset α) : ∃C : ℝ,0<C ∧ AllocatedBound (fun i : T=>b i) (fun i : T=>M i) C ε :=
    allocated_energy (fun i : T=>b i) (fun i : T=>M i) (fun i=>hM i) ε hε
  choose C hC hb using he
  let B : ℝ:=1+∑T : Finset α,C T
  have hsum : 0≤∑T : Finset α,C T:=Finset.sum_nonneg (fun T _=>(hC T).le)
  refine ⟨B,by dsimp [B];linarith,?_⟩
  intro T D a ι _ η z hz R hR V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ hp hP hβ hs E hE hchild
  have hCB : C T≤B := by
    have hh:=Finset.single_le_sum (fun G _=>(hC G).le) (Finset.mem_univ T)
    dsimp [B]
    linarith
  exact (hb T D a η z hz R hR V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ hp hP hβ hs E hE hchild).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE)

theorem natural_nonprincipal_width (η : Character) (z : O) (hz : z≠0)
    (Q R : Ideal O) (hR : R≠0)
    (hex : ¬CenteredExceptionalProfile.FixedInducingRow η Q
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z)
    (Z m q Cz : ℝ) (hZ : 0<Z) (hCz : 0≤Cz)
    (hη : (η.modulus.absNorm:ℝ)≤Z^m) (hrow : ((Ideal.span {z}).absNorm:ℝ)≤Cz*Z^q) :
    (naturalRow η z hz).character.residue≠1 ∧
    ((naturalRow η z hz).character.modulus.absNorm:ℝ)≤(fixedConductorFactor:ℝ)*Cz*Z^(m+q) :=
  ⟨(naturalRow η z hz).nonprincipal hz Q R hR hex,
    (naturalRow η z hz).modulus_power_bound Z m q Cz hZ hCz hη hrow⟩

structure Slots (α : Type*) (b M : α→ℝ) where
  pool : α→Finset (Ideal O)
  ν : α→Ideal O→ℂ
  W : α→ℝ→ℂ
  P : α→ℝ
  prime : ∀i,∀I∈pool i,Prime I
  P_pos : ∀i,0<P i
  ν_bound : ∀i I,‖ν i I‖≤1
  W_bound : ∀i x,‖W i x‖≤M i
  support : ∀i,Function.support (W i)⊆Set.Iic (b i)

def Slots.coefficient {b M : α→ℝ} (s : Slots α b M) (i : α) (I : Ideal O) : ℂ :=
  s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)

omit [Fintype α] [DecidableEq α] in
lemma Slots.controls {b M : α→ℝ} (s : Slots α b M) :
    (∀i I,‖s.coefficient i I‖≤M i) ∧
    (∀i I,s.coefficient i I≠0 → (I.absNorm:ℝ)≤b i*s.P i) :=
  slot_controls s.ν s.W s.P b M s.P_pos s.ν_bound s.W_bound s.support

structure Row (α : Type*) (b M : α→ℝ) where
  η : Character
  z : O
  z_ne : z≠0
  plain₁ : Plain
  plain₂ : Plain
  slots : Slots α b M
  t : ℝ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  X₁_pos : 0<X₁
  X₂_pos : 0<X₂
  Y₁_pos : 0<Y₁
  Y₂_pos : 0<Y₂
  same_product : X₁*X₂=Y₁*Y₂

lemma Row.extracted_same_product {b M : α→ℝ} (s : Row α b M)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) :
    rawScale D a s.X₁ 0*rawScale D a s.X₂ 1=rawScale D a s.Y₁ 0*rawScale D a s.Y₂ 1 :=
  raw_same_product D a _ _ _ _ s.same_product

theorem uniform_paired_nuW_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀T : Finset α,
    ∀(D : Ideal O)(a : Allocation D (Finset.univ : Finset (T⊕Fin 2))),
    ∀{ι : Type*} [Fintype ι],∀s : ι→Row T (fun i=>b i) (fun i=>M i),
    ∀(R : Ideal O),R≠0 → ∀E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀D₁∈(CompletedGauss.primeSupport R).powerset,
     ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
       (∑i,‖child (naturalRow (s i).η (s i).z (s i).z_ne).character D a
         (s i).plain₁ (s i).plain₂ (s i).slots.pool (s i).slots.coefficient (s i).slots.P
         (s i).t (s i).X₁ (s i).X₂ (s i).X₁_pos (s i).X₂_pos D₁ D₂ J‖^2)≤E₁) →
    (∀D₁∈(CompletedGauss.primeSupport R).powerset,
     ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
       (∑i,‖child (naturalRow (s i).η (s i).z (s i).z_ne).character D a
         (s i).plain₁ (s i).plain₂ (s i).slots.pool (s i).slots.coefficient (s i).slots.P
         (s i).t (s i).Y₁ (s i).Y₂ (s i).Y₁_pos (s i).Y₂_pos D₁ D₂ J‖^2)≤E₂) →
    (∑i,(‖allocatedPositiveRow (s i).η
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 (s i).z (s i).t (s i).slots.pool (s i).slots.coefficient (s i).slots.P D a
      (s i).plain₁.W (s i).plain₂.W (s i).X₁ (s i).X₂‖^2+
      ‖allocatedPositiveRow (s i).η
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 (s i).z (s i).t (s i).slots.pool (s i).slots.coefficient (s i).slots.P D a
      (s i).plain₁.W (s i).plain₂.W (s i).Y₁ (s i).Y₂‖^2))≤
      C*(Ideal.absNorm R.radical:ℝ)^ε*(E₁+E₂) := by
  obtain ⟨C,hC,hbound⟩:=uniform_allocated_energy b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro T D a ι _ s R hR E₁ E₂ hE₁ hE₂ hleft hright
  have hl:=hbound T D a (fun i=>(s i).η) (fun i=>(s i).z) (fun i=>(s i).z_ne) R hR
    (fun i=>(s i).plain₁) (fun i=>(s i).plain₂) (fun i=>(s i).slots.pool)
    (fun i=>(s i).slots.coefficient) (fun i=>(s i).slots.P) (fun i=>(s i).t)
    (fun i=>(s i).X₁) (fun i=>(s i).X₂) (fun i=>(s i).X₁_pos) (fun i=>(s i).X₂_pos)
    (fun i=>(s i).slots.prime) (fun i=>(s i).slots.P_pos)
    (fun i j I _=>(s i).slots.controls.1 j I) (fun i j I _=>(s i).slots.controls.2 j I)
    E₁ hE₁ hleft
  have hr:=hbound T D a (fun i=>(s i).η) (fun i=>(s i).z) (fun i=>(s i).z_ne) R hR
    (fun i=>(s i).plain₁) (fun i=>(s i).plain₂) (fun i=>(s i).slots.pool)
    (fun i=>(s i).slots.coefficient) (fun i=>(s i).slots.P) (fun i=>(s i).t)
    (fun i=>(s i).Y₁) (fun i=>(s i).Y₂) (fun i=>(s i).Y₁_pos) (fun i=>(s i).Y₂_pos)
    (fun i=>(s i).slots.prime) (fun i=>(s i).slots.P_pos)
    (fun i j I _=>(s i).slots.controls.1 j I) (fun i j I _=>(s i).slots.controls.2 j I)
    E₂ hE₂ hright
  rw [Finset.sum_add_distrib,mul_add]
  exact add_le_add hl hr

def inputSlots (s : CenteredMomentCommonRadialData.Input α) : Slots α s.hi s.M where
  pool:=s.slots
  ν:=s.ν
  W:=s.W
  P:=s.P
  prime:=s.prime
  P_pos:=s.P_pos
  ν_bound:=s.ν_bound
  W_bound:=s.W_bound
  support:=fun i _ hx=>(s.support i hx).2

omit [DecidableEq α] in
lemma inputSlots_coefficient (s : CenteredMomentCommonRadialData.Input α) :
    (inputSlots s).coefficient=s.toData.coefficient := rfl

def commonSlots (s : CenteredMomentCommonRadialData.Input α) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    Slots (CenteredMomentCommonProfile.liveIndices B.val) (fun i=>s.hi i) (fun i=>s.M i) where
  pool:=fun i=>s.slots i
  ν:=fun i=>s.ν i
  W:=fun i=>s.W i
  P:=fun i=>s.P i
  prime:=fun i=>s.prime i
  P_pos:=fun i=>s.P_pos i
  ν_bound:=fun i=>s.ν_bound i
  W_bound:=fun i=>s.W_bound i
  support:=fun i _ hx=>(s.support i hx).2

omit [DecidableEq α] in
lemma commonSlots_coefficient (s : CenteredMomentCommonRadialData.Input α) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    (commonSlots s C B).coefficient=(CenteredMomentCommonRadialData.commonData s C R B).coefficient := rfl

end SevenEighths.CenteredMomentAllocatedNaturalSource

end

end OAI
