import OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalSource
import OAI.NumberTheory.DirichletL.Moments.CommonMaskRadialEnergy
import OAI.NumberTheory.DirichletL.Moments.SecondOriginalChildren

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentAllocatedNaturalRadial
open HeckeFamily HeckeDyadic ConcreteTraceCRT MeasureTheory
open CenteredMomentAllocatedNaturalSource CenteredMomentCommonMaskRadialEnergy
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentRetainedProfile CenteredMomentLattice
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentOriginalRadialComparison CenteredMomentRadialPolynomialEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope CenteredMomentEligibleEnergy
open CenteredMomentCommonAllocationSum CenteredMomentRadialEligibleEnergy
local notation "O" => HeckeFamily.O

lemma profile_support (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) :
    Function.support (V.profile U hU t : ℝ→ℂ)⊆Set.Icc (V.a/max 1 V.b) (max 1 V.b) := by
  by_cases h : 1≤U*V.b
  · rw [V.profile_retained U hU t h]
    exact (retainedProfile_support V.W V.a V.b V.a_pos V.support V.smooth U hU h t).trans
      (fun _ hx=>⟨hx.1,hx.2.trans (le_max_right _ _)⟩)
  · rw [V.profile_zero U hU t (lt_of_not_ge h)]
    simp

def naturalCharacter (η : Character) (z : O) : Character :=
  if h : z≠0 then (naturalRow η z h).character else η

lemma naturalCharacter_eq (η : Character) (z : O) (hz : z≠0) :
    naturalCharacter η z=(naturalRow η z hz).character := by simp [naturalCharacter,hz]

variable {α : Type*} [Fintype α] [DecidableEq α]

def Shared (F : Finset α) (b M : α→ℝ) (C ε : ℝ) : Prop :=
  ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)
      (χ : O→Character)(W₁ W₂ : 𝓢(ℝ,ℂ))(X₁ X₂ a₁ b₁ a₂ b₂ : ℝ)
      (pool : α→Finset (Ideal O))(β : α→Ideal O→ℂ)(P : α→ℝ)
      (keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K E : ℝ),
      0<X₁ → 0<X₂ → 0≤b₁ → 0≤b₂ →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      (∀j∈F,∀I∈pool j,Prime I) → (∀j∈F,0<P j) →
      (∀j∈F,∀I∈pool j,‖β j I‖≤M j) →
      (∀j∈F,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) →
      0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) → 0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        radialEnergy (fun z=>polynomial (χ z) false W₁
          (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          polynomial (χ z) false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ z) (pool j) (β j) (P j)) keep Φ K≤E) →
      radialEnergy (fun z=>polynomial ((χ z).excludePrimes R hR) false W₁ X₁ 0 0 *
        polynomial ((χ z).excludePrimes R hR) false W₂ X₂ 0 0 *
        ∏j∈F,naturalSlot ((χ z).excludePrimes R hR) (pool j) (β j) (P j)) keep Φ K≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E

theorem uniform_shared (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀T : Finset α,∀F : Finset T,
      Shared F (fun i=>b i) (fun i=>M i) C ε := by
  have he (T : Finset α) (F : Finset T) : ∃C : ℝ,0<C ∧ Shared F (fun i=>b i) (fun i=>M i) C ε :=
    actual_radial_shared_energy F (fun i=>b i) (fun i=>M i) (fun i _=>hM i) ε hε
  choose C hC hb using he
  let B : ℝ:=1+∑T : Finset α,∑F : Finset T,C T F
  have hp (T : Finset α) : 0≤∑F : Finset T,C T F:=Finset.sum_nonneg (fun F _=>(hC T F).le)
  refine ⟨B,by have hh : 0≤∑T : Finset α,∑F : Finset T,C T F:=Finset.sum_nonneg (fun T _=>hp T);dsimp [B];linarith,?_⟩
  intro T F R hR χ W₁ W₂ X₁ X₂ a₁ b₁ a₂ b₂ pool β P keep Φ K E
    hX₁ hX₂ hb₁ hb₂ hs₁ hs₂ hprime hP hβ hs hK hΦ hE hchild
  have hCB : C T F≤B := by
    have h₁:=Finset.single_le_sum (fun G _=>(hC T G).le) (Finset.mem_univ F)
    have h₂:=Finset.single_le_sum (fun T _=>hp T) (Finset.mem_univ T)
    dsimp [B];linarith
  exact (hb T F R hR χ W₁ W₂ X₁ X₂ a₁ b₁ a₂ b₂ pool β P keep Φ K E
    hX₁ hX₂ hb₁ hb₂ hs₁ hs₂ hprime hP hβ hs hK hΦ hE hchild).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE)

def commonChild (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂ : Plain) (left : Bool) (z : O) (D₁ D₂ : Finset (Ideal O))
    (J : Finset (CenteredMomentCommonProfile.liveIndices B.val)) : ℂ :=
  let d:=commonData (withHeight s τ v) C R B
  if left then child (naturalCharacter τ z) L a V₁ V₂ d.slots d.coefficient d.P v
    d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J
  else child (naturalCharacter τ z) L a V₁ V₂ d.slots d.coefficient d.P v
    d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J

lemma common_rawScale (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))) :
    rawScale L a (commonData (withHeight s τ v) C R B).X₁ 0=
      s.X₁/(Ideal.absNorm (B.val (Sum.inr 0)*CenteredMomentDivisorRectangle.selectedPlain L a 0):ℝ) := by
  simp only [rawScale,commonData,withHeight,map_mul,Nat.cast_mul,div_div]

theorem common_allocated_normalized (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (hRC : R*C≠0) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂ : Plain) (hV₁ : V₁.W=s.W₁) (hV₂ : V₂.W=s.W₂) (z : O) (hz : z≠0) :
    let d:=commonData (withHeight s τ v) C R B
    allocatedPositiveRow d.η d.m d.A z d.t d.slots d.coefficient d.P L a d.W₁ d.W₂ d.X₁ d.X₂=
      (((clippedScale (rawScale L a d.X₁ 0)):ℂ)^(Complex.I*v)*
       ((clippedScale (rawScale L a d.X₂ 1)):ℂ)^(Complex.I*v))*
       (polynomial (excluded (naturalCharacter τ z) (R*C)) false
          (V₁.profile _ (rawScale_pos L a d.X₁ d.X₁_pos 0) v) (clippedScale (rawScale L a d.X₁ 0)) 0 0*
        polynomial (excluded (naturalCharacter τ z) (R*C)) false
          (V₂.profile _ (rawScale_pos L a d.X₂ d.X₂_pos 1) v) (clippedScale (rawScale L a d.X₂ 1)) 0 0*
        ∏i∈liveIndices L a,naturalSlot (excluded (naturalCharacter τ z) (R*C))
          (d.slots i) (heightCoefficient (d.coefficient i) v) (d.P i)) := by
  dsimp only
  rw [naturalCharacter_eq τ z hz]
  have hh:=allocated_normalized τ z hz (R*C) hRC L a V₁ V₂
    (commonData (withHeight s τ v) C R B).slots
    (commonData (withHeight s τ v) C R B).coefficient
    (commonData (withHeight s τ v) C R B).P
    (commonData (withHeight s τ v) C R B).P_pos v
    (commonData (withHeight s τ v) C R B).X₁ (commonData (withHeight s τ v) C R B).X₂
    (commonData (withHeight s τ v) C R B).X₁_pos (commonData (withHeight s τ v) C R B).X₂_pos
  simpa only [hV₁,hV₂,commonData,withHeight] using hh

theorem allocated_radial_bound (b M : α→ℝ) (C₀ ε : ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (hb : Shared (liveIndices D a) b M C₀ ε)
    (η : Character) (R : Ideal O) (hR : R≠0) (V₁ V₂ : Plain)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (hprime : ∀i,∀I∈pool i,Prime I) (hP : ∀i,0<P i)
    (hβ : ∀i,∀I∈pool i,‖β i I‖≤M i)
    (hs : ∀i,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (r : Radial) (hkeep : ∀z,r.keep z → z≠0) (E : ℝ) (hE : 0≤E)
    (hchild : ∀D₁∈(CompletedGauss.primeSupport R).powerset,
      ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
      radialEnergy (fun z=>child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂
        hX₁ hX₂ D₁ D₂ J) r.keep r.profile r.scale≤E) :
    radialEnergy (fun z=>allocatedPositiveRow η
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z t pool β P D a V₁.W V₂.W X₁ X₂) r.keep r.profile r.scale≤
        C₀*(Ideal.absNorm R.radical:ℝ)^ε*E := by
  have hh:=hb (CompletedGauss.primeSupport R) (support_prime R) (naturalCharacter η)
    (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (clippedScale (rawScale D a X₁ 0)) (clippedScale (rawScale D a X₂ 1))
    (V₁.a/max 1 V₁.b) (max 1 V₁.b) (V₂.a/max 1 V₂.b) (max 1 V₂.b)
    pool (fun i=>heightCoefficient (β i) t) P r.keep r.profile r.scale E
    (by unfold clippedScale;positivity) (by unfold clippedScale;positivity)
    (by positivity) (by positivity) (profile_support V₁ _ _ t) (profile_support V₂ _ _ t)
    (fun i _=>hprime i) (fun i _=>hP i)
    (fun i _ I hi=>by rw [heightCoefficient_norm _ _ _ (hprime i I hi).ne_zero];exact hβ i I hi)
    (fun i _ I hi hn=>hs i I hi (left_ne_zero_of_mul hn)) r.scale_pos r.nonneg hE hchild
  rw [←primeSupport_product_radical R hR]
  convert hh using 1
  unfold radialEnergy
  apply tsum_congr
  intro z
  split_ifs with hz
  · dsimp only
    rw [allocated_normalized η z (hkeep z hz) R hR D a V₁ V₂ pool β P hP t X₁ X₂ hX₁ hX₂,
      naturalCharacter_eq η z (hkeep z hz)]
    have hphase (U : ℝ) : ‖((clippedScale U):ℂ)^(Complex.I*t)‖=1 :=
      positive_height_phase_norm _ _ (by unfold clippedScale;positivity)
    simp only [excluded,norm_mul,hphase,one_mul]
  · rfl

theorem natural_child_summable (η : Character) (R : Ideal O)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆CompletedGauss.primeSupport R)
    (hD₂ : D₂⊆CompletedGauss.primeSupport R) (J : Finset α) (r : Radial) :
    Summable (fun z=>if r.keep z then
      ‖child (naturalCharacter η z) D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ J‖^2*
        (r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0) := by
  have hn (S : Finset (Ideal O)) (hS : S⊆CompletedGauss.primeSupport R) :
      (0:ℝ)<Ideal.absNorm (∏I∈S,I) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun I hI=>(support_prime R I (hS hI)).ne_zero)))
  obtain ⟨PB,hPB,hbound⟩:=slots_bounded (liveIndices D a\J) pool (fun i=>heightCoefficient (β i) t) P
  exact pair_radial_summable (naturalCharacter η)
    (fun z=>∏i∈liveIndices D a\J,naturalSlot (naturalCharacter η z) (pool i) (heightCoefficient (β i) t) (P i))
    (fun _=>0) (fun _=>0)
    (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t) (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (V₁.a/max 1 V₁.b) (max 1 V₁.b) (V₂.a/max 1 V₂.b) (max 1 V₂.b)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) PB
    (by positivity) (by positivity) (div_pos (by unfold clippedScale;positivity) (hn D₁ hD₁))
    (div_pos (by unfold clippedScale;positivity) (hn D₂ hD₂))
    (profile_support V₁ _ _ t) (profile_support V₂ _ _ t) (fun z=>hbound (naturalCharacter η z))
    r.keep r.profile r.scale r.scale_pos

omit [DecidableEq α] in
lemma common_nonzero (s : Input α) (C : Ideal O) (B : actualAllocations s.pools C) : C≠0 := by
  rw [←(Finset.mem_filter.mp B.property).2]
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>alloc_ne s C B i)

lemma child_energy_eq_radial (s : Data α) (r : Radial) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) :
    childEnergy s r D a=
      radialEnergy (fun z=>allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P
        D a s.W₁ s.W₂ s.X₁ s.X₂) r.keep r.profile r.scale+
      radialEnergy (fun z=>allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P
        D a s.W₁ s.W₂ s.Y₁ s.Y₂) r.keep r.profile r.scale := by
  have hx:=CenteredMomentPositiveSummability.allocated_positive_summable s.η s.m s.A s.t
    s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.support₁ s.support₂ s.X₁_pos s.X₂_pos
    s.slots s.coefficient s.P D a r.keep r.profile r.scale r.scale_pos
  have hy:=CenteredMomentPositiveSummability.allocated_positive_summable s.η s.m s.A s.t
    s.W₁ s.W₂ s.b₁ s.b₂ s.Y₁ s.Y₂ s.support₁ s.support₂ s.Y₁_pos s.Y₂_pos
    s.slots s.coefficient s.P D a r.keep r.profile r.scale r.scale_pos
  unfold childEnergy radialEnergy
  rw [←hx.tsum_add hy]
  apply tsum_congr
  intro z
  unfold Radial.weight
  split_ifs <;> ring

def CommonBound (b M : α→ℝ) (C₀ ε : ℝ) : Prop :=
  ∀s : Input α,(∀i,s.hi i≤b i) → (∀i,s.M i≤M i) →
    ∀(τ : Character) (v : ℝ) (C R : Ideal O),R≠0 → ∀B : actualAllocations s.pools C,
    ∀(L : Ideal O) (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂ : Plain,V₁.W=s.W₁ → V₂.W=s.W₂ → ∀r : Radial,(∀z,r.keep z → z≠0) →
    ∀E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ true z D₁ D₂ J) r.keep r.profile r.scale≤E₁) →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ false z D₁ D₂ J) r.keep r.profile r.scale≤E₂) →
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂)

theorem actual_common_radial_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ CommonBound b M C₀ ε := by
  obtain ⟨C₀,hC₀,hbound⟩:=uniform_shared b M hM ε hε
  refine ⟨C₀,hC₀,?_⟩
  intro s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r hkeep E₁ E₂ hE₁ hE₂ hleft hright
  let d:=commonData (withHeight s τ v) C R B
  have hRC : R*C≠0:=mul_ne_zero hR (common_nonzero s C B)
  have hb:=hbound (CenteredMomentCommonProfile.liveIndices B.val) (liveIndices L a)
  have hc:= (commonSlots s C B).controls
  have hβ : ∀i,∀I∈d.slots i,‖d.coefficient i I‖≤M i := by
    intro i I _
    exact (hc.1 i I).trans (hMs i)
  have hs : ∀i,∀I∈d.slots i,d.coefficient i I≠0 → (I.absNorm:ℝ)≤b i*d.P i := by
    intro i I _ hn
    exact (hc.2 i I hn).trans (mul_le_mul_of_nonneg_right (hhi i) (s.P_pos i).le)
  have hl:=allocated_radial_bound (fun i : CenteredMomentCommonProfile.liveIndices B.val=>b i)
    (fun i=>M i) C₀ ε L a hb τ (R*C) hRC V₁ V₂ d.slots d.coefficient d.P
    d.prime d.P_pos hβ hs v d.X₁ d.X₂ d.X₁_pos d.X₂_pos r hkeep E₁ hE₁ hleft
  have hr:=allocated_radial_bound (fun i : CenteredMomentCommonProfile.liveIndices B.val=>b i)
    (fun i=>M i) C₀ ε L a hb τ (R*C) hRC V₁ V₂ d.slots d.coefficient d.P
    d.prime d.P_pos hβ hs v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos r hkeep E₂ hE₂ hright
  rw [child_energy_eq_radial]
  have hh:=add_le_add hl hr
  rw [←mul_add] at hh
  simpa only [d,commonData,withHeight,hV₁,hV₂] using hh

lemma nonexceptional_nonzero (η : Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (m A z : O)
    (hz : CenteredMomentRestrictedEnergy.nonexceptional η χ Q m A z) : z≠0 := hz.1

theorem uniform_initial_common_radial_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀T : Finset α,CommonBound (fun i : T=>b i) (fun i : T=>M i) C₀ ε := by
  have he (T : Finset α) : ∃C₀ : ℝ,0<C₀ ∧ CommonBound (fun i : T=>b i) (fun i : T=>M i) C₀ ε :=
    actual_common_radial_energy (fun i : T=>b i) (fun i : T=>M i) (fun i=>hM i) ε hε
  choose C hC hb using he
  let C₀ : ℝ:=1+∑T : Finset α,C T
  have hsum : 0≤∑T : Finset α,C T:=Finset.sum_nonneg (fun T _=>(hC T).le)
  refine ⟨C₀,by dsimp [C₀];linarith,?_⟩
  intro T s hhi hMs τ v I R hR B L a V₁ V₂ hV₁ hV₂ r hkeep E₁ E₂ hE₁ hE₂ hleft hright
  have hCB : C T≤C₀ := by
    have hh:=Finset.single_le_sum (fun T _=>(hC T).le) (Finset.mem_univ T)
    dsimp [C₀];linarith
  exact (hb T s hhi hMs τ v I R hR B L a V₁ V₂ hV₁ hV₂ r hkeep E₁ E₂ hE₁ hE₂ hleft hright).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (add_nonneg hE₁ hE₂))

lemma common_raw_same_product (s : Input α) (τ : Character) (v : ℝ) (C R : Ideal O)
    (B : actualAllocations s.pools C) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))) :
    let d:=commonData (withHeight s τ v) C R B
    rawScale L a d.X₁ 0*rawScale L a d.X₂ 1=rawScale L a d.Y₁ 0*rawScale L a d.Y₂ 1 :=
  raw_same_product L a _ _ _ _ (commonData (withHeight s τ v) C R B).same_product.symm

theorem original_nonexceptional_common_radial_energy (b M : α→ℝ) (hM : ∀i,0≤M i)
    (ε : ℝ) (hε : 0<ε) :
    ∃C₀ : ℝ,0<C₀ ∧ ∀s : Input α,(∀i,s.hi i≤b i) → (∀i,s.M i≤M i) →
    ∀(τ : Character) (v : ℝ) (C R : Ideal O),R≠0 → ∀B : actualAllocations s.pools C,
    ∀(L : Ideal O) (a : Allocation L (Finset.univ : Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂ : Plain,V₁.W=s.W₁ → V₂.W=s.W₂ → ∀(η : Character) (χ : RayFourExpansion.RayCharacter) (Q : Ideal O) (m A : O)
      (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H)
      (hΦ : ∀z : O,0≤(Φ (CenteredMomentSectorLocalization.normValue z/H)).re),
    let r:=CenteredMomentSecondOriginalChildren.sourceRadial
      (CenteredMomentRestrictedEnergy.nonexceptional η χ Q m A) Φ H hH hΦ

    ∀E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ true z D₁ D₂ J) r.keep r.profile r.scale≤E₁) →
    (∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
     ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      radialEnergy (fun z=>commonChild s τ v C R B L a V₁ V₂ false z D₁ D₂ J) r.keep r.profile r.scale≤E₂) →
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂) := by
  obtain ⟨C₀,hC₀,hb⟩:=actual_common_radial_energy b M hM ε hε
  refine ⟨C₀,hC₀,?_⟩
  intro s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ η χ Q m A Φ H hH hΦ r
    E₁ E₂ hE₁ hE₂ hleft hright
  exact hb s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r
    (fun _ hz=>hz.1) E₁ E₂ hE₁ hE₂ hleft hright

end SevenEighths.CenteredMomentAllocatedNaturalRadial

end

end OAI
