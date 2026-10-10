import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDegree
import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalEnergy
import OAI.NumberTheory.DirichletL.Moments.ExceptionalAllocationShell

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentExceptionalCappedAmplitude
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentCounting CenteredMomentHeckeTwist CenteredMomentTwist CenteredMomentHeight CenteredMomentLattice
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondExceptionalCount
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentForcing CenteredMomentChildRows
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge UniqueFactorizationMonoid
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => HeckeFamily.O

theorem rowTwistedSum_absolute (η : Character) (m A z : O) (W : ℝ→ℂ)
    (b M t X : ℝ) (hb : 0≤b) (hM : 0≤M) (hX : 0<X)
    (hs : Function.support W⊆Set.Iic b) (hW : ∀x,‖W x‖≤M) :
    ‖rowTwistedSum η m A z W t X‖≤(128*b*M)*X := by
  have hh := norm_tsum_ideal_ball
    (fun I : Ideal O => (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I)*
      (Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)) (b*X) M
    (mul_nonneg hb hX.le) hM (by
      change (idealCoeff η (0:Ideal O)*_)*_*_=0
      rw [map_zero,zero_mul,zero_mul,zero_mul]) (by
      intro I
      by_cases hI : I=0
      · subst I; simpa only [map_zero,zero_mul,mul_zero,norm_zero] using hM
      · rw [norm_mul]
        exact (mul_le_mul (row_twisted_coefficient_norm η m A z t I hI) (hW _)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul M)) (by
      intro I hI
      exact (div_le_iff₀ hX).mp (hs (right_ne_zero_of_mul hI)))
  exact hh.trans_eq (by ring)

theorem normalized_rectangle_absolute (η : Character) (m A z : O)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ M₁ M₂ : ℝ)
    (hb₁ : 0≤b₁) (hb₂ : 0≤b₂) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (hW₁ : ∀x,‖W₁ x‖≤M₁) (hW₂ : ∀x,‖W₂ x‖≤M₂)
    (t X₁ X₂ Y₁ Y₂ T : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hpX : X₁*X₂=T) (hpY : Y₁*Y₂=T) :
    ‖(Real.sqrt T:ℂ)⁻¹ *
      (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
       rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)‖≤
      (2*(128*b₁*M₁)*(128*b₂*M₂))*Real.sqrt T := by
  have hT : 0<T := hpX ▸ mul_pos hX₁ hX₂
  have hsq : 0<Real.sqrt T := Real.sqrt_pos.2 hT
  have hprod (U V : ℝ) (hU : 0<U) (hV : 0<V) :
      ‖rowTwistedSum η m A z W₁ t U*rowTwistedSum η m A z W₂ t V‖≤
        ((128*b₁*M₁)*(128*b₂*M₂))*(U*V) := by
    rw [norm_mul]
    apply (mul_le_mul (rowTwistedSum_absolute η m A z W₁ b₁ M₁ t U hb₁ hM₁ hU hs₁ hW₁)
      (rowTwistedSum_absolute η m A z W₂ b₂ M₂ t V hb₂ hM₂ hV hs₂ hW₂)
      (norm_nonneg _) (by positivity)).trans_eq
    ring
  have hraw := (norm_sub_le
    (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)
    (rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)).trans
      (add_le_add (hprod X₁ X₂ hX₁ hX₂) (hprod Y₁ Y₂ hY₁ hY₂))
  rw [hpX,hpY] at hraw
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsq.le]
  apply (mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hsq.le)).trans_eq
  have he := Real.sq_sqrt hT.le
  field_simp
  rw [he]
  ring

theorem capped_rectangle_uniform_degree
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hb₁ : 0≤b₁) (hb₂ : 0≤b₂) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∀W₁ W₂ : ℝ→ℂ,
      ∀_hs₁ : Function.support W₁⊆Set.Icc a₁ b₁,
      ∀_hs₂ : Function.support W₂⊆Set.Icc a₂ b₂,
      ∀_hW₁ : ContDiff ℝ ∞ W₁,∀_hW₂ : ContDiff ℝ ∞ W₂,
      ∃C : ℝ,0<C ∧ ∀Z : ℝ,1≤Z → ∀(η : Character)(m A z : O),
      m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹ *
        (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
         rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)‖≤
        C*Z^ε*(1+‖t‖)^J*(Real.sqrt T/max 1 L) := by
  obtain ⟨J,hJ⟩ := row_rectangle_uniform_degree a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hcancel⟩ := hJ Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  let M₁ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ 0)
  let M₂ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ 0)
  have hM₁ : 0≤M₁ := apply_nonneg _ _
  have hM₂ : 0≤M₂ := apply_nonneg _ _
  have hbound₁ (x : ℝ) : ‖W₁ x‖≤M₁ := by
    rw [←normPowerProfile_norm W₁ a₁ b₁ ha₁ hs₁ hW₁ 0 x]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hbound₂ (x : ℝ) : ‖W₂ x‖≤M₂ := by
    rw [←normPowerProfile_norm W₂ a₂ b₂ ha₂ hs₂ hW₂ 0 x]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  let D : ℝ := 2*(128*b₁*M₁)*(128*b₂*M₂)
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨C+D,by positivity,?_⟩
  intro Z hZ η m A z hm hA hz hml hm2 hc he t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hpow : 0≤Z^ε := Real.rpow_nonneg (zero_le_one.trans hZ) _
  by_cases hlarge : 1≤L
  · rw [max_eq_right hlarge]
    exact (hcancel Z hZ η m A z hm hA hz hml hm2 hc he t X₁ X₂ Y₁ Y₂ T L
      hL hX₁ hX₂ hY₁ hY₂ hpX hpY).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) hpow) (by positivity))
          (div_nonneg (Real.sqrt_nonneg _) hL.le))
  · rw [max_eq_left (le_of_not_ge hlarge),div_one]
    have ha := normalized_rectangle_absolute η m A z W₁ W₂ b₁ b₂ M₁ M₂ hb₁ hb₂ hM₁ hM₂
      (fun _ hx=>(hs₁ hx).2) (fun _ hx=>(hs₂ hx).2) hbound₁ hbound₂
      t X₁ X₂ Y₁ Y₂ T (hL.trans_le hX₁) (hL.trans_le hX₂)
      (hL.trans_le hY₁) (hL.trans_le hY₂) hpX hpY
    apply ha.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg T)
    calc
      D≤C+D := le_add_of_nonneg_left hC.le
      _≤(C+D)*Z^ε := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hZ hε.le)
      _≤(C+D)*Z^ε*(1+‖t‖)^J := le_mul_of_one_le_right (by positivity)
        (one_le_pow₀ (by linarith [norm_nonneg t]))

theorem actual_capped_slots
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hb₁ : 0≤b₁) (hb₂ : 0≤b₂) (hε : 0<ε) (hB : 0≤B) :
    ∃J : ℕ,∀Q : Ideal O,Q≠0 → ∀W₁ W₂ : ℝ→ℂ,
      ∀_hs₁ : Function.support W₁⊆Set.Icc a₁ b₁,
      ∀_hs₂ : Function.support W₂⊆Set.Icc a₂ b₂,
      ∀_hW₁ : ContDiff ℝ ∞ W₁,∀_hW₂ : ContDiff ℝ ∞ W₂,
      ∃C : ℝ,0<C ∧ ∀(ι : Type*) [Fintype ι],∀Z : ℝ,1≤Z →
      ∀(η : Character)(m A z : O),m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (HeckeRowClosure.rowConductorBound η m 1 (A*z):ℝ)≤Z^B →
      CenteredExceptionalProfile.FixedInducingRow η Q m A z →
      ∀(S : ι→Finset (Ideal O))(β : ι→Ideal O→ℂ)(P b M : ι→ℝ),
      (∀i,0<P i) → (∀i,0≤b i) → (∀i,0≤M i) →
      (∀i,∀I∈S i,‖β i I‖≤M i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀t X₁ X₂ Y₁ Y₂ T L : ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖≤
        C*Z^ε*(1+‖t‖)^J*(∏i,128*b i*M i)*(Real.sqrt (T*∏i,P i)/max 1 L) := by
  obtain ⟨J,hJ⟩ := capped_rectangle_uniform_degree a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ Q hQ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro ι _ Z hZ η m A z hm hA hz hml hm2 hc he S β P b M hP hb hM hβ hN
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0<T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hslots (i : ι) : ‖rowSlot η m A z (S i) (β i) t‖≤(128*b i*M i)*P i := by
    convert rowSlot_bound η m A z (S i) (β i) t (b i*P i) (M i)
      (mul_nonneg (hb i) (hP i).le) (hM i) (hβ i) (hN i) using 1; ring
  exact whole_product_normalization _ (fun i=>rowSlot η m A z (S i) (β i) t)
    (fun i=>128*b i*M i) P (C*Z^ε*(1+‖t‖)^J) T (max 1 L) (by positivity) hT
    (zero_lt_one.trans_le (le_max_left _ _))
    (fun i=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hM i)) hP hslots
    (hbound Z hZ η m A z hm hA hz hml hm2 hc he t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY)

theorem actual_canonical_capped_energy
    (a₁ b₁ a₂ b₂ ε B:ℝ) (ha₁:0<a₁) (ha₂:0<a₂)
    (hb₁:0≤b₁) (hb₂:0≤b₂) (hε:0<ε) (hB:0≤B) :
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∀W₁ W₂:ℝ→ℂ,Function.support W₁⊆Set.Icc a₁ b₁ →
      Function.support W₂⊆Set.Icc a₂ b₂ → ContDiff ℝ ∞ W₁ → ContDiff ℝ ∞ W₂ →
      ∃C0:ℝ,0<C0 ∧ ∀(ι:Type*) [Fintype ι],∀Z:ℝ,1<Z →
      ∀(η:Character) (χ:RayFourExpansion.RayCharacter) (C D:Ideal O) (_hC:Supported C)
        (U:Finset (CommonIndex C D)),IsCoprime Q C → idealCoeff η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m A z) →
      (∀z∈rows,(HeckeRowClosure.rowConductorBound (childCharacter η χ) m 1 (A*z):ℝ)≤Z^B) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b Ms:ι→ℝ),
      (∀i,0<P i) → (∀i,0≤b i) → (∀i,0≤Ms i) →
      (∀i,∀I∈S i,‖β i I‖≤Ms i) →
      (∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) →
      ∀t X₁ X₂ Y₁ Y₂ T L:ℝ,0<L → L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ →
      X₁*X₂=T → Y₁*Y₂=T →
      (∑z∈rows,‖centeredSlotRow (childCharacter η χ) m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2)≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun p:CommonIndex C D=>p.val)
          (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6))*
        (C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/max 1 L))^2 := by
  obtain ⟨J,hJ⟩:=actual_capped_slots a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro Q hQ0 hQ hQ72 W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C0,hC0,hpoint⟩:=hJ Q hQ0 W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C0,hC0,?_⟩
  intro ι _ Z hZ η χ C D hC U hQC hη m hm hmLam hm2 A rows hrows hex hcond Cr M hCr hN
    S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hXT hYT
  have hA:A≠0:=mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC)
    (nonunitFrequencyGenerator_ne_zero C D hC U)
  have hc:=actual_canonical_exceptional_count η χ C D hC U Q hQ0 hQ hQ72 hQC hη m hm hmLam hm2
    rows hrows hex Z Cr M hZ hCr hN
  have hp:∀z∈rows,‖centeredSlotRow (childCharacter η χ) m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖≤
      C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/max 1 L):=by
    intro z hz
    exact hpoint ι Z hZ.le (childCharacter η χ) m A z hm hA (hrows z hz) hmLam hm2
      (hcond z hz) (hex z hz) S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hXT hYT
  calc
    _≤∑z∈rows,(C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/max 1 L))^2 :=
      Finset.sum_le_sum (fun z hz=>pow_le_pow_left₀ (norm_nonneg _) (hp z hz) 2)
    _=(rows.card:ℝ)*(C0*Z^ε*(1+‖t‖)^J*(∏i,128*b i*Ms i)*(Real.sqrt (T*∏i,P i)/max 1 L))^2 := by simp
    _≤_:=mul_le_mul_of_nonneg_right hc (sq_nonneg _)

theorem max_raw_reduction (Z Rred r : ℝ) (hZ : 1<Z) (hR : 0<Rred) :
    max 1 (Z^r/Rred)=Z^(max (r-Real.logb Z Rred) 0) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have he : Z^r/Rred=Z^(r-Real.logb Z Rred) := by
    rw [Real.rpow_sub hz,Real.rpow_logb hz hZ.ne' hR]
  rw [he]
  by_cases h : 0≤r-Real.logb Z Rred
  · rw [max_eq_left h,max_eq_right (Real.one_le_rpow hZ.le h)]
  · rw [max_eq_right (le_of_not_ge h),Real.rpow_zero,
      max_eq_left (Real.rpow_le_one_of_one_le_of_nonpos hZ.le (le_of_not_ge h))]

theorem reciprocal_max_raw_reduction (Z Rred r : ℝ) (hZ : 1<Z) (hR : 0<Rred) :
    1/max 1 (Z^r/Rred)=Z^(-max (r-Real.logb Z Rred) 0) := by
  rw [max_raw_reduction Z Rred r hZ hR,Real.rpow_neg (zero_le_one.trans hZ.le),one_div]

theorem allocation_reciprocal_max {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : CenteredMomentActiveDivisorShell.Source ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (Z r : ℝ) (hZ : 1<Z) :
    1/max 1 (Z^r/formalReductionFactor D a s.P)=
      Z^(-max (r-Real.logb Z (formalReductionFactor D a s.P)) 0) := by
  apply reciprocal_max_raw_reduction Z _ r hZ
  exact mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))

end SevenEighths.CenteredMomentExceptionalCappedAmplitude

end

end OAI
