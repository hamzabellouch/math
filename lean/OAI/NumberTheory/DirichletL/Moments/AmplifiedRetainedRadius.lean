import OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
import OAI.NumberTheory.DirichletL.Moments.SmoothedWindowEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplifiedRetainedRadius
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstAmplificationChoice CenteredMomentGaussEnergy
open CenteredMomentSmoothedWindowEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentAmplificationErrorEnergy CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentGaussNormalization
local notation "O" => ActualEisensteinCubic.O

theorem ballProfile_support_upper (x : ℝ) (hx : 0≤x) (h : ballProfile x≠0) : x<2 := by
  have hb : x∈Function.support QuadraticInitialBound.sieveBump := by
    intro hz
    exact h (by simp only [ballProfile,QuadraticInitialBound.sieveCutoff_apply,hz,Complex.ofReal_zero])
  rw [QuadraticInitialBound.sieveBump.support_eq] at hb
  simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hx,
    QuadraticInitialBound.sieveBump] using hb

theorem ballProfile_radius_le (x Y V : ℝ) (hx : 0≤x) (hY : 0<Y) (hV : 0<V)
    (hscale : 2*Y≤V) : (ballProfile (x/Y)).re≤(ballProfile (x/V)).re := by
  by_cases hz : ballProfile (x/Y)=0
  · simpa only [hz,Complex.zero_re] using ballProfile_nonneg (x/V)
  have hs := ballProfile_support_upper (x/Y) (div_nonneg hx hY.le) hz
  have hxy : x≤V := ((div_lt_iff₀ hY).mp hs).le.trans hscale
  rw [ballProfile_one (x/V) (div_nonneg hx hV.le) ((div_le_one hV).mpr hxy)]
  exact ballProfile_le_one _

theorem gaussEnergy_radius_le {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (Y V : ℝ) (hY : 0<Y) (hV : 0<V) (hscale : 2*Y≤V) :
    (gaussEnergy S a ha c ballProfile Y).re≤(gaussEnergy S a ha c ballProfile V).re := by
  have h1 := gaussEnergy_hasSum_re S a ha c ballProfile Y hY
  have h2 := gaussEnergy_hasSum_re S a ha c ballProfile V hV
  rw [←h1.tsum_eq,←h2.tsum_eq]
  apply Summable.tsum_le_tsum _ h1.summable h2.summable
  intro z
  exact mul_le_mul_of_nonneg_left
    (ballProfile_radius_le _ Y V (sq_nonneg _) hY hV hscale) (sq_nonneg _)

theorem sourceGaussEnergy_radius_le (Q : Finset (Ideal O)) (c f : Ideal O→ℂ)
    (Y V : ℝ) (hY : 0<Y) (hV : 0<V) (hscale : 2*Y≤V) :
    (sourceGaussEnergy Q c f ballProfile Y).re≤(sourceGaussEnergy Q c f ballProfile V).re :=
  gaussEnergy_radius_le _ _ _ _ Y V hY hV hscale

theorem childEnergy_radius_le {ι : Type*} [Fintype ι]
    (D : OriginalData ι) (τ : RayFourExpansion.RayCharacter→Character) (p : O) (n : ℕ)
    (t T Y V : ℝ) (hT : 0≤T) (hY : 0<Y) (hV : 0<V) (hscale : 2*Y≤V) :
    D.childEnergy τ p n t T Y≤D.childEnergy τ p n t T V := by
  unfold OriginalData.childEnergy
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (by positivity) (localErrorCost_nonneg p n))
  apply div_le_div_of_nonneg_right _ (div_nonneg hT (by positivity))
  apply Finset.sum_le_sum
  intro χ _
  apply Finset.sum_le_sum
  intro B _
  exact sourceGaussEnergy_radius_le _ _ _ Y V hY hV hscale

lemma exponent_max (d K0 j c g : ℝ) :
    j+(max (d+K0-j-c) 0+g)=max (j+g) (d+K0-c+g) := by
  by_cases h : d+K0-j-c≤0
  · rw [max_eq_right h,max_eq_left (by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge h),max_eq_right (by linarith)]
    ring

lemma rpow_exponent_max (Z a b : ℝ) (hZ : 1≤Z) :
    Z^(max a b)=max (Z^a) (Z^b) := by
  rcases le_total a b with h|h
  · rw [max_eq_right h,max_eq_right (Real.rpow_le_rpow_of_exponent_le hZ h)]
  · rw [max_eq_left h,max_eq_left (Real.rpow_le_rpow_of_exponent_le hZ h)]

theorem main_radius_identity (Z d K0 j c sigma : ℝ) (hZ : 1≤Z) :
    Z^(j+mainGain (d+K0-j) c sigma)=
      max (Z^(j+2*sigma)) (Z^(d+K0-c+2*sigma)) := by
  rw [mainGain,exponent_max,rpow_exponent_max Z _ _ hZ]

theorem error_radius_identity (Z d K0 j c sigma : ℝ) (p : O) (k : ℕ) (hZ : 1≤Z) :
    Z^(j+errorGain (d+K0-j) c sigma Z p k)=
      max (Z^(j+sigma))
        (Z^(d+K0-c-2*errorRemoval p Z k+errorMoving p Z k+sigma)) := by
  have he := exponent_max d K0 j (c+2*errorRemoval p Z k-errorMoving p Z k) sigma
  have hbase : j+errorGain (d+K0-j) c sigma Z p k=
      max (j+sigma) (d+K0-c-2*errorRemoval p Z k+errorMoving p Z k+sigma) := by
    unfold errorGain
    convert he using 1 <;> ring_nf
  rw [hbase,rpow_exponent_max Z _ _ hZ]

lemma envelope_exponent (d K0 j c g δ : ℝ) (hδ : 0≤δ) (hj : j≤K0+δ) :
    j+(max (d+K0-j-c) 0+g)≤K0+max (d-c) 0+g+δ := by
  rw [exponent_max]
  apply max_le
  · linarith [le_max_right (d-c) (0:ℝ)]
  · linarith [le_max_left (d-c) (0:ℝ)]

theorem main_exponent_envelope (d K0 j c sigma δ : ℝ) (hδ : 0≤δ) (hj : j≤K0+δ) :
    j+mainGain (d+K0-j) c sigma≤K0+max (d-c) 0+2*sigma+δ :=
  envelope_exponent d K0 j c (2*sigma) δ hδ hj

theorem error_exponent_envelope (d K0 j c sigma δ Z : ℝ) (p : O) (k : ℕ)
    (hδ : 0≤δ) (hj : j≤K0+δ) :
    j+errorGain (d+K0-j) c sigma Z p k≤
      K0+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma+δ := by
  have he := envelope_exponent d K0 j (c+2*errorRemoval p Z k-errorMoving p Z k) sigma δ hδ hj
  unfold errorGain
  convert he using 1 <;> ring_nf

theorem eventually_support_reserve (reserve : ℝ) (hreserve : 0<reserve) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ 2≤Z^reserve := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hreserve).eventually (eventually_ge_atTop (2:ℝ))] with Z hZ hpow
  exact ⟨hZ,hpow⟩

lemma doubled_radius_le (Z a b reserve : ℝ) (hZ : 1<Z) (hab : a≤b)
    (hreserve : 2≤Z^reserve) : 2*Z^a≤Z^(b+reserve) := by
  rw [Real.rpow_add (zero_lt_one.trans hZ)]
  calc
    _≤2*Z^b := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le hab) (by norm_num)
    _≤Z^b*Z^reserve := by
      rw [mul_comm (Z^b)]
      exact mul_le_mul_of_nonneg_right hreserve (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

theorem unamplified_radius_identity (Z d K0 j c sigma : ℝ) (hZ : 1≤Z) :
    Z^(j+(max (d+K0-j-c) 0+sigma))=
      max (Z^(j+sigma)) (Z^(d+K0-c+sigma)) := by
  rw [exponent_max,rpow_exponent_max Z _ _ hZ]

theorem dyadic_to_common_ball {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (coeff : α→ℂ)
    (Z d K0 c sigma δ reserve : ℝ) (hZ : 1<Z) (hsigma : 0≤sigma) (hδ : 0≤δ)
    (n : ℤ) (hn : Real.logb Z (dyadicScale n)≤K0+δ) (hreserve : 2≤Z^reserve) :
    (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha coeff h‖^2)≤
      (gaussEnergy S a ha coeff ballProfile (Z^(K0+max (d-c) 0+sigma+δ+reserve))).re := by
  apply (dyadic_to_ball S a ha coeff Z sigma
    (d+K0-Real.logb Z (dyadicScale n)) c hZ hsigma n).trans
  apply gaussEnergy_radius_le _ _ _ _ _ _
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact doubled_radius_le Z _ _ reserve hZ
    (envelope_exponent d K0 _ c sigma δ hδ hn) hreserve

def mainCommonRadius (Z d K0 c sigma δ reserve : ℝ) : ℝ :=
  Z^(K0+max (d-c) 0+2*sigma+δ+reserve)

def errorCommonRadius (Z d K0 c sigma δ reserve : ℝ) (p : O) (k : ℕ) : ℝ :=
  Z^(K0+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma+δ+reserve)

theorem main_energy_common {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (coeff : α→ℂ)
    (Z d K0 j c sigma δ reserve : ℝ) (hZ : 1<Z) (hδ : 0≤δ)
    (hj : j≤K0+δ) (hreserve : 2≤Z^reserve) :
    (gaussEnergy S a ha coeff ballProfile (Z^(j+mainGain (d+K0-j) c sigma))).re≤
      (gaussEnergy S a ha coeff ballProfile (mainCommonRadius Z d K0 c sigma δ reserve)).re := by
  apply gaussEnergy_radius_le _ _ _ _ _ _
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact doubled_radius_le Z _ _ reserve hZ
    (main_exponent_envelope d K0 j c sigma δ hδ hj) hreserve

theorem child_energy_common {ι : Type*} [Fintype ι]
    (D : OriginalData ι) (τ : RayFourExpansion.RayCharacter→Character) (p : O) (n : ℕ)
    (t T Z d K0 j c sigma δ reserve : ℝ) (hT : 0≤T) (hZ : 1<Z) (hδ : 0≤δ)
    (hj : j≤K0+δ) (hreserve : 2≤Z^reserve) :
    D.childEnergy τ p n t T (Z^(j+errorGain (d+K0-j) c sigma Z p (n+1)))≤
      D.childEnergy τ p n t T (errorCommonRadius Z d K0 c sigma δ reserve p (n+1)) := by
  apply childEnergy_radius_le D τ p n t T _ _ hT
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact doubled_radius_le Z _ _ reserve hZ
    (error_exponent_envelope d K0 j c sigma δ Z p (n+1) hδ hj) hreserve

theorem errorCommonRadius_six (Z d K0 c sigma δ reserve : ℝ) (p : O) :
    errorCommonRadius Z d K0 c sigma δ reserve p 6=
      Z^(K0+max (d-c-2*errorRemoval p Z 6) 0+sigma+δ+reserve) := by
  simp only [errorCommonRadius,errorMoving,ite_true,add_zero]

open CenteredMomentFirstScale

theorem retained_nominal_upper (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi : ℝ) (hK : 0<K) (hX : 0<X) (hZ : 1<Z)
    (hC : 0<Csec) (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) :
    Real.logb Z (dyadicScale n)≤nominalLog I J E K X Z+frequencyLoss Z Csec xi := by
  apply retained_first_dyad_enclosure Tsec Z Csec (nominalLog I J E K X Z) xi hZ hC _ n hn
  rw [nominalLog,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
    (firstNominalScale_pos I J E hE K X hK hX)]
  exact hsec

theorem actual_retained_radii (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi d c sigma reserve : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 1≤Csec) (hxi : 0≤xi)
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) (hreserve : 2≤Z^reserve) :
    let K0 := nominalLog I J E K X Z
    let j := Real.logb Z (dyadicScale n)
    let δ := frequencyLoss Z Csec xi
    2*Z^(j+mainGain (d+K0-j) c sigma)≤mainCommonRadius Z d K0 c sigma δ reserve ∧
      ∀(p:O)(k:ℕ),2*Z^(j+errorGain (d+K0-j) c sigma Z p k)≤
        errorCommonRadius Z d K0 c sigma δ reserve p k := by
  dsimp only
  have hj := retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec n hn
  have hδ := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  constructor
  · exact doubled_radius_le Z _ _ reserve hZ (main_exponent_envelope _ _ _ _ _ _ hδ hj) hreserve
  · intro p k
    exact doubled_radius_le Z _ _ reserve hZ (error_exponent_envelope _ _ _ _ _ _ Z p k hδ hj) hreserve

open CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationOriginalErrors CenteredMomentAmplificationGlobal

theorem eventually_original_amplification_common {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec xi reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6)
    (hC : 1≤Csec) (hxi : 0≤xi) (hreserve : 0<reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayFourExpansion.RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          HeckeRowClosure.rowConductorBound (CenteredMomentChildRows.childCharacter η χ) m 1 (p.val^(2*CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i)))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T d cLog : ℝ),0<T →
          ∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (j : ℤ),Retained (frequencyRadius Tsec Z xi) j →
          Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve)).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve p (errorIndex i+1))) := by
  filter_upwards [eventually_original_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap,
    eventually_support_reserve reserve hreserve] with Z hz hsupport
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
    I J E hE K X Tsec hK hX hsec j hj hMdyad
  let K0 := nominalLog I J E K X Z
  let kdyad := Real.logb Z (dyadicScale j)
  have henclose : kdyad≤K0+frequencyLoss Z Csec xi :=
    retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
      (zero_lt_one.trans_le hC) hsec j hj
  have hδ := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  have he := henergy D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T
    (d+K0-kdyad) cLog hT j hMdyad
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact main_energy_common _ _ _ _ Z d K0 kdyad cLog sigma _ reserve hZ hδ henclose hsupport.2
  · apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro i _
    exact child_energy_common D.active (τ p i) p (errorIndex i) t T Z d K0 kdyad cLog sigma
      _ reserve hT.le hZ hδ henclose hsupport.2

end SevenEighths.CenteredMomentAmplifiedRetainedRadius

end

end OAI
