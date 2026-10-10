import OAI.NumberTheory.DirichletL.Moments.ReflectionMass

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonMaskExpansion
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def naturalSlot (χ : Character) (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) : ℂ :=
  (Real.sqrt P:ℂ)⁻¹ * ∑ I∈pool,idealCoeff χ I*β I

def profileSlot (χ : Character) (pool : Finset (Ideal O))
    (ν : Ideal O→ℂ) (W : ℝ→ℂ) (P : ℝ) : ℂ :=
  naturalSlot χ pool (fun I=>ν I*W ((I.absNorm:ℝ)/P)) P

lemma outside_prime (R : Finset (Ideal O)) (hR : ∀ I∈R,Prime I)
    (I : Ideal O) (hI : Prime I) : outside R I ↔ I∉R := by
  constructor
  · intro h hi
    exact h I hi dvd_rfl
  · intro h J hj hd
    have he : J=I := (prime_dvd_prime_iff_eq (hR J hj) hI).mp hd
    exact h (he ▸ hj)

lemma deleted_prime (χ : Character) (R : Finset (Ideal O)) (hR : ∀ I∈R,Prime I)
    (I : Ideal O) (hI : Prime I) :
    idealCoeff (χ.excludePrimes R hR) I = if I∈R then 0 else idealCoeff χ I := by
  have h:=deleted_coefficient χ R hR ⟨I,hI.ne_zero⟩
  simpa only [outside_prime R hR I hI,ite_not] using h

theorem naturalSlot_delete (χ : Character) (R : Finset (Ideal O)) (hR : ∀ I∈R,Prime I)
    (pool : Finset (Ideal O)) (hp : ∀ I∈pool,Prime I) (β : Ideal O→ℂ) (P : ℝ) :
    naturalSlot (χ.excludePrimes R hR) pool β P =
      naturalSlot χ pool β P - naturalSlot χ (pool∩R) β P := by
  unfold naturalSlot
  have hinter : pool∩R=pool.filter (fun I=>I∈R) := by ext I;simp
  rw [←mul_sub,hinter,Finset.sum_filter,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro I hi
  rw [deleted_prime χ R hR I (hp I hi)]
  by_cases h:I∈R <;> simp [h]

lemma prod_sub_expansion {α : Type*} [DecidableEq α] (F : Finset α) (a b : α→ℂ) :
    (∏i∈F,(a i-b i))=∑J∈F.powerset,(-1:ℂ)^J.card*(∏i∈J,b i)*(∏i∈F\J,a i) := by
  have he : (∏i∈F,(a i-b i))=∏i∈F,((-b i)+a i) := by
    apply Finset.prod_congr rfl
    intro i hi
    ring
  rw [he,Finset.prod_add]
  simp only [Finset.prod_neg]

def plainCoefficient (χ : Character) (D : Finset (Ideal O)) : ℂ :=
  (moebius (∏I∈D,I):ℂ)*(idealCoeff χ (∏I∈D,I)/(Real.sqrt (Ideal.absNorm (∏I∈D,I):ℝ):ℂ))

variable {α : Type*} [DecidableEq α]

def signedCoefficient (χ : Character) (R D₁ D₂ : Finset (Ideal O))
    (J : Finset α) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) : ℂ :=
  plainCoefficient χ D₁*plainCoefficient χ D₂*(-1:ℂ)^J.card*
    ∏i∈J,naturalSlot χ (pool i∩R) (β i) (P i)

theorem simultaneous_deletion (χ : Character) (R : Finset (Ideal O))
    (hR : ∀ I∈R,Prime I) (W₁ W₂ : 𝓢(ℝ,ℂ)) (X₁ X₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (F : Finset α)
    (pool : α→Finset (Ideal O)) (hp : ∀i∈F,∀I∈pool i,Prime I)
    (β : α→Ideal O→ℂ) (P : α→ℝ) :
    HeckeDyadic.polynomial (χ.excludePrimes R hR) false W₁ X₁ 0 0 *
      HeckeDyadic.polynomial (χ.excludePrimes R hR) false W₂ X₂ 0 0 *
      (∏i∈F,naturalSlot (χ.excludePrimes R hR) (pool i) (β i) (P i)) =
    ∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
      signedCoefficient χ R D₁ D₂ J pool β P *
        (HeckeDyadic.polynomial χ false W₁ (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
         HeckeDyadic.polynomial χ false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
         ∏i∈F\J,naturalSlot χ (pool i) (β i) (P i)) := by
  have hs : (∏i∈F,naturalSlot (χ.excludePrimes R hR) (pool i) (β i) (P i))=
      ∑J∈F.powerset,(-1:ℂ)^J.card*(∏i∈J,naturalSlot χ (pool i∩R) (β i) (P i))*
        (∏i∈F\J,naturalSlot χ (pool i) (β i) (P i)) := by
    have hh:=prod_sub_expansion F (fun i=>naturalSlot χ (pool i) (β i) (P i))
      (fun i=>naturalSlot χ (pool i∩R) (β i) (P i))
    exact (Finset.prod_congr rfl (fun i hi=>naturalSlot_delete χ R hR (pool i) (hp i hi) (β i) (P i))).trans hh
  rw [normalized_finite_deletion_moebius χ R hR W₁ (schwartz_decayTwo W₁) X₁ hX₁,
    normalized_finite_deletion_moebius χ R hR W₂ (schwartz_decayTwo W₂) X₂ hX₂,hs]
  rw [Finset.sum_mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro D₁ hD₁
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro D₂ hD₂
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  dsimp only [signedCoefficient,plainCoefficient]
  ring

def slotMass (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) : ℝ :=
  (Real.sqrt P)⁻¹ * ∑I∈pool∩R,‖β I‖

lemma slotMass_nonneg (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    0≤slotMass R pool β P := by unfold slotMass;positivity

lemma naturalSlot_norm (χ : Character) (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    ‖naturalSlot χ (pool∩R) β P‖≤slotMass R pool β P := by
  rw [naturalSlot,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hi
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)

lemma plainCoefficient_norm (χ : Character) (D : Finset (Ideal O))
    (hD : ∀I∈D,Prime I) : ‖plainCoefficient χ D‖≤weight (∏I∈D,I) := by
  rw [plainCoefficient,subset_product_moebius D hD]
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_div_of_nonneg_right (idealCoeff_norm_le_one χ _) (Real.sqrt_nonneg _)).trans_eq
    (by simp only [weight,one_div])

lemma slot_point_mass (I : Ideal O) (hI : Prime I) (β : Ideal O→ℂ)
    (P b M : ℝ) (hP : 0<P) (hM : 0≤M) (hβ : ‖β I‖≤M)
    (hs : β I≠0 → (I.absNorm:ℝ)≤b*P) :
    (Real.sqrt P)⁻¹*‖β I‖≤(Real.sqrt (max 1 b)*M)*weight I := by
  by_cases hz : β I=0
  · simp only [hz,norm_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hM) (weight_nonneg _)
  have hN : (0:ℝ)<I.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI.ne_zero)
  have hB : 0≤max 1 b := le_trans zero_le_one (le_max_left _ _)
  have hsqrt : Real.sqrt (I.absNorm:ℝ)≤Real.sqrt (max 1 b)*Real.sqrt P := by
    rw [←Real.sqrt_mul hB]
    exact Real.sqrt_le_sqrt ((hs hz).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hP.le))
  have hi : (Real.sqrt P)⁻¹≤Real.sqrt (max 1 b)*weight I := by
    rw [weight,←div_eq_mul_inv,inv_eq_one_div,
      div_le_div_iff₀ (Real.sqrt_pos.mpr hP) (Real.sqrt_pos.mpr hN)]
    simpa using hsqrt
  calc
    _≤(Real.sqrt (max 1 b)*weight I)*M :=
      mul_le_mul hi hβ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (weight_nonneg _))
    _=_ := by ring

lemma slotMass_bound (R pool : Finset (Ideal O)) (hp : ∀I∈pool,Prime I)
    (β : Ideal O→ℂ) (P b M : ℝ) (hP : 0<P) (hM : 0≤M)
    (hβ : ∀I∈pool,‖β I‖≤M) (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤b*P) :
    slotMass R pool β P≤(Real.sqrt (max 1 b)*M)*∑I∈R,weight I := by
  unfold slotMass
  rw [Finset.mul_sum]
  calc
    _≤∑I∈pool∩R,(Real.sqrt (max 1 b)*M)*weight I :=
      Finset.sum_le_sum (fun I hi=>slot_point_mass I (hp I (Finset.mem_inter.mp hi).1)
        β P b M hP hM (hβ I (Finset.mem_inter.mp hi).1) (hs I (Finset.mem_inter.mp hi).1))
    _=(Real.sqrt (max 1 b)*M)*∑I∈pool∩R,weight I := (Finset.mul_sum _ _ _).symm
    _≤_ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun I hi hn=>weight_nonneg I))
      (mul_nonneg (Real.sqrt_nonneg _) hM)

lemma one_add_sum_weight (R : Finset (Ideal O)) :
    1+∑I∈R,weight I≤∏I∈R,(1+weight I) := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert I R hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi]
    have hw:=weight_nonneg I
    have hs:0≤∑J∈R,weight J:=Finset.sum_nonneg (fun J _=>weight_nonneg J)
    nlinarith

lemma deletion_le_euler (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I) :
    (∏I∈R,(1+weight I))≤∏I∈R,localMass I := by
  apply Finset.prod_le_prod₀ (fun I hi=>by linarith [weight_nonneg I])
  intro I hi
  apply (le_div_iff₀ (sub_pos.mpr (prime_weight_lt_one I (hR I hi)))).mpr
  have h:=weight_nonneg I
  nlinarith

lemma euler_ge_one (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I) :
    1≤∏I∈R,localMass I :=
  (show 1≤∏I∈R,(1+weight I) by
    linarith [Finset.sum_nonneg (s:=R) (fun I _=>weight_nonneg I),one_add_sum_weight R]).trans
    (deletion_le_euler R hR)

lemma one_add_slotMass (R pool : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (hp : ∀I∈pool,Prime I) (β : Ideal O→ℂ) (P b M : ℝ) (hP : 0<P) (hM : 0≤M)
    (hβ : ∀I∈pool,‖β I‖≤M) (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤b*P) :
    1+slotMass R pool β P≤max 1 (Real.sqrt (max 1 b)*M)*(∏I∈R,localMass I) := by
  have ha:=slotMass_bound R pool hp β P b M hP hM hβ hs
  have hb:1+∑I∈R,weight I≤∏I∈R,localMass I:=
    (one_add_sum_weight R).trans (deletion_le_euler R hR)
  have hc:=le_max_left 1 (Real.sqrt (max 1 b)*M)
  have hd:=le_max_right 1 (Real.sqrt (max 1 b)*M)
  have he:0≤∑I∈R,weight I:=Finset.sum_nonneg (fun I _=>weight_nonneg I)
  nlinarith

def coefficientMajorant (R D₁ D₂ : Finset (Ideal O)) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) : ℝ :=
  weight (∏I∈D₁,I)*weight (∏I∈D₂,I)*∏i∈J,slotMass R (pool i) (β i) (P i)

omit [DecidableEq α] in
lemma signedCoefficient_norm (χ : Character) (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆R) (hD₂ : D₂⊆R) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) :
    ‖signedCoefficient χ R D₁ D₂ J pool β P‖≤coefficientMajorant R D₁ D₂ J pool β P := by
  simp only [signedCoefficient,norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one,norm_prod]
  apply mul_le_mul
  · exact mul_le_mul (plainCoefficient_norm χ D₁ (fun I hi=>hR I (hD₁ hi)))
      (plainCoefficient_norm χ D₂ (fun I hi=>hR I (hD₂ hi))) (norm_nonneg _) (weight_nonneg _)
  · exact Finset.prod_le_prod₀ (fun i _=>norm_nonneg _) (fun i _=>naturalSlot_norm χ R (pool i) (β i) (P i))
  · positivity
  · exact mul_nonneg (weight_nonneg _) (weight_nonneg _)

omit [DecidableEq α] in
lemma majorant_mass (R : Finset (Ideal O)) (F : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) :
    (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
      coefficientMajorant R D₁ D₂ J pool β P)=
      (∏I∈R,(1+weight I))^2*(∏i∈F,(1+slotMass R (pool i) (β i) (P i))) := by
  simp only [coefficientMajorant,←Finset.mul_sum]
  rw [←Finset.prod_one_add]
  simp only [←Finset.sum_mul]
  rw [←Finset.sum_mul_sum,deletion_mass]
  ring

def uniformMajorant (R D₁ D₂ : Finset (Ideal O)) (J : Finset α) (b M : α→ℝ) : ℝ :=
  weight (∏I∈D₁,I)*weight (∏I∈D₂,I)*
    ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)

omit [DecidableEq α] in
lemma uniformMajorant_nonneg (R D₁ D₂ : Finset (Ideal O)) (J : Finset α)
    (b M : α→ℝ) (hM : ∀i∈J,0≤M i) :
    0≤uniformMajorant R D₁ D₂ J b M := by
  apply mul_nonneg (mul_nonneg (weight_nonneg _) (weight_nonneg _))
  exact Finset.prod_nonneg (fun i hi=>mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
    (Finset.sum_nonneg (fun I _=>weight_nonneg I)))

omit [DecidableEq α] in
lemma signedCoefficient_uniform (χ : Character) (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆R) (hD₂ : D₂⊆R) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P b M : α→ℝ)
    (hp : ∀i∈J,∀I∈pool i,Prime I) (hP : ∀i∈J,0<P i) (hM : ∀i∈J,0≤M i)
    (hβ : ∀i∈J,∀I∈pool i,‖β i I‖≤M i)
    (hs : ∀i∈J,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i) :
    ‖signedCoefficient χ R D₁ D₂ J pool β P‖≤uniformMajorant R D₁ D₂ J b M := by
  apply (signedCoefficient_norm χ R hR D₁ D₂ hD₁ hD₂ J pool β P).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (weight_nonneg _) (weight_nonneg _))
  exact Finset.prod_le_prod₀ (fun i _=>slotMass_nonneg _ _ _ _)
    (fun i hi=>slotMass_bound R (pool i) (hp i hi) (β i) (P i) (b i) (M i)
      (hP i hi) (hM i hi) (hβ i hi) (hs i hi))

omit [DecidableEq α] in
lemma uniformMajorant_mass (R : Finset (Ideal O)) (F : Finset α) (b M : α→ℝ) :
    (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,uniformMajorant R D₁ D₂ J b M)=
      (∏I∈R,(1+weight I))^2*
        ∏i∈F,(1+(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)) := by
  simp only [uniformMajorant,←Finset.mul_sum]
  rw [←Finset.prod_one_add]
  simp only [←Finset.sum_mul]
  rw [←Finset.sum_mul_sum,deletion_mass]
  ring

omit [DecidableEq α] in
lemma uniformMajorant_mass_le (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (F : Finset α) (b M : α→ℝ) (hM : ∀i∈F,0≤M i) :
    (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,uniformMajorant R D₁ D₂ J b M)≤
      (∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)) * (∏I∈R,localMass I)^(2+F.card) := by
  rw [uniformMajorant_mass]
  have hE:=euler_ge_one R hR
  have hp (i : α) (hi : i∈F) :
      1+(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)≤
        max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I) := by
    have ha:1+∑I∈R,weight I≤∏I∈R,localMass I:=(one_add_sum_weight R).trans (deletion_le_euler R hR)
    have hb:=le_max_left 1 (Real.sqrt (max 1 (b i))*M i)
    have hc:=le_max_right 1 (Real.sqrt (max 1 (b i))*M i)
    have hs:0≤∑I∈R,weight I:=Finset.sum_nonneg (fun I _=>weight_nonneg I)
    nlinarith
  calc
    _≤(∏I∈R,localMass I)^2*
        ∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (Finset.prod_nonneg (fun I _=>by linarith [weight_nonneg I]))
          (deletion_le_euler R hR) 2
      · exact Finset.prod_le_prod₀ (fun i hi=>add_nonneg zero_le_one
          (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
            (Finset.sum_nonneg (fun I _=>weight_nonneg I)))) hp
      · exact Finset.prod_nonneg (fun i hi=>add_nonneg zero_le_one
          (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
            (Finset.sum_nonneg (fun I _=>weight_nonneg I))))
      · exact sq_nonneg _
    _=_ := by rw [Finset.prod_mul_distrib,Finset.prod_const,pow_add];ring

omit [DecidableEq α] in

theorem uniform_mass_subpower (F : Finset α) (b M : α→ℝ) (hM : ∀i∈F,0≤M i)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (R : Finset (Ideal O)) (_hR : ∀I∈R,Prime I),
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,uniformMajorant R D₁ D₂ J b M)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
  let n:ℕ:=2+F.card
  have hn:(0:ℝ)<n:=by dsimp [n];positivity
  let δ:ℝ:=ε/n
  have hδ:0<δ:=div_pos hε hn
  obtain ⟨C₀,hC₀,hbound⟩:=euler_mass_subpower δ hδ
  let A:ℝ:=∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)
  have hA:0<A:=Finset.prod_pos (fun i _=>lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨A*C₀^n,mul_pos hA (pow_pos hC₀ n),?_⟩
  intro R hR
  have he:0≤∏I∈R,localMass I:=(euler_ge_one R hR).trans' zero_le_one
  have hr:0≤(Ideal.absNorm (∏I∈R,I):ℝ):=Nat.cast_nonneg _
  have hpow:((Ideal.absNorm (∏I∈R,I):ℝ)^δ)^n=(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr]
    congr 1
    dsimp [δ]
    exact div_mul_cancel₀ _ hn.ne'
  calc
    _≤A*(∏I∈R,localMass I)^n:=uniformMajorant_mass_le R hR F b M hM
    _≤A*(C₀*(Ideal.absNorm (∏I∈R,I):ℝ)^δ)^n:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he (hbound R hR) n) hA.le
    _=_:=by rw [mul_pow,hpow];ring

omit [DecidableEq α] in

theorem signed_mass_subpower (F : Finset α) (b M : α→ℝ) (hM : ∀i∈F,0≤M i)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (R : Finset (Ideal O)) (_hR : ∀I∈R,Prime I)
      (χ : Character) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ),
      (∀i∈F,∀I∈pool i,Prime I) → (∀i∈F,0<P i) →
      (∀i∈F,∀I∈pool i,‖β i I‖≤M i) →
      (∀i∈F,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i) →
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        ‖signedCoefficient χ R D₁ D₂ J pool β P‖)≤C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩:=uniform_mass_subpower F b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro R hR χ pool β P hp hP hβ hs
  apply le_trans _ (hbound R hR)
  apply Finset.sum_le_sum
  intro D₁ hD₁
  apply Finset.sum_le_sum
  intro D₂ hD₂
  apply Finset.sum_le_sum
  intro J hJ
  have hj:=Finset.mem_powerset.mp hJ
  exact signedCoefficient_uniform χ R hR D₁ D₂ (Finset.mem_powerset.mp hD₁)
    (Finset.mem_powerset.mp hD₂) J pool β P b M
    (fun i hi=>hp i (hj hi)) (fun i hi=>hP i (hj hi)) (fun i hi=>hM i (hj hi))
    (fun i hi=>hβ i (hj hi)) (fun i hi=>hs i (hj hi))

lemma profile_bounds (pool : Finset (Ideal O)) (ν : Ideal O→ℂ) (W : ℝ→ℂ)
    (P b M : ℝ) (hP : 0<P) (hν : ∀I∈pool,‖ν I‖≤1)
    (hW : ∀x,‖W x‖≤M) (hs : Function.support W⊆Set.Iic b) :
    (∀I∈pool,‖ν I*W ((I.absNorm:ℝ)/P)‖≤M) ∧
      (∀I∈pool,ν I*W ((I.absNorm:ℝ)/P)≠0 → (I.absNorm:ℝ)≤b*P) := by
  constructor
  · intro I hi
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hν I hi)).trans (hW _)
  · intro I hi hn
    exact (div_le_iff₀ hP).mp (hs (right_ne_zero_of_mul hn))

omit [DecidableEq α] in

theorem profile_signed_mass_subpower (F : Finset α) (b M : α→ℝ)
    (hM : ∀i∈F,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (R : Finset (Ideal O)) (_hR : ∀I∈R,Prime I)
      (χ : Character) (pool : α→Finset (Ideal O)) (ν : α→Ideal O→ℂ)
      (W : α→ℝ→ℂ) (P : α→ℝ),
      (∀i∈F,∀I∈pool i,Prime I) → (∀i∈F,0<P i) →
      (∀i∈F,∀I∈pool i,‖ν i I‖≤1) → (∀i∈F,∀x,‖W i x‖≤M i) →
      (∀i∈F,Function.support (W i)⊆Set.Iic (b i)) →
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        ‖signedCoefficient χ R D₁ D₂ J pool
          (fun i I=>ν i I*W i ((I.absNorm:ℝ)/P i)) P‖)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩:=signed_mass_subpower F b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro R hR χ pool ν W P hp hP hν hW hs
  exact hbound R hR χ pool (fun i I=>ν i I*W i ((I.absNorm:ℝ)/P i)) P hp hP
    (fun i hi=>(profile_bounds (pool i) (ν i) (W i) (P i) (b i) (M i)
      (hP i hi) (hν i hi) (hW i hi) (hs i hi)).1)
    (fun i hi=>(profile_bounds (pool i) (ν i) (W i) (P i) (b i) (M i)
      (hP i hi) (hν i hi) (hW i hi) (hs i hi)).2)

end SevenEighths.CenteredMomentCommonMaskExpansion

end

end OAI
