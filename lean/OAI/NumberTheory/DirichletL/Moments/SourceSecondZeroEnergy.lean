import OAI.NumberTheory.DirichletL.Moments.SecondDiagonal
import OAI.NumberTheory.DirichletL.Moments.SourceZeroEnergy
import OAI.NumberTheory.DirichletL.Moments.HeckeColumnWindow

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSourceSecondZeroEnergy
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondDiagonal
local notation "O" => ActualEisensteinCubic.O

def sourceSecondZero (S : Finset (Ideal O)) (β : Ideal O→ℂ) (η : Character) (t : ℝ) : ℂ :=
  secondZeroEnergy Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
    (fun I => β I*heightCoeff η t I)

lemma heightCoeff_norm_le_one (η : Character) (t : ℝ) (I : Ideal O) (hI : I≠0) :
    ‖heightCoeff η t I‖≤1 := by
  have hn : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp : ‖(Ideal.absNorm I:ℂ)^(Complex.I*t)‖=1 := by
    rw [show (Ideal.absNorm I:ℂ)=((Ideal.absNorm I:ℝ):ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp
  rw [heightCoeff,norm_mul,hp,mul_one]
  exact idealCoeff_norm_le_one η I

theorem secondZeroEnergy_filter {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (p : α→Prop) [DecidablePred p] (hc : ∀ i∈S,¬p i→c i=0) :
    secondZeroEnergy S a ha c=secondZeroEnergy (S.filter p) a ha c := by
  unfold secondZeroEnergy
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hpi : p i
  · rw [ite_eq_left hpi]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hpj : p j
    · rw [ite_eq_left hpj]
    · simp only [ite_eq_right hpj,hc j hj hpj,star_zero,mul_zero,zero_mul]
  · simp only [ite_eq_right hpi,hc i hi hpi,zero_mul,Finset.sum_const_zero]

lemma sourceGenerator_span (S : Finset (Ideal O)) (I : supportedColumns S) :
    Ideal.span {sourceGenerator S I}=(I:Ideal O) :=
  primary_span_supported I (Finset.mem_filter.mp I.property).2
lemma sourceGenerator_primary (S : Finset (Ideal O)) (I : supportedColumns S) :
    ConcretePrimeRowBridge.goodLambda^2∣sourceGenerator S I-1 :=
  (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I (Finset.mem_filter.mp I.property).2)).2
lemma sourceGenerator_injective (S : Finset (Ideal O)) : Function.Injective (sourceGenerator S) := by
  intro I J h
  apply Subtype.ext
  rw [←sourceGenerator_span S I,←sourceGenerator_span S J,h]

theorem sourceSecondZero_divisor_bound (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (η : Character) (t B Y : ℝ) (hB : 0≤B) (hY : 0≤Y)
    (s : Ideal O) (hs : s≠0)
    (hc : ∀ I∈supportedColumns S,β I≠0→‖β I‖≤B)
    (hdiv : ∀ I∈supportedColumns S,β I≠0→s∣I)
    (hN : ∀ I∈supportedColumns S,β I≠0→(Ideal.absNorm I:ℝ)≤Y) :
    ‖sourceSecondZero S β η t‖≤128*B^2*Y/(Ideal.absNorm s:ℝ) := by
  let Q : Finset (supportedColumns S) := Finset.univ.filter (fun I => β I≠0)
  rw [sourceSecondZero,secondZeroEnergy_filter Finset.univ (sourceGenerator S)
    (sourceGenerator_supported S) (fun I => β I*heightCoeff η t I) (fun I => β I≠0)
      (by intro I _ h; simp only [not_not] at h; rw [h,zero_mul])]
  refine secondZeroEnergy_divisor_bound Q (sourceGenerator S) (sourceGenerator_supported S)
    (sourceGenerator_primary S) (sourceGenerator_injective S).injOn _ B hB ?_ s hs ?_ Y hY ?_
  · intro I hI
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (heightCoeff_norm_le_one η t I
      (Finset.mem_filter.mp I.property).2.1) (norm_nonneg _)).trans
      (by simpa only [mul_one] using hc I I.property (Finset.mem_filter.mp hI).2)
  · intro I hI
    rw [sourceGenerator_span]
    exact hdiv I I.property (Finset.mem_filter.mp hI).2
  · intro I hI
    rw [sourceGenerator_span]
    exact hN I I.property (Finset.mem_filter.mp hI).2

theorem sourceSecondZero_eq_zero_of_subunit (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (η : Character) (t Y : ℝ) (hY : Y<1)
    (hN : ∀ I∈supportedColumns S,β I≠0→(Ideal.absNorm I:ℝ)≤Y) :
    sourceSecondZero S β η t=0 := by
  have hc (I : supportedColumns S) : β I=0 := by
    by_contra hn
    have hi : (1:ℝ)≤Ideal.absNorm (I:Ideal O) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.mem_filter.mp I.property).2.1)
    linarith [hN I I.property hn]
  simp only [sourceSecondZero,secondZeroEnergy,hc,zero_mul,star_zero,mul_zero,Finset.sum_const_zero]

theorem tuple_second_zero_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (η : Character) (t B Y : ℝ),
      0≤B → 1≤Y → (∀ v∈S,finiteTupleProduct v≠0→‖β v‖≤B) →
      ∀ (s : Ideal O),s≠0 →
      (∀ v∈S,β v≠0→s∣finiteTupleProduct v) →
      (∀ v∈S,β v≠0→(Ideal.absNorm (finiteTupleProduct v):ℝ)≤Y) →
      ‖sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t‖≤
        C*B^2*Y^(1+ε)/(Ideal.absNorm s:ℝ) := by
  let δ := ε/(2*(N+2:ℕ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδn : δ*(N+2:ℕ)=ε/2 := by dsimp [δ]; push_cast; field_simp
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨128*((1+D)^(N+2))^2,by positivity,?_⟩
  intro ι _ hi S β η t B Y hB hY hβ s hs hdiv hN
  let c := finiteColumnCoefficient S β
  have hY0 : 0<Y := zero_lt_one.trans_le hY
  have hbound (I : Ideal O) (hI : I∈supportedColumns (finiteColumns S)) (hn : c I≠0) :
      (Ideal.absNorm I:ℝ)≤Y := by
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv hv0
  have hbase : 1≤(1+D)*Y^δ := by
    have hp := Real.one_le_rpow hY hδ.le
    nlinarith
  have hcoeff (I : Ideal O) (hI : I∈supportedColumns (finiteColumns S)) (hn : c I≠0) :
      ‖c I‖≤B*((1+D)^(N+2)*Y^(ε/2)) := by
    have hI0 := (Finset.mem_filter.mp hI).2.1
    have hdI : ((IdealMobiusDivisorSum.idealDivisors I).card:ℝ)≤(1+D)*Y^δ :=
      (hd I hI0).trans (mul_le_mul (by linarith)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hbound I hI hn) hδ.le) (by positivity) (by positivity))
    have hp : ((1+D)*Y^δ)^(N+2)=(1+D)^(N+2)*Y^(ε/2) := by
      rw [mul_pow,←Real.rpow_mul_natCast hY0.le,hδn]
    calc
      _ ≤ B*((IdealMobiusDivisorSum.idealDivisors I).card:ℝ)^(Fintype.card ι+2) :=
        finiteColumnCoefficient_norm_le S β B hB hβ I hI0
      _ ≤ B*((1+D)*Y^δ)^(Fintype.card ι+2) := by gcongr
      _ ≤ B*((1+D)*Y^δ)^(N+2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by omega)) hB
      _ = _ := by rw [hp]
  have hb := sourceSecondZero_divisor_bound (finiteColumns S) c η t
    (B*((1+D)^(N+2)*Y^(ε/2))) Y (by positivity) hY0.le s hs hcoeff
    (by
      intro I hI hn
      obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
      rw [←he]
      exact hdiv v hv hv0) hbound
  apply hb.trans_eq
  have hp : (Y^(ε/2))^2*Y=Y^(1+ε) := by
    rw [←Real.rpow_mul_natCast hY0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show ε/2*(2:ℝ)=ε by ring,Real.rpow_add hY0,Real.rpow_one]
    ring
  calc
    _ = (128*((1+D)^(N+2))^2)*B^2*((Y^(ε/2))^2*Y)/(Ideal.absNorm s:ℝ) := by ring
    _ = _ := by rw [hp]

theorem normalized_tuple_second_zero_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (η : Character) (t B L T : ℝ),
      0≤B → 0<L → 0<T → (∀ v∈S,finiteTupleProduct v≠0→‖β v‖≤B) →
      ∀ (s : Ideal O),s≠0 →
      (∀ v∈S,β v≠0→s∣finiteTupleProduct v) →
      (∀ v∈S,β v≠0→(Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*T) →
      (L*T<1 → sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t=0) ∧
      ∀ κ : ℂ,‖(κ/(T:ℂ))*sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t‖≤
        C*‖κ‖*B^2*L^(1+ε)*T^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := tuple_second_zero_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi S β η t B L T hB hL hT hβ s hs hdiv hN
  have hz (hsmall : L*T<1) : sourceSecondZero (finiteColumns S) (finiteColumnCoefficient S β) η t=0 := by
    apply sourceSecondZero_eq_zero_of_subunit _ _ η t (L*T) hsmall
    intro I hI hn
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv hv0
  refine ⟨hz,?_⟩
  intro κ
  by_cases hsmall : L*T<1
  · rw [hz hsmall,mul_zero,norm_zero]
    positivity
  have hb := hbound hi S β η t B (L*T) hB (le_of_not_gt hsmall) hβ s hs hdiv hN
  rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
  apply (mul_le_mul_of_nonneg_left hb (div_nonneg (norm_nonneg _) hT.le)).trans_eq
  rw [Real.mul_rpow hL.le hT.le,Real.rpow_add hT,Real.rpow_one]
  field_simp

lemma profileCoefficient_dvd {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι)
    (hv : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    s∣finiteTupleProduct v := by
  by_contra h
  exact hv (by simp only [profileCoefficient,ite_eq_right h,mul_zero])

theorem profile_second_zero_energy (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : ι→Ideal O→ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (Wslot : ι→ℝ→ℂ) (P D b : ι→ℝ)
      (W₁ W₂ : ℝ→ℂ) (D₁ D₂ b₁ b₂ : ℝ),
      (∀ j,0≤D j) → 0≤D₁ → 0≤D₂ → (∀ j,0≤b j) → 0≤b₁ → 0≤b₂ →
      (∀ j x,‖Wslot j x‖≤D j) → (∀ x,‖W₁ x‖≤D₁) → (∀ x,‖W₂ x‖≤D₂) →
      (∀ j,Wslot j 0=0) → W₁ 0=0 → W₂ 0=0 →
      (∀ j x,Wslot j x≠0→x≤b j) → (∀ x,W₁ x≠0→x≤b₁) → (∀ x,W₂ x≠0→x≤b₂) →
      ∀ (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)
      let L := (∏ j,b j)*b₁*b₂
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (L*Traw<1 → E=0) ∧ ∀ κ : ℂ,
        ‖(κ/(Traw:ℂ))*E‖≤C*‖κ‖*(2*D₁*D₂*(∏ j,D j))^2*(1+L)^(1+ε)*Traw^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := normalized_tuple_second_zero_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η t R ν hν Wslot P D b W₁ W₂ D₁ D₂ b₁ b₂
    hD hD₁ hD₂ hb hb₁ hb₂ hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S Traw L E
  let β := profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hβ (v : Tuple ι) : ‖β v‖≤2*D₁*D₂*(∏ j,D j) :=
    profileCoefficient_norm_le R ν hν Wslot P D W₁ W₂ D₁ D₂ hD hD₁ hD₂
      hslot h₁ h₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hn₁ : (0:ℝ)<Ideal.absNorm B₁ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hn₂ : (0:ℝ)<Ideal.absNorm B₂ := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  have hraw : 0<Traw := mul_pos (div_pos hT (mul_pos hn₁ hn₂)) (Finset.prod_pos (fun j _=>hP j))
  have hL : 0≤L := mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun j _=>hb j)) hb₁) hb₂
  have hN (v : Tuple ι) (hv : β v≠0) : (Ideal.absNorm (finiteTupleProduct v):ℝ)≤L*Traw := by
    have hh := profileCoefficient_product_bound R ν Wslot P b W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
      hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hz hz₁ hz₂ hs hs₁ hs₂ v hv
    exact hh.2.trans_eq (by dsimp only [L,Traw];ring)
  refine ⟨?_,?_⟩
  · intro hsmall
    apply sourceSecondZero_eq_zero_of_subunit _ _ η t (L*Traw) hsmall
    intro I hI hn
    obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
    rw [←he]
    exact hN v hv0
  · exact (hbound hi S β η t (2*D₁*D₂*(∏ j,D j)) (1+L) Traw
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD₁) hD₂) (Finset.prod_nonneg (fun j _=>hD j)))
      (by linarith) hraw (fun v _ _=>hβ v) s hsz
      (fun v _ hv=>profileCoefficient_dvd R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v hv)
      (fun v _ hv=>(hN v hv).trans (mul_le_mul_of_nonneg_right (by linarith : L≤1+L) hraw.le))).2

theorem bounded_profile_second_zero_energy (N : ℕ) (ε : ℝ) (hε : 0<ε)
    (D b : ℝ) (hD : 0≤D) (hb : 0≤b) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : ι→Ideal O→ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ),
      (∀ j x,‖Wslot j x‖≤D) → (∀ x,‖W₁ x‖≤D) → (∀ x,‖W₂ x‖≤D) →
      (∀ j,Wslot j 0=0) → W₁ 0=0 → W₂ 0=0 →
      (∀ j x,Wslot j x≠0→x≤b) → (∀ x,W₁ x≠0→x≤b) → (∀ x,W₂ x≠0→x≤b) →
      ∀ (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j)
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (b^(Fintype.card ι+2)*Traw<1 → E=0) ∧ ∀ κ : ℂ,
        ‖(κ/(Traw:ℂ))*E‖≤C*‖κ‖*Traw^ε/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C₀,hC₀,hmain⟩ := profile_second_zero_energy N ε hε
  let B := 2*D*D*(1+D)^N
  let L := (1+b)^(N+2)
  let C := C₀*(1+B^2)*(1+L)^(1+ε)
  have hB : 0≤B := by dsimp [B];positivity
  have hL : 0≤L := by dsimp [L];positivity
  have hC : 0<C := mul_pos (mul_pos hC₀ (by positivity)) (Real.rpow_pos_of_pos (by linarith) _)
  refine ⟨C,hC,?_⟩
  intro ι _ hi η t R ν hν Wslot P W₁ W₂ hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S Traw E
  have hTpos : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hraw0 : 0≤Traw := mul_nonneg (div_nonneg hTpos.le (by positivity))
    (Finset.prod_nonneg (fun j _=>(hP j).le))
  have hh := hmain hi η t R ν hν Wslot P (fun _=>D) (fun _=>b) W₁ W₂ D D b b
    (fun _=>hD) hD hD (fun _=>hb) hb hb hslot h₁ h₂ hz hz₁ hz₂ hs hs₁ hs₂
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S
  dsimp only at hh
  simp only [Finset.prod_const,Finset.card_univ] at hh
  have heL : b^Fintype.card ι*b*b=b^(Fintype.card ι+2) := by
    rw [pow_add,pow_two];ring
  rw [heL] at hh
  refine ⟨hh.1,?_⟩
  intro κ
  have hBbound : 2*D*D*D^Fintype.card ι≤B := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (pow_le_pow_left₀ hD (by linarith) _).trans (pow_le_pow_right₀ (by linarith) hi)
  have hLbound : b^(Fintype.card ι+2)≤L :=
    (pow_le_pow_left₀ hb (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
  have hpow : (1+b^(Fintype.card ι+2))^(1+ε)≤(1+L)^(1+ε) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hcoef : C₀*(2*D*D*D^Fintype.card ι)^2*(1+b^(Fintype.card ι+2))^(1+ε)≤C := by
    dsimp only [C]
    apply mul_le_mul _ hpow (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_left _ hC₀.le
    exact (pow_le_pow_left₀ (by positivity) hBbound 2).trans (by linarith)
  apply (hh.2 κ).trans
  calc
    _ = (C₀*(2*D*D*D^Fintype.card ι)^2*(1+b^(Fintype.card ι+2))^(1+ε))*
        (‖κ‖*Traw^ε/(Ideal.absNorm s:ℝ)) := by ring
    _ ≤ C*(‖κ‖*Traw^ε/(Ideal.absNorm s:ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by ring

theorem smooth_subset_source_second_zero_energy {α : Type*} (F : Finset α)
    (Wslot : α→ℝ→ℂ) (W₁ W₂ : ℝ→ℂ) (a b : α→ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (t : ℝ) (R : Ideal O) (ν : α→Ideal O→ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) → ∀ (P : α→ℝ)
      (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 → s≠0 →
      X₁*X₂=T → Y₁*Y₂=T →
      ∀ (pools : (J⊕Fin 2)→Finset (Ideal O)) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ),
      let S := Fintype.piFinset pools
      let Traw := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let Y := (∏ j∈J,b j)*b₁*b₂*Traw
      let E := sourceSecondZero (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J=>ν j.val)
          (fun j : J=>Wslot j.val) (fun j : J=>P j.val) W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) η t
      (Y<1 → E=0) ∧
        ‖(((K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier Φ 0)/(Traw:ℂ))*E‖≤
          C*‖(K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier Φ 0‖*Traw^ε/(Ideal.absNorm s:ℝ) := by
  choose D hD hDb hz hsb using fun j : F => smooth_annular_bound
    (Wslot j.val) (a j.val) (b j.val) (ha j.val j.property)
    (hsSlot j.val j.property) (hWslot j.val j.property)
  obtain ⟨D₁,hD₁,hDb₁,hz₁,hsb₁⟩ := smooth_annular_bound W₁ a₁ b₁ ha₁ hs₁ hW₁
  obtain ⟨D₂,hD₂,hDb₂,hz₂,hsb₂⟩ := smooth_annular_bound W₂ a₂ b₂ ha₂ hs₂ hW₂
  let Dmax := 1+D₁+D₂+∑ j : F,D j
  let bmax := 1+b₁+b₂+∑ j : F,b j.val
  have hDs : 0≤∑ j : F,D j := Finset.sum_nonneg (fun j _=>hD j)
  have hbs : 0≤∑ j : F,b j.val := Finset.sum_nonneg (fun j _=>hb j.val j.property)
  have hDmax : 0≤Dmax := by dsimp only [Dmax];linarith
  have hbmax : 0≤bmax := by dsimp only [bmax];linarith
  have hD₁max : D₁≤Dmax := by dsimp only [Dmax];linarith
  have hD₂max : D₂≤Dmax := by dsimp only [Dmax];linarith
  have hb₁max : b₁≤bmax := by dsimp only [bmax];linarith
  have hb₂max : b₂≤bmax := by dsimp only [bmax];linarith
  have hDj (j : F) : D j≤Dmax := by
    have h := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset F))=>hD k) (Finset.mem_univ j)
    dsimp only [Dmax]
    linarith
  have hbj (j : F) : b j.val≤bmax := by
    have h := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset F))=>hb k.val k.property) (Finset.mem_univ j)
    dsimp only [bmax]
    linarith
  obtain ⟨C,hC,hbound⟩ := bounded_profile_second_zero_energy F.card ε hε Dmax bmax hDmax hbmax
  refine ⟨C,hC,?_⟩
  intro J hJ η t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY pools Φ K S Traw Y E
  let β := profileCoefficient R (fun j : J=>ν j.val) (fun j : J=>Wslot j.val) (fun j : J=>P j.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s
  have hcard : Fintype.card J≤F.card := by simpa only [Fintype.card_coe] using Finset.card_le_card hJ
  have hh := hbound hcard η t R (fun j : J=>ν j.val) (fun j I=>hν j.val j.property I)
    (fun j : J=>Wslot j.val) (fun j : J=>P j.val) W₁ W₂
    (fun j x=>(hDb ⟨j.val,hJ j.property⟩ x).trans (hDj ⟨j.val,hJ j.property⟩))
    (fun x=>(hDb₁ x).trans hD₁max) (fun x=>(hDb₂ x).trans hD₂max)
    (fun j=>hz ⟨j.val,hJ j.property⟩) hz₁ hz₂
    (fun j x hx=>(hsb ⟨j.val,hJ j.property⟩ x hx).trans (hbj ⟨j.val,hJ j.property⟩))
    (fun x hx=>(hsb₁ x hx).trans hb₁max) (fun x hx=>(hsb₂ x hx).trans hb₂max)
    X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j=>hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hsz hX hY S
  dsimp only at hh
  rw [Finset.prod_coe_sort] at hh
  refine ⟨?_,hh.2 ((K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier Φ 0)⟩
  intro hsmall
  apply sourceSecondZero_eq_zero_of_subunit _ _ η t Y hsmall
  intro I hI hn
  obtain ⟨v,hv,hv0,he⟩ := finiteColumnCoefficient_witness S β I hn
  have hN := profileCoefficient_product_bound R (fun j : J=>ν j.val)
    (fun j : J=>Wslot j.val) (fun j : J=>P j.val) (fun j : J=>b j.val)
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s (fun j=>hP j.val j.property)
    hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY (fun j=>hz ⟨j.val,hJ j.property⟩) hz₁ hz₂
    (fun j=>hsb ⟨j.val,hJ j.property⟩) hsb₁ hsb₂ v hv0
  rw [←he]
  exact hN.2.trans_eq (by rw [Finset.prod_coe_sort,Finset.prod_coe_sort];dsimp only [Y,Traw];ring)

end SevenEighths.CenteredMomentSourceSecondZeroEnergy

end

end OAI
