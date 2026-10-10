import OAI.NumberTheory.DirichletL.Moments.ZeroMeanBridge
import OAI.NumberTheory.DirichletL.Moments.SourceMass

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSupportedZeroEnergy
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentZeroMode
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentFirstLocalization
open CenteredMomentZeroMeanBridge EisensteinSchwartzPoisson HeckeFamily
local notation "O" => ActualEisensteinCubic.O

theorem idealZeroEnergy_filter (S : Finset (Ideal O)) (hS : ∀ I∈S,Supported I)
    (c : Ideal O → ℂ) (K : ℝ) (p : Ideal O → Prop) [DecidablePred p]
    (hc : ∀ I∈S, ¬p I → c I=0) :
    idealZeroEnergy S hS c K =
      idealZeroEnergy (S.filter p) (fun I h => hS I (Finset.mem_filter.mp h).1) c K := by
  let e : S.filter p → S := fun I => ⟨I.val,(Finset.mem_filter.mp I.property).1⟩
  let ep : (S.filter p) × (S.filter p) → S × S := fun q => (e q.1,e q.2)
  have he : Function.Injective e := by
    intro I J h
    apply Subtype.ext
    exact congrArg (fun x : S => x.val) h
  have hep : Function.Injective ep := by
    intro q r h
    exact Prod.ext (he (congrArg Prod.fst h)) (he (congrArg Prod.snd h))
  let f : S × S → ℂ := fun q => (c q.1.val * star (c q.2.val)) *
    (((K / ‖eisEmbedding (idealColumn S q.1 * idealColumn S q.2)‖^2 : ℝ) : ℂ) *
      CenteredMomentRowNorm.pairFourier (idealColumn S q.1) (idealColumn S q.2)
        (idealColumn_supported S hS q.1) (idealColumn_supported S hS q.2) 0)
  have hs : Function.support f ⊆ Set.range ep := by
    intro q hq
    have hi : p q.1.val := by
      by_contra hn
      exact hq (by simp only [f,hc q.1.val q.1.property hn,zero_mul])
    have hj : p q.2.val := by
      by_contra hn
      exact hq (by simp only [f,hc q.2.val q.2.property hn,star_zero,mul_zero,zero_mul])
    exact ⟨(⟨q.1.val,Finset.mem_filter.mpr ⟨q.1.property,hi⟩⟩,
      ⟨q.2.val,Finset.mem_filter.mpr ⟨q.2.property,hj⟩⟩),rfl⟩
  have ht := hep.tsum_eq hs
  simpa only [tsum_fintype,Fintype.sum_prod_type,f,ep,e,idealZeroEnergy,idealColumn] using ht.symm

def activeColumns (S : Finset (Ideal O)) (c : Ideal O → ℂ) : Finset (Ideal O) :=
  (supportedColumns S).filter (fun I => c I≠0)

lemma activeColumns_supported (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (I : Ideal O) (hI : I∈activeColumns S c) : Supported I :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2

theorem zeroEnergy_eq_active_original (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K =
      idealZeroEnergy (activeColumns S c) (activeColumns_supported S c)
        (fun I => c I*rowWeight η m A 1 t I) K * paperRadialFourier W 0 := by
  rw [zeroEnergy_eq_original]
  congr 1
  exact idealZeroEnergy_filter (supportedColumns S) (fun I h => (Finset.mem_filter.mp h).2)
    (fun I => c I*rowWeight η m A 1 t I) K (fun I => c I≠0)
    (fun I _ h => by simp only [not_not] at h; rw [h,zero_mul])

theorem zeroEnergy_eq_active (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K = zeroEnergy η m A t (activeColumns S c) c W K := by
  rw [zeroEnergy_eq_active_original,zeroEnergy_eq_original]
  have he : supportedColumns (activeColumns S c)=activeColumns S c :=
    Finset.filter_eq_self.mpr (activeColumns_supported S c)
  simp only [he]

theorem finiteColumnCoefficient_witness {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (I : Ideal O)
    (hI : finiteColumnCoefficient S β I≠0) :
    ∃ v∈S, β v≠0 ∧ finiteTupleProduct v=I := by
  obtain ⟨v,hv,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hI
  exact ⟨v,(Finset.mem_filter.mp hv).1,hne,(Finset.mem_filter.mp hv).2⟩

theorem finite_tuple_fiber_card {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (I : Ideal O) (hI : I≠0) :
    (S.filter (fun v => finiteTupleProduct v=I)).card ≤
      (idealDivisors I).card^(Fintype.card ι+2) := by
  let T := S.filter (fun v => finiteTupleProduct v=I)
  let f (v : T) : (ι ⊕ Fin 2) → idealDivisors I := fun i => ⟨v.val i,by
    apply (mem_idealDivisors hI).mpr
    rw [← (Finset.mem_filter.mp v.property).2]
    exact Finset.dvd_prod_of_mem v.val (Finset.mem_univ i)⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_sum,Fintype.card_fin,T]
    using Fintype.card_le_of_injective f hf

theorem finiteColumnCoefficient_norm_le {ι : Type*} [Fintype ι]
    (S : Finset (Tuple ι)) (β : Tuple ι → ℂ) (B : ℝ) (hB : 0≤B)
    (hβ : ∀ v∈S, finiteTupleProduct v≠0 → ‖β v‖≤B) (I : Ideal O) (hI : I≠0) :
    ‖finiteColumnCoefficient S β I‖ ≤ B*((idealDivisors I).card:ℝ)^(Fintype.card ι+2) := by
  calc
    _ ≤ ∑ v∈S.filter (fun v => finiteTupleProduct v=I),‖β v‖ := norm_sum_le _ _
    _ ≤ ∑ _v∈S.filter (fun v => finiteTupleProduct v=I),B := by
      apply Finset.sum_le_sum
      intro v hv
      exact hβ v (Finset.mem_filter.mp hv).1 ((Finset.mem_filter.mp hv).2 ▸ hI)
    _ = B*((S.filter (fun v => finiteTupleProduct v=I)).card:ℝ) := by simp; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact_mod_cast finite_tuple_fiber_card S I hI

theorem active_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤X → 0≤K → 0≤B →
      (∀ v∈S,finiteTupleProduct v≠0 → ‖β v‖≤B) →
      (∀ I∈supportedColumns (finiteColumns S),finiteColumnCoefficient S β I≠0 →
        (Ideal.absNorm I:ℝ)≤X) →
      ‖zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^(1+ε) := by
  let δ := ε/(4*(N+2:ℕ))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hn : (N+2:ℝ)≠0 := by positivity
  have hδn : δ*(N+2:ℕ)=ε/4 := by dsimp [δ]; push_cast; field_simp
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  obtain ⟨C,hC,hc⟩ := ideal_zero_energy_bound (ε/2) (by positivity)
  refine ⟨C*((1+D)^(N+2))^2,by positivity,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  let c := finiteColumnCoefficient S β
  let Q := activeColumns (finiteColumns S) c
  have hQ : ∀ I∈Q,Supported I := activeColumns_supported _ _
  have hX0 : 0<X := zero_lt_one.trans_le hX
  have hNX (I : Ideal O) (hI : I∈Q) : (Ideal.absNorm I:ℝ)≤X :=
    hN I (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hI).2
  have hbase : 1≤(1+D)*X^δ := by
    have hxδ : 1≤X^δ := Real.one_le_rpow hX hδ.le
    nlinarith
  have hcoeff (I : Ideal O) (hI : I∈Q) :
      ‖c I*rowWeight η m A 1 t I‖ ≤ B*((1+D)^(N+2)*X^(ε/4)) := by
    have hI0 := (hQ I hI).1
    have hdI : ((idealDivisors I).card:ℝ) ≤ (1+D)*X^δ := by
      apply (hd I hI0).trans
      apply mul_le_mul (by linarith : D≤1+D)
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hNX I hI) hδ.le) (by positivity) (by positivity)
    have hp : ((1+D)*X^δ)^(N+2) = (1+D)^(N+2)*X^(ε/4) := by
      rw [mul_pow,←Real.rpow_mul_natCast hX0.le,hδn]
    rw [norm_mul]
    calc
      _ ≤ ‖c I‖*1 := mul_le_mul_of_nonneg_left
        (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A 1 t I hI0) (norm_nonneg _)
      _ = ‖c I‖ := mul_one _
      _ ≤ B*((idealDivisors I).card:ℝ)^(Fintype.card ι+2) :=
        finiteColumnCoefficient_norm_le S β B hB hβ I hI0
      _ ≤ B*((1+D)*X^δ)^(Fintype.card ι+2) := by gcongr
      _ ≤ B*((1+D)*X^δ)^(N+2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by omega)) hB
      _ = _ := by rw [hp]
  have hb := hc Q hQ (fun I => c I*rowWeight η m A 1 t I)
    X K (B*((1+D)^(N+2)*X^(ε/4))) hX hK (by positivity) hNX hcoeff
  rw [zeroEnergy_eq_active_original,norm_mul]
  apply (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq
  have hxpow : (X^(ε/4))^2*X^(1+ε/2)=X^(1+ε) := by
    rw [←Real.rpow_mul_natCast hX0.le,←Real.rpow_add hX0]
    congr 1
    ring
  calc
    _ = C*((1+D)^(N+2))^2*K*B^2*‖paperRadialFourier W 0‖*
      ((X^(ε/4))^2*X^(1+ε/2)) := by ring
    _ = _ := by rw [hxpow]

theorem normalized_active_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤X → 0≤K → 0≤B →
      (∀ v∈S,finiteTupleProduct v≠0 → ‖β v‖≤B) →
      (∀ I∈supportedColumns (finiteColumns S),finiteColumnCoefficient S β I≠0 →
        (Ideal.absNorm I:ℝ)≤X) →
      ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^ε := by
  obtain ⟨C,hC,hc⟩ := active_tuple_zero_energy_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  have hX0 : 0<X := zero_lt_one.trans_le hX
  have hb := hc hi η m A t S β W X K B hX hK hB hβ hN
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hX0)]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hX0.le)).trans_eq
  rw [Real.rpow_add hX0,Real.rpow_one]
  field_simp

theorem normalized_supported_tuple_zero_energy_bound (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι], Fintype.card ι≤N →
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Tuple ι))
        (β : Tuple ι → ℂ) (W : 𝓢(ℝ,ℂ)) (X K B : ℝ),
      1≤X → 0≤K → 0≤B →
      (∀ v∈S,‖β v‖≤B) →
      (∀ v∈S,β v≠0 → (Ideal.absNorm (finiteTupleProduct v):ℝ)≤X) →
      ‖((X⁻¹:ℝ):ℂ)*zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K‖ ≤
        C*K*B^2*‖paperRadialFourier W 0‖*X^ε := by
  obtain ⟨C,hC,hc⟩ := normalized_active_tuple_zero_energy_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ hi η m A t S β W X K B hX hK hB hβ hN
  apply hc hi η m A t S β W X K B hX hK hB (fun v hv _ => hβ v hv)
  intro I _ hI
  obtain ⟨v,hv,hne,he⟩ := finiteColumnCoefficient_witness S β I hI
  rw [←he]
  exact hN v hv hne

end SevenEighths.CenteredMomentSupportedZeroEnergy

end

end OAI
