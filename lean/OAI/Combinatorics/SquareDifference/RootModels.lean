import OAI.Combinatorics.SquareDifference.ConductorBounds

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace LiftTheory
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference

lemma truncatedSieveMean_bound {I : Type*} [DecidableEq I]
    (S : Finset I) (p : I → ℕ) (H : ℝ) (a b : I → ℂ) (k : I → ℝ)
    (ha : ∀i∈S, ‖a i‖≤k i) (hb : ∀i∈S, ‖b i‖≤k i) :
    ‖truncatedSieveMean S p H a b‖≤(2 : ℝ)^S.card*∏i∈S, k i := by
  unfold truncatedSieveMean
  calc
    _ ≤ ∑T∈S.powerset, ∏i∈S, k i := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro T hT
      split_ifs
      · exact localSieveTerm_norm S T (mem_powerset.mp hT) a b k ha hb
      · rw [norm_zero]
        exact prod_nonneg (fun i hi => (norm_nonneg _).trans (ha i hi))
    _ = _ := by simp only [sum_const,nsmul_eq_mul,card_powerset,Nat.cast_pow,Nat.cast_ofNat]

lemma truncatedSieveMean_complete {I : Type*} [DecidableEq I]
    (S : Finset I) (p : I → ℕ) (H : ℝ) (a b : I → ℂ)
    (hp : ∀i∈S, 1≤p i) (hH : ((∏i∈S, p i : ℕ) : ℝ)≤H) :
    truncatedSieveMean S p H a b=∏i∈S, (a i-b i) := by
  unfold truncatedSieveMean
  calc
    _ = ∑T∈S.powerset, localSieveTerm S a b T := by
      apply sum_congr rfl
      intro T hT
      rw [ite_eq_left]
      apply le_trans _ hH
      exact_mod_cast prod_le_prod_of_subset_of_one_le₀ (mem_powerset.mp hT)
        (fun _ _ => Nat.zero_le _) (fun i hi _ => hp i hi)
    _ = _ := (prod_sub a b S).symm

lemma localSieveTerm_product {I : Type*} [DecidableEq I]
    (S T : Finset I) (hTS : T⊆S) (a b : I → ℂ) :
    localSieveTerm S a b T=(-1 : ℂ)^T.card*∏i∈S, if i∈T then b i else a i := by
  dsimp only [localSieveTerm]
  rw [prod_ite]
  have h1 : S.filter (fun i => i∈T)=T := by ext i; simp only [mem_filter]; exact ⟨And.right,fun h => ⟨hTS h,h⟩⟩
  have h2 : S.filter (fun i => i∉T)=S\T := by ext i; simp
  rw [h1,h2]
  ring

lemma localSieveTerm_zero {I : Type*} [DecidableEq I]
    (S U T : Finset I) (a b : I → ℂ) (hTU : ¬T⊆U)
    (hb : ∀i∈T, i∉U → b i=0) : localSieveTerm S a b T=0 := by
  obtain ⟨i,hi,hiU⟩ := not_subset.mp hTU
  rw [localSieveTerm,prod_eq_zero hi (hb i hi hiU),mul_zero]

lemma quadratic_sieve_bounds {p q : ℕ} [Fact p.Prime] [NeZero q]
    (hpq : p∣q) (hq : IsUnit (2 : ZMod q))
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) :
    ‖𝔼 x : ZMod q, ψ (x^2)‖≤(q : ℝ)^(-(1 : ℝ)/2) ∧
    ‖𝔼 x : ZMod q,
      (primeSieveWeight p (ZMod.castHom hpq (ZMod p) x) : ℂ)*ψ (x^2)‖≤
      (q : ℝ)^(-(1 : ℝ)/2) := by
  constructor
  · simpa only [mul_one,one_mul,ZMod.card] using
      (hasFourierBound_one ψ).gauss hψ 1 (by simpa only [mul_one] using hq)
  · simpa only [mul_one,one_mul,ZMod.card] using
      (primeSieveWeight_fourier_dvd hpq ψ hψ).gauss hψ 1 (by simpa only [mul_one] using hq)

lemma nonprime_sieve_mean_zero {p q : ℕ} [Fact p.Prime] [NeZero q] (hpq : p∣q) :
    (𝔼 x : ZMod q, (primeSieveWeight p (ZMod.castHom hpq (ZMod p) x) : ℂ))=0 := by
  have h := expect_surjective_addHom (ZMod.castHom hpq (ZMod p)).toAddMonoidHom
    (ZMod.ringHom_surjective _) (fun x => (primeSieveWeight p x : ℂ))
  change (𝔼 x : ZMod q, (primeSieveWeight p (ZMod.castHom hpq (ZMod p) x) : ℂ))=
    (𝔼 x : ZMod p, (primeSieveWeight p x : ℂ)) at h
  rw [h]
  have hz := primeSieveWeight_mean_zero (p := p)
  exact_mod_cast hz

noncomputable def unitQuadraticMean {R : Type*} [CommRing R] [Fintype R]
    [DecidableEq R] (ψ : AddChar R ℂ) : ℂ := 𝔼 x : Rˣ, ψ ((x : R)^2)

lemma prime_unit_quadratic {p : ℕ} [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) :
    (𝔼 x : ZMod p, ψ (x^2))-
      (𝔼 x : ZMod p, (primeSieveWeight p x : ℂ)*ψ (x^2))=unitQuadraticMean ψ := by
  classical
  have he (x : ZMod p) : ψ (x^2)-(primeSieveWeight p x : ℂ)*ψ (x^2)=
      ((p : ℂ)/(p-1))*(if x≠0 then ψ (x^2) else 0) := by
    have hh := congrArg (fun z : ℝ => (z : ℂ)) (primeSieveWeight_unit_density x)
    push_cast at hh
    calc
      _ = (1-(primeSieveWeight p x : ℂ))*ψ (x^2) := by ring
      _ = _ := by rw [hh]; split_ifs <;> simp only [Complex.ofReal_one,Complex.ofReal_zero] <;> ring
  rw [← expect_sub_distrib]
  simp_rw [he]
  rw [← mul_expect]
  have hs : (∑x : ZMod p, if x≠0 then ψ (x^2) else 0)=
      ∑x : (ZMod p)ˣ, ψ ((x : ZMod p)^2) := by
    rw [← sum_filter]
    rw [sum_subtype (p := fun x : ZMod p => x≠0) _ (by intro x; simp only [mem_filter,mem_univ,true_and])]
    symm
    exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)
  rw [expect_eq_sum_div_card,hs,unitQuadraticMean,expect_eq_sum_div_card]
  simp only [Finset.card_univ,Fintype.card_units,ZMod.card]
  have hp : (p : ℂ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : (1 : ℕ)≤p := (Fact.out : p.Prime).one_lt.le
  rw [Nat.cast_sub hp1,Nat.cast_one]
  field_simp

lemma prime_power_sieved_zero {p k : ℕ} [Fact p.Prime] [NeZero k]
    (hp : p≠2) (hpk : p∣k) (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (p*k), ψ (x^2))-
      (𝔼 x : ZMod (p*k),
        (primeSieveWeight p (ZMod.castHom (dvd_mul_right p k) (ZMod p) x) : ℂ)*ψ (x^2))=0 := by
  classical
  have he (x : ZMod (p*k)) :
      ψ (x^2)-(primeSieveWeight p (ZMod.castHom (dvd_mul_right p k) (ZMod p) x) : ℂ)*ψ (x^2)=
      ((p : ℂ)/(p-1))*
      ((if ZMod.castHom (dvd_mul_right p k) (ZMod p) x≠0 then (1 : ℂ) else 0)*ψ (x^2)) := by
    have hh := congrArg (fun z : ℝ => (z : ℂ))
      (primeSieveWeight_unit_density (ZMod.castHom (dvd_mul_right p k) (ZMod p) x))
    push_cast at hh
    calc
      _ = (1-(primeSieveWeight p (ZMod.castHom (dvd_mul_right p k) (ZMod p) x) : ℂ))*ψ (x^2) := by ring
      _ = _ := by rw [hh]; split_ifs <;> simp only [Complex.ofReal_one,Complex.ofReal_zero] <;> ring
  rw [← expect_sub_distrib]
  simp_rw [he]
  rw [← mul_expect,odd_unit_gauss_zero_char hp hpk ψ hψ,mul_zero]

lemma two_le_rpow_sixth {x : ℝ} (hx : 64≤x) : 2≤x^((1 : ℝ)/6) := by
  have h : (2 : ℝ)≤x^(6 : ℝ)⁻¹ := by
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) (by linarith : 0≤x) (by norm_num)).mpr
    norm_num
    exact hx
  simpa only [one_div] using h

lemma smallPrime_product_bound (S : Finset ℕ) (a : ℕ → ℕ)
    (ha : ∀p∈S, p≤a p) (hp : ∀p∈S, 1≤p) :
    (2 : ℝ)^S.card≤2^64*((∏p∈S, (a p : ℝ))^((1 : ℝ)/6)) := by
  let K := S.filter (fun p => p<64)
  have hK : K⊆range 64 := by intro p hp; exact mem_range.mpr (mem_filter.mp hp).2
  have hcard : K.card≤64 := le_trans (card_le_card hK) (by simp)
  have hk0 : ∀p∈S, 0≤(a p : ℝ) := fun _ _ => Nat.cast_nonneg _
  have hle (p : ℕ) (hps : p∈S) : (2 : ℝ)≤
      (if p<64 then (2 : ℝ) else 1)*(a p : ℝ)^((1 : ℝ)/6) := by
    split_ifs with h
    · have h1 : (1 : ℝ)≤(a p : ℝ)^((1 : ℝ)/6) :=
        Real.one_le_rpow (by exact_mod_cast (hp p hps).trans (ha p hps)) (by norm_num)
      linarith
    · rw [one_mul]
      apply two_le_rpow_sixth
      exact_mod_cast (le_trans (Nat.le_of_not_gt h) (ha p hps))
  calc
    _ = ∏p∈S, (2 : ℝ) := (prod_const 2).symm
    _ ≤ ∏p∈S, (if p<64 then (2 : ℝ) else 1)*(a p : ℝ)^((1 : ℝ)/6) :=
      Finset.prod_le_prod₀ (by intros; norm_num) hle
    _ = (2 : ℝ)^K.card*(∏p∈S, (a p : ℝ))^((1 : ℝ)/6) := by
      rw [prod_mul_distrib,prod_ite]
      simp only [prod_const,one_pow,mul_one]
      rw [Real.finsetProd_rpow _ _ (fun p hp => hk0 p hp)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard)
      (Real.rpow_nonneg (prod_nonneg hk0) _)

lemma truncatedSieveMean_decay (S : Finset ℕ) (a : ℕ → ℕ) (H : ℝ) (A B : ℕ → ℂ)
    (ha : ∀p∈S, p≤a p) (hp : ∀p∈S, 1≤p)
    (hA : ∀p∈S, ‖A p‖≤(a p : ℝ)^(-(1 : ℝ)/2))
    (hB : ∀p∈S, ‖B p‖≤(a p : ℝ)^(-(1 : ℝ)/2)) :
    ‖truncatedSieveMean S id H A B‖≤2^64*(∏p∈S, (a p : ℝ))^(-(1 : ℝ)/3) := by
  have hpos (p : ℕ) (hps : p∈S) : (0 : ℝ)<a p := by exact_mod_cast (hp p hps).trans (ha p hps)
  have hprod : 0<∏p∈S, (a p : ℝ) := prod_pos hpos
  apply (truncatedSieveMean_bound S id H A B _ hA hB).trans
  rw [Real.finsetProd_rpow _ _ (fun p hp => (hpos p hp).le)]
  calc
    _ ≤ (2^64*(∏p∈S, (a p : ℝ))^((1 : ℝ)/6))*(∏p∈S, (a p : ℝ))^(-(1 : ℝ)/2) :=
      mul_le_mul_of_nonneg_right (smallPrime_product_bound S a ha hp) (Real.rpow_nonneg hprod.le _)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hprod]; norm_num

end SquareDifference

namespace SquareDifference

open scoped ComplexConjugate

lemma prime_unit_mean_decay {p : ℕ} [Fact p.Prime] (hp : 64≤p)
    (a : ZMod p) (ha : a≠0) :
    ‖𝔼 u : (ZMod p)ˣ,ZMod.stdAddChar (a*(u : ZMod p)^2)‖≤(p : ℝ)^(-(1:ℝ)/3) := by
  let ψ := (ZMod.stdAddChar (N:=p)).mulShift a
  have hψ : ψ.IsPrimitive := AddChar.IsPrimitive.of_ne_one (ZMod.isPrimitive_stdAddChar p ha)
  have htwo : IsUnit (2 : ZMod p) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff (2:ℕ) p).mp (by simpa using hz)
    have := Nat.le_of_dvd (by decide : 0<2) hd
    omega
  have hb := quadratic_sieve_bounds (p:=p) (q:=p) (dvd_refl p) htwo ψ hψ
  simp only [ZMod.castHom_self,RingHom.id_apply] at hb
  have he := prime_unit_quadratic ψ
  have hle : ‖unitQuadraticMean ψ‖≤2*(p:ℝ)^(-(1:ℝ)/2) := by
    rw [← he]
    exact (norm_sub_le _ _).trans (by linarith [hb.1,hb.2])
  have hp0 : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpow : 2*(p:ℝ)^(-(1:ℝ)/2)≤(p:ℝ)^(-(1:ℝ)/3) := by
    calc
      _ ≤ (p:ℝ)^((1:ℝ)/6)*(p:ℝ)^(-(1:ℝ)/2) :=
        mul_le_mul_of_nonneg_right (two_le_rpow_sixth (by exact_mod_cast hp)) (by positivity)
      _ = _ := by rw [← Real.rpow_add hp0]; congr 1 ; norm_num
  exact hle.trans hpow

section PairTail

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ)
  [∀j,Fact (p j).Prime]

lemma squareMultiplier_decay (hp : ∀j,64≤p j) (a : ResidueSpace p) :
    ‖squareMultiplier p a‖≤(supportDenominator p a:ℝ)^(-(1:ℝ)/3) := by
  rw [squareMultiplier_product,norm_prod]
  have he : (∏j,‖𝔼 u : (ZMod (p j))ˣ,ZMod.stdAddChar (a j*(u : ZMod (p j))^2)‖)=
      ∏j∈primeSupport p a,‖𝔼 u : (ZMod (p j))ˣ,ZMod.stdAddChar (a j*(u : ZMod (p j))^2)‖ := by
    symm
    apply prod_subset (subset_univ _)
    intro j _ hj
    have hz : a j=0 := by simpa [primeSupport] using hj
    simp [hz]
  rw [he,supportDenominator,Nat.cast_prod,← Real.finsetProd_rpow _ (fun j => (p j:ℝ)) (fun j _ => Nat.cast_nonneg (p j))]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  exact prime_unit_mean_decay (hp j) (a j) (by simpa [primeSupport] using hj)

lemma squarePair_tail_bound (hp : ∀j,64≤p j) (F G : ResidueSpace p → ℂ)
    (H : ℝ) (hH : 0<H) :
    ‖∑a∈univ.filter (fun a => H<(supportDenominator p a:ℝ)),
      residueFourier p F (-a)*residueFourier p G a*squareMultiplier p a‖^2≤
      H^(-(2:ℝ)/3)*(𝔼 x,‖F x‖^2)*(𝔼 x,‖G x‖^2) := by
  have he : (H^(-(1:ℝ)/3))^2=H^(-(2:ℝ)/3) := by
    rw [← Real.rpow_mul_natCast hH.le]; congr 1 ; norm_num
  rw [← he]
  apply fourier_pair_tail p F G _ _ _ (by positivity)
  intro a ha
  apply (squareMultiplier_decay p hp a).trans
  exact Real.rpow_le_rpow_of_nonpos hH (mem_filter.mp ha).2.le (by norm_num)

end PairTail

end SquareDifference

namespace SquareDifference

open Finset

section RootModel

variable {I : Type*} [instFintypeI : Fintype I] [instDecidableEqI : DecidableEq I]
  (m : I → ℕ) [∀i,NeZero (m i)] (R : Finset I)

abbrev OutsideModulus : {i : I // i∉R} → ℕ := fun i => m i.val

noncomputable def rootCharacter (a s : ResidueSpace m) : ℂ :=
  ∏i∈R,ZMod.stdAddChar (a i*s i)

def outsideCoordinate (a : ResidueSpace m) : ResidueSpace (OutsideModulus m R) := fun i => a i.val

lemma prodChar_split (a x : ResidueSpace m) :
    prodChar m a x=rootCharacter m R a x*
      prodChar (OutsideModulus m R) (outsideCoordinate m R a) (outsideCoordinate m R x) := by
  unfold prodChar rootCharacter outsideCoordinate OutsideModulus
  rw [← prod_subtype Rᶜ (fun i => mem_compl) (fun i => ZMod.stdAddChar (a i*x i))]
  rw [prod_mul_prod_compl]

lemma rootCharacter_neg {I : Type*}
    [Fintype I]
    [DecidableEq I]
    (m : I → ℕ)
    [∀ (i : I), NeZero (m i)]
    (R : Finset I) (a s : ResidueSpace m) :
    rootCharacter m R (-a) s=conj (rootCharacter m R a s) := by
  simp only [rootCharacter,Pi.neg_apply,neg_mul,AddChar.map_neg_eq_conj,map_prod]

lemma rootCharacter_diff_cancel (a r s t : ResidueSpace m)
    (h : ∀i∈R,r i=t i-s i) :
    rootCharacter m R a r*conj (rootCharacter m R (-a) s)*
      conj (rootCharacter m R a t)=1 := by
  rw [rootCharacter_neg,starRingEnd_self_apply]
  simp only [rootCharacter,map_prod,← prod_mul_distrib]
  apply prod_eq_one
  intro i hi
  rw [← AddChar.map_neg_eq_conj,← AddChar.map_add_eq_mul,← AddChar.map_add_eq_mul]
  rw [h i hi,show a i*(t i-s i)+a i*s i+-(a i*t i)=0 by ring,AddChar.map_zero_eq_one]

lemma sum_outside_coordinate {E : Type*} [AddCommMonoid E]
    (f : ResidueSpace (OutsideModulus m R) → E) :
    (∑a : ResidueSpace m,f (outsideCoordinate m R a))=
      (∏i∈R,m i) • ∑b,f b := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i : I => i∈R) (fun i => ZMod (m i))
  rw [Fintype.sum_equiv e (fun a => f (outsideCoordinate m R a)) (fun b => f b.2) (fun _ => rfl),Fintype.sum_prod_type]
  simp only [sum_const,card_univ,Fintype.card_pi,ZMod.card]
  congr 1
  exact (prod_subtype R (fun _ => Iff.rfl) m).symm

noncomputable def sequenceResidueFourier {Ω : Type*} [Fintype Ω]
    (L : ℕ) (F : Ω → ℂ) (n : Ω → ℕ) (a : ResidueSpace m) : ℂ :=
  (L : ℂ)⁻¹*∑z,F z*conj (prodChar m a (fun i => (n z : ZMod (m i))))

lemma sequenceResidueFourier_root {Ω : Type*} [Fintype Ω]
    (L : ℕ) (F : Ω → ℂ) (n : Ω → ℕ) (s a : ResidueSpace m)
    (hF : ∀z,F z≠0 → ∀i∈R,(n z : ZMod (m i))=s i) :
    sequenceResidueFourier m L F n a=conj (rootCharacter m R a s)*
      sequenceResidueFourier (OutsideModulus m R) L F n (outsideCoordinate m R a) := by
  unfold sequenceResidueFourier
  simp only [prodChar_split m R,map_mul,mul_sum]
  apply sum_congr rfl
  intro z _
  by_cases hz : F z=0
  · simp [hz]
  · have he : rootCharacter m R a (fun i => (n z : ZMod (m i)))=rootCharacter m R a s := by
      apply prod_congr rfl
      intro i hi
      change ZMod.stdAddChar (a i*(n z : ZMod (m i)))=_
      rw [hF z hz i hi]
    rw [he]
    ring_nf
    rfl

lemma root_model_sum {Ω : Type*} [Fintype Ω]
    (L : ℕ) (F G : Ω → ℂ) (n : Ω → ℕ)
    (s t r : ResidueSpace m) (hr : ∀i∈R,r i=t i-s i)
    (hF : ∀z,F z≠0 → ∀i∈R,(n z : ZMod (m i))=s i)
    (hG : ∀z,G z≠0 → ∀i∈R,(n z : ZMod (m i))=t i)
    (c : ResidueSpace (OutsideModulus m R) → ℂ) :
    (∑a : ResidueSpace m,rootCharacter m R a r*c (outsideCoordinate m R a)*
      sequenceResidueFourier m L F n (-a)*sequenceResidueFourier m L G n a)=
      ((∏i∈R,m i : ℕ):ℂ)*∑b,c b*
        sequenceResidueFourier (OutsideModulus m R) L F n (-b)*
        sequenceResidueFourier (OutsideModulus m R) L G n b := by
  have he (a : ResidueSpace m) : rootCharacter m R a r*c (outsideCoordinate m R a)*
      sequenceResidueFourier m L F n (-a)*sequenceResidueFourier m L G n a=
      c (outsideCoordinate m R a)*
        sequenceResidueFourier (OutsideModulus m R) L F n (-(outsideCoordinate m R a))*
        sequenceResidueFourier (OutsideModulus m R) L G n (outsideCoordinate m R a) := by
    rw [sequenceResidueFourier_root m R L F n s (-a) hF,
      sequenceResidueFourier_root m R L G n t a hG]
    have hn : outsideCoordinate m R (-a)=-(outsideCoordinate m R a) := rfl
    rw [hn]
    calc
      _ = (rootCharacter m R a r*conj (rootCharacter m R (-a) s)*
          conj (rootCharacter m R a t))*(c (outsideCoordinate m R a)*
          sequenceResidueFourier (OutsideModulus m R) L F n (-(outsideCoordinate m R a))*
          sequenceResidueFourier (OutsideModulus m R) L G n (outsideCoordinate m R a)) := by ring
      _ = _ := by rw [rootCharacter_diff_cancel m R a r s t hr,one_mul]
  simp_rw [he]
  rw [sum_outside_coordinate m R (fun b => c b*
    sequenceResidueFourier (OutsideModulus m R) L F n (-b)*
    sequenceResidueFourier (OutsideModulus m R) L G n b)]
  simp only [nsmul_eq_mul]

end RootModel

end SquareDifference

end LiftTheory

namespace SquareDifference

open Finset

open scoped ComplexConjugate

section ModelPair

variable {I : Type*} [Fintype I] [DecidableEq I]
  (m : I → ℕ) [∀i,NeZero (m i)]
  (hcop : Pairwise fun i j => (m i).Coprime (m j))

local instance productNonzero : NeZero (∏i,m i) :=
  ⟨(prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (m i)))).ne'⟩

lemma grid_phase_char (a : ZMod (∏i,m i)) (n : ℕ) :
    expPhase ((n:ℝ)*(rationalGridPoint _ a:ℝ))=
      LiftTheory.SquareDifference.prodChar m (dualCRTEquiv m hcop a) (fun i => (n:ZMod (m i))) := by
  have he := rationalChar_int (rationalGridPoint _ a) (n:ℤ)
  simp only [Int.cast_natCast] at he
  rw [show (n:ℝ)*(rationalGridPoint _ a:ℝ)=(rationalGridPoint _ a:ℝ)*(n:ℝ) by ring, ←he]
  have hc := congrArg (fun χ : AddChar (ZMod (∏i,m i)) ℂ => χ (n : ZMod (∏i,m i))) (rationalGrid_char (q:=∏i,m i) a)
  simp only [AddChar.compAddMonoidHom_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_natCast] at hc
  rw [hc]
  simpa only [LiftTheory.SquareDifference.prodChar,standardCharEquiv_apply] using dualCRT_nat m hcop a n

lemma intervalFourier_grid {q : ℕ} [NeZero q] (N : ℕ) (F : ZMod q → ℂ)
    (a : ZMod (∏i,m i)) :
    intervalFourier N F (rationalGridPoint _ a:ℝ)=
      LiftTheory.SquareDifference.sequenceResidueFourier m N F ZMod.val (dualCRTEquiv m hcop a) := by
  unfold intervalFourier LiftTheory.SquareDifference.sequenceResidueFourier
  congr 1
  apply sum_congr rfl
  intro x _
  congr 1
  rw [neg_mul,expPhase_neg,grid_phase_char m hcop]

lemma intervalFourier_neg_grid {q : ℕ} [NeZero q] (N : ℕ) (F : ZMod q → ℂ)
    (a : ZMod (∏i,m i)) :
    intervalFourier N F (-(rationalGridPoint _ a:ℝ))=
      LiftTheory.SquareDifference.sequenceResidueFourier m N F ZMod.val (-(dualCRTEquiv m hcop a)) := by
  unfold intervalFourier LiftTheory.SquareDifference.sequenceResidueFourier
  congr 1
  apply sum_congr rfl
  intro x _
  congr 1
  rw [neg_mul_neg,grid_phase_char m hcop,LiftTheory.SquareDifference.prodChar_neg,starRingEnd_self_apply]

end ModelPair

end SquareDifference

namespace SquareDifference

open Finset

section RootCombination

variable {I : Type*} [Fintype I] [DecidableEq I]
  (m : I → ℕ) [instNeZeromi : ∀i,NeZero (m i)] (R : Finset I)

lemma root_unit_product (a r : ∀i,ZMod (m i)) :
    (∏i,if i∈R then ZMod.stdAddChar (a i*r i) else unitQuadraticMean (standardCharEquiv (a i)))=
      LiftTheory.SquareDifference.rootCharacter m R a r*
        LiftTheory.SquareDifference.squareMultiplier (LiftTheory.SquareDifference.OutsideModulus m R)
          (LiftTheory.SquareDifference.outsideCoordinate m R a) := by
  rw [←prod_mul_prod_compl R (fun i => if i∈R then ZMod.stdAddChar (a i*r i) else unitQuadraticMean (standardCharEquiv (a i)))]
  congr 1
  · exact prod_congr rfl (fun i hi => ite_eq_left hi)
  · rw [LiftTheory.SquareDifference.squareMultiplier_product]
    change (∏i∈Rᶜ,if i∈R then ZMod.stdAddChar (a i*r i) else unitQuadraticMean (standardCharEquiv (a i)))=
      ∏i : {i : I // i∉R},unitQuadraticMean (standardCharEquiv (a i))
    rw [←prod_subtype Rᶜ (fun i => mem_compl) (fun i => unitQuadraticMean (standardCharEquiv (a i)))]
    apply prod_congr rfl
    intro i hi
    rw [ite_eq_right (mem_compl.mp hi)]

lemma outside_support_denominator {I : Type*}
    [Fintype I]
    [DecidableEq I]
    (m : I → ℕ)
    [∀ (i : I), NeZero (m i)]
    (R : Finset I) (a : ∀i,ZMod (m i)) :
    LiftTheory.SquareDifference.supportDenominator (LiftTheory.SquareDifference.OutsideModulus m R)
      (LiftTheory.SquareDifference.outsideCoordinate m R a)=
      ∏i∈Rᶜ.filter (fun i => a i≠0),m i := by
  classical
  unfold LiftTheory.SquareDifference.supportDenominator LiftTheory.SquareDifference.primeSupport
  rw [prod_filter]
  change (∏i : {i : I // i∉R}, if a i≠0 then m i else 1)=_
  rw [←prod_subtype Rᶜ (fun i => mem_compl) (fun i => if a i≠0 then m i else 1)]
  rw [prod_filter]

end RootCombination

section ActualRootCombination

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime] (hinj : Function.Injective p)

lemma small_outside_support (R : Finset I) (htwo : ∀i,p i=2 → i∈R)
    (a : ∀i,ZMod (smallQuadraticModulus (p i))) :
    LiftTheory.SquareDifference.supportDenominator
      (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R)
      (LiftTheory.SquareDifference.outsideCoordinate _ R a)=
      ∏i∈Rᶜ.filter (fun i => a i≠0),p i := by
  rw [outside_support_denominator]
  apply prod_congr rfl
  intro i hi
  exact ite_eq_right (fun h => mem_compl.mp (mem_filter.mp hi).1 (htwo i h))

lemma kernelModelCoefficient_root (a : ZMod (∏i,smallQuadraticModulus (p i)))
    (R : Finset I) (c : ∀i,ZMod (p i)) (H : ℝ)
    (htwo : ∀i,p i=2 → i∈R) (hc : ∀i∈R,p i=2 → c i=1) :
    kernelModelCoefficient p R c H (rationalGridPoint _ a)=
      LiftTheory.SquareDifference.rootCharacter (fun i => smallQuadraticModulus (p i)) R
        (smallDualEquiv p hinj a) (fun i => smallRootSquare (p i) (c i))*
      (if (LiftTheory.SquareDifference.supportDenominator
          (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R)
          (LiftTheory.SquareDifference.outsideCoordinate _ R (smallDualEquiv p hinj a)):ℝ)≤H then
        LiftTheory.SquareDifference.squareMultiplier
          (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R)
          (LiftTheory.SquareDifference.outsideCoordinate _ R (smallDualEquiv p hinj a)) else 0) := by
  rw [kernelModelCoefficient_dual p hinj a R c H htwo hc,small_outside_support p R htwo]
  split_ifs
  · exact root_unit_product _ R _ _
  · exact (mul_zero _).symm

end ActualRootCombination

end SquareDifference

namespace SquareDifference

open Finset

section BilinearGrid

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime] (hinj : Function.Injective p)

include hinj

lemma modelBilinear_grid (R : Finset I) (c : ∀i,ZMod (p i)) (H : ℝ) (L N : ℕ)
    (hmodel : (rootSquareModulus p R:ℝ)*H≤L)
    (hcover : ∀b : ℚ,b.den≤L → b.den∣∏i,primaryModulus b.den (p i))
    (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    {q : ℕ} [NeZero q] (F G : ZMod q → ℂ) :
    (∑b : boundedRationals L,kernelModelCoefficient p R c H b.val*
      intervalFourier N F (-(b.val:ℝ))*intervalFourier N G b.val)=
      ∑a : ZMod (∏i,smallQuadraticModulus (p i)),
        kernelModelCoefficient p R c H (rationalGridPoint _ a)*
          intervalFourier N F (-(rationalGridPoint _ a:ℝ))*
          intervalFourier N G (rationalGridPoint _ a:ℝ) := by
  rw [Finset.sum_coe_sort (boundedRationals L) (fun b : ℚ =>
    kernelModelCoefficient p R c H b*intervalFourier N F (-(b:ℝ))*intervalFourier N G b)]
  apply bounded_sum_grid_of
  · intro b hb hh
    exact kernelModelCoefficient_den_smallProduct p hinj R c b
      (hcover b ((mem_boundedRationals L b).mp hb).2.2) H htwo hc
      (left_ne_zero_of_mul (left_ne_zero_of_mul hh))
  · intro b hb hh
    have hb' := smallProduct_primary_cover p hinj b ((mem_rationalGrid _ b).mp hb).2.2
    have hne := left_ne_zero_of_mul (left_ne_zero_of_mul hh)
    rw [←primaryModelCoefficient_eq_kernelModel p R c hinj b hb' H htwo] at hne
    exact_mod_cast (primaryModelCoefficient_denominator_le p hinj b hb' R c H htwo hc hne).trans hmodel

lemma modelBilinear_root (R : Finset I) (c : ∀i,ZMod (p i)) (H : ℝ) (L N : ℕ)
    (hmodel : (rootSquareModulus p R:ℝ)*H≤L)
    (hcover : ∀b : ℚ,b.den≤L → b.den∣∏i,primaryModulus b.den (p i))
    (htwo : ∀i,p i=2 → i∈R)
    (hc : ∀i∈R,if p i=2 then c i=1 else c i≠0)
    {q : ℕ} [NeZero q] (F G : ZMod q → ℂ)
    (s t : ∀i,ZMod (smallQuadraticModulus (p i)))
    (hr : ∀i∈R,smallRootSquare (p i) (c i)=t i-s i)
    (hF : ∀z,F z≠0 → ∀i∈R,(z.val:ZMod (smallQuadraticModulus (p i)))=s i)
    (hG : ∀z,G z≠0 → ∀i∈R,(z.val:ZMod (smallQuadraticModulus (p i)))=t i) :
    (∑b : boundedRationals L,kernelModelCoefficient p R c H b.val*
      intervalFourier N F (-(b.val:ℝ))*intervalFourier N G b.val)=
      ((∏i∈R,smallQuadraticModulus (p i):ℕ):ℂ)*
        ∑a : LiftTheory.SquareDifference.ResidueSpace
            (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R),
          (if (LiftTheory.SquareDifference.supportDenominator
              (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R) a:ℝ)≤H then
            LiftTheory.SquareDifference.squareMultiplier
              (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R) a else 0)*
          LiftTheory.SquareDifference.sequenceResidueFourier
            (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R) N F ZMod.val (-a)*
          LiftTheory.SquareDifference.sequenceResidueFourier
            (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R) N G ZMod.val a := by
  rw [modelBilinear_grid p hinj R c H L N hmodel hcover htwo hc]
  simp_rw [kernelModelCoefficient_root p hinj _ R c H htwo (fun i hi h => by simpa only [h,ite_true] using hc i hi),
    intervalFourier_grid (fun i => smallQuadraticModulus (p i))
      (smallQuadraticModuli_pairwise p (fun i => Fact.out) hinj),
    intervalFourier_neg_grid (fun i => smallQuadraticModulus (p i))
      (smallQuadraticModuli_pairwise p (fun i => Fact.out) hinj)]
  have hh := LiftTheory.SquareDifference.root_model_sum (fun i => smallQuadraticModulus (p i)) R N F G ZMod.val s t
    (fun i => smallRootSquare (p i) (c i)) hr hF hG
    (fun a => if (LiftTheory.SquareDifference.supportDenominator
      (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R) a:ℝ)≤H then
      LiftTheory.SquareDifference.squareMultiplier
        (LiftTheory.SquareDifference.OutsideModulus (fun i => smallQuadraticModulus (p i)) R) a else 0)
  apply Eq.trans _ hh
  exact Fintype.sum_equiv (smallDualEquiv p hinj) _ _ (fun a => rfl)

end BilinearGrid

end SquareDifference

end

end OAI
