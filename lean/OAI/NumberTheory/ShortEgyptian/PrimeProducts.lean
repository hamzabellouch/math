import OAI.NumberTheory.ShortEgyptian.PrimeLists

namespace OAI

universe uJ uA uB uE uK

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

theorem prime_product_fiber_card {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p) (n : ℕ) :
    Nat.card {f : J → A // ∏ j, p (f j) = n} ≤ (Fintype.card J)^(Fintype.card J) := by
  classical
  by_cases h : Nonempty {f : J → A // ∏ j, p (f j) = n}
  · let f₀ := Classical.choice h
    let T : Finset A := univ.image f₀.val
    have hmem (f : {f : J → A // ∏ j, p (f j) = n}) (j : J) : f.val j ∈ T := by
      have hd : p (f.val j) ∣ ∏ k, p (f₀.val k) := by
        exact (dvd_prod_of_mem (fun k => p (f.val k)) (mem_univ j)).trans (dvd_of_eq (f.property.trans f₀.property.symm))
      rcases (hp (f.val j)).prime.exists_mem_finset_dvd hd with ⟨k,_,hk⟩
      have heq : p (f.val j) = p (f₀.val k) := (Nat.prime_dvd_prime_iff_eq (hp (f.val j)) (hp (f₀.val k))).mp hk
      exact mem_image.mpr ⟨k,mem_univ _,hinj heq.symm⟩
    let F (f : {f : J → A // ∏ j, p (f j) = n}) : J → T := fun j => ⟨f.val j,hmem f j⟩
    have hF : Function.Injective F := by
      intro f g hfg
      apply Subtype.ext
      funext j
      exact congrArg Subtype.val (congrFun hfg j)
    calc
      _ ≤ Fintype.card (J → T) := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_le_of_injective F hF
      _ = T.card ^ Fintype.card J := by simp
      _ ≤ _ := Nat.pow_le_pow_left (by simpa [T] using card_image_le (s := (univ : Finset J)) (f := f₀.val)) _
  · have : IsEmpty {f : J → A // ∏ j, p (f j) = n} := not_nonempty_iff.mp h
    simp

noncomputable def finiteMass {A : Type uA} {B : Type uB} [Fintype A] (f : A → B) (b : B) : ℝ :=
  (Nat.card {a : A // f a = b} : ℝ) / Fintype.card A

lemma finiteMass_nonneg {A : Type uA} {B : Type uB} [Fintype A] (f : A → B) (b : B) :
    0 ≤ finiteMass f b := by unfold finiteMass; positivity

lemma finiteMass_sum {A : Type uA} {B : Type uB} [Fintype A] [Nonempty A] [Fintype B] (f : A → B) :
    ∑ b, finiteMass f b = 1 := by
  classical
  simp only [finiteMass,← sum_div]
  have hc : (∑ b : B, Nat.card {a : A // f a = b}) = Fintype.card A := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  rw [← Nat.cast_sum,hc,div_self]
  exact_mod_cast Fintype.card_ne_zero

lemma finiteMass_expect {A : Type uA} {B : Type uB} [Fintype A] [Fintype B] (f : A → B) (g : B → ℂ) :
    (𝔼 a, g (f a)) = ∑ b, (finiteMass f b : ℂ)*g b := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  have heq : ∑ a : A, g (f a) = ∑ b : B, (Nat.card {a : A // f a = b}:ℂ)*g b := by
    simpa only [Nat.card_eq_fintype_card,Fintype.sum_sigma, sum_const, card_univ, nsmul_eq_mul] using (Fintype.sum_equiv (Equiv.sigmaFiberEquiv f) (fun x => g x.1) (fun a => g (f a)) (by intro x; exact congrArg g x.2.property.symm)).symm
  rw [heq,sum_div]
  apply sum_congr rfl
  intro b _
  simp only [finiteMass,Complex.ofReal_div,Complex.ofReal_natCast]
  ring

lemma prime_product_atom {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p) (n : ℕ) :
    finiteMass (fun f : J → A => ∏ j, p (f j)) n ≤
      (Fintype.card J :ℝ)^(Fintype.card J) / (Fintype.card A:ℝ)^(Fintype.card J) := by
  unfold finiteMass
  rw [Fintype.card_fun,Nat.cast_pow]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast prime_product_fiber_card (J := J) p hp hinj n

lemma prime_product_mod_atom {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (q : ℕ) [NeZero q] (hprod : ∀ f : J → A, ∏ j, p (f j) < q) (b : ZMod q) :
    finiteMass (fun f : J → A => ((∏ j, p (f j) : ℕ) : ZMod q)) b ≤
      (Fintype.card J :ℝ)^(Fintype.card J) / (Fintype.card A:ℝ)^(Fintype.card J) := by
  have heq : ∀ f : J → A, ((∏ j, p (f j) : ℕ) : ZMod q) = b ↔ ∏ j, p (f j) = b.val := by
    intro f
    rw [← (ZMod.val_injective q).eq_iff, ZMod.val_natCast_of_lt (hprod f)]
  have hh : finiteMass (fun f : J → A => ((∏ j, p (f j) : ℕ) : ZMod q)) b =
      finiteMass (fun f : J → A => ∏ j, p (f j)) b.val := by
    unfold finiteMass
    congr 2
    exact Nat.card_congr (Equiv.subtypeEquivRight heq)
  rw [hh]
  exact prime_product_atom p hp hinj b.val

lemma expect_prod_pi {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] (f : J → A → ℝ) :
    (𝔼 x : J → A, ∏ j, f j (x j)) = ∏ j, 𝔼 a : A, f j a := by
  simp only [Fintype.expect_eq_sum_div_card,prod_div_distrib,prod_const,card_univ,
    Fintype.card_fun,Nat.cast_pow]
  congr 1
  simpa using (prod_univ_sum (fun _ : J => (univ : Finset A)) f).symm

lemma finiteMass_indicator {A : Type uA} {B : Type uB} [Fintype A] (f : A → B) (b : B) :
    finiteMass f b = 𝔼 a, if f a = b then (1:ℝ) else 0 := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [finiteMass,Nat.card_eq_fintype_card,Fintype.card_subtype, sum_boole]

lemma finite_markov {A : Type uA} [Fintype A] (f : A → ℝ) (hnonneg : ∀ a, 0 ≤ f a)
    (c : ℝ) (hc : 0 < c) :
    (𝔼 a, if c ≤ f a then (1:ℝ) else 0) ≤ (𝔼 a, f a)/c := by
  apply (le_div_iff₀ hc).mpr
  rw [Finset.expect_mul]
  apply expect_le_expect
  intro a _
  split_ifs with h
  · simpa using h
  · simpa using hnonneg a

lemma finite_union_bound {A : Type uA} {J : Type uJ} [Fintype A] [Fintype J] (P : J → A → Prop) :
    (𝔼 a, if ∃ j, P j a then (1:ℝ) else 0) ≤ ∑ j, 𝔼 a, if P j a then (1:ℝ) else 0 := by
  rw [← expect_sum_comm]
  apply expect_le_expect
  intro a _
  split_ifs with h
  · obtain ⟨j,hj⟩ := h
    have hh := single_le_sum (fun j _ => by positivity : ∀ j ∈ (univ : Finset J), 0 ≤ if P j a then (1:ℝ) else 0) (mem_univ j)
    simpa [hj] using hh
  · exact sum_nonneg (fun _ _ => by positivity)

lemma gcd_prod_le_hits {J : Type uJ} {A : Type uA} [Fintype J]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (f : J → A) (u : ℕ) :
    Nat.gcd (∏ j, p (f j)) u ≤ ∏ j, if p (f j) ∣ u then p (f j) else 1 := by
  have hd : Nat.gcd (∏ j, p (f j)) u ∣ ∏ j, Nat.gcd (p (f j)) u := by
    have aux (T : Finset J) : Nat.gcd u (∏ j ∈ T, p (f j)) ∣ ∏ j ∈ T, Nat.gcd u (p (f j)) := by
      induction T using Finset.induction_on with
      | empty => simp
      | @insert a T ha ih =>
        rw [prod_insert ha,prod_insert ha]
        exact (gcd_mul_dvd_mul_gcd u (p (f a)) _).trans (Nat.mul_dvd_mul_left _ ih)
    simpa only [Nat.gcd_comm] using aux univ
  have heq : ∀ j, Nat.gcd (p (f j)) u = if p (f j) ∣ u then p (f j) else 1 := by
    intro j
    split_ifs with h
    · exact Nat.gcd_eq_left h
    · exact (hp (f j)).coprime_iff_not_dvd.mpr h
  simp_rw [heq] at hd
  exact Nat.le_of_dvd (prod_pos (fun j _ => by split_ifs; exact (hp _).pos; omega)) hd

lemma gcd_product_moment {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (u : ℕ)
    (H h a : ℝ) (hH : 0 ≤ H) (ha : 0 ≤ a) (hprob : 0 ≤ h)
    (hmax : ∀ x, (p x:ℝ) ≤ H)
    (hhit : (𝔼 x, if p x ∣ u then (1:ℝ) else 0) ≤ h) :
    (𝔼 f : J → A, (Nat.gcd (∏ j, p (f j)) u : ℝ)^a) ≤
      Real.exp ((Fintype.card J:ℝ)*h*H^a) := by
  let w (x : A) : ℝ := if p x ∣ u then (p x:ℝ)^a else 1
  have hw : ∀ x, 0 ≤ w x := by intro x; unfold w; split_ifs <;> positivity
  have hpoint (f : J → A) : (Nat.gcd (∏ j, p (f j)) u : ℝ)^a ≤ ∏ j, w (f j) := by
    have hg : (Nat.gcd (∏ j, p (f j)) u:ℝ) ≤ ∏ j, if p (f j) ∣ u then (p (f j):ℝ) else 1 := by
      exact_mod_cast gcd_prod_le_hits p hp f u
    apply (Real.rpow_le_rpow (by positivity) hg ha).trans_eq
    rw [← Real.finsetProd_rpow _ _ (fun _ _ => by split_ifs <;> positivity)]
    apply prod_congr rfl
    intro j _
    dsimp [w]
    split_ifs <;> simp
  have he : (𝔼 x, w x) ≤ 1+h*H^a := by
    calc
      _ ≤ 𝔼 x, (1+(if p x ∣ u then (1:ℝ) else 0)*H^a) := by
        apply expect_le_expect
        intro x _
        dsimp [w]
        split_ifs
        · have ht := Real.rpow_le_rpow (Nat.cast_nonneg (p x)) (hmax x) ha
          simpa only [one_mul] using ht.trans (by linarith : H^a ≤ 1+H^a)
        · simp
      _ = 1+(𝔼 x, if p x ∣ u then (1:ℝ) else 0)*H^a := by
        rw [expect_add_distrib,Fintype.expect_const,← expect_mul]
      _ ≤ _ := by gcongr
  calc
    _ ≤ 𝔼 f : J → A, ∏ j, w (f j) := expect_le_expect (fun f _ => hpoint f)
    _ = (𝔼 x, w x)^(Fintype.card J) := by rw [expect_prod_pi]; simp
    _ ≤ (1+h*H^a)^(Fintype.card J) := pow_le_pow_left₀ (expect_nonneg (fun x _ => hw x)) he _
    _ ≤ Real.exp (h*H^a)^(Fintype.card J) := by
      apply pow_le_pow_left₀ (by positivity) _
      linarith [Real.add_one_le_exp (h*H^a)]
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma prime_divisor_count (u : ℕ) (hu : u ≠ 0) :
    (u.primeFactors.card:ℝ)*Real.log 2 ≤ Real.log u := by
  have hp : 2^u.primeFactors.card ≤ u := by
    calc
      _ ≤ ∏ p ∈ u.primeFactors, p := by
        rw [← prod_const]
        exact prod_le_prod (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ u := Nat.le_of_dvd (Nat.pos_of_ne_zero hu) (Nat.prod_primeFactors_dvd u)
  have hh := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)^u.primeFactors.card)
    (show (2:ℝ)^u.primeFactors.card ≤ u by exact_mod_cast hp)
  simpa only [Real.log_pow] using hh

lemma prime_hit_probability {A : Type uA} [Fintype A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p) (u : ℕ) (hu : u ≠ 0) :
    (𝔼 a, if p a ∣ u then (1:ℝ) else 0) ≤
      (Real.log u / Real.log 2) / Fintype.card A := by
  rw [Fintype.expect_eq_sum_div_card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [sum_boole]
  have hc : (univ.filter (fun a => p a ∣ u)).card ≤ u.primeFactors.card := by
    apply card_le_card_of_injOn p
    · intro a ha
      exact Nat.mem_primeFactors.mpr ⟨hp a,(mem_filter.mp ha).2,hu⟩
    · exact hinj.injOn
  apply (show ((univ.filter (fun a => p a ∣ u)).card:ℝ) ≤ u.primeFactors.card by exact_mod_cast hc).trans
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr (prime_divisor_count u hu)

lemma uniform_prime_bilinear {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (q : ℕ) [NeZero q] (hprod : ∀ f : J → A, ∏ j, p (f j) < q) (c : (ZMod q)ˣ) :
    ‖𝔼 f : J → A, 𝔼 g : J → A,
      ZMod.stdAddChar ((c:ZMod q)*((∏ j, p (f j) : ℕ):ZMod q)*((∏ j, p (g j) : ℕ):ZMod q))‖ ≤
      Real.sqrt ((q:ℝ)*((Fintype.card J:ℝ)^Fintype.card J/(Fintype.card A:ℝ)^Fintype.card J)^2) := by
  let F (f : J → A) : ZMod q := (∏ j, p (f j) : ℕ)
  let α := finiteMass F
  have heq : (𝔼 f : J → A, 𝔼 g : J → A, ZMod.stdAddChar ((c:ZMod q)*F f*F g)) =
      ∑ x : ZMod q, ∑ y : ZMod q, (α x:ℂ)*(α y:ℂ)*ZMod.stdAddChar ((c:ZMod q)*x*y) := by
    rw [finiteMass_expect F (fun x => 𝔼 g, ZMod.stdAddChar ((c:ZMod q)*x*F g))]
    apply sum_congr rfl
    intro x _
    rw [finiteMass_expect F (fun y => ZMod.stdAddChar ((c:ZMod q)*x*y))]
    simp only [α,mul_sum,mul_assoc]
  change ‖𝔼 f : J → A, 𝔼 g : J → A, ZMod.stdAddChar ((c:ZMod q)*F f*F g)‖ ≤ _
  rw [heq]
  simpa only [pow_two,mul_assoc] using bilinear_probability_bound c α α
    ((Fintype.card J:ℝ)^Fintype.card J/(Fintype.card A:ℝ)^Fintype.card J)
    ((Fintype.card J:ℝ)^Fintype.card J/(Fintype.card A:ℝ)^Fintype.card J)
    (finiteMass_nonneg F) (finiteMass_nonneg F) (finiteMass_sum F) (finiteMass_sum F)
    (prime_product_mod_atom p hp hinj q hprod) (prime_product_mod_atom p hp hinj q hprod)

lemma expect_pi_split {J : Type uJ} {A : Type uA} {E : Type uE} [Fintype J] [Fintype A]
    [AddCommMonoid E] [Module ℚ≥0 E] (P : J → Prop) (F : (J → A) → E) :
    (𝔼 f : J → A, F f) =
      𝔼 g : {j // P j} → A, 𝔼 h : {j // ¬P j} → A,
        F (fun j => if hj : P j then g ⟨j,hj⟩ else h ⟨j,hj⟩) := by
  let e := Equiv.piEquivPiSubtypeProd P (fun _ => A)
  calc
    _ = 𝔼 gh : ({j // P j} → A) × ({j // ¬P j} → A), F (e.symm gh) := by
      exact Fintype.expect_equiv e _ _ (fun f => by simp)
    _ = _ := by
      rw [show (univ : Finset (({j // P j} → A) × ({j // ¬P j} → A))) = univ ×ˢ univ by simp]
      rw [expect_product]
      rfl

lemma expect_restrict_subtype {J : Type uJ} {A : Type uA} {E : Type uE} [Fintype J] [Fintype A] [Nonempty A]
    [AddCommMonoid E] [Module ℚ≥0 E] (P : J → Prop) (F : ({j // P j} → A) → E) :
    (𝔼 f : J → A, F (fun j => f j)) = 𝔼 g : {j // P j} → A, F g := by
  rw [expect_pi_split P]
  apply expect_congr rfl
  intro g _
  have heq (h : {j // ¬P j} → A) :
      (fun j : {j // P j} => if hj : P j.val then g ⟨j.val,hj⟩ else h ⟨j.val,hj⟩) = g := by
    funext j
    simp [j.property]
  simp only [heq,Fintype.expect_const]

lemma expect_restrict_injective {J : Type uJ} {K : Type uK} {A : Type uA} {E : Type uE} [Fintype J] [Fintype K] [Fintype A] [Nonempty A]
    [AddCommMonoid E] [Module ℚ≥0 E] (i : J → K) (hi : Function.Injective i) (F : (J → A) → E) :
    (𝔼 f : K → A, F (fun j => f (i j))) = 𝔼 g : J → A, F g := by
  let e : J ≃ Set.range i := Equiv.ofInjective i hi
  have hh := expect_restrict_subtype (fun k => k ∈ Set.range i)
    (fun g : Set.range i → A => F (fun j => g (e j)))
  change (𝔼 f : K → A, F (fun j => f (i j))) = _ at hh
  rw [hh]
  have ht := Fintype.expect_equiv (Equiv.arrowCongr e.symm (Equiv.refl A))
    (fun g : Set.range i → A => F (fun j => g (e j))) F (fun g => rfl)
  convert ht using 1
  exact expect_congr (by ext; simp) (fun _ _ => rfl)

end ShortEgyptian

end OAI
