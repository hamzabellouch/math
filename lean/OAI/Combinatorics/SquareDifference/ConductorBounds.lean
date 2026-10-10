import OAI.Combinatorics.SquareDifference.ResidueFourier

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

def HasFourierBound {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (w : R → ℂ) (C : ℝ) : Prop :=
  ∃ c : R → ℂ, (∀x, w x=∑a, c a*ψ (a*x)) ∧ (∑a, ‖c a‖)≤C

lemma hasFourierBound_of_expansion {R I : Type*} [CommRing R] [Fintype R] [Fintype I]
    (ψ : AddChar R ℂ) (w : R → ℂ) (b : I → R) (c : I → ℂ) (C : ℝ)
    (hw : ∀x, w x=∑i, c i*ψ (b i*x)) (hc : (∑i, ‖c i‖)≤C) :
    HasFourierBound ψ w C := by
  classical
  refine ⟨fun a => ∑i, if b i=a then c i else 0, ?_, ?_⟩
  · intro x
    rw [hw]
    simp only [sum_mul, ite_mul, zero_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    simp
  · calc
      _ ≤ ∑a : R, ∑i : I, ‖if b i=a then c i else 0‖ := sum_le_sum fun _ _ => norm_sum_le _ _
      _ = ∑i, ‖c i‖ := by
        simp only [apply_ite norm, norm_zero]
        rw [sum_comm]
        simp
      _ ≤ C := hc

lemma hasFourierBound_one {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) : HasFourierBound ψ (fun _ => 1) 1 := by
  apply hasFourierBound_of_expansion ψ (fun _ => 1) (fun _ : Unit => 0) (fun _ => 1)
  · intro x; simp
  · simp

lemma HasFourierBound.mul {R : Type*} [CommRing R] [Fintype R]
    {ψ : AddChar R ℂ} {w v : R → ℂ} {C D : ℝ}
    (hw : HasFourierBound ψ w C) (hv : HasFourierBound ψ v D) :
    HasFourierBound ψ (fun x => w x*v x) (C*D) := by
  rcases hw with ⟨c,hc,hC⟩
  rcases hv with ⟨d,hd,hD⟩
  have h0 : 0≤C := (sum_nonneg fun _ _ => norm_nonneg _).trans hC
  apply hasFourierBound_of_expansion ψ _ (fun a : R×R => a.1+a.2)
    (fun a => c a.1*d a.2)
  · intro x
    rw [hc, hd, ← univ_product_univ, sum_product, sum_mul]
    apply sum_congr rfl
    intro a _
    rw [mul_sum]
    apply sum_congr rfl
    intro b _
    simp only [add_mul, AddChar.map_add_eq_mul]
    ring
  · rw [← univ_product_univ, sum_product]
    simp only [norm_mul, ← mul_sum, ← sum_mul]
    exact mul_le_mul hC hD (sum_nonneg fun _ _ => norm_nonneg _) h0

lemma hasFourierBound_prod {R I : Type*} [CommRing R] [Fintype R] [DecidableEq I]
    (ψ : AddChar R ℂ) (S : Finset I) (w : I → R → ℂ)
    (hw : ∀i∈S, HasFourierBound ψ (w i) 1) :
    HasFourierBound ψ (fun x => ∏i∈S, w i x) 1 := by
  induction S using Finset.induction_on with
  | empty => simpa only [prod_empty] using hasFourierBound_one ψ
  | @insert a S ha ih =>
    have h1 := hw a (mem_insert_self _ _)
    have h2 := ih (fun i hi => hw i (mem_insert_of_mem hi))
    simpa only [one_mul, prod_insert ha] using h1.mul h2

lemma primeSieveWeight_fourier_bound {p k : ℕ} [Fact p.Prime] [NeZero k]
    (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) :
    HasFourierBound ψ (fun x => (primeSieveWeight p (ZMod.castHom (dvd_mul_right p k) (ZMod p) x) : ℂ)) 1 := by
  classical
  apply hasFourierBound_of_expansion ψ _ (fun a : ZMod p => zmodScaleHom p k a)
    (fun a : ZMod p => if a=0 then 0 else (p-1 : ℂ)⁻¹)
  · intro x
    rw [primeSieveWeight_fourier_char _ (zmodScale_primitive (NeZero.ne k) ψ hψ)]
    simp only [AddChar.compAddMonoidHom_apply, zmodScaleHom_mul, mul_sum, ite_mul, zero_mul]
    rw [← sum_erase (univ : Finset (ZMod p)) (a := 0) (f := fun a => if a=0 then 0 else (p-1 : ℂ)⁻¹*ψ (zmodScaleHom p k a*x)) (by simp)]
    apply sum_congr rfl
    intro a ha
    rw [ite_eq_right (mem_erase.mp ha).1]
  · have hp : (0:ℝ)<p-1 := by
      have h : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
      linarith
    have hn : ‖(p-1 : ℂ)‖=(p : ℝ)-1 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hp]
    rw [← sum_erase (univ : Finset (ZMod p)) (a := 0) (f := fun a => ‖if a=0 then (0 : ℂ) else (p-1 : ℂ)⁻¹‖) (by simp)]
    have he : (∑a∈(univ : Finset (ZMod p)).erase 0, ‖if a=0 then (0 : ℂ) else (p-1 : ℂ)⁻¹‖)=
        ((p : ℝ)-1)*((p : ℝ)-1)⁻¹ := by
      calc
        _ = ∑_a∈(univ : Finset (ZMod p)).erase 0, ((p : ℝ)-1)⁻¹ := by
          apply sum_congr rfl
          intro a ha
          rw [ite_eq_right (mem_erase.mp ha).1, norm_inv, hn]
        _ = _ := by
          rw [sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ 0), card_univ, ZMod.card,
            Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
    rw [he, mul_inv_cancel₀ hp.ne']

lemma HasFourierBound.gauss {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {ψ : AddChar R ℂ} {w : R → ℂ} {C : ℝ} (hw : HasFourierBound ψ w C)
    (hψ : ψ.IsPrimitive) (a : R) (ha : IsUnit (2*a)) :
    ‖𝔼 x, w x*ψ (a*x^2)‖≤C*(Fintype.card R : ℝ)^(-(1:ℝ)/2) := by
  rcases hw with ⟨c,hc,hC⟩
  simp_rw [hc]
  exact (fourier_weighted_gauss ψ hψ a ha id c).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))

lemma primitive_transport {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    (ψ.compAddMonoidHom e.symm.toAddMonoidHom).IsPrimitive := by
  intro a ha he
  apply hψ (show e.symm a≠0 by exact fun h => ha (e.symm.injective (by simpa using h)))
  ext x
  have h := congrArg (fun φ : AddChar S ℂ => φ (e x)) he
  change ψ (e.symm (a*e x))=1 at h
  simpa only [AddChar.mulShift_apply, AddChar.one_apply, map_mul, RingEquiv.symm_apply_apply] using h

lemma primitive_mulShift {R : Type*} [CommRing R] (ψ : AddChar R ℂ)
    (hψ : ψ.IsPrimitive) (a : R) (ha : IsUnit a) : (ψ.mulShift a).IsPrimitive := by
  intro b hb he
  apply hψ (show a*b≠0 by exact fun h => hb ((ha.mul_right_eq_zero).mp h))
  ext x
  have h := congrArg (fun φ : AddChar R ℂ => φ x) he
  simpa only [AddChar.mulShift_apply, AddChar.one_apply, mul_assoc] using h

noncomputable def coordinateChar {I : Type*} [DecidableEq I] {R : I → Type*}
    [∀i, CommRing (R i)] (ψ : AddChar (∀i, R i) ℂ) (i : I) : AddChar (R i) ℂ :=
  ψ.compAddMonoidHom (AddMonoidHom.single R i)

lemma coordinateChar_apply {I : Type*} [DecidableEq I] {R : I → Type*}
    [∀i, CommRing (R i)] (ψ : AddChar (∀i, R i) ℂ) (i : I) (x : R i) :
    coordinateChar ψ i x=ψ (Pi.single i x) := rfl

lemma coordinateChar_primitive {I : Type*} [DecidableEq I] {R : I → Type*}
    [∀i, CommRing (R i)] (ψ : AddChar (∀i, R i) ℂ) (hψ : ψ.IsPrimitive) (i : I) :
    (coordinateChar ψ i).IsPrimitive := by
  intro a ha he
  have hs : (Pi.single i a : ∀i, R i)≠0 := by
    intro h
    have hh := congrFun h i
    exact ha (by simpa only [Pi.single_eq_same, Pi.zero_apply] using hh)
  apply hψ hs
  ext x
  have h := congrArg (fun φ : AddChar (R i) ℂ => φ (x i)) he
  have hm : (Pi.single i a : ∀i, R i)*x=Pi.single i (a*x i) := by
    ext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Pi.single_eq_of_ne hj]
  simpa only [AddChar.mulShift_apply, coordinateChar_apply, AddChar.one_apply, hm] using h

lemma addChar_finset_sum {I A : Type*} [AddCommMonoid A] (ψ : AddChar A ℂ)
    (S : Finset I) (f : I → A) : ψ (∑i∈S, f i)=∏i∈S, ψ (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => rw [sum_insert ha, prod_insert ha, AddChar.map_add_eq_mul, ih]

lemma additive_character_product {I : Type*} [Fintype I] [DecidableEq I]
    {R : I → Type*} [∀i, CommRing (R i)] (ψ : AddChar (∀i, R i) ℂ) (x : ∀i, R i) :
    ψ x=∏i, coordinateChar ψ i (x i) := by
  have h : x=∑i, Pi.single i (x i) := by
    ext j
    simp only [Finset.sum_apply]
    rw [sum_eq_single j]
    · simp
    · intro i _ hij; exact Pi.single_eq_of_ne (Ne.symm hij) _
    · simp
  conv_lhs => rw [h]
  rw [addChar_finset_sum]
  rfl

lemma complex_expect_pi_prod {I : Type*} [Fintype I] [DecidableEq I]
    {X : I → Type*} [∀i, Fintype (X i)] (f : ∀i, X i → ℂ) :
    (𝔼 x : ∀i, X i, ∏i, f i (x i))=∏i, 𝔼 t : X i, f i t := by
  simp only [expect_eq_sum_div_card, card_univ, Fintype.card_pi, Nat.cast_prod,
    Finset.prod_div_distrib]
  rw [Fintype.prod_sum]

lemma product_quadratic_mean {I : Type*} [Fintype I] [DecidableEq I]
    {R : I → Type*} [∀i, CommRing (R i)] [∀i, Fintype (R i)]
    (ψ : AddChar (∀i, R i) ℂ) (w : ∀i, R i → ℂ) :
    (𝔼 x : ∀i, R i, (∏i, w i (x i))*ψ (x^2))=
      ∏i, 𝔼 t : R i, w i t*coordinateChar ψ i (t^2) := by
  have h (x : ∀i, R i) : (∏i, w i (x i))*ψ (x^2)=
      ∏i, w i (x i)*coordinateChar ψ i ((x i)^2) := by
    rw [additive_character_product ψ (x^2), ← prod_mul_distrib]
    rfl
  calc
    _ = 𝔼 x : ∀i, R i, ∏i, w i (x i)*coordinateChar ψ i ((x i)^2) :=
      expect_congr rfl (fun x _ => h x)
    _ = _ := complex_expect_pi_prod (I := I) (X := R)
      (fun i t => w i t*coordinateChar ψ i (t^2))

lemma primeSieveWeight_fourier_dvd {p q : ℕ} [Fact p.Prime] [NeZero q]
    (hpq : p∣q) (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) :
    HasFourierBound ψ (fun x => (primeSieveWeight p (ZMod.castHom hpq (ZMod p) x) : ℂ)) 1 := by
  obtain ⟨k,rfl⟩ := hpq
  have hk : k≠0 := by
    intro h; have hh := NeZero.ne (p*k); simp [h] at hh
  let : NeZero k := ⟨hk⟩
  exact primeSieveWeight_fourier_bound ψ hψ

lemma fiber_gauss_zero_char {p k : ℕ} [NeZero p] [NeZero k]
    (hpk : p∣k) (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) (c : ZMod p)
    (hc : (2 : ZMod p)*c≠0) :
    (𝔼 x : ZMod (p*k),
      (if ZMod.castHom (dvd_mul_right p k) (ZMod p) x=c then (p : ℂ) else 0)*ψ (x^2))=0 := by
  classical
  let φ := ZMod.castHom (dvd_mul_right p k) (ZMod p)
  let R := ZMod (p*k)
  have ht : φ (k : R)=0 := by
    dsimp only [φ]
    rw [map_natCast]
    exact (ZMod.natCast_eq_zero_iff k p).mpr hpk
  have ht2 : (k : R)^2=0 := by
    rw [pow_two]
    exact zmod_kernel_factor p k (k : R) ht
  let ζ := ψ ((2*(c.val : R))*(k : R))
  have hζ : ζ≠1 := by
    intro he
    have he0 : (2*(c.val : R))*(k : R)=0 :=
      (hψ.zmod_char_eq_one_iff (p*k) _).mp he
    have hz : ((2*(c.val : ℤ) : ℤ) : ZMod p)=0 :=
      (zmod_factor_zero p k (NeZero.ne k) (2*c.val)).mp (by simpa using he0)
    exact hc (by simpa using hz)
  have hz : (∑x : R, (if φ x=c then (1 : ℂ) else 0)*ψ (x^2))=0 := by
    have h := quadratic_shift_cancellation ψ (1 : R) (k : R)
      (fun x => if φ x=c then (1 : ℂ) else 0) ζ hζ
    simp only [one_mul] at h
    apply h
    · exact zmod_fiber_translation p k c (k : R) ht
    · intro x hx
      have hxc : φ x=c := by
        by_contra hh
        exact hx (ite_eq_right hh)
      have hkern : (x-(c.val : R))*(k : R)=0 := by
        apply zmod_kernel_factor p k
        change φ (x-(c.val : R))=0
        rw [map_sub, map_natCast, ZMod.natCast_zmod_val, hxc, sub_self]
      have hxk : x*(k : R)=(c.val : R)*(k : R) := by linear_combination hkern
      apply congrArg ψ
      calc
        _ = 2*(x*(k : R))+(k : R)^2 := by ring
        _ = _ := by rw [hxk, ht2]; ring
  rw [expect_eq_sum_div_card]
  have hs : (∑x : R, (if φ x=c then (p : ℂ) else 0)*ψ (x^2))=
      (p : ℂ)*∑x : R, (if φ x=c then (1 : ℂ) else 0)*ψ (x^2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    split_ifs <;> ring
  rw [hs,hz,mul_zero,zero_div]

lemma quadratic_mean_equiv {R S : Type*} [CommRing R] [CommRing S]
    [Fintype R] [Fintype S] (e : R ≃+* S) (ψ : AddChar R ℂ) (w : S → ℂ) :
    (𝔼 x : R, w (e x)*ψ (x^2))=
      𝔼 x : S, w x*(ψ.compAddMonoidHom e.symm.toAddMonoidHom) (x^2) := by
  classical
  apply Fintype.expect_equiv e.toEquiv
  intro x
  change w (e x)*ψ (x^2)=w (e x)*ψ (e.symm ((e x)^2))
  rw [← map_pow, RingEquiv.symm_apply_apply]

lemma crt_quadratic_mean {I : Type*} [Fintype I] [DecidableEq I]
    (m : I → ℕ) [∀i, NeZero (m i)] [NeZero (∏i, m i)]
    (hcop : Pairwise (Function.onFun Nat.Coprime m))
    (ψ : AddChar (ZMod (∏i, m i)) ℂ) (w : ∀i, ZMod (m i) → ℂ) :
    (𝔼 x : ZMod (∏i, m i),
      (∏i, w i (ZMod.prodEquivPi m hcop x i))*ψ (x^2)) =
    ∏i, 𝔼 t : ZMod (m i), w i t*
      coordinateChar (ψ.compAddMonoidHom (ZMod.prodEquivPi m hcop).symm.toAddMonoidHom) i (t^2) := by
  rw [quadratic_mean_equiv (ZMod.prodEquivPi m hcop) ψ (fun x => ∏i, w i (x i))]
  exact product_quadratic_mean _ w

lemma fiber_sum_gauss_zero_char {p k : ℕ} [NeZero p] [NeZero k]
    (hpk : p∣k) (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) (c : ZMod p)
    (hc : (2 : ZMod p)*c≠0) :
    (∑x : ZMod (p*k),
      (if ZMod.castHom (dvd_mul_right p k) (ZMod p) x=c then (1 : ℂ) else 0)*ψ (x^2))=0 := by
  classical
  have h := fiber_gauss_zero_char hpk ψ hψ c hc
  rw [expect_eq_sum_div_card, div_eq_zero_iff] at h
  have hc0 : (Fintype.card (ZMod (p*k)) : ℂ)≠0 := by
    simp only [ZMod.card, ne_eq, Nat.cast_eq_zero]
    exact mul_ne_zero (NeZero.ne p) (NeZero.ne k)
  have hs := h.resolve_right hc0
  have he : (∑x : ZMod (p*k),
      (if ZMod.castHom (dvd_mul_right p k) (ZMod p) x=c then (p : ℂ) else 0)*ψ (x^2))=
      (p : ℂ)*(∑x : ZMod (p*k),
      (if ZMod.castHom (dvd_mul_right p k) (ZMod p) x=c then (1 : ℂ) else 0)*ψ (x^2)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    split_ifs <;> ring
  rw [he] at hs
  exact (mul_eq_zero.mp hs).resolve_left (by exact_mod_cast NeZero.ne p)

lemma gauss_zero_of_fiber_char {p k : ℕ} [NeZero p] [NeZero k]
    (hpk : p∣k) (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) (w : ZMod p → ℂ)
    (hw : ∀c, w c≠0 → (2 : ZMod p)*c≠0) :
    (𝔼 x : ZMod (p*k), w (ZMod.castHom (dvd_mul_right p k) (ZMod p) x)*ψ (x^2))=0 := by
  classical
  rw [expect_eq_sum_div_card, weighted_fiber_sum]
  suffices (∑c : ZMod p, w c*∑x : ZMod (p*k),
      (if ZMod.castHom (dvd_mul_right p k) (ZMod p) x=c then (1 : ℂ) else 0)*ψ (x^2))=0 by
    rw [this, zero_div]
  apply sum_eq_zero
  intro c _
  by_cases hc : w c=0
  · rw [hc, zero_mul]
  · rw [fiber_sum_gauss_zero_char hpk ψ hψ c (hw c hc), mul_zero]

lemma odd_unit_gauss_zero_char {p k : ℕ} [Fact p.Prime] [NeZero k]
    (hp : p≠2) (hpk : p∣k) (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (p*k),
      (if ZMod.castHom (dvd_mul_right p k) (ZMod p) x≠0 then (1 : ℂ) else 0)*ψ (x^2))=0 := by
  apply gauss_zero_of_fiber_char hpk ψ hψ (fun c => if c≠0 then 1 else 0)
  intro c hc
  have hc0 : c≠0 := by intro h; simp [h] at hc
  have h2 : (2 : ZMod p)≠0 := Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
  exact mul_ne_zero h2 hc0

lemma two_unit_gauss_zero_char {k : ℕ} [NeZero k]
    (hk : 4∣k) (ψ : AddChar (ZMod (4*k)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (4*k),
      (if IsUnit (ZMod.castHom (dvd_mul_right 4 k) (ZMod 4) x) then (1 : ℂ) else 0)*ψ (x^2))=0 := by
  classical
  apply gauss_zero_of_fiber_char hk ψ hψ (fun c => if IsUnit c then 1 else 0)
  intro c hc
  have hc0 : IsUnit c := by by_contra h; simp [h] at hc
  simpa only [mul_one] using four_unit_mul_two isUnit_one hc0

lemma finite_complete_sieve {I : Type*} [DecidableEq I] (S : Finset I) (w : I → ℂ) :
    (∑T∈S.powerset, (-1 : ℂ)^T.card*∏i∈T, w i)=∏i∈S, (1-w i) := by
  have h := Finset.prod_add (fun i => -w i) (fun _ => (1 : ℂ)) S
  simp only [Finset.prod_const_one, mul_one, Finset.prod_neg] at h
  simpa only [add_comm (-w _) 1, sub_eq_add_neg] using h.symm

lemma zmodScale_primitive_general {m k : ℕ} [NeZero m] [NeZero k]
    (ψ : AddChar (ZMod (m*k)) ℂ) (hψ : ψ.IsPrimitive) :
    (ψ.compAddMonoidHom (zmodScaleHom m k)).IsPrimitive := by
  intro a ha he
  have h := congrArg (fun χ : AddChar (ZMod m) ℂ => χ 1) he
  simp only [AddChar.mulShift_apply, mul_one, AddChar.compAddMonoidHom_apply, AddChar.one_apply] at h
  have hz := (hψ.zmod_char_eq_one_iff (m*k) _).mp h
  apply ha
  exact zmodScaleHom_injective m k (NeZero.ne k) (by simpa only [map_zero] using hz)

noncomputable def residueDensity {m q : ℕ} (hmq : m∣q) (c : ZMod m) (x : ZMod q) : ℝ :=
  if ZMod.castHom hmq (ZMod m) x=c then m else 0

lemma residueDensity_fourier_bound {m k : ℕ} [NeZero m] [NeZero k]
    (ψ : AddChar (ZMod (m*k)) ℂ) (hψ : ψ.IsPrimitive) (c : ZMod m) :
    HasFourierBound ψ (fun x => (residueDensity (dvd_mul_right m k) c x : ℂ)) m := by
  classical
  let φ := ZMod.castHom (dvd_mul_right m k) (ZMod m)
  let χ := ψ.compAddMonoidHom (zmodScaleHom m k)
  have hχ : χ.IsPrimitive := zmodScale_primitive_general ψ hψ
  apply hasFourierBound_of_expansion ψ _ (fun a : ZMod m => zmodScaleHom m k a)
    (fun a => χ (-a*c)) m
  · intro x
    have h := AddChar.sum_mulShift (φ x-c) hχ
    simp only [ZMod.card, sub_eq_zero, Nat.cast_ite, Nat.cast_zero] at h
    have he (a : ZMod m) : χ (-a*c)*ψ (zmodScaleHom m k a*x)=χ (a*(φ x-c)) := by
      rw [← zmodScaleHom_mul]
      change χ (-a*c)*χ (a*φ x)=χ (a*(φ x-c))
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    simp_rw [he]
    rw [h]
    simp only [residueDensity,φ]
    split_ifs <;> simp
  · simp only [AddChar.norm_apply, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one, le_refl]

lemma residueDensity_fourier_dvd {m q : ℕ} [NeZero m] [NeZero q]
    (hmq : m∣q) (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (c : ZMod m) :
    HasFourierBound ψ (fun x => (residueDensity hmq c x : ℂ)) m := by
  obtain ⟨k,rfl⟩ := hmq
  have hk : k≠0 := by intro hk; have hh := NeZero.ne (m*k); simp [hk] at hh
  let : NeZero k := ⟨hk⟩
  exact residueDensity_fourier_bound ψ hψ c

lemma residueDensity_mean {m q : ℕ} [NeZero m] [NeZero q]
    (hmq : m∣q) (c : ZMod m) : (𝔼 x : ZMod q, (residueDensity hmq c x : ℂ))=1 := by
  classical
  have hsur : Function.Surjective (ZMod.castHom hmq (ZMod m)) :=
    ZMod.ringHom_surjective _
  have h := expect_surjective_addHom (ZMod.castHom hmq (ZMod m)).toAddMonoidHom hsur
    (fun x => if x=c then (m : ℂ) else 0)
  have he (x : ZMod q) : (residueDensity hmq c x : ℂ) =
      if ZMod.castHom hmq (ZMod m) x=c then (m : ℂ) else 0 := by
    unfold residueDensity
    split_ifs <;> simp
  simp_rw [he]
  change (𝔼 x : ZMod q, if ZMod.castHom hmq (ZMod m) x=c then (m : ℂ) else 0)=
    (𝔼 x : ZMod m, if x=c then (m : ℂ) else 0) at h
  have hm : (m : ℂ)≠0 := by exact_mod_cast NeZero.ne m
  simpa only [expect_eq_sum_div_card, sum_ite_eq', mem_univ, ite_true, card_univ,
    ZMod.card, div_self hm] using h

lemma residueDensity_self (m : ℕ) [NeZero m] (c x : ZMod m) :
    residueDensity (dvd_refl m) c x = if x=c then (m : ℝ) else 0 := by
  have he : ZMod.castHom (dvd_refl m) (ZMod m)=RingHom.id (ZMod m) := Subsingleton.elim _ _
  simp only [residueDensity,he,RingHom.id_apply]

lemma residueDensity_self_quadratic (m : ℕ) [NeZero m] (c : ZMod m)
    (ψ : AddChar (ZMod m) ℂ) :
    (𝔼 x : ZMod m, (residueDensity (dvd_refl m) c x : ℂ)*ψ (x^2))=ψ (c^2) := by
  classical
  have he (x : ZMod m) : (residueDensity (dvd_refl m) c x : ℂ)*ψ (x^2)=
      if x=c then (m : ℂ)*ψ (c^2) else 0 := by
    rw [residueDensity_self]
    split_ifs with hx
    · rw [hx]; simp
    · simp
  simp_rw [he]
  simp only [expect_eq_sum_div_card,sum_ite_eq',mem_univ,ite_true,card_univ,ZMod.card]
  have hm : (m : ℂ)≠0 := by exact_mod_cast NeZero.ne m
  field_simp

lemma residueDensity_quadratic_zero {p k : ℕ} [NeZero p] [NeZero k]
    (hpk : p∣k) (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive)
    (c : ZMod p) (hc : (2 : ZMod p)*c≠0) :
    (𝔼 x : ZMod (p*k), (residueDensity (dvd_mul_right p k) c x : ℂ)*ψ (x^2))=0 := by
  have he (x : ZMod (p*k)) : (residueDensity (dvd_mul_right p k) c x : ℂ)=
      if ZMod.castHom (dvd_mul_right p k) (ZMod p) x=c then (p : ℂ) else 0 := by
    unfold residueDensity
    split_ifs <;> simp
  simp_rw [he]
  exact fiber_gauss_zero_char hpk ψ hψ c hc

lemma zmod_cast_comp {a b c : ℕ} (hab : a∣b) (hbc : b∣c) :
    (ZMod.castHom hab (ZMod a)).comp (ZMod.castHom hbc (ZMod b)) =
      ZMod.castHom (hab.trans hbc) (ZMod a) := Subsingleton.elim _ _

lemma odd_square_eight (x : ZMod 8)
    (hx : ZMod.castHom (by norm_num : 2∣8) (ZMod 2) x=1) : x^2=1 := by
  revert x
  decide

lemma odd_square_of_dvd_eight {q : ℕ} [NeZero q] (h2 : 2∣q) (h8 : q∣8)
    (x : ZMod q) (hx : ZMod.castHom h2 (ZMod 2) x=1) : x^2=1 := by
  obtain ⟨z,rfl⟩ := ZMod.ringHom_surjective (ZMod.castHom h8 (ZMod q)) x
  have hz : ZMod.castHom (h2.trans h8) (ZMod 2) z=1 := by
    rw [← zmod_cast_comp h2 h8]
    exact hx
  have h := congrArg (ZMod.castHom h8 (ZMod q)) (odd_square_eight z hz)
  simpa only [map_pow,map_one] using h

lemma odd_root_quadratic_small {q : ℕ} [NeZero q] (h2 : 2∣q) (h8 : q∣8)
    (ψ : AddChar (ZMod q) ℂ) :
    (𝔼 x : ZMod q, (residueDensity h2 1 x : ℂ)*ψ (x^2))=ψ 1 := by
  have he (x : ZMod q) : (residueDensity h2 1 x : ℂ)*ψ (x^2)=
      (residueDensity h2 1 x : ℂ)*ψ 1 := by
    by_cases hx : ZMod.castHom h2 (ZMod 2) x=1
    · rw [odd_square_of_dvd_eight h2 h8 x hx]
    · simp only [residueDensity,ite_eq_right hx,Complex.ofReal_zero,zero_mul]
  simp_rw [he]
  rw [← expect_mul,residueDensity_mean,one_mul]

lemma unit_four_iff_odd (x : ZMod 4) :
    IsUnit x ↔ ZMod.castHom (by norm_num : 2∣4) (ZMod 2) x=1 := by
  revert x
  decide

lemma odd_root_quadratic_large {k : ℕ} [NeZero k] (hk : 4∣k)
    (ψ : AddChar (ZMod (4*k)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (4*k),
      (residueDensity ((by norm_num : 2∣4).trans (dvd_mul_right 4 k)) 1 x : ℂ)*ψ (x^2))=0 := by
  classical
  have he (x : ZMod (4*k)) :
      (residueDensity ((by norm_num : 2∣4).trans (dvd_mul_right 4 k)) 1 x : ℂ)=
      2*(if IsUnit (ZMod.castHom (dvd_mul_right 4 k) (ZMod 4) x) then (1 : ℂ) else 0) := by
    simp only [unit_four_iff_odd]
    have hc := DFunLike.congr_fun (zmod_cast_comp (by norm_num : 2∣4) (dvd_mul_right 4 k)) x
    change ZMod.castHom (by norm_num : 2∣4) (ZMod 2)
      (ZMod.castHom (dvd_mul_right 4 k) (ZMod 4) x)=_ at hc
    rw [hc]
    unfold residueDensity
    split_ifs <;> norm_num
  simp_rw [he,mul_assoc]
  rw [← mul_expect,two_unit_gauss_zero_char hk ψ hψ,mul_zero]

noncomputable def localSieveTerm {I : Type*} [DecidableEq I]
    (S : Finset I) (a b : I → ℂ) (T : Finset I) : ℂ :=
  (-1)^T.card*(∏i∈S\T, a i)*∏i∈T, b i

noncomputable def truncatedSieveMean {I : Type*} [DecidableEq I]
    (S : Finset I) (p : I → ℕ) (H : ℝ) (a b : I → ℂ) : ℂ :=
  ∑T∈S.powerset, if ((∏i∈T, p i : ℕ) : ℝ)≤H then localSieveTerm S a b T else 0

lemma localSieveTerm_norm {I : Type*} [DecidableEq I]
    (S T : Finset I) (hTS : T⊆S) (a b : I → ℂ) (k : I → ℝ)
    (ha : ∀i∈S, ‖a i‖≤k i) (hb : ∀i∈S, ‖b i‖≤k i) :
    ‖localSieveTerm S a b T‖≤∏i∈S, k i := by
  have hk (i : I) (hi : i∈S) : 0≤k i := (norm_nonneg _).trans (ha i hi)
  simp only [localSieveTerm,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_prod]
  calc
    _ ≤ (∏i∈S\T, k i)*(∏i∈T, k i) := by
      apply mul_le_mul
      · exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i hi => ha i (mem_sdiff.mp hi).1)
      · exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i hi => hb i (hTS hi))
      · exact prod_nonneg (fun _ _ => norm_nonneg _)
      · exact prod_nonneg (fun i hi => hk i (mem_sdiff.mp hi).1)
    _ = _ := prod_sdiff hTS

end SquareDifference
end LiftTheory
end

end OAI
