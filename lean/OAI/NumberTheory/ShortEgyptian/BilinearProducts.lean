import OAI.NumberTheory.ShortEgyptian.SamplePartitions

namespace OAI

universe uJ uK uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma character_ratio_eq {u q : ℕ} [NeZero u] [NeZero q] (k c n : ℕ)
    (hcross : k*q = c*u) :
    ZMod.stdAddChar ((k*n:ℕ) : ZMod u) = ZMod.stdAddChar ((c*n:ℕ) : ZMod q) := by
  rw [ZMod.stdAddChar_apply,ZMod.toCircle_natCast,ZMod.stdAddChar_apply,ZMod.toCircle_natCast]
  congr 1
  have hu : (u:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne u
  have hq : (q:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hh : (k:ℂ)*q = (c:ℂ)*u := by exact_mod_cast hcross
  push_cast
  field_simp
  linear_combination (n:ℂ) * hh

lemma reduced_cross (k u : ℕ) (hu : 0 < u) :
    k*(u/k.gcd u) = (k/k.gcd u)*u := by
  have hg : 0 < k.gcd u := Nat.gcd_pos_of_pos_right k hu
  have hk := Nat.mul_div_cancel' (Nat.gcd_dvd_left k u)
  have hu' := Nat.mul_div_cancel' (Nat.gcd_dvd_right k u)
  apply Nat.eq_of_mul_eq_mul_left hg
  calc
    _ = k*(k.gcd u*(u/k.gcd u)) := by ring
    _ = k*u := by rw [hu']
    _ = (k.gcd u*(k/k.gcd u))*u := by rw [hk]
    _ = _ := by ring

lemma gcd_mul_le (l v u : ℕ) (hl : 0 < l) (hu : 0 < u) :
    (l*v).gcd u ≤ l*(v.gcd u) := by
  have hpos : 0 < (l.gcd u)*(v.gcd u) :=
    Nat.mul_pos (Nat.gcd_pos_of_pos_right l hu) (Nat.gcd_pos_of_pos_right v hu)
  have hd : (l*v).gcd u ∣ (l.gcd u)*(v.gcd u) := by
    have hh := gcd_mul_dvd_mul_gcd u l v
    change Nat.gcd u (l*v) ∣ Nat.gcd u l * Nat.gcd u v at hh
    simpa only [Nat.gcd_comm] using hh
  exact (Nat.le_of_dvd hpos hd).trans (Nat.mul_le_mul_right _ (Nat.gcd_le_left u hl))

lemma fixed_prime_bilinear {J : Type uJ} {K : Type uK} {A : Type uA} [Fintype J] [Fintype K] [Fintype A] [Nonempty A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (u l v : ℕ) [NeZero u] (hu : 0 < u) (hl : 0 < l) (hcard : Fintype.card K = Fintype.card J)
    (Q G B : ℝ) (hG : 0 < G) (hB : 0 ≤ B)
    (hgcd : (v.gcd u:ℝ) ≤ G) (hscale : (l:ℝ)*G*Q ≤ u)
    (hprod : ∀ f : J → A, (∏ j, p (f j):ℕ) < Q)
    (hprodK : ∀ f : K → A, (∏ j, p (f j):ℕ) < Q)
    (hatom : (Fintype.card J:ℝ)^Fintype.card J/(Fintype.card A:ℝ)^Fintype.card J ≤ B) :
    ‖𝔼 f : J → A, 𝔼 g : K → A,
      ZMod.stdAddChar (((l*v)*((∏ j, p (f j))*(∏ j, p (g j))):ℕ):ZMod u)‖ ≤ Real.sqrt u*B := by
  let d := (l*v).gcd u
  let q := u/d
  have hd : 0 < d := Nat.gcd_pos_of_pos_right _ hu
  have hq : 0 < q := Nat.div_gcd_pos_of_pos_right (l*v) hu
  let : NeZero q := ⟨hq.ne'⟩
  have hdu : d*q = u := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hdb : (d:ℝ) ≤ (l:ℝ)*G := by
    calc
      _ ≤ (l:ℝ)*(v.gcd u:ℝ) := by exact_mod_cast gcd_mul_le l v u hl hu
      _ ≤ _ := mul_le_mul_of_nonneg_left hgcd (Nat.cast_nonneg l)
  have hqu : (Q:ℝ) ≤ q := by
    have hduR : (d:ℝ)*(q:ℝ) = u := by exact_mod_cast hdu
    have hmult := mul_le_mul_of_nonneg_right hdb (Nat.cast_nonneg q)
    have hpos : 0 < (l:ℝ)*G := mul_pos (by exact_mod_cast hl) hG
    nlinarith
  let c : (ZMod q)ˣ := ZMod.unitOfCoprime ((l*v)/d) (Nat.coprime_div_gcd_div_gcd hd)
  have hpJ : ∀ f : J → A, ∏ j, p (f j) < q := by
    intro f
    exact_mod_cast (hprod f).trans_le hqu
  have hpK : ∀ f : K → A, ∏ j, p (f j) < q := by
    intro f
    exact_mod_cast (hprodK f).trans_le hqu
  have heq (f : J → A) (g : K → A) :
      ZMod.stdAddChar (((l*v)*((∏ j, p (f j))*(∏ j, p (g j))):ℕ):ZMod u) =
      ZMod.stdAddChar ((c:ZMod q)*((∏ j, p (f j) : ℕ):ZMod q)*((∏ j, p (g j) : ℕ):ZMod q)) := by
    have hh := character_ratio_eq (l*v) ((l*v)/d) ((∏ j, p (f j))*(∏ j, p (g j))) (reduced_cross (l*v) u hu)
    simpa only [c,ZMod.coe_unitOfCoprime,Nat.cast_mul,mul_assoc] using hh
  simp_rw [heq]
  apply (uniform_prime_bilinear_two p hp hinj q hpJ hpK hcard c).trans
  have hqu' : (q:ℝ) ≤ u := by exact_mod_cast Nat.div_le_self u d
  calc
    _ ≤ Real.sqrt ((u:ℝ)*B^2) := by
      apply Real.sqrt_le_sqrt
      gcongr
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg u),Real.sqrt_sq hB]

lemma finset_fixed_bilinear {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (u l v : ℕ) [NeZero u] (hu : 0 < u) (hl : 0 < l) (L R : Finset J) (hcard : R.card = L.card)
    (Q G B : ℝ) (hG : 0 < G) (hB : 0 ≤ B)
    (hgcd : (v.gcd u:ℝ) ≤ G) (hscale : (l:ℝ)*G*Q ≤ u)
    (hprod : ∀ f : L → A, (∏ j,p (f j):ℕ) < Q)
    (hprodR : ∀ f : R → A, (∏ j,p (f j):ℕ) < Q)
    (hatom : (L.card:ℝ)^L.card/(Fintype.card A:ℝ)^L.card ≤ B) :
    ‖𝔼 x : L → A, 𝔼 y : R → A,
      ZMod.stdAddChar (((l*v)*((∏ j,p (x j))*(∏ j,p (y j))):ℕ):ZMod u)‖ ≤ Real.sqrt u*B := by
  have hc : Fintype.card R = Fintype.card L := by simpa only [Fintype.card_coe] using hcard
  have ha : (Fintype.card L:ℝ)^Fintype.card L/(Fintype.card A:ℝ)^Fintype.card L ≤ B := by
    simpa only [Fintype.card_coe] using hatom
  convert fixed_prime_bilinear (J := L) (K := R) p hp hinj u l v hu hl hc Q G B hG hB hgcd hscale hprod hprodR ha using 1
  congr 1
  apply expect_congr (by ext; simp)
  intro x _
  apply expect_congr (by ext; simp)
  intro y _
  rfl

end ShortEgyptian

end OAI
