import OAI.NumberTheory.ShortEgyptian.ProductCorrelations

namespace OAI

universe uJ uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma random_lengths (S V : ℝ) (hlog : 1 ≤ Real.log S) (hS : 200*Real.log S ≤ S)
    (hV : 100000*Real.log S ≤ V) (hVS : V ≤ S) :
    let m := ⌊S/Real.log S⌋₊
    let s := ⌊3*V/(400*Real.log S)⌋₊
    S/(2*Real.log S) ≤ (m:ℝ) ∧ (m:ℝ) ≤ S ∧
      V/(140*Real.log S) ≤ (s:ℝ) ∧ (s:ℝ) ≤ 3*V/(400*Real.log S) ∧
      8*s ≤ m ∧ (s:ℝ) ≤ S ∧ 100 ≤ min (m:ℝ) V := by
  have hL : 0 < Real.log S := by linarith
  have hSpos : 0 < S := by linarith
  have hVpos : 0 < V := by linarith
  dsimp only
  have hmU := Nat.floor_le (div_nonneg hSpos.le hL.le)
  have hmL := Nat.sub_one_lt_floor (S/Real.log S)
  have hsU := Nat.floor_le (div_nonneg (by positivity : 0 ≤ 3*V) (by positivity : 0 ≤ 400*Real.log S))
  have hsL := Nat.sub_one_lt_floor (3*V/(400*Real.log S))
  have h200 : 200 ≤ S/Real.log S := (le_div_iff₀ hL).mpr hS
  have hm : S/(2*Real.log S) ≤ (⌊S/Real.log S⌋₊:ℝ) := by
    have heq : S/(2*Real.log S) = (S/Real.log S)/2 := by ring
    rw [heq]
    linarith
  have hs : V/(140*Real.log S) ≤ (⌊3*V/(400*Real.log S)⌋₊:ℝ) := by
    have hr : 100000 ≤ V/Real.log S := (le_div_iff₀ hL).mpr hV
    have heq : 3*V/(400*Real.log S) = (3/400)*(V/Real.log S) := by ring
    have heq' : V/(140*Real.log S) = (1/140)*(V/Real.log S) := by ring
    nth_rw 1 [heq] at hsL
    rw [heq']
    linarith
  have hmS : (⌊S/Real.log S⌋₊:ℝ) ≤ S := hmU.trans ((div_le_self hSpos.le hlog))
  have h8 : 8*(⌊3*V/(400*Real.log S)⌋₊:ℝ) ≤ (⌊S/Real.log S⌋₊:ℝ) := by
    have hh : 8*(3*V/(400*Real.log S)) ≤ S/(2*Real.log S) := by
      rw [←mul_div_assoc]
      apply (div_le_div_iff₀ (by positivity : 0 < 400*Real.log S) (by positivity : 0 < 2*Real.log S)).mpr
      nlinarith
    exact (mul_le_mul_of_nonneg_left hsU (by norm_num)).trans (hh.trans hm)
  refine ⟨hm,hmS,hs,hsU,by exact_mod_cast h8,?_,?_⟩
  · linarith
  · apply le_min
    · have heq : S/(2*Real.log S) = (S/Real.log S)/2 := by ring
      rw [heq] at hm
      linarith
    · linarith

lemma random_fresh_bound {J : Type uJ} {A : Type uA} [Fintype J]
    (p : A → ℕ) (S V : ℝ) (hS : 2 ≤ S) (hV : 0 < V)
    (hmax : ∀ a, (p a:ℝ) ≤ 2*S^100)
    (hs : (Fintype.card J:ℝ) ≤ 3*V/(400*Real.log S)) (f : J → A) :
    (∏ j,p (f j):ℕ) < Real.exp (4/5*V) := by
  have hSpos : 0 < S := by linarith
  have hL : 0 < Real.log S := Real.log_pos (by linarith)
  have hmax' (a : A) : (p a:ℝ) ≤ S^101 := by
    calc
      _ ≤ 2*S^100 := hmax a
      _ ≤ S*S^100 := mul_le_mul_of_nonneg_right hS (by positivity)
      _ = _ := by ring
  have hprod : ((∏ j,p (f j):ℕ):ℝ) ≤ (S^101)^Fintype.card J := by
    push_cast
    calc
      _ ≤ ∏ _j : J, S^101 := prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => hmax' (f j))
      _ = _ := by simp
  have hExp : (S^101)^Fintype.card J = Real.exp ((Fintype.card J:ℝ)*101*Real.log S) := by
    calc
      _ = Real.exp (Real.log ((S^101)^Fintype.card J)) := (Real.exp_log (by positivity)).symm
      _ = _ := by rw [Real.log_pow,Real.log_pow]; congr 1; ring
  apply hprod.trans_lt
  rw [hExp]
  apply Real.exp_lt_exp.mpr
  have hh := (le_div_iff₀ (by positivity : 0 < 400*Real.log S)).mp hs
  nlinarith

lemma random_atom_bound (S V P : ℝ) (s : ℕ) (hS : 2 ≤ S)
    (hP : S^99 ≤ P) (hsS : (s:ℝ) ≤ S) (hs : V/(140*Real.log S) ≤ (s:ℝ)) :
    (s:ℝ)^s/P^s ≤ Real.exp (-(7/10:ℝ)*V) := by
  have hSpos : 0 < S := by linarith
  have hL : 0 < Real.log S := Real.log_pos (by linarith)
  have hPpos : 0 < P := (pow_pos hSpos 99).trans_le hP
  have hratio : (s:ℝ)/P ≤ S/S^99 :=
    div_le_div₀ hSpos.le hsS (pow_pos hSpos 99) hP
  have heq : S/S^99 = Real.exp (-98*Real.log S) := by
    calc
      _ = Real.exp (Real.log S)/Real.exp (99*Real.log S) := by
        congr 1
        · exact (Real.exp_log hSpos).symm
        · rw [show (99:ℝ) = (99:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hSpos]
      _ = Real.exp (Real.log S-99*Real.log S) := (Real.exp_sub _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = ((s:ℝ)/P)^s := (div_pow _ _ _).symm
    _ ≤ (S/S^99)^s := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg s) hPpos.le) hratio s
    _ = Real.exp ((s:ℝ)*(-98*Real.log S)) := by rw [heq,Real.exp_nat_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := (div_le_iff₀ (by positivity : 0 < 140*Real.log S)).mp hs
      nlinarith

lemma random_gcd_exponent (S M : ℝ) (hS : 2 ≤ S) (hMS : M ≤ S) :
    M*(2/S^98)*(S^101)^(3/4:ℝ) ≤ 1 := by
  have hSpos : 0 < S := by linarith
  have hh : (S^101)^(3/4:ℝ) ≤ S^76 := by
    rw [←Real.rpow_natCast_mul hSpos.le]
    apply (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ S) (by norm_num : (101:ℝ)*(3/4) ≤ 76)).trans_eq
    exact Real.rpow_natCast S 76
  have hp : S^21 ≥ 2 := by
    calc
      _ ≥ S^1 := pow_le_pow_right₀ (by linarith : 1 ≤ S) (by norm_num : 1 ≤ 21)
      _ ≥ 2 := by simpa using hS
  calc
    _ ≤ S*(2/S^98)*S^76 := by gcongr
    _ = 2/S^21 := by field_simp
    _ ≤ 1 := (div_le_one (pow_pos hSpos 21)).mpr hp

lemma random_error_sum (m V : ℝ) (hw : 100 ≤ min m V) :
    Real.exp (-m/16)+Real.exp (-(1/20:ℝ)*V)+Real.exp (-(1/5:ℝ)*V) ≤
      Real.exp (-(1/100:ℝ)*min m V) := by
  let w := min m V
  have hm : w ≤ m := min_le_left _ _
  have hV : w ≤ V := min_le_right _ _
  have hw0 : 0 ≤ w := by dsimp [w]; linarith
  have h1 : Real.exp (-m/16) ≤ Real.exp (-(1/20:ℝ)*w) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(1/20:ℝ)*V) ≤ Real.exp (-(1/20:ℝ)*w) := Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (-(1/5:ℝ)*V) ≤ Real.exp (-(1/20:ℝ)*w) := Real.exp_le_exp.mpr (by linarith)
  have h4 : (3:ℝ) ≤ Real.exp ((1/25:ℝ)*w) := by
    have hh := Real.add_one_le_exp ((1/25:ℝ)*w)
    dsimp [w] at *
    linarith
  calc
    _ ≤ 3*Real.exp (-(1/20:ℝ)*w) := by linarith
    _ ≤ Real.exp ((1/25:ℝ)*w)*Real.exp (-(1/20:ℝ)*w) := mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add]; congr 1; dsimp [w]; ring
lemma random_hit_bound {A : Type uA} [Fintype A] [Nonempty A]
    (S : ℝ) (hS : 0 < S) (p : A → ℕ) (hp : ∀ a, (p a).Prime)
    (hinj : Function.Injective p) (hP : S^99 ≤ (Fintype.card A:ℝ))
    (u : ℕ) (hu : 0 < u) (hVS : Real.log u ≤ S) :
    (𝔼 a, if p a ∣ u then (1:ℝ) else 0) ≤ 2/S^98 := by
  have hPpos : 0 < (Fintype.card A:ℝ) := (pow_pos hS 99).trans_le hP
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hVb : Real.log u/Real.log 2 ≤ 2*S := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))).mpr
    nlinarith
  calc
    _ ≤ (Real.log u/Real.log 2)/(Fintype.card A:ℝ) := prime_hit_probability p hp hinj u hu.ne'
    _ ≤ (2*S)/(Fintype.card A:ℝ) := div_le_div_of_nonneg_right hVb hPpos.le
    _ ≤ 2*S/S^99 := div_le_div_of_nonneg_left (by positivity) (pow_pos hS 99) hP
    _ = _ := by field_simp

lemma random_outside_moment {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (S : ℝ) (hS : 2 ≤ S) (hcount : (Fintype.card J:ℝ) ≤ S)
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (hmax : ∀ a, (p a:ℝ) ≤ 2*S^100) (hP : S^99 ≤ (Fintype.card A:ℝ))
    (u : ℕ) (hu : 0 < u) (hVS : Real.log u ≤ S) :
    (𝔼 f : J → A, (Nat.gcd (∏ j,p (f j)) u:ℝ)^(3/4:ℝ)) ≤ Real.exp 1 := by
  have hSpos : 0 < S := by linarith
  have hmax' (a : A) : (p a:ℝ) ≤ S^101 := by
    calc
      _ ≤ 2*S^100 := hmax a
      _ ≤ S*S^100 := mul_le_mul_of_nonneg_right hS (by positivity)
      _ = _ := by ring
  have hhit := random_hit_bound S hSpos p hp hinj hP u hu hVS
  apply (gcd_product_moment p hp u (S^101) (2/S^98) (3/4) (by positivity) (by norm_num)
    (by positivity) hmax' hhit).trans
  exact Real.exp_le_exp.mpr (random_gcd_exponent S _ hS hcount)

lemma random_reduced_scale (u l : ℕ) (hu : 0 < u) (hV : 0 ≤ Real.log u)
    (hlmax : (l:ℝ) ≤ Real.exp ((1/200:ℝ)*Real.log u)) :
    (l:ℝ)*Real.exp (Real.log u/10)*Real.exp (4/5*Real.log u) ≤ u := by
  have huR : 0 < (u:ℝ) := by exact_mod_cast hu
  calc
    _ ≤ Real.exp ((1/200:ℝ)*Real.log u)*Real.exp (Real.log u/10)*Real.exp (4/5*Real.log u) := by gcongr
    _ = Real.exp ((181/200:ℝ)*Real.log u) := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (Real.log u) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := Real.exp_log huR

lemma random_pair_scalar (u : ℕ) (hV : 40 ≤ Real.log u) :
    Real.exp 1/(Real.exp (Real.log u/10))^(3/4:ℝ)+
      Real.sqrt u*Real.exp (-(7/10:ℝ)*Real.log u) ≤
      Real.exp (-(1/20:ℝ)*Real.log u)+Real.exp (-(1/5:ℝ)*Real.log u) := by
  have huR : 0 < (u:ℝ) := by
    contrapose! hV
    have hh : u = 0 := by exact_mod_cast (le_antisymm hV (Nat.cast_nonneg u))
    simp [hh]
  apply add_le_add
  · rw [←Real.exp_mul,←Real.exp_sub]
    apply Real.exp_le_exp.mpr
    nlinarith
  · rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos huR,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    norm_num
    ring_nf
    rfl

end ShortEgyptian

end OAI
