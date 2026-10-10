import OAI.Combinatorics.SquareDifference.WordReflection

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

noncomputable def affineEquiv {F : Type*} [Field F] (q a : F) (hq : q ≠ 0) : F ≃ F where
  toFun x := q^2*x+a
  invFun y := (y-a)/q^2
  left_inv x := by field_simp; ring
  right_inv y := by field_simp; ring

lemma tupleComponent_affine {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (q a : ZMod p) (hq : q ≠ 0) (F : (TupleVertex → ZMod p) → ℝ) :
    tupleComponent S (fun z => F (fun v => q^2*z v+a)) = tupleComponent S F := by
  classical
  let e : (TupleListEntry S → ZMod p) ≃ (TupleListEntry S → ZMod p) :=
    Equiv.piCongrRight fun _ => affineEquiv q a hq
  unfold tupleComponent
  let g := fun Y => 𝔼 j : TupleVertex → TupleListIndex S,
    tupleValidity S Y * tupleWeight S j * F (tupleOutput S Y j)
  have hr : (𝔼 Y, g (e Y)) = 𝔼 Y, g Y :=
    Fintype.expect_equiv e _ _ (fun _ => rfl)
  rw [← hr]
  apply expect_congr rfl
  intro Y _
  apply expect_congr rfl
  intro j _
  change _ = tupleValidity S (fun i => q^2*Y i+a) * tupleWeight S j *
    F (fun v => q^2 * tupleOutput S Y j v + a)
  rw [tupleValidity_affine S q a hq]

lemma tupleMixture_affine {p : ℕ} [Fact p.Prime]
    (q a : ZMod p) (hq : q ≠ 0) (F : (TupleVertex → ZMod p) → ℝ) :
    tupleMixture (fun z => F (fun v => q^2*z v+a)) = tupleMixture F := by
  unfold tupleMixture
  simp_rw [tupleComponent_affine _ q a hq]

lemma tupleLaw_affine {p : ℕ} [Fact p.Prime]
    (q a : ZMod p) (hq : q ≠ 0) (F : (TupleVertex → ZMod p) → ℝ) :
    tupleLaw (fun z => F (fun v => q^2*z v+a)) = tupleLaw F := by
  simp only [tupleLaw, LinearMap.smul_apply, smul_eq_mul, tupleMixtureMap_apply]
  rw [tupleMixture_affine q a hq]

lemma invariant_marginal_uniform {V G : Type*} [Nonempty G] [Fintype G] [AddGroup G]
    (L : ((V → G) → ℝ) →ₗ[ℝ] ℝ)
    (hinv : ∀ a F, L (fun z => F (fun v => z v+a))=L F)
    (v : V) (f : G → ℝ) : L (fun z => f (z v)) = L (fun _ => 1) * 𝔼 x, f x := by
  classical
  have he (z : V → G) : 𝔼 a : G, f (z v+a) = 𝔼 x, f x := by
    exact Fintype.expect_equiv (Equiv.addLeft (z v)) _ _ (fun _ => rfl)
  have hsum : (fun z : V → G => 𝔼 a : G, f (z v+a)) =
      (Fintype.card G : ℝ)⁻¹ • ∑ a : G, (fun z : V → G => f (z v+a)) := by
    ext z
    rw [Fintype.expect_eq_sum_div_card]
    simp [div_eq_mul_inv, mul_comm]
  have hlinear := congrArg L hsum
  simp only [he, map_smul, map_sum] at hlinear
  have hi (a : G) : L (fun z => f (z v+a)) = L (fun z => f (z v)) :=
    hinv a (fun z => f (z v))
  simp_rw [hi] at hlinear
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [sum_const, card_univ, nsmul_eq_mul, smul_eq_mul,
    inv_mul_cancel_left₀ hcard] at hlinear
  rw [← hlinear]
  have hc : (fun _ : V → G => 𝔼 x : G, f x) = (𝔼 x : G, f x) • (fun _ => (1 : ℝ)) := by
    ext; simp
  rw [hc, map_smul]
  simp only [smul_eq_mul, mul_comm]

lemma tupleLaw_marginal {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold ≤ (p : ℝ)) (v : TupleVertex) (f : ZMod p → ℝ) :
    tupleLaw (fun z => f (z v)) = 𝔼 x, f x := by
  have hinv (a : ZMod p) (F : (TupleVertex → ZMod p) → ℝ) :
      tupleLaw (fun z => F (fun v => z v+a))=tupleLaw F := by
    simpa only [one_pow, one_mul] using tupleLaw_affine 1 a one_ne_zero F
  rw [invariant_marginal_uniform tupleLaw hinv v f, tupleLaw_probability hp, one_mul]

lemma diagonalRoot_one {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hL : L (fun _ => 1)=1) :
    diagonalRoot L (fun _ => 1)=1 := by
  simp [diagonalRoot, diagonalIntegral, multilinearIntegral, hL]

lemma holder_mean {V X : Type*} [Fintype V] [Fintype X] [Nonempty V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hL : L (fun _ => 1)=1)
    (hm : ∀ v (f : X → ℝ), L (fun z => f (z v))=𝔼 x, f x)
    (hh : ∀ a : V → X → ℝ, |multilinearIntegral L a| ≤ ∏ v, diagonalRoot L (a v))
    (f : X → ℝ) : |𝔼 x, f x| ≤ diagonalRoot L f := by
  classical
  let v : V := Classical.choice inferInstance
  have h := hh (fun w => if w=v then f else fun _ => 1)
  have he : multilinearIntegral L (fun w => if w=v then f else fun _ => 1) = 𝔼 x, f x := by
    unfold multilinearIntegral
    simp only [ite_apply]
    rw [show (fun z : V → X => ∏ w, if w=v then f (z w) else (1 : ℝ)) =
      (fun z => f (z v)) by funext z; simp]
    exact hm v f
  rw [he] at h
  have he' : (∏ w : V, diagonalRoot L (if w=v then f else fun _ => 1))=diagonalRoot L f := by
    simp only [apply_ite, diagonalRoot_one L hL]
    simp
  rwa [he'] at h

lemma lawDensity_equiv {Ω : Type*} [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ Ω)
    (hL : ∀ F, L (fun z => F (e z))=L F) (x : Ω) :
    lawDensity L (e x)=lawDensity L x := by
  unfold lawDensity
  rw [← hL (fun y => if y=e x then 1 else 0)]
  simp only [Equiv.apply_eq_iff_eq]

lemma tensorLaw_equiv {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)] (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (e : ∀ j, X j ≃ X j)
    (hL : ∀ j F, L j (fun z => F (fun v => e j (z v)))=L j F)
    (F : (V → ∀ j, X j) → ℝ) :
    tensorLaw L (fun z => F (fun v j => e j (z v j)))=tensorLaw L F := by
  classical
  let ej (j : J) : (V → X j) ≃ (V → X j) := Equiv.piCongrRight fun _ => e j
  let E : (∀ j, V → X j) ≃ (∀ j, V → X j) := Equiv.piCongrRight ej
  have hinv (j : J) (z : V → X j) : lawDensity (L j) (ej j z)=lawDensity (L j) z :=
    lawDensity_equiv (L j) (ej j) (hL j) z
  unfold tensorLaw
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  apply Fintype.sum_equiv E _ _
  intro z
  change (∏ j, lawDensity (L j) (z j))*F (fun v j => e j (z j v)) =
    (∏ j, lawDensity (L j) (ej j (z j)))*F (fun v j => e j (z j v))
  simp only [hinv]

lemma productTupleLaw_affine {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime]
    (q a : ∀ j, ZMod (p j)) (hq : ∀ j, q j ≠ 0)
    (F : (TupleVertex → ∀ j, ZMod (p j)) → ℝ) :
    productTupleLaw p (fun z => F (fun v j => q j^2*z v j+a j))=productTupleLaw p F := by
  exact tensorLaw_equiv (fun _ => tupleLaw) (fun j => affineEquiv (q j) (a j) (hq j))
    (fun j => tupleLaw_affine (q j) (a j) (hq j)) F

lemma productTupleLaw_probability {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] (hp : ∀ j, tupleMassThreshold ≤ (p j : ℝ)) :
    productTupleLaw p (fun _ => 1)=1 :=
  tensorLaw_probability _ (fun j => tupleLaw_probability (hp j))

lemma productTupleLaw_marginal {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] (hp : ∀ j, tupleMassThreshold ≤ (p j : ℝ))
    (v : TupleVertex) (f : (∀ j, ZMod (p j)) → ℝ) :
    productTupleLaw p (fun z => f (z v)) = 𝔼 x, f x := by
  have hinv (a : ∀ j, ZMod (p j)) (F : (TupleVertex → ∀ j, ZMod (p j)) → ℝ) :
      productTupleLaw p (fun z => F (fun v => z v+a))=productTupleLaw p F := by
    change productTupleLaw p (fun z => F (fun v j => z v j+a j))=productTupleLaw p F
    simpa only [one_pow, one_mul] using
      productTupleLaw_affine p (fun _ => 1) a (fun _ => one_ne_zero) F
  rw [invariant_marginal_uniform _ hinv v f, productTupleLaw_probability p hp, one_mul]

lemma productTupleLaw_mean {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime]
    (hp : ∀ j, max tupleMassThreshold tupleReflectionThreshold ≤ (p j : ℝ))
    (f : (∀ j, ZMod (p j)) → ℝ) :
    |𝔼 x, f x| ≤ diagonalRoot (productTupleLaw p) f := by
  apply holder_mean _ (productTupleLaw_probability p (fun j => (le_max_left _ _).trans (hp j)))
    (productTupleLaw_marginal p (fun j => (le_max_left _ _).trans (hp j)))
  exact productTupleLaw_signed_holder p (fun j => (le_max_right _ _).trans (hp j))

lemma weighted_expect_cauchy {X : Type*} [Fintype X] (f k : X → ℝ)
    (hk : ∀ x, 0 ≤ k x) :
    (𝔼 x, f x*k x)^2 ≤ (𝔼 x, k x)*(𝔼 x, f x^2*k x) := by
  have hh := expect_mul_sq_le_sq_mul_sq univ (fun x => Real.sqrt (k x))
    (fun x => f x*Real.sqrt (k x))
  have he (x : X) : Real.sqrt (k x)*(f x*Real.sqrt (k x))=f x*k x := by
    rw [mul_left_comm, Real.mul_self_sqrt (hk x)]
  have he' (x : X) : (f x*Real.sqrt (k x))^2=f x^2*k x := by
    rw [mul_pow, Real.sq_sqrt (hk x)]
  simpa only [he, he', Real.sq_sqrt (hk _)] using hh

lemma weighted_expect_cauchy_le {X : Type*} [Fintype X] (f k : X → ℝ)
    (hk : ∀ x, 0 ≤ k x) (hk1 : ∀ x, k x ≤ 1) :
    (𝔼 x, f x*k x)^2 ≤ (𝔼 x, k x)*(𝔼 x, f x^2) := by
  apply (weighted_expect_cauchy f k hk).trans
  apply mul_le_mul_of_nonneg_left _ (expect_nonneg fun x _ => hk x)
  apply expect_le_expect
  intro x _
  exact mul_le_of_le_one_right (sq_nonneg _) (hk1 x)

lemma ratio_energy_pointwise (a b c F : ℝ) (ha : 0 ≤ a) (hc : 0 < c)
    (hF : 0 ≤ F) (hb : b^2 ≤ a*F) :
    b^2/a ≤ (2/c)*b^2+(4/c^2)*(a-c)^2*F := by
  have hr : b^2/a ≤ F := by
    by_cases hz : a=0
    · simp [hz, hF]
    · exact (div_le_iff₀ (lt_of_le_of_ne ha (Ne.symm hz))).mpr (by nlinarith)
  by_cases hl : c/2 ≤ a
  · have hap : 0 < a := by linarith
    have hratio : b^2/a ≤ (2/c)*b^2 := by
      apply (div_le_iff₀ hap).mpr
      have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2/c*b^2)
      have he : (2/c*b^2)*(c/2)=b^2 := by field_simp
      rw [he] at hm
      exact hm
    exact hratio.trans (le_add_of_nonneg_right (by positivity))
  · have hs : c^2 ≤ 4*(a-c)^2 := by nlinarith
    have hfrac : 1 ≤ (4/c^2)*(a-c)^2 := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ (sq_pos_of_pos hc)).mpr (by simpa using hs)
    exact hr.trans (by nlinarith [mul_nonneg (by positivity : 0 ≤ 2/c) (sq_nonneg b)])

lemma bayes_energy_bound {Y : Type*} [Fintype Y] (a b L : Y → ℝ)
    (c δ F : ℝ) (hc : 0 < c) (hF : 0 ≤ F)
    (ha : ∀ y, 0 ≤ a y) (hL : ∀ y, L y ≤ 1)
    (hpoint : ∀ y, b y^2 ≤ a y*F)
    (hb : (𝔼 y, b y^2) ≤ δ^2*F)
    (herror : (𝔼 y, (a y-c)^2) ≤ δ^2) :
    (𝔼 y, L y*(b y^2/a y)) ≤ (2/c+4/c^2)*δ^2*F := by
  calc
    _ ≤ (𝔼 y, ((2/c)*b y^2+(4/c^2)*(a y-c)^2*F)) := by
      apply expect_le_expect
      intro y _
      exact (mul_le_of_le_one_left (div_nonneg (sq_nonneg _) (ha y)) (hL y)).trans
        (ratio_energy_pointwise (a y) (b y) c F (ha y) hc hF (hpoint y))
    _ = (2/c)*(𝔼 y, b y^2)+(4/c^2)*(𝔼 y, (a y-c)^2)*F := by
      rw [expect_add_distrib]
      congr 1
      · exact (mul_expect _ _ _).symm
      · rw [show (𝔼 y, 4/c^2*(a y-c)^2*F) = (𝔼 y, 4/c^2*(a y-c)^2)*F from (expect_mul _ _ _).symm, ← mul_expect]
    _ ≤ (2/c)*(δ^2*F)+(4/c^2)*δ^2*F := by gcongr
    _ = _ := by ring

noncomputable def conditionalEnergy {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (f : X → ℝ) : ℝ :=
  𝔼 y, (𝔼 x, f x*W x y)^2/(𝔼 x, W x y)

lemma conditionalEnergy_nonneg {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (f : X → ℝ) (hW : ∀ x y, 0 ≤ W x y) :
    0 ≤ conditionalEnergy W f :=
  expect_nonneg fun y _ => div_nonneg (sq_nonneg _) (expect_nonneg fun x _ => hW x y)

lemma conditionalEnergy_le {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (f : X → ℝ) (hW : ∀ x y, 0 ≤ W x y) :
    conditionalEnergy W f ≤ 𝔼 x, f x^2*(𝔼 y, W x y) := by
  calc
    _ ≤ 𝔼 y, 𝔼 x, f x^2*W x y := by
      apply expect_le_expect
      intro y _
      have ha : 0 ≤ 𝔼 x, W x y := expect_nonneg (fun x _ => hW x y)
      have hb := weighted_expect_cauchy f (fun x => W x y) (fun x => hW x y)
      by_cases hz : (𝔼 x, W x y)=0
      · simp only [hz, div_zero]
        exact expect_nonneg fun x _ => mul_nonneg (sq_nonneg _) (hW x y)
      · exact (div_le_iff₀ (lt_of_le_of_ne ha (Ne.symm hz))).mpr (by nlinarith)
    _ = _ := by rw [expect_comm]; simp only [mul_expect]

lemma conditionalEnergy_uniform {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (f : X → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (M : ℝ) (hM : ∀ x, (𝔼 y, W x y)=M) :
    conditionalEnergy W f ≤ M*(𝔼 x, f x^2) := by
  calc
    _ ≤ 𝔼 x, f x^2*(𝔼 y, W x y) := conditionalEnergy_le W f hW
    _ = _ := by simp only [hM, ← expect_mul]; ring

lemma ratio_add_le (a b c d : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hab : a=0 → b=0) (hcd : c=0 → d=0) :
    (b+d)^2/(a+c) ≤ b^2/a+d^2/c := by
  by_cases ha0 : a=0
  · simp [ha0, hab ha0]
  by_cases hc0 : c=0
  · simp [hc0, hcd hc0]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  apply (div_le_iff₀ (add_pos hap hcp)).mpr
  have he : (b^2/a+d^2/c)*(a+c)-(b+d)^2 = (b*c-d*a)^2/(a*c) := by
    field_simp
    ring
  have hnon : 0 ≤ (b*c-d*a)^2/(a*c) := by positivity
  linarith

lemma conditionalEnergy_add_le {X Y : Type*} [Fintype X] [Fintype Y]
    (W T : X → Y → ℝ) (f : X → ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (hT : ∀ x y, 0 ≤ T x y) :
    conditionalEnergy (fun x y => W x y+T x y) f ≤
      conditionalEnergy W f+conditionalEnergy T f := by
  unfold conditionalEnergy
  rw [← expect_add_distrib]
  apply expect_le_expect
  intro y _
  simp only [mul_add, expect_add_distrib]
  apply ratio_add_le
  · exact expect_nonneg fun x _ => hW x y
  · exact expect_nonneg fun x _ => hT x y
  · intro hz
    have hb := weighted_expect_cauchy f (fun x => W x y) (fun x => hW x y)
    rw [hz, zero_mul] at hb
    nlinarith [sq_nonneg (𝔼 x, f x*W x y)]
  · intro hz
    have hb := weighted_expect_cauchy f (fun x => T x y) (fun x => hT x y)
    rw [hz, zero_mul] at hb
    nlinarith [sq_nonneg (𝔼 x, f x*T x y)]

lemma conditionalEnergy_smul {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (f : X → ℝ) (c : ℝ) :
    conditionalEnergy (fun x y => c*W x y) f = c*conditionalEnergy W f := by
  unfold conditionalEnergy
  rw [mul_expect]
  apply expect_congr rfl
  intro y _
  simp only [mul_left_comm (f _) c, ← mul_expect, mul_pow]
  by_cases hc : c=0
  · simp [hc]
  · field_simp

lemma conditionalEnergy_leading {X Y : Type*} [Fintype X] [Fintype Y]
    (K : X → Y → ℝ) (L : Y → ℝ) (f : X → ℝ)
    (c δ : ℝ) (hc : 0 < c) (hK : ∀ x y, 0 ≤ K x y)
    (hK1 : ∀ x y, K x y ≤ 1) (hL : ∀ y, L y ≤ 1)
    (hb : (𝔼 y, (𝔼 x, f x*K x y)^2) ≤ δ^2*(𝔼 x, f x^2))
    (he : (𝔼 y, ((𝔼 x, K x y)-c)^2) ≤ δ^2) :
    conditionalEnergy (fun x y => L y*K x y) f ≤
      (2/c+4/c^2)*δ^2*(𝔼 x, f x^2) := by
  have hid : conditionalEnergy (fun x y => L y*K x y) f =
      𝔼 y, L y*((𝔼 x, f x*K x y)^2/(𝔼 x, K x y)) := by
    unfold conditionalEnergy
    apply expect_congr rfl
    intro y _
    simp only [mul_left_comm (f _) (L y), ← mul_expect, mul_pow]
    by_cases hz : L y=0
    · simp [hz]
    · field_simp
  rw [hid]
  apply bayes_energy_bound _ _ L c δ (𝔼 x, f x^2) hc
    (expect_nonneg fun x _ => sq_nonneg _) _ hL _ hb he
  · intro y; exact expect_nonneg fun x _ => hK x y
  · intro y; exact weighted_expect_cauchy_le f (fun x => K x y)
      (fun x => hK x y) (fun x => hK1 x y)

lemma bilinear_l2_bound {X Y : Type*} [Fintype X] [Fintype Y]
    (K : X → Y → ℝ) (δ : ℝ) (_hδ : 0 ≤ δ)
    (h : ∀ (f : X → ℝ) (g : Y → ℝ), |𝔼 x, 𝔼 y, f x*K x y*g y| ≤
      δ*Real.sqrt (𝔼 x, f x^2)*Real.sqrt (𝔼 y, g y^2)) (f : X → ℝ) :
    (𝔼 y, (𝔼 x, f x*K x y)^2) ≤ δ^2*(𝔼 x, f x^2) := by
  let g := fun y => 𝔼 x, f x*K x y
  let A := 𝔼 y, g y^2
  let F := 𝔼 x, f x^2
  have hA : 0 ≤ A := expect_nonneg fun y _ => sq_nonneg _
  have hF : 0 ≤ F := expect_nonneg fun x _ => sq_nonneg _
  have he : (𝔼 x, 𝔼 y, f x*K x y*g y)=A := by
    rw [expect_comm]
    dsimp only [A, g]
    simp only [← expect_mul, pow_two]
  have hh := h f g
  rw [he, abs_of_nonneg hA] at hh
  change A ≤ δ^2*F
  by_cases hA0 : A=0
  · rw [hA0]; positivity
  have hAp : 0 < Real.sqrt A := Real.sqrt_pos.mpr (lt_of_le_of_ne hA (Ne.symm hA0))
  have hs : Real.sqrt A ≤ δ*Real.sqrt F := by
    have hsq := Real.sq_sqrt hA
    nlinarith
  have hs' := mul_self_le_mul_self (Real.sqrt_nonneg A) hs
  rw [← sq, ← sq, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hF] at hs'
  exact hs'

lemma list_mixing_l2 {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × J)) (dir : I → J → Bool)
    (f : (I → ZMod p) → ℝ) :
    (𝔼 y : J → ZMod p, (𝔼 x : I → ZMod p,
      f x*(listKernel E dir x y-(1/2 : ℝ)^E.card))^2) ≤
      ((32*E.card : ℝ)^((1 : ℝ)/4)*(p : ℝ)^(-(1 : ℝ)/8))^2 *
      (𝔼 x, f x^2) := by
  apply bilinear_l2_bound _ _ (by positivity)
  intro f g
  exact list_mixing hp E dir f g

lemma listKernel_nonneg {I J : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × J)) (dir : I → J → Bool) (x : I → ZMod p) (y : J → ZMod p) :
    0 ≤ listKernel E dir x y := by
  apply prod_nonneg
  intro e _
  split <;> exact squareIndicator_nonneg _

lemma listKernel_le_one {I J : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × J)) (dir : I → J → Bool) (x : I → ZMod p) (y : J → ZMod p) :
    listKernel E dir x y ≤ 1 := by
  apply prod_le_one₀
  · intro e _; split <;> exact squareIndicator_nonneg _
  · intro e _; split <;> exact squareIndicator_le_one _

lemma list_conditional_mixing {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (E : Finset (I × J)) (dir : I → J → Bool)
    (L : (J → ZMod p) → ℝ) (hL : ∀ y, L y ≤ 1)
    (f : (I → ZMod p) → ℝ) (hf : (𝔼 x, f x)=0) :
    conditionalEnergy (fun x y => L y*listKernel E dir x y) f ≤
      (2/(1/2 : ℝ)^E.card+4/((1/2 : ℝ)^E.card)^2)*
      ((32*E.card : ℝ)^((1 : ℝ)/4)*(p : ℝ)^(-(1 : ℝ)/8))^2 *
      (𝔼 x, f x^2) := by
  apply conditionalEnergy_leading (listKernel E dir) L f _ _ (by positivity)
    (listKernel_nonneg E dir) (listKernel_le_one E dir) hL
  · have he (y : J → ZMod p) :
        (𝔼 x : I → ZMod p, f x*(listKernel E dir x y-(1/2 : ℝ)^E.card)) =
        (𝔼 x, f x*listKernel E dir x y) := by
      simp only [mul_sub, expect_sub_distrib, ← expect_mul, hf, zero_mul, sub_zero]
    simpa only [he] using list_mixing_l2 hp E dir f
  · have he (y : J → ZMod p) :
        (𝔼 x : I → ZMod p, (1 : ℝ)*(listKernel E dir x y-(1/2 : ℝ)^E.card)) =
        (𝔼 x : I → ZMod p, listKernel E dir x y)-(1/2 : ℝ)^E.card := by
      simp only [one_mul, expect_sub_distrib, Fintype.expect_const]
    simpa only [he, one_pow, Fintype.expect_const, mul_one] using
      list_mixing_l2 hp E dir (fun _ => 1)

noncomputable def jointDensity {Ω X Y : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ X×Y) (x : X) (y : Y) : ℝ :=
  Fintype.card Ω * lawDensity L (e.symm (x,y))

lemma lawDensity_expect {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (F : Ω → ℝ) :
    L F = 𝔼 z, (Fintype.card Ω : ℝ)*lawDensity L z*F z := by
  rw [Fintype.expect_eq_sum_div_card]
  simp_rw [mul_assoc]
  rw [← mul_sum]
  rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  exact linearFunctional_density L F

lemma jointDensity_integral {Ω X Y : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    [Fintype X] [Fintype Y] (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ X×Y)
    (F : X → Y → ℝ) : L (fun z => F (e z).1 (e z).2) =
      𝔼 x, 𝔼 y, jointDensity L e x y*F x y := by
  rw [lawDensity_expect]
  have h := Fintype.expect_equiv e
    (fun z => (Fintype.card Ω : ℝ)*lawDensity L z*F (e z).1 (e z).2)
    (fun xy => jointDensity L e xy.1 xy.2*F xy.1 xy.2) (by intro z; simp [jointDensity])
  rw [h, ← univ_product_univ, expect_product]

lemma jointDensity_nonneg {Ω X Y : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ X×Y)
    (hL : ∀F, (∀z, 0 ≤ F z) → 0 ≤ L F) (x : X) (y : Y) :
    0 ≤ jointDensity L e x y := by
  apply mul_nonneg (Nat.cast_nonneg _) (hL _ _)
  intro z; split <;> norm_num

lemma jointDensity_marginal {Ω X Y : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    [Fintype X] [Nonempty X] [Fintype Y]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ X×Y) (m : ℝ)
    (hL : ∀f : X → ℝ, L (fun z => f (e z).1)=m*(𝔼 x, f x)) (x : X) :
    (𝔼 y, jointDensity L e x y)=m := by
  classical
  have h := jointDensity_integral L e (fun a _ => if a=x then 1 else 0)
  rw [hL (fun a => if a=x then 1 else 0)] at h
  simp only [mul_ite, mul_one, mul_zero] at h
  have he : (𝔼 a : X, if a=x then (1:ℝ) else 0)=(Fintype.card X : ℝ)⁻¹ := by
    simp
  rw [he] at h
  have he' : (𝔼 a, 𝔼 y, if a=x then jointDensity L e a y else 0)=
      (𝔼 y, jointDensity L e x y)/(Fintype.card X : ℝ) := by
    rw [expect_comm, Fintype.expect_eq_sum_div_card]
    simp only [Fintype.expect_eq_sum_div_card, sum_ite_eq', mem_univ, ite_true]
    rw [← sum_div]
    ring
  rw [he'] at h
  have hc : (Fintype.card X : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp at h
  nlinarith

lemma jointDensity_uniform {Ω X Y : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ X×Y) (w : Ω → ℝ)
    (hL : ∀F, L F=𝔼 z, w z*F z) (x : X) (y : Y) :
    jointDensity L e x y=w (e.symm (x,y)) := by
  unfold jointDensity lawDensity
  rw [hL, Fintype.expect_eq_sum_div_card]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

lemma conditionalEnergy_equiv {X X' Y Y' : Type*}
    [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
    (e : X ≃ X') (d : Y ≃ Y') (W : X' → Y' → ℝ) (f : X' → ℝ) :
    conditionalEnergy (fun x y => W (e x) (d y)) (fun x => f (e x))=
      conditionalEnergy W f := by
  unfold conditionalEnergy
  have hb y : (𝔼 x, f (e x)*W (e x) y)=(𝔼 x, f x*W x y) :=
    Fintype.expect_equiv e _ _ (fun _ => rfl)
  have ha y : (𝔼 x, W (e x) y)=(𝔼 x, W x y) :=
    Fintype.expect_equiv e _ _ (fun _ => rfl)
  simp only [hb, ha]
  exact Fintype.expect_equiv d _ _ (fun _ => rfl)

noncomputable def splitIndex {V : Type*} [DecidableEq V] (v : V) :
    Unit ⊕ {w : V // w≠v} ≃ V where
  toFun := Sum.elim (fun _ => v) Subtype.val
  invFun w := if h : w=v then Sum.inl () else Sum.inr ⟨w,h⟩
  left_inv i := by cases i with
    | inl i => cases i; simp
    | inr i => simp [i.property]
  right_inv w := by by_cases h : w=v <;> simp [h]

noncomputable def crossEdges {I J : Type*} [Fintype I] [Fintype J]
    (E : Finset ((I⊕J)×(I⊕J))) : Finset (I×J) :=
  univ.filter fun e => (Sum.inl e.1,Sum.inr e.2)∈E ∨ (Sum.inr e.2,Sum.inl e.1)∈E

noncomputable def crossDir {I J : Type*} (E : Finset ((I⊕J)×(I⊕J)))
    (i : I) (j : J) : Bool := decide ((Sum.inl i,Sum.inr j)∈E)

end SquareDifference
end

end OAI
