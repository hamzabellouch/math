import OAI.Combinatorics.SquareDifference.TupleWeights

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open Finset

lemma patch_insert_update {J : Type*} [DecidableEq J] {X : J → Type*}
    (s : Finset J) (j : J) (_hj : j∉s) (x y : ∀ j, X j) (t : X j) :
    patch (insert j s) x (Function.update y j t)=Function.update (patch s x y) j t := by
  ext k
  by_cases hk : k=j
  · subst k; simp [patch]
  · simp [patch, hk]

noncomputable def partialOp {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)]
    (K : ∀ j, Matrix (X j) (X j) ℝ) (s : Finset J)
    (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) : ℝ :=
  𝔼 y : ∀ j, X j, (∏ j ∈ s, K j (x j) (y j))*f (patch s x y)

lemma partialOp_empty {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    (K : ∀ j, Matrix (X j) (X j) ℝ) (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    partialOp K ∅ f x=f x := by simp [partialOp, patch_empty]

lemma partialOp_smul {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)]
    (K : ∀ j, Matrix (X j) (X j) ℝ) (s : Finset J)
    (f : (∀ j, X j) → ℝ) (c : ℝ) (x : ∀ j, X j) :
    partialOp K s (fun y => c*f y) x=c*partialOp K s f x := by
  simp only [partialOp, mul_left_comm _ c, ← mul_expect]

lemma partialOp_insert {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    (K : ∀ j, Matrix (X j) (X j) ℝ) (s : Finset J) (j : J) (hj : j∉s)
    (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    partialOp K (insert j s) f x=partialOp K s (coordOp K j f) x := by
  unfold partialOp
  rw [← expect_update_dep j (fun y : ∀ j, X j =>
    (∏ k ∈ insert j s, K k (x k) (y k))*f (patch (insert j s) x y))]
  apply expect_congr rfl
  intro y _
  unfold coordOp
  rw [mul_expect]
  apply expect_congr rfl
  intro t _
  have hp : (∏ k ∈ s, K k (x k) (Function.update y j t k))=
      ∏ k ∈ s, K k (x k) (y k) := by
    apply prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hj)]
  simp only [prod_insert hj, Function.update_self, hp, patch_insert_update s j hj,
    patch, ite_eq_right hj]
  ring

lemma partialOp_eigen {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    (K : ∀ j, Matrix (X j) (X j) ℝ) (lam : J → ℝ) (f : (∀ j, X j) → ℝ)
    (he : ∀ j, coordOp K j f=fun x => lam j*f x) (s : Finset J) (x : ∀ j, X j) :
    partialOp K s f x=(∏ j ∈ s, lam j)*f x := by
  induction s using Finset.induction_on with
  | empty => simp [partialOp_empty]
  | @insert j s hj ih =>
    rw [partialOp_insert K s j hj, he j, partialOp_smul, ih, prod_insert hj, mul_assoc]

lemma product_kernel_eigen {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    (K : ∀ j, Matrix (X j) (X j) ℝ) (lam : J → ℝ) (f : (∀ j, X j) → ℝ)
    (he : ∀ j, coordOp K j f=fun x => lam j*f x) (x : ∀ j, X j) :
    (𝔼 y, (∏ j, K j (x j) (y j))*f y)=(∏ j, lam j)*f x := by
  simpa only [partialOp, patch_univ] using partialOp_eigen K lam f he univ x

def ExactSupport {J : Type*} [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] (U : Finset J)
    (f : (∀ j, X j) → ℝ) : Prop :=
  (∀ j∈U, ∀ x, (𝔼 t : X j, f (Function.update x j t))=0) ∧
  (∀ j∉U, ∀ x t, f (Function.update x j t)=f x)

lemma coordOp_noise {J : Type*} [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    [∀ j, DecidableEq (X j)] (d : J → ℝ) (j : J)
    (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) :
    coordOp (fun j => noiseKernel (X := X j) (d j)) j f x =
      (1-(d j)^2)*(𝔼 t, f (Function.update x j t))+(d j)^2*f x := by
  have hn : (Fintype.card (X j) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hh : (𝔼 t : X j, (if x j=t then (1 : ℝ) else 0)*f (Function.update x j t))=
      f x/(Fintype.card (X j) : ℝ) := by
    simp [expect_eq_sum_div_card]
  unfold coordOp noiseKernel
  simp only [add_mul, expect_add_distrib, ← mul_expect, mul_assoc, hh]
  field_simp

lemma noise_product_exactSupport {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    [∀ j, DecidableEq (X j)] (d : J → ℝ) (U : Finset J)
    (f : (∀ j, X j) → ℝ) (hf : ExactSupport U f) (x : ∀ j, X j) :
    (𝔼 y, (∏ j, noiseKernel (d j) (x j) (y j))*f y)=
      (∏ j∈U, (d j)^2)*f x := by
  have he j : coordOp (fun j => noiseKernel (X := X j) (d j)) j f =
      fun x => (if j∈U then (d j)^2 else 1)*f x := by
    funext x
    rw [coordOp_noise]
    by_cases hj : j∈U
    · rw [ite_eq_left hj, hf.1 j hj x, mul_zero, zero_add]
    · simp only [ite_eq_right hj, hf.2 j hj, Fintype.expect_const]
      ring
  have hh := product_kernel_eigen (fun j => noiseKernel (X := X j) (d j))
    (fun j => if j∈U then (d j)^2 else 1) f he x
  simpa only [prod_ite_mem, univ_inter] using hh

lemma exactSupport_orthogonal {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    {U V : Finset J} (hUV : U≠V) (f g : (∀ j, X j) → ℝ)
    (hf : ExactSupport U f) (hg : ExactSupport V g) : (𝔼 x, f x*g x)=0 := by
  have hsep {U V : Finset J} (f g : (∀ j, X j) → ℝ)
      (hf : ExactSupport U f) (hg : ExactSupport V g) (j : J) (hju : j∈U) (hjv : j∉V) :
      (𝔼 x, f x*g x)=0 := by
    rw [← expect_update_dep j]
    simp only [hg.2 j hjv, ← expect_mul, hf.1 j hju, zero_mul, Fintype.expect_const]
  by_cases h : U⊆V
  · obtain ⟨j,hjv,hju⟩ := not_subset.mp (show ¬V⊆U from fun hh => hUV (Subset.antisymm h hh))
    simpa only [mul_comm] using hsep g f hg hf j hjv hju
  · obtain ⟨j,hju,hjv⟩ := not_subset.mp h
    exact hsep f g hf hg j hju hjv

lemma orthogonal_sum_square {I X : Type*} [Fintype X] [DecidableEq I]
    (s : Finset I) (f : I → X → ℝ)
    (horth : ∀ i∈s, ∀ j∈s, i≠j → (𝔼 x, f i x*f j x)=0) :
    (𝔼 x, (∑ i∈s, f i x)^2)=∑ i∈s, (𝔼 x, f i x^2) := by
  simp only [pow_two, sum_mul, mul_sum, expect_sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_eq_single i]
  · intro j hj hji
    exact horth j hj i hi hji
  · simp [hi]

lemma kernelForm_eigen_sum {I X : Type*} [Fintype X] [DecidableEq I]
    (K : Matrix X X ℝ) (s : Finset I) (f : I → X → ℝ) (lam : I → ℝ)
    (heigen : ∀ i∈s, ∀ x, (𝔼 y, K x y*f i y)=lam i*f i x)
    (horth : ∀ i∈s, ∀ j∈s, i≠j → (𝔼 x, f i x*f j x)=0) :
    kernelForm K (fun x => ∑ i∈s, f i x) (fun x => ∑ i∈s, f i x) =
      ∑ i∈s, lam i*(𝔼 x, f i x^2) := by
  have hm x : (𝔼 y, K x y*(∑ i∈s, f i y))=∑ i∈s, lam i*f i x := by
    rw [show (fun y => K x y*(∑ i∈s, f i y)) =
      (fun y => ∑ i∈s, K x y*f i y) from funext fun _ => mul_sum .., expect_sum_comm]
    exact sum_congr rfl fun i hi => heigen i hi x
  change (𝔼 x, 𝔼 y, (∑ i∈s, f i x)*K x y*(∑ i∈s, f i y))=_
  simp only [mul_assoc, ← mul_expect, hm]
  simp only [sum_mul, mul_sum, expect_sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [sum_eq_single j]
  · simp only [mul_left_comm (f j _) (lam j), ← mul_expect, pow_two]
  · intro i hi hij
    simp only [mul_left_comm (f i _) (lam j), ← mul_expect, horth i hi j hj hij, mul_zero]
  · simp [hj]

lemma noise_product_bound {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    [∀ j, DecidableEq (X j)] (d : J → ℝ) (s : Finset (Finset J))
    (f : Finset J → (∀ j, X j) → ℝ) (hf : ∀ U∈s, ExactSupport U (f U))
    (a : ℝ) (ha : ∀ U∈s, (∏ j∈U, (d j)^2) ≤ a) :
    kernelForm (fun x y => ∏ j, noiseKernel (d j) (x j) (y j))
      (fun x => ∑ U∈s, f U x) (fun x => ∑ U∈s, f U x) ≤
      a*(𝔼 x, (∑ U∈s, f U x)^2) := by
  have ho U hU V hV hUV := exactSupport_orthogonal hUV (f U) (f V) (hf U hU) (hf V hV)
  rw [kernelForm_eigen_sum _ s f (fun U => ∏ j∈U, (d j)^2)
    (fun U hU x => noise_product_exactSupport d U (f U) (hf U hU) x) ho,
    orthogonal_sum_square s f ho, mul_sum]
  exact sum_le_sum fun U hU => mul_le_mul_of_nonneg_right (ha U hU)
    (expect_nonneg fun _ _ => sq_nonneg _)

lemma expect_prod_pi {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] (f : ∀ j, X j → ℝ) :
    (𝔼 x : ∀ j, X j, ∏ j, f j (x j))=∏ j, (𝔼 t : X j, f j t) := by
  simp only [expect_eq_sum_div_card, card_univ, prod_div_distrib,
    Fintype.card_pi, Nat.cast_prod]
  rw [Fintype.prod_sum]

lemma conditionalGram_product {J : Type*} [Fintype J] [DecidableEq J]
    {X Y : J → Type*} [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
    (W : ∀ j, X j → Y j → ℝ) :
    conditionalGram (fun (x : ∀ j, X j) (y : ∀ j, Y j) => ∏ j, W j (x j) (y j)) =
      fun (x : ∀ j, X j) (x' : ∀ j, X j) => ∏ j, conditionalGram (W j) (x j) (x' j) := by
  funext x x'
  change (𝔼 y : ∀ j, Y j, (∏ j, W j (x j) (y j))*(∏ j, W j (x' j) (y j))/
    (𝔼 z : ∀ j, X j, ∏ j, W j (z j) (y j))) =
    ∏ j, (𝔼 t : Y j, W j (x j) t*W j (x' j) t/(𝔼 z : X j, W j z t))
  have hd (y : ∀ j, Y j) : (𝔼 z : ∀ j, X j, ∏ j, W j (z j) (y j)) =
      ∏ j, (𝔼 z : X j, W j z (y j)) := expect_prod_pi (fun j z => W j z (y j))
  simp only [hd, ← prod_mul_distrib, ← prod_div_distrib]
  exact expect_prod_pi (fun j t => W j (x j) t*W j (x' j) t/(𝔼 z : X j, W j z t))

lemma tensor_conditional_decay {J : Type*} [Fintype J] [DecidableEq J]
    {X Y : J → Type*} [∀ j, Fintype (X j)] [∀ j, Nonempty (X j)]
    [∀ j, DecidableEq (X j)] [∀ j, Fintype (Y j)]
    (W : ∀ j, X j → Y j → ℝ) (hW : ∀ j x y, 0 ≤ W j x y)
    (hrow : ∀ j x, (𝔼 y, W j x y)=1) (d : J → ℝ)
    (hmix : ∀ j, ∀ f : X j → ℝ, (𝔼 x, f x)=0 →
      conditionalEnergy (W j) f ≤ (d j)^2*(𝔼 x, f x^2))
    (s : Finset (Finset J)) (f : Finset J → (∀ j, X j) → ℝ)
    (hf : ∀ U∈s, ExactSupport U (f U)) (a : ℝ)
    (ha : ∀ U∈s, (∏ j∈U, (d j)^2) ≤ a) :
    conditionalEnergy (fun (x : ∀ j, X j) (y : ∀ j, Y j) => ∏ j, W j (x j) (y j)) (fun x => ∑ U∈s, f U x) ≤
      a*(𝔼 x, (∑ U∈s, f U x)^2) := by
  have hd := product_kernel_monotone
    (fun j => conditionalGram (W j)) (fun j => noiseKernel (X := X j) (d j))
    (fun j => conditionalGram_posSemidef (W j) (hW j))
    (fun j => conditionalGram_noise_domination (W j) (hW j) (hrow j) (d j) (hmix j))
  let g := fun x => ∑ U∈s, f U x
  have hd' : 0 ≤ kernelForm (fun x y =>
      (∏ j, noiseKernel (d j) (x j) (y j))-
      (∏ j, conditionalGram (W j) (x j) (y j))) g g := by
    apply (kernelForm_nonneg_iff _ ?_).mp hd g
    intro x y
    simp only [noiseKernel, eq_comm, conditionalGram_symm]
  have he : kernelForm (fun x y =>
      (∏ j, noiseKernel (d j) (x j) (y j))-
      (∏ j, conditionalGram (W j) (x j) (y j))) g g =
      kernelForm (fun x y => ∏ j, noiseKernel (d j) (x j) (y j)) g g-
      conditionalEnergy (fun (x : ∀ j, X j) (y : ∀ j, Y j) => ∏ j, W j (x j) (y j)) g := by
    rw [← kernelForm_conditionalGram, conditionalGram_product]
    unfold kernelForm
    simp only [mul_sub, sub_mul, expect_sub_distrib]
  rw [he] at hd'
  exact (sub_nonneg.mp hd').trans (noise_product_bound d s f hf a ha)

end SquareDifference

namespace SquareDifference

open Finset

lemma conditional_bilinear_sq {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (hW : ∀x y,0≤W x y) (f : X → ℝ) (g : Y → ℝ) :
    (𝔼 x, 𝔼 y, W x y*f x*g y)^2≤
      conditionalEnergy W f*(𝔼 y, (𝔼 x, W x y)*g y^2) := by
  let A : Y → ℝ := fun y => 𝔼 x, W x y
  let B : Y → ℝ := fun y => 𝔼 x, f x*W x y
  have hA y : 0≤A y := expect_nonneg (fun x _ => hW x y)
  have hB y : A y=0 → B y=0 := by
    intro hz
    have hh := weighted_expect_cauchy f (fun x => W x y) (fun x => hW x y)
    change (B y)^2≤A y*(𝔼 x, f x^2*W x y) at hh
    rw [hz,zero_mul] at hh
    exact (sq_eq_zero_iff).mp (le_antisymm hh (sq_nonneg _))
  have he y : (B y/Real.sqrt (A y))*(g y*Real.sqrt (A y))=B y*g y := by
    by_cases hz : A y=0
    · rw [hB y hz]; ring
    · have hs : Real.sqrt (A y)≠0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne (hA y) (Ne.symm hz))).ne'
      field_simp
  have hsq y : (B y/Real.sqrt (A y))^2=(B y)^2/A y := by
    rw [div_pow, Real.sq_sqrt (hA y)]
  have hsq' y : (g y*Real.sqrt (A y))^2=A y*g y^2 := by
    rw [mul_pow, Real.sq_sqrt (hA y),mul_comm]
  have hh := expect_mul_sq_le_sq_mul_sq univ (fun y => B y/Real.sqrt (A y))
    (fun y => g y*Real.sqrt (A y))
  simp only [he,hsq,hsq'] at hh
  have hi : (𝔼 x, 𝔼 y, W x y*f x*g y)=𝔼 y, B y*g y := by
    rw [expect_comm]
    simp only [B,← expect_mul,mul_comm (W _ _) (f _)]
  rw [hi]
  exact hh

lemma prod_le_average_powers {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) (hf : ∀v,0≤f v) :
    (∏v,f v)≤𝔼 v, (f v)^(Fintype.card V) := by
  have hc : (Fintype.card V:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hi v : ((f v)^(Fintype.card V))^((1:ℝ)/(Fintype.card V))=f v := by
    rw [← Real.rpow_natCast_mul (hf v),mul_one_div_cancel hc,Real.rpow_one]
  have h := Real.geom_mean_le_arith_mean_weighted univ
    (fun _ : V => (1:ℝ)/(Fintype.card V)) (fun v => (f v)^(Fintype.card V))
    (by intros; positivity) (by simp [hc]) (fun i _ => pow_nonneg (hf i) _)
  simp only [hi] at h
  convert h using 1
  rw [expect_eq_sum_div_card,card_univ,div_eq_mul_inv,sum_mul]
  apply sum_congr rfl
  intros
  ring

lemma positiveLaw_mono {Ω : Type*} (L : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀F,(∀z,0≤F z) → 0≤L F) {f g : Ω → ℝ} (hfg : ∀z,f z≤g z) :
    L f≤L g := by
  have h := hL (g-f) (fun z => sub_nonneg.mpr (hfg z))
  rw [map_sub] at h
  exact sub_nonneg.mp h

lemma positiveLaw_abs {Ω : Type*} (L : (Ω → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀F,(∀z,0≤F z) → 0≤L F) (f : Ω → ℝ) : |L f|≤L (fun z => |f z|) := by
  rw [abs_le]
  constructor
  · have h := positiveLaw_mono L hL (f:=fun z => -|f z|) (g:=f) (fun z => neg_abs_le _)
    change L (-(fun z => |f z|))≤L f at h
    rwa [map_neg] at h
  · exact positiveLaw_mono L hL (fun z => le_abs_self _)

lemma positiveLaw_product_bound {Ω V : Type*} [Fintype V] [Nonempty V]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hL : ∀F,(∀z,0≤F z) → 0≤L F)
    (f : V → Ω → ℝ) (M : ℝ)
    (hm : ∀v,L (fun z => |f v z|^(Fintype.card V))≤M) :
    |L (fun z => ∏v,f v z)|≤M := by
  calc
    _ ≤ L (fun z => |∏v,f v z|) := positiveLaw_abs L hL _
    _ ≤ L (fun z => 𝔼 v, |f v z|^(Fintype.card V)) := by
      apply positiveLaw_mono L hL
      intro z
      rw [abs_prod]
      exact prod_le_average_powers _ (fun v => abs_nonneg _)
    _ = 𝔼 v, L (fun z => |f v z|^(Fintype.card V)) := by
      simp only [expect_eq_sum_div_card,card_univ]
      have he : (fun z => (∑v, |f v z|^(Fintype.card V))/(Fintype.card V:ℝ))=
          (Fintype.card V:ℝ)⁻¹ • ∑v,(fun z => |f v z|^(Fintype.card V)) := by
        funext z
        simp only [Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
        ring
      rw [he,map_smul,map_sum]
      simp only [smul_eq_mul]
      ring
    _ ≤ M := expect_le univ_nonempty (fun v _ => hm v)

end SquareDifference

namespace SquareDifference

open Finset

lemma tensorLaw_density {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀j,Fintype (X j)]
    [∀j,DecidableEq (X j)] (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (z : V → ∀j,X j) : lawDensity (tensorLaw L) z=∏j,lawDensity (L j) (fun v => z v j) := by
  unfold lawDensity
  have he (w : V → ∀j,X j) : (if w=z then (1:ℝ) else 0)=
      ∏j,if (fun v => w v j)=(fun v => z v j) then 1 else 0 := by
    rw [prod_indicator_forall]
    congr 1
    apply propext
    constructor
    · intro h; subst w; simp
    · intro h; funext v j; exact congrFun (h j) v
  rw [show (fun w => if w=z then (1:ℝ) else 0)=
      (fun w => ∏j,if (fun v => w v j)=(fun v => z v j) then 1 else 0) from funext he]
  exact tensorLaw_fubini L (fun j w => if w=(fun v => z v j) then 1 else 0)

lemma jointDensity_tensor {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀j,Fintype (X j)]
    [∀j,DecidableEq (X j)] (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (v : V) (x : ∀j,X j) (y : {w : V // w≠v} → ∀j,X j) :
    jointDensity (tensorLaw L) (Equiv.funSplitAt v _) x y=
      ∏j,jointDensity (L j) (Equiv.funSplitAt v _) (x j) (fun w => y w j) := by
  simp only [jointDensity,tensorLaw_density]
  have hc : (Fintype.card (V → ∀j,X j):ℝ)=∏j,(Fintype.card (V → X j):ℝ) := by
    rw [Fintype.card_congr (Equiv.piComm (fun _ j => X j)), Fintype.card_pi,Nat.cast_prod]
  rw [hc,← prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  congr 2
  funext w
  simp only [Equiv.funSplitAt_symm_apply]
  split_ifs <;> rfl

lemma tensorLaw_conditional_decay {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀j,Fintype (X j)]
    [∀j,Nonempty (X j)] [∀j,DecidableEq (X j)]
    (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀j F,(∀z,0≤F z) → 0≤L j F)
    (hmarg : ∀j v (f : X j → ℝ),L j (fun z => f (z v))=𝔼 x,f x)
    (v : V) (d : J → ℝ)
    (hmix : ∀j (f : X j → ℝ),(𝔼 x,f x)=0 →
      conditionalEnergy (jointDensity (L j) (Equiv.funSplitAt v _)) f≤
        (d j)^2*(𝔼 x,f x^2))
    (s : Finset (Finset J)) (f : Finset J → (∀j,X j) → ℝ)
    (hf : ∀U∈s,ExactSupport U (f U)) (a : ℝ)
    (ha : ∀U∈s,(∏j∈U,(d j)^2)≤a) :
    conditionalEnergy (jointDensity (tensorLaw L) (Equiv.funSplitAt v _))
      (fun x => ∑U∈s,f U x)≤a*(𝔼 x,(∑U∈s,f U x)^2) := by
  let W := fun j => jointDensity (L j) (Equiv.funSplitAt v (X j))
  have h := tensor_conditional_decay W (fun j => jointDensity_nonneg (L j) _ (hL j))
    (fun j x => jointDensity_marginal (L j) _ 1
      (fun g => by simpa using hmarg j v g) x) d hmix s f hf a ha
  have he := conditionalEnergy_equiv (Equiv.refl (∀j,X j))
    (Equiv.piComm (fun (_ : {w : V // w≠v}) j => X j))
    (fun x y => ∏j,W j (x j) (y j)) (fun x => ∑U∈s,f U x)
  simp only [Equiv.refl_apply] at he
  rw [← he] at h
  convert h using 1
  congr 1
  funext x y
  exact jointDensity_tensor L v x y

end SquareDifference

namespace SquareDifference

open Finset

lemma law_slot_bilinear_sq {Ω X Y : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] [Fintype X] [Fintype Y]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (hL : ∀F,(∀z,0≤F z) → 0≤L F)
    (e : Ω ≃ X×Y) (f : X → ℝ) (g : Y → ℝ) :
    (L (fun z => f (e z).1*g (e z).2))^2≤
      conditionalEnergy (jointDensity L e) f*L (fun z => g (e z).2^2) := by
  rw [jointDensity_integral L e (fun x y => f x*g y),jointDensity_integral L e (fun _ y => g y^2)]
  have he : (𝔼 x,𝔼 y,jointDensity L e x y*g y^2)=
      𝔼 y,(𝔼 x,jointDensity L e x y)*g y^2 := by
    rw [expect_comm]
    simp only [expect_mul]
  rw [he]
  simpa only [mul_assoc] using conditional_bilinear_sq (jointDensity L e)
    (jointDensity_nonneg L e hL) f g

lemma law_slot_product_sq {V X : Type*} [Fintype V] [DecidableEq V]
    [Fintype X] [Nonempty X] [DecidableEq X] (v : V)
    [Nonempty {w : V // w≠v}]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀F,(∀z,0≤F z) → 0≤L F) (f : X → ℝ) (F : V → X → ℝ) (M : ℝ)
    (hm : ∀w : {w : V // w≠v},L (fun z => |F w (z w)|^(2*Fintype.card {w : V // w≠v}))≤M) :
    (L (fun z => f (z v)*∏w : {w : V // w≠v},F w (z w)))^2≤
      conditionalEnergy (jointDensity L (Equiv.funSplitAt v X)) f*M := by
  have hh := law_slot_bilinear_sq L hL (Equiv.funSplitAt v X) f
    (fun z => ∏w : {w : V // w≠v},F w (z w))
  change (L (fun z => f (z v)*∏w : {w : V // w≠v},F w (z w)))^2≤
    conditionalEnergy (jointDensity L (Equiv.funSplitAt v X)) f*
      L (fun z => (∏w : {w : V // w≠v},F w (z w))^2) at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (conditionalEnergy_nonneg _ f (jointDensity_nonneg L _ hL))
  have hp := positiveLaw_product_bound L hL
    (fun (w : {w : V // w≠v}) z => (F w (z w))^2) M
    (fun w => by simpa only [abs_pow,← pow_mul] using hm w)
  apply le_trans (le_abs_self _) _
  simpa only [prod_pow] using hp

end SquareDifference

namespace SquareDifference

open Finset

lemma tensorLaw_marginal {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀j,Fintype (X j)]
    [∀j,DecidableEq (X j)]
    (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ) (v : V)
    (hm : ∀j (g : X j → ℝ),L j (fun z => g (z v))=𝔼 x,g x)
    (f : (∀j,X j) → ℝ) : tensorLaw L (fun z => f (z v))=𝔼 x,f x := by
  have hd (a : ∀j,X j) : tensorLaw L (fun z => if z v=a then 1 else 0)=
      (Fintype.card (∀j,X j) : ℝ)⁻¹ := by
    have he (z : V → ∀j,X j) : (if z v=a then (1:ℝ) else 0)=
        ∏j,if z v j=a j then 1 else 0 := by
      rw [prod_indicator_forall]
      congr 1
      exact propext (funext_iff)
    simp_rw [he]
    rw [tensorLaw_fubini L (fun j z => if z v=a j then 1 else 0)]
    have hh (j : J) : L j (fun z => if z v=a j then (1:ℝ) else 0)=
        𝔼 x : X j, if x=a j then (1:ℝ) else 0 := hm j (fun x => if x=a j then 1 else 0)
    simp_rw [hh]
    simp only [expect_eq_sum_div_card,card_univ,sum_ite_eq',mem_univ,ite_true,
      one_div,← prod_inv_distrib,Fintype.card_pi,Nat.cast_prod]
  have hf : (fun z : V → ∀j,X j => f (z v))=
      ∑a : ∀j,X j, f a • (fun z => if z v=a then (1:ℝ) else 0) := by
    funext z
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_ite,mul_one,mul_zero]
    simp
  rw [hf,map_sum]
  simp only [map_smul,smul_eq_mul,hd,← sum_mul,expect_eq_sum_div_card,card_univ,div_eq_mul_inv]

lemma tensorLaw_prime_conductor_energy {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] (p : J → ℕ) [∀j,Fact (p j).Prime]
    (L : ∀j,((V → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀j F,(∀z,0≤F z) → 0≤L j F)
    (hmarg : ∀j v (f : ZMod (p j) → ℝ),L j (fun z => f (z v))=𝔼 x,f x)
    (v : V)
    (hmix : ∀j (f : ZMod (p j) → ℝ),(𝔼 x,f x)=0 →
      conditionalEnergy (jointDensity (L j) (Equiv.funSplitAt v _)) f≤
        (p j : ℝ)^(-(1:ℝ)/32)*(𝔼 x,f x^2))
    (s : Finset (Finset J)) (f : Finset J → (∀j,ZMod (p j)) → ℝ)
    (hf : ∀U∈s,ExactSupport U (f U)) (T : ℝ) (hT : 0<T)
    (hden : ∀U∈s,T≤(∏j∈U,p j : ℝ)) :
    conditionalEnergy (jointDensity (tensorLaw L) (Equiv.funSplitAt v _))
      (fun x => ∑U∈s,f U x)≤T^(-(1:ℝ)/32)*(𝔼 x,(∑U∈s,f U x)^2) := by
  have hm' (j : J) (g : ZMod (p j) → ℝ) (hg : (𝔼 x,g x)=0) :
      conditionalEnergy (jointDensity (L j) (Equiv.funSplitAt v _)) g≤
        (Real.sqrt ((p j : ℝ)^(-(1:ℝ)/32)))^2*(𝔼 x,g x^2) := by
    simpa only [Real.sq_sqrt (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using hmix j g hg
  apply tensorLaw_conditional_decay L hL hmarg v
    (fun j => Real.sqrt ((p j : ℝ)^(-(1:ℝ)/32))) hm' s f hf
  intro U hU
  simp only [Real.sq_sqrt (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  rw [Real.finsetProd_rpow U (fun j => (p j : ℝ)) (fun _ _ => Nat.cast_nonneg _) _]
  exact Real.rpow_le_rpow_of_nonpos hT (hden U hU) (by norm_num)

lemma tupleGoodTensor_conductor_energy {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀j,Fact (p j).Prime]
    (hp : ∀j, max tupleMassThreshold tupleConditionalThreshold≤(p j : ℝ))
    (v : TupleVertex) (s : Finset (Finset J))
    (f : Finset J → (∀j,ZMod (p j)) → ℝ) (hf : ∀U∈s,ExactSupport U (f U))
    (T : ℝ) (hT : 0<T) (hden : ∀U∈s,T≤(∏j∈U,p j : ℝ)) :
    conditionalEnergy (jointDensity (tensorLaw (fun j => tupleGoodLaw (p:=p j)))
      (Equiv.funSplitAt v _)) (fun x => ∑U∈s,f U x)≤
      T^(-(1:ℝ)/32)*(𝔼 x,(∑U∈s,f U x)^2) := by
  apply tensorLaw_prime_conductor_energy p (fun j => tupleGoodLaw (p:=p j))
    (fun _ => tupleGoodLaw_nonneg)
    (fun j => tupleGoodLaw_marginal ((le_max_left _ _).trans (hp j))) v
    (fun j => tupleGoodLaw_conditional ((le_max_right _ _).trans (hp j)) v) s f hf T hT hden

lemma tupleTensor_conductor_energy {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀j,Fact (p j).Prime]
    (hp : ∀j, max tupleMassThreshold tupleConditionalThreshold≤(p j : ℝ))
    (v : TupleVertex) (s : Finset (Finset J))
    (f : Finset J → (∀j,ZMod (p j)) → ℝ) (hf : ∀U∈s,ExactSupport U (f U))
    (T : ℝ) (hT : 0<T) (hden : ∀U∈s,T≤(∏j∈U,p j : ℝ)) :
    conditionalEnergy (jointDensity (productTupleLaw p) (Equiv.funSplitAt v _))
      (fun x => ∑U∈s,f U x)≤T^(-(1:ℝ)/32)*(𝔼 x,(∑U∈s,f U x)^2) := by
  apply tensorLaw_prime_conductor_energy p (fun j => tupleLaw (p:=p j))
    (fun _ => tupleLaw_nonneg)
    (fun j => tupleLaw_marginal ((le_max_left _ _).trans (hp j))) v
    (fun j => tupleLaw_conditional ((le_max_right _ _).trans (hp j)) v) s f hf T hT hden

end SquareDifference

end

end OAI
