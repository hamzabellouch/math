import OAI.NumberTheory.ShortEgyptian.HammingDistance

namespace OAI

universe uJ uA uE uM uK

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def mergeSamples {J : Type uJ} {A : Type uA} [Fintype J] (L R : Finset J)
    (z : ((L∪R)ᶜ : Finset J) → A) (x : L → A) (y : R → A) (j : J) : A :=
  if hj : j ∈ L then x ⟨j,hj⟩ else if hjR : j ∈ R then y ⟨j,hjR⟩ else
    z ⟨j,by simp only [mem_compl,mem_union]; tauto⟩

noncomputable def partitionSamples {J : Type uJ} {A : Type uA} [Fintype J] (L R : Finset J)
    (hdis : Disjoint L R) :
    (J → A) ≃ ((((L∪R)ᶜ : Finset J) → A) × ((L → A) × (R → A))) where
  toFun f := (fun j => f j,(fun j => f j, fun j => f j))
  invFun v := mergeSamples L R v.1 v.2.1 v.2.2
  left_inv f := by funext j; simp only [mergeSamples]; split_ifs <;> rfl
  right_inv v := by
    apply Prod.ext
    · funext j
      have hl : j.val ∉ L := by have hh := mem_compl.mp j.property; exact fun h => hh (mem_union.mpr (Or.inl h))
      have hr : j.val ∉ R := by have hh := mem_compl.mp j.property; exact fun h => hh (mem_union.mpr (Or.inr h))
      simp [mergeSamples,hl,hr]
    · apply Prod.ext
      · funext j; simp only [mergeSamples,j.property,dite_eq_left]
      · funext j
        have hl : j.val ∉ L := fun h => disjoint_left.mp hdis h j.property
        simp [mergeSamples,hl,j.property]

lemma expect_partition {J : Type uJ} {A : Type uA} {E : Type uE} [Fintype J] [Fintype A]
    [AddCommMonoid E] [Module ℚ≥0 E] (L R : Finset J) (hdis : Disjoint L R)
    (F : (J → A) → E) :
    (𝔼 f : J → A, F f) =
      𝔼 z : ((L∪R)ᶜ : Finset J) → A, 𝔼 x : L → A, 𝔼 y : R → A,
        F (mergeSamples L R z x y) := by
  let e := partitionSamples (A := A) L R hdis
  calc
    _ = 𝔼 v, F (e.symm v) := Fintype.expect_equiv e _ _ (fun f => by simp)
    _ = _ := by
      rw [show (univ : Finset ((((L∪R)ᶜ : Finset J) → A) × ((L → A) × (R → A)))) = univ ×ˢ univ by simp,expect_product]
      apply expect_congr rfl
      intro z _
      rw [show (univ : Finset ((L → A) × (R → A))) = univ ×ˢ univ by simp,expect_product]
      rfl

lemma prod_partition {J : Type uJ} {M : Type uM} [Fintype J] [CommMonoid M]
    (L R : Finset J) (hdis : Disjoint L R) (f : J → M) :
    (∏ j, f j) = (∏ j : ((L∪R)ᶜ : Finset J), f j)*(∏ j : L, f j)*(∏ j : R, f j) := by
  simp only [prod_coe_sort]
  rw [mul_assoc,← prod_union hdis]
  exact (prod_compl_mul_prod _ _).symm

lemma prod_mergeSamples {J : Type uJ} {A : Type uA} [Fintype J] (L R : Finset J) (hdis : Disjoint L R)
    (z : ((L∪R)ᶜ : Finset J) → A) (x : L → A) (y : R → A) (p : A → ℕ) :
    (∏ j, p (mergeSamples L R z x y j)) = (∏ j, p (z j))*(∏ j, p (x j))*(∏ j, p (y j)) := by
  rw [prod_partition L R hdis]
  have heq := (partitionSamples (A := A) L R hdis).apply_symm_apply (z,(x,y))
  have hz := congrArg (fun f => f.1) heq
  have hx := congrArg (fun f => f.2.1) heq
  have hy := congrArg (fun f => f.2.2) heq
  change (fun j : ((L∪R)ᶜ : Finset J) => mergeSamples L R z x y j) = z at hz
  change (fun j : L => mergeSamples L R z x y j) = x at hx
  change (fun j : R => mergeSamples L R z x y j) = y at hy
  have hz' := congrArg (fun f : ((L∪R)ᶜ : Finset J) → A => ∏ j, p (f j)) hz
  have hx' := congrArg (fun f : L → A => ∏ j, p (f j)) hx
  have hy' := congrArg (fun f : R → A => ∏ j, p (f j)) hy
  rw [hz',hx',hy']

noncomputable def normalizeSamples {J : Type uJ} {A : Type uA} (I : J → Bool) :
    ((J × Bool) → A) ≃ ((J → A) × (J → A)) where
  toFun f := (fun j => f (j,I j),fun j => f (j,!(I j)))
  invFun v jb := if jb.2 = I jb.1 then v.1 jb.1 else v.2 jb.1
  left_inv f := by funext ⟨j,b⟩; cases hj : I j <;> cases b <;> simp [hj]
  right_inv v := by
    apply Prod.ext <;> funext j <;> simp

lemma expect_normalize {J : Type uJ} {A : Type uA} {E : Type uE} [Fintype J] [Fintype A]
    [AddCommMonoid E] [Module ℚ≥0 E] (I : J → Bool) (F : ((J × Bool) → A) → E) :
    (𝔼 f, F f) = 𝔼 x : J → A, 𝔼 y : J → A,
      F (fun jb => if jb.2 = I jb.1 then x jb.1 else y jb.1) := by
  let e := normalizeSamples (A := A) I
  calc
    _ = 𝔼 v, F (e.symm v) := Fintype.expect_equiv e _ _ (fun f => by simp)
    _ = _ := by
      rw [show (univ : Finset ((J → A) × (J → A))) = univ ×ˢ univ by simp,expect_product]
      rfl

lemma uniform_prime_bilinear_two {J : Type uJ} {K : Type uK} {A : Type uA} [Fintype J] [Fintype K] [Fintype A] [Nonempty A]
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (q : ℕ) [NeZero q] (hprod : ∀ f : J → A, ∏ j, p (f j) < q)
    (hprodK : ∀ f : K → A, ∏ j, p (f j) < q) (hcard : Fintype.card K = Fintype.card J) (c : (ZMod q)ˣ) :
    ‖𝔼 f : J → A, 𝔼 g : K → A,
      ZMod.stdAddChar ((c:ZMod q)*((∏ j, p (f j) : ℕ):ZMod q)*((∏ j, p (g j) : ℕ):ZMod q))‖ ≤
      Real.sqrt ((q:ℝ)*((Fintype.card J:ℝ)^Fintype.card J/(Fintype.card A:ℝ)^Fintype.card J)^2) := by
  let F (f : J → A) : ZMod q := (∏ j, p (f j) : ℕ)
  let G (f : K → A) : ZMod q := (∏ j, p (f j) : ℕ)
  let α := finiteMass F
  let β := finiteMass G
  have heq : (𝔼 f : J → A, 𝔼 g : K → A, ZMod.stdAddChar ((c:ZMod q)*F f*G g)) =
      ∑ x : ZMod q, ∑ y : ZMod q, (α x:ℂ)*(β y:ℂ)*ZMod.stdAddChar ((c:ZMod q)*x*y) := by
    rw [finiteMass_expect F (fun x => 𝔼 g, ZMod.stdAddChar ((c:ZMod q)*x*G g))]
    apply sum_congr rfl
    intro x _
    rw [finiteMass_expect G (fun y => ZMod.stdAddChar ((c:ZMod q)*x*y))]
    simp only [α,β,mul_sum,mul_assoc]
  change ‖𝔼 f : J → A, 𝔼 g : K → A, ZMod.stdAddChar ((c:ZMod q)*F f*G g)‖ ≤ _
  rw [heq]
  simpa only [pow_two,mul_assoc] using bilinear_probability_bound c α β
    ((Fintype.card J:ℝ)^Fintype.card J/(Fintype.card A:ℝ)^Fintype.card J)
    ((Fintype.card J:ℝ)^Fintype.card J/(Fintype.card A:ℝ)^Fintype.card J)
    (finiteMass_nonneg F) (finiteMass_nonneg G) (finiteMass_sum F) (finiteMass_sum G)
    (prime_product_mod_atom p hp hinj q hprod)
    (by simpa only [hcard] using prime_product_mod_atom (J := K) p hp hinj q hprodK)

end ShortEgyptian

end OAI
