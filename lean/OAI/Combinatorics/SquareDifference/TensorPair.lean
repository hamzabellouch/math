import OAI.Combinatorics.SquareDifference.TensorLaw

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

section TensorPair

variable {J V : Type*} [Fintype J] [instDecidableEqJ : DecidableEq J] [Fintype V] [DecidableEq V]
  {X Ω : J → Type*} [instFintypeXj : ∀j,Fintype (X j)] [∀j,DecidableEq (X j)] [∀j,Fintype (Ω j)]
  (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ) (u v : V)
  (a b : ∀j,Ω j → X j)

noncomputable def pairPush : (((∀j,X j) × (∀j,X j)) → ℝ) →ₗ[ℝ] ℝ where
  toFun F := tensorLaw L (fun z => F (z u,z v))
  map_add' F G := by simp only [Pi.add_apply,←Pi.add_def,map_add]
  map_smul' c F := by simp only [Pi.smul_apply,←Pi.smul_def,map_smul,RingHom.id_apply]

noncomputable def pairSample : (((∀j,X j) × (∀j,X j)) → ℝ) →ₗ[ℝ] ℝ where
  toFun F := 𝔼 w : ∀j,Ω j,F (fun j => a j (w j),fun j => b j (w j))
  map_add' F G := by simp only [Pi.add_apply,expect_add_distrib]
  map_smul' c F := by simp only [Pi.smul_apply,smul_eq_mul,mul_expect,RingHom.id_apply]

lemma pair_indicator_pi {J : Type*}
    [Fintype J]
    [DecidableEq J]
    {X : J → Type*}
    [(j : J) → Fintype (X j)]
    [(j : J) → DecidableEq (X j)] (x y r s : ∀j,X j) :
    (if (x,y)=(r,s) then (1:ℝ) else 0)=∏j,if (x j,y j)=(r j,s j) then 1 else 0 := by
  rw [prod_indicator_forall]
  congr 1
  apply propext
  constructor
  · intro h; cases h; simp
  · intro h
    apply Prod.ext
    · funext j; exact congrArg Prod.fst (h j)
    · funext j; exact congrArg Prod.snd (h j)

lemma tensorLaw_pair_sampling
    (hloc : ∀j (F : X j → X j → ℝ),L j (fun z => F (z u) (z v))=𝔼 w,F (a j w) (b j w))
    (F : (∀j,X j) → (∀j,X j) → ℝ) :
    tensorLaw L (fun z => F (z u) (z v))=
      𝔼 w : ∀j,Ω j,F (fun j => a j (w j)) (fun j => b j (w j)) := by
  have hd (y : (∀j,X j) × (∀j,X j)) :
      lawDensity (pairPush L u v) y=lawDensity (pairSample a b) y := by
    rcases y with ⟨r,s⟩
    change tensorLaw L (fun z => if (z u,z v)=(r,s) then (1:ℝ) else 0)=
      𝔼 w : ∀j,Ω j,if ((fun j => a j (w j)),(fun j => b j (w j)))=(r,s) then 1 else 0
    simp_rw [pair_indicator_pi]
    rw [tensorLaw_fubini L (fun j z => if (z u,z v)=(r j,s j) then 1 else 0)]
    rw [expect_prod_pi (fun j w => if (a j w,b j w)=(r j,s j) then (1:ℝ) else 0)]
    apply prod_congr rfl
    intro j _
    exact hloc j (fun x y => if (x,y)=(r j,s j) then 1 else 0)
  change pairPush L u v (fun z => F z.1 z.2)=pairSample a b (fun z => F z.1 z.2)
  rw [linearFunctional_density,linearFunctional_density]
  exact sum_congr rfl (fun y _ => congrArg (fun t => t*F y.1 y.2) (hd y))

end TensorPair

section PiProduct

variable {J : Type*} [Fintype J] [DecidableEq J] {X Y : J → Type*}
  [∀j,Fintype (X j)] [∀j,Fintype (Y j)]

def piProductEquiv : (∀j,X j × Y j) ≃ (∀j,X j) × (∀j,Y j) where
  toFun z := (fun j => (z j).1,fun j => (z j).2)
  invFun z j := (z.1 j,z.2 j)
  left_inv _ := rfl
  right_inv _ := rfl

lemma expect_pi_product (F : (∀j,X j) → (∀j,Y j) → ℝ) :
    (𝔼 w : ∀j,X j × Y j,F (fun j => (w j).1) (fun j => (w j).2))=𝔼 x,𝔼 y,F x y := by
  rw [Fintype.expect_equiv piProductEquiv (fun w => F (fun j => (w j).1) (fun j => (w j).2)) (fun w => F w.1 w.2) (fun _ => rfl)]
  rw [←univ_product_univ,expect_product]

end PiProduct

lemma tensorLaw_pair_product_sampling {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X Y : J → Type*} [∀j,Fintype (X j)]
    [∀j,DecidableEq (X j)] [∀j,Fintype (Y j)]
    (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ) (u v : V) (t : ∀j,Y j → X j → X j)
    (hloc : ∀j (G : X j → X j → ℝ),L j (fun z => G (z u) (z v))=
      𝔼 w : Y j × X j,G w.2 (t j w.1 w.2))
    (F : (∀j,X j) → (∀j,X j) → ℝ) :
    tensorLaw L (fun z => F (z u) (z v))=
      𝔼 w : ∀j,Y j,𝔼 x,F x (fun j => t j (w j) (x j)) := by
  exact (tensorLaw_pair_sampling L u v (fun j (w : Y j × X j) => w.2)
    (fun j (w : Y j × X j) => t j w.1 w.2) hloc F).trans
      (expect_pi_product (fun w x => F x (fun j => t j (w j) (x j))))

lemma tupleGoodLaw_pair_product {p : ℕ} [Fact p.Prime]
    (hp : tupleMassThreshold ≤ (p:ℝ)) (k : ℕ) (G : ZMod p → ZMod p → ℝ) :
    tupleGoodLaw (fun z => G (z (cycleVertex k)) (z (cycleVertex (k+1))))=
      𝔼 w : (ZMod p)ˣ × ZMod p,G w.2 (w.2+(w.1:ZMod p)^2) := by
  rw [tupleGoodLaw_pair hp,squarePairAverage,←univ_product_univ,expect_product]

lemma tensorLaw_squarePair_sampling {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    (p : J → ℕ) [∀j,Fact (p j).Prime]
    (L : ∀j,((V → ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ) (u v : V)
    (hloc : ∀j (G : ZMod (p j) → ZMod (p j) → ℝ),L j
      (fun z => G (z u) (z v))=𝔼 w : (ZMod (p j))ˣ × ZMod (p j),G w.2 (w.2+(w.1:ZMod (p j))^2))
    (F : (∀j,ZMod (p j)) → (∀j,ZMod (p j)) → ℝ) :
    tensorLaw L (fun z => F (z u) (z v))=
      𝔼 w : ∀j,(ZMod (p j))ˣ × ZMod (p j),
        F (fun j => (w j).2) (fun j => (w j).2+((w j).1:ZMod (p j))^2) := by
  exact tensorLaw_pair_sampling (X:=fun j => ZMod (p j))
    (Ω:=fun j => (ZMod (p j))ˣ × ZMod (p j)) L u v
    (fun j (w : (ZMod (p j))ˣ × ZMod (p j)) => w.2)
    (fun j (w : (ZMod (p j))ˣ × ZMod (p j)) => w.2+(w.1:ZMod (p j))^2) hloc F

lemma tensorGood_pair [Fintype TupleVertex] [DecidableEq TupleVertex] {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀j,Fact (p j).Prime] (hp : ∀j,tupleMassThreshold ≤ (p j:ℝ))
    (k : ℕ) (F : (∀j,ZMod (p j)) → (∀j,ZMod (p j)) → ℝ) :
    tensorLaw (fun j => tupleGoodLaw (p:=p j))
      (fun z => F (z (cycleVertex k)) (z (cycleVertex (k+1))))=
      𝔼 w : ∀j,(ZMod (p j))ˣ,𝔼 x : ∀j,ZMod (p j),F x (fun j => x j+(w j:ZMod (p j))^2) := by
  calc
    _ = 𝔼 w : ∀j,(ZMod (p j))ˣ × ZMod (p j),
        F (fun j => (w j).2) (fun j => (w j).2+((w j).1:ZMod (p j))^2) := by
      apply tensorLaw_squarePair_sampling p (fun j => tupleGoodLaw (p:=p j))
        (cycleVertex k) (cycleVertex (k+1))
      intro j G
      exact tupleGoodLaw_pair_product (hp j) k G
    _ = _ := expect_pi_product (fun (w : ∀j,(ZMod (p j))ˣ) (x : ∀j,ZMod (p j)) =>
      F x (fun j => x j+(w j:ZMod (p j))^2))

lemma expect_restrict_compl {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀j,Fintype (X j)] [∀j,Nonempty (X j)] (B : Finset J)
    {E : Type*} [AddCommMonoid E] [Module ℚ≥0 E]
    (F : (∀j : {j : J // j∉B},X j.val) → E) :
    (𝔼 x : ∀j,X j,F (fun j => x j.val))=𝔼 x,F x := by
  let e := Equiv.piEquivPiSubtypeProd (fun j : J => j∈B) X
  rw [Fintype.expect_equiv e (fun x => F (fun j => x j.val)) (fun x => F x.2) (fun _ => rfl)]
  rw [←univ_product_univ,expect_product]
  simp only [Fintype.expect_const]

section FrozenPair

variable [Fintype TupleVertex] [DecidableEq TupleVertex]

open LiftTheory.SquareDifference PairBridge

variable {J : Type*} [Fintype J] [DecidableEq J]
  (p : J → ℕ) [∀j,Fact (p j).Prime] (hp : ∀j,tupleMassThreshold ≤ (p j:ℝ))

include hp in
lemma tensorGood_frozen_pair (k : ℕ) (B : Finset J) (r s : ResidueSpace p)
    (F G : ResidueSpace p → ℝ) :
    (tensorLaw (fun j => tupleGoodLaw (p:=p j)) (fun z =>
      F (freezeCoordinates B r (z (cycleVertex k)))*
      G (freezeCoordinates B s (z (cycleVertex (k+1))))):ℂ)=
      squarePairForm (OutsideModulus p B)
        (fun x => (F (assembleOutside p B r x):ℂ))
        (fun x => (G (assembleOutside p B s x):ℂ)) := by
  rw [tensorGood_pair p hp k (fun x y => F (freezeCoordinates B r x)*G (freezeCoordinates B s y))]
  have he (w : ∀j,(ZMod (p j))ˣ) (x : ResidueSpace p) :
      freezeCoordinates B s (fun j => x j+(w j:ZMod (p j))^2)=
        assembleOutside p B s ((outsideCoordinate p B x)+(fun j : {j : J // j∉B} => (w j.val:ZMod (p j.val))^2)) := by
    funext j
    simp only [freezeCoordinates,assembleOutside,Pi.add_apply,outsideCoordinate]
    split_ifs <;> rfl
  simp_rw [←assembleOutside_freeze p B r,he]
  have hbase (w : ∀j,(ZMod (p j))ˣ) := expect_outside p B
    (fun x => F (assembleOutside p B r x)*G (assembleOutside p B s (x+(fun j : {j : J // j∉B} => (w j.val:ZMod (p j.val))^2))))
  simp_rw [hbase]
  rw [expect_restrict_compl (X:=fun j => (ZMod (p j))ˣ) B
    (fun w => 𝔼 x,F (assembleOutside p B r x)*G (assembleOutside p B s (x+(fun j => (w j:ZMod (p j.val))^2))))]
  simp only [squarePairForm,expect_eq_sum_div_card,Complex.ofReal_div,Complex.ofReal_sum,
    Complex.ofReal_natCast,Complex.ofReal_mul]

end FrozenPair

end SquareDifference

end

end OAI
