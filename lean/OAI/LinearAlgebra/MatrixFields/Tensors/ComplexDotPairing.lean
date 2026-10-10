import Mathlib

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation

abbrev Tensor (K X Y Z : Type*) := X → Y → Z → K

namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def rankOne (a : X → K) (b : Y → K) (c : Z → K) : Tensor K X Y Z :=
  fun x y z => a x * b y * c z

def RankAtMost (T : Tensor K X Y Z) (r : ℕ) : Prop :=
  ∃ (a : Fin r → X → K) (b : Fin r → Y → K) (c : Fin r → Z → K),
    T = fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z

def restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x' y' z' => ∑ x, ∑ y, ∑ z,
    A x' x * B y' y * C z' z * T x y z

def contract (T : Tensor K X Y Z) [Fintype X] [Fintype Y]
    (a : X → K) (b : Y → K) : Z → K :=
  fun z => ∑ x, ∑ y, T x y z * a x * b y

def product {U V W : Type*} (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X × U) (Y × V) (Z × W) :=
  fun x y z => T x.1 y.1 z.1 * S x.2 y.2 z.2

def directSum {ι : Type*} [DecidableEq ι] (T : ι → Tensor K X Y Z) :
    Tensor K (ι × X) (ι × Y) (ι × Z) :=
  fun x y z => if x.1 = y.1 ∧ x.1 = z.1 then T x.1 x.2 y.2 z.2 else 0

def power (T : Tensor K X Y Z) (n : ℕ) :
    Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, T (x i) (y i) (z i)

@[simp] theorem directSum_matching {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (i : ι) (x : X) (y : Y) (z : Z) :
    directSum T (i, x) (i, y) (i, z) = T i x y z := by
  simp [directSum]

theorem directSum_zero_of_left_ne {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (x : ι × X) (y : ι × Y) (z : ι × Z)
    (h : x.1 ≠ y.1) : directSum T x y z = 0 := by
  simp [directSum, h]

@[simp] theorem rankAtMost_zero : RankAtMost (0 : Tensor K X Y Z) 0 := by
  refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
  funext x y z
  simp

theorem rankOne_rankAtMost (a : X → K) (b : Y → K) (c : Z → K) :
    RankAtMost (rankOne a b c) 1 := by
  refine ⟨fun _ => a, fun _ => b, fun _ => c, ?_⟩
  funext x y z
  simp

theorem RankAtMost.map {L : Type*} [CommSemiring L]
    (f : K →+* L) {T : Tensor K X Y Z} {r : ℕ} (h : RankAtMost T r) :
    RankAtMost (fun x y z => f (T x y z)) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x => f (a i x), fun i y => f (b i y), fun i z => f (c i z), ?_⟩
  funext x y z
  simp [rankOne]

theorem RankAtMost.scale {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (u : K) :
    RankAtMost (fun x y z => u * T x y z) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x => u * a i x, b, c, ?_⟩
  funext x y z
  simp [rankOne, Finset.mul_sum, mul_assoc]

theorem rankAtMost_sum_rankOne {ι : Type*} [Fintype ι]
    (a : ι → X → K) (b : ι → Y → K) (c : ι → Z → K) :
    RankAtMost (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (Fintype.card ι) := by
  classical
  refine ⟨fun i => a ((Fintype.equivFin ι).symm i),
    fun i => b ((Fintype.equivFin ι).symm i),
    fun i => c ((Fintype.equivFin ι).symm i), ?_⟩
  funext x y z
  exact ((Fintype.equivFin ι).symm.sum_comp
    (fun i => rankOne (a i) (b i) (c i) x y z)).symm

theorem RankAtMost.product {U V W : Type*}
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r s : ℕ}
    (hT : RankAtMost T r) (hS : RankAtMost S s) :
    RankAtMost (Tensor.product T S) (r * s) := by
  rcases hT with ⟨a, b, c, rfl⟩
  rcases hS with ⟨d, e, f, rfl⟩
  let aa : (Fin r × Fin s) → (X × U) → K := fun i x => a i.1 x.1 * d i.2 x.2
  let bb : (Fin r × Fin s) → (Y × V) → K := fun i y => b i.1 y.1 * e i.2 y.2
  let cc : (Fin r × Fin s) → (Z × W) → K := fun i z => c i.1 z.1 * f i.2 z.2
  have heq : Tensor.product
      (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (fun u v w => ∑ j, rankOne (d j) (e j) (f j) u v w) =
      fun x y z => ∑ i, rankOne (aa i) (bb i) (cc i) x y z := by
    funext x y z
    simp only [Tensor.product, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [rankOne, aa, bb, cc]
    ring
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

theorem RankAtMost.power {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (n : ℕ) : RankAtMost (Tensor.power T n) (r ^ n) := by
  rcases h with ⟨a, b, c, rfl⟩
  let aa : (Fin n → Fin r) → (Fin n → X) → K := fun f x => ∏ i, a (f i) (x i)
  let bb : (Fin n → Fin r) → (Fin n → Y) → K := fun f y => ∏ i, b (f i) (y i)
  let cc : (Fin n → Fin r) → (Fin n → Z) → K := fun f z => ∏ i, c (f i) (z i)
  have heq : Tensor.power (fun x y z => ∑ j, rankOne (a j) (b j) (c j) x y z) n =
      fun x y z => ∑ f, rankOne (aa f) (bb f) (cc f) x y z := by
    funext x y z
    simp only [Tensor.power, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro f hf
    simp only [rankOne, aa, bb, cc, Finset.prod_mul_distrib]
  rw [heq]
  simpa only [Fintype.card_pi_const, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

variable [Fintype X] [Fintype Y] [Fintype Z]

theorem restrict_rankOne (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (a : X → K) (b : Y → K) (c : Z → K) :
    restrict A B C (rankOne a b c) =
      rankOne (fun x' => ∑ x, A x' x * a x)
        (fun y' => ∑ y, B y' y * b y)
        (fun z' => ∑ z, C z' z * c z) := by
  funext x' y' z'
  simp only [restrict, rankOne]
  conv_rhs => rw [mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem restrict_sum {ι : Type*} [Fintype ι]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : ι → Tensor K X Y Z) :
    restrict A B C (fun x y z => ∑ i, T i x y z) =
      fun x' y' z' => ∑ i, restrict A B C (T i) x' y' z' := by
  funext x' y' z'
  simp only [restrict, Finset.mul_sum]
  calc
    (∑ x, ∑ y, ∑ z, ∑ i, A x' x * B y' y * C z' z * T i x y z) =
        ∑ x, ∑ y, ∑ i, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z :=
      Finset.sum_comm

theorem RankAtMost.restrict {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : RankAtMost (Tensor.restrict A B C T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x' => ∑ x, A x' x * a i x,
    fun i y' => ∑ y, B y' y * b i y,
    fun i z' => ∑ z, C z' z * c i z, ?_⟩
  rw [restrict_sum]
  funext x' y' z'
  apply Finset.sum_congr rfl
  intro i hi
  exact congrFun (congrFun (congrFun (restrict_rankOne A B C (a i) (b i) (c i)) x') y') z'

end Algebra

section Pullback
variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def pullback (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x y z => T (fx x) (fy y) (fz z)

theorem pullback_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) (T : Tensor K X Y Z) :
    pullback fx fy fz T = restrict
      (fun x' x => if x = fx x' then 1 else 0)
      (fun y' y => if y = fy y' then 1 else 0)
      (fun z' z => if z = fz z' then 1 else 0) T := by
  classical
  funext x y z
  simp [pullback, restrict, ite_mul, mul_ite]

theorem RankAtMost.pullback {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (pullback fx fy fz T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨fun i x => a i (fx x), fun i y => b i (fy y),
    fun i z => c i (fz z), rfl⟩

end Pullback

section ComplexTopology

variable {X Y Z X' Y' Z' : Type*}

def BorderRankAtMost [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) (r : ℕ) : Prop :=
  T ∈ closure {S | RankAtMost S r}

def restrictionOrbit [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor ℂ X Y Z) : Set (Tensor ℂ X' Y' Z') :=
  {U | ∃ (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ),
    U = restrict A B C T}

def DegeneratesTo [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor ℂ X Y Z) (U : Tensor ℂ X' Y' Z') : Prop :=
  U ∈ closure (restrictionOrbit T)

theorem RankAtMost.borderRankAtMost [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor ℂ X Y Z} {r : ℕ} (h : RankAtMost T r) :
    BorderRankAtMost T r := subset_closure h

theorem continuous_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ) :
    Continuous (Tensor.restrict A B C) := by
  unfold restrict
  fun_prop

theorem BorderRankAtMost.restrict [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor ℂ X Y Z} {r : ℕ} (h : BorderRankAtMost T r)
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ) :
    BorderRankAtMost (Tensor.restrict A B C T) r := by
  have hclosed : IsClosed {S : Tensor ℂ X Y Z |
      BorderRankAtMost (Tensor.restrict A B C S) r} :=
    isClosed_closure.preimage (continuous_restrict A B C)
  have hsubset : {S : Tensor ℂ X Y Z | RankAtMost S r} ⊆
      {S | BorderRankAtMost (Tensor.restrict A B C S) r} := by
    intro S hS
    exact (hS.restrict A B C).borderRankAtMost
  exact closure_minimal hsubset hclosed h

theorem continuous_product_left {U V W : Type*} (S : Tensor ℂ U V W) :
    Continuous (fun T : Tensor ℂ X Y Z => Tensor.product T S) := by
  unfold product
  fun_prop

theorem continuous_product_right {U V W : Type*} (T : Tensor ℂ X Y Z) :
    Continuous (fun S : Tensor ℂ U V W => Tensor.product T S) := by
  unfold product
  fun_prop

theorem BorderRankAtMost.product {U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor ℂ X Y Z} {S : Tensor ℂ U V W} {r s : ℕ}
    (hT : BorderRankAtMost T r) (hS : BorderRankAtMost S s) :
    BorderRankAtMost (Tensor.product T S) (r * s) := by
  have hexact : ∀ T' : Tensor ℂ X Y Z, RankAtMost T' r →
      BorderRankAtMost (Tensor.product T' S) (r * s) := by
    intro T' hT'
    have hclosed : IsClosed {S' : Tensor ℂ U V W |
        BorderRankAtMost (Tensor.product T' S') (r * s)} :=
      isClosed_closure.preimage (continuous_product_right T')
    have hsubset : {S' : Tensor ℂ U V W | RankAtMost S' s} ⊆
        {S' | BorderRankAtMost (Tensor.product T' S') (r * s)} := by
      intro S' hS'
      exact (hT'.product hS').borderRankAtMost
    exact closure_minimal hsubset hclosed hS
  have hclosed : IsClosed {T' : Tensor ℂ X Y Z |
      BorderRankAtMost (Tensor.product T' S) (r * s)} :=
    isClosed_closure.preimage (continuous_product_left S)
  exact closure_minimal hexact hclosed hT

theorem BorderRankAtMost.of_degeneration [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'} {r : ℕ}
    (hT : BorderRankAtMost T r) (hTU : DegeneratesTo T U) :
    BorderRankAtMost U r := by
  have hsubset : restrictionOrbit T ⊆
      {S : Tensor ℂ X' Y' Z' | BorderRankAtMost S r} := by
    rintro S ⟨A, B, C, rfl⟩
    exact hT.restrict A B C
  exact closure_minimal hsubset isClosed_closure hTU

end ComplexTopology

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

def diagonal (ι : Type*) [DecidableEq ι] : Tensor K ι ι ι :=
  fun i j k => if i = j ∧ i = k then 1 else 0

theorem diagonal_rankAtMost (ι : Type*) [Fintype ι] [DecidableEq ι] :
    RankAtMost (diagonal (K := K) ι) (Fintype.card ι) := by
  let a : ι → ι → K := fun i j => if i = j then 1 else 0
  have heq : diagonal (K := K) ι =
      fun x y z => ∑ i, rankOne (a i) (a i) (a i) x y z := by
    funext x y z
    simp [diagonal, rankOne, a, mul_ite, ite_and]
    split_ifs <;> simp_all
  rw [heq]
  exact rankAtMost_sum_rankOne a a a

theorem RankAtMost.repeat_batch {S : Tensor K U V W} {k r R B : ℕ}
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r) (hfit : R ≤ B * k) :
    RankAtMost (directSum (fun _ : Fin R => S)) (B * r) := by
  classical
  let f : Fin R → Fin B × Fin k := fun i => finProdFinEquiv.symm (Fin.castLE hfit i)
  have hf : Function.Injective f := finProdFinEquiv.symm.injective.comp (Fin.castLE_injective hfit)
  have hbig := (diagonal_rankAtMost (K := K) (Fin B)).product hbatch
  simp only [Fintype.card_fin] at hbig
  rcases hbig with ⟨a, b, c, heq⟩
  let liftU : (Fin R × U) → Fin B × (Fin k × U) := fun x => ((f x.1).1, (f x.1).2, x.2)
  let liftV : (Fin R × V) → Fin B × (Fin k × V) := fun y => ((f y.1).1, (f y.1).2, y.2)
  let liftW : (Fin R × W) → Fin B × (Fin k × W) := fun z => ((f z.1).1, (f z.1).2, z.2)
  refine ⟨fun i x => a i (liftU x), fun i y => b i (liftV y),
    fun i z => c i (liftW z), ?_⟩
  funext x y z
  change directSum (fun _ : Fin R => S) x y z =
    ∑ i, rankOne (a i) (b i) (c i) (liftU x) (liftV y) (liftW z)
  have hentry := congrFun (congrFun (congrFun heq (liftU x)) (liftV y)) (liftW z)
  rw [← hentry]
  by_cases hxy : x.1 = y.1
  · by_cases hxz : x.1 = z.1
    · have hyz : y.1 = z.1 := hxy.symm.trans hxz
      simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxy, hyz]
    · have hn : f x.1 ≠ f z.1 := fun h => hxz (hf h)
      have hs : (f x.1).1 ≠ (f z.1).1 ∨ (f x.1).2 ≠ (f z.1).2 := by
        by_cases hfirst : (f x.1).1 = (f z.1).1
        · exact Or.inr (fun hsecond => hn (Prod.ext hfirst hsecond))
        · exact Or.inl hfirst
      rcases hs with hs | hs <;>
        simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxz, hs]
  · have hn : f x.1 ≠ f y.1 := fun h => hxy (hf h)
    have hs : (f x.1).1 ≠ (f y.1).1 ∨ (f x.1).2 ≠ (f y.1).2 := by
      by_cases hfirst : (f x.1).1 = (f y.1).1
      · exact Or.inr (fun hsecond => hn (Prod.ext hfirst hsecond))
      · exact Or.inl hfirst
    rcases hs with hs | hs <;>
      simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxy, hs]

theorem RankAtMost.batch_substitute [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r b : ℕ}
    (hT : RankAtMost T r)
    (hbatch : RankAtMost (directSum (fun _ : Fin r => S)) b) :
    RankAtMost (Tensor.product T S) b := by
  classical
  rcases hT with ⟨a, c, e, rfl⟩
  let A : (X × U) → (Fin r × U) → K :=
    fun x i => if x.2 = i.2 then a i.1 x.1 else 0
  let B : (Y × V) → (Fin r × V) → K :=
    fun y i => if y.2 = i.2 then c i.1 y.1 else 0
  let C : (Z × W) → (Fin r × W) → K :=
    fun z i => if z.2 = i.2 then e i.1 z.1 else 0
  have heq : Tensor.restrict A B C (directSum (fun _ : Fin r => S)) =
      Tensor.product (fun x y z => ∑ i, rankOne (a i) (c i) (e i) x y z) S := by
    funext x y z
    simp [Tensor.restrict, directSum, Tensor.product, rankOne, A, B, C,
      Fintype.sum_prod_type, ite_and, ite_mul, mul_ite, Finset.sum_mul]
  rw [← heq]
  exact hbatch.restrict A B C

theorem RankAtMost.batch_product [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {R k r B : ℕ}
    (hT : RankAtMost T R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r)
    (hfit : R ≤ B * k) : RankAtMost (Tensor.product T S) (B * r) :=
  hT.batch_substitute (hbatch.repeat_batch hfit)

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' X'' Y'' Z'' : Type*} [CommSemiring K]

def composeRestrictionMatrix [Fintype X']
    (D : X'' → X' → K) (A : X' → X → K) : X'' → X → K :=
  fun x'' x => ∑ x', D x'' x' * A x' x

private theorem sum_three_mul [Fintype X] [Fintype Y] [Fintype Z]
    (a : X → K) (b : Y → K) (c : Z → K) (t : K) :
    (∑ x, a x) * (∑ y, b y) * (∑ z, c z) * t =
      ∑ x, ∑ y, ∑ z, a x * b y * c z * t := by
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]

private theorem sum_six_comm [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (f : X' → Y' → Z' → X → Y → Z → K) :
    (∑ x', ∑ y', ∑ z', ∑ x, ∑ y, ∑ z, f x' y' z' x y z) =
      ∑ x, ∑ y, ∑ z, ∑ x', ∑ y', ∑ z', f x' y' z' x y z := by
  calc
    _ = ∑ p : X' × Y' × Z', ∑ q : X × Y × Z,
        f p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ q : X × Y × Z, ∑ p : X' × Y' × Z',
        f p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type]

private theorem sum_interleaved_triples {U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (f : X → Y → Z → U → V → W → K) :
    (∑ x, ∑ u, ∑ y, ∑ v, ∑ z, ∑ w, f x y z u v w) =
      ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w, f x y z u v w := by
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ u, ∑ y, ∑ v, ∑ z, ∑ w, f x y z u v w) =
        ∑ y, ∑ u, ∑ v, ∑ z, ∑ w, f x y z u v w := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      calc
        (∑ u, ∑ v, ∑ z, ∑ w, f x y z u v w) =
            ∑ u, ∑ z, ∑ v, ∑ w, f x y z u v w := by
          apply Finset.sum_congr rfl
          intro u hu
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

theorem restrict_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (D : X'' → X' → K) (E : Y'' → Y' → K) (F : Z'' → Z' → K)
    (T : Tensor K X Y Z) :
    restrict D E F (restrict A B C T) =
      restrict (composeRestrictionMatrix D A) (composeRestrictionMatrix E B)
        (composeRestrictionMatrix F C) T := by
  funext x'' y'' z''
  unfold restrict composeRestrictionMatrix
  calc
    _ = ∑ x', ∑ y', ∑ z', ∑ x, ∑ y, ∑ z,
        D x'' x' * E y'' y' * F z'' z' *
          (A x' x * B y' y * C z' z * T x y z) := by
      simp only [Finset.mul_sum]
    _ = ∑ x, ∑ y, ∑ z, ∑ x', ∑ y', ∑ z',
        D x'' x' * E y'' y' * F z'' z' *
          (A x' x * B y' y * C z' z * T x y z) := sum_six_comm _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      rw [sum_three_mul]
      apply Finset.sum_congr rfl
      intro x' hx'
      apply Finset.sum_congr rfl
      intro y' hy'
      apply Finset.sum_congr rfl
      intro z' hz'
      ring

theorem restrict_product {U V W U' V' W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (D : U' → U → K) (E : V' → V → K) (F : W' → W → K)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    restrict (fun (x : X' × U') (u : X × U) => A x.1 u.1 * D x.2 u.2)
      (fun (y : Y' × V') (v : Y × V) => B y.1 v.1 * E y.2 v.2)
      (fun (z : Z' × W') (w : Z × W) => C z.1 w.1 * F z.2 w.2) (product T S) =
      product (restrict A B C T) (restrict D E F S) := by
  funext x' y' z'
  simp only [restrict, product, Fintype.sum_prod_type]
  calc
    _ = ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w,
        (A x'.1 x * D x'.2 u) * (B y'.1 y * E y'.2 v) *
          (C z'.1 z * F z'.2 w) * (T x y z * S u v w) :=
      sum_interleaved_triples _
    _ = ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w,
        (A x'.1 x * B y'.1 y * C z'.1 z * T x y z) *
          (D x'.2 u * E y'.2 v * F z'.2 w * S u v w) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = _ := by
      simp_rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]

theorem restrict_identity [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (T : Tensor K X Y Z) :
    restrict (fun x' x => if x = x' then 1 else 0)
      (fun y' y => if y = y' then 1 else 0)
      (fun z' z => if z = z' then 1 else 0) T = T := by
  exact (pullback_eq_restrict id id id T).symm

end Algebra

section ComplexTopology

variable {X Y Z X' Y' Z' X'' Y'' Z'' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']
variable [Fintype X''] [Fintype Y''] [Fintype Z'']

theorem degeneratesTo_restrict (T : Tensor ℂ X Y Z)
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ) :
    DegeneratesTo T (restrict A B C T) :=
  subset_closure ⟨A, B, C, rfl⟩

theorem DegeneratesTo.refl (T : Tensor ℂ X Y Z) : DegeneratesTo T T := by
  classical
  have h := degeneratesTo_restrict T
    (fun x' x => if x = x' then 1 else 0)
    (fun y' y => if y = y' then 1 else 0)
    (fun z' z => if z = z' then 1 else 0)
  simpa only [restrict_identity] using h

omit [Fintype X''] [Fintype Y''] [Fintype Z''] in
theorem mem_restrictionOrbit_restrict {T : Tensor ℂ X Y Z}
    {U : Tensor ℂ X' Y' Z'} (h : U ∈ restrictionOrbit T)
    (D : X'' → X' → ℂ) (E : Y'' → Y' → ℂ) (F : Z'' → Z' → ℂ) :
    restrict D E F U ∈ restrictionOrbit T := by
  rcases h with ⟨A, B, C, rfl⟩
  exact ⟨composeRestrictionMatrix D A, composeRestrictionMatrix E B,
    composeRestrictionMatrix F C, restrict_restrict A B C D E F T⟩

theorem DegeneratesTo.restrict {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'}
    (h : DegeneratesTo T U)
    (D : X'' → X' → ℂ) (E : Y'' → Y' → ℂ) (F : Z'' → Z' → ℂ) :
    DegeneratesTo T (Tensor.restrict D E F U) := by
  have hclosed : IsClosed {S : Tensor ℂ X' Y' Z' |
      DegeneratesTo T (Tensor.restrict D E F S)} :=
    isClosed_closure.preimage (continuous_restrict D E F)
  have hsubset : restrictionOrbit T ⊆
      {S : Tensor ℂ X' Y' Z' | DegeneratesTo T (Tensor.restrict D E F S)} := by
    intro S hS
    exact subset_closure (mem_restrictionOrbit_restrict hS D E F)
  exact closure_minimal hsubset hclosed h

theorem DegeneratesTo.trans {T : Tensor ℂ X Y Z} {U : Tensor ℂ X' Y' Z'}
    {V : Tensor ℂ X'' Y'' Z''} (hTU : DegeneratesTo T U)
    (hUV : DegeneratesTo U V) : DegeneratesTo T V := by
  have hsubset : restrictionOrbit U ⊆
      {S : Tensor ℂ X'' Y'' Z'' | DegeneratesTo T S} := by
    rintro S ⟨D, E, F, rfl⟩
    exact hTU.restrict D E F
  exact closure_minimal hsubset isClosed_closure hUV

theorem DegeneratesTo.of_restrict {T : Tensor ℂ X Y Z} {V : Tensor ℂ X'' Y'' Z''}
    (A : X' → X → ℂ) (B : Y' → Y → ℂ) (C : Z' → Z → ℂ)
    (h : DegeneratesTo (Tensor.restrict A B C T) V) : DegeneratesTo T V :=
  (degeneratesTo_restrict T A B C).trans h

end ComplexTopology

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.Replication

variable {K I R X Y Z X' Y' Z' : Type*} [CommSemiring K]

theorem restrict_directSum
    [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y] [Fintype Z]
    (T : I → Tensor K X Y Z)
    (a : I → X' → X → K) (b : I → Y' → Y → K) (c : I → Z' → Z → K) :
    Tensor.restrict
      (fun x s => if x.1 = s.1 then a x.1 x.2 s.2 else 0)
      (fun y s => if y.1 = s.1 then b y.1 y.2 s.2 else 0)
      (fun z s => if z.1 = s.1 then c z.1 z.2 s.2 else 0)
      (Tensor.directSum T) = Tensor.directSum (fun i => Tensor.restrict (a i) (b i) (c i) (T i)) := by
  classical
  funext x y z
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases z with ⟨k, z⟩
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
        ite_and, ite_mul, mul_ite]
    · simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
        ite_and, ite_mul, mul_ite, hik]
  · simp [Tensor.restrict, Tensor.directSum, Fintype.sum_prod_type,
      ite_and, ite_mul, mul_ite, hij]
    intro hjk hik
    exact (hij (hik.trans hjk.symm)).elim

theorem swap_replication [DecidableEq I] [DecidableEq R]
    (T : I → Tensor K X Y Z) :
    Tensor.pullback
      (fun x : I × (R × X) => (x.2.1, (x.1, x.2.2)))
      (fun y : I × (R × Y) => (y.2.1, (y.1, y.2.2)))
      (fun z : I × (R × Z) => (z.2.1, (z.1, z.2.2)))
      (Tensor.directSum (fun _ : R => Tensor.directSum T)) =
      Tensor.directSum (fun i => Tensor.directSum (fun _ : R => T i)) := by
  funext x y z
  simp only [Tensor.pullback, Tensor.directSum]
  split_ifs <;> simp_all

theorem repair_branches
    [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : I → Tensor K X Y Z) (Q : I → Tensor K X' Y' Z')
    (a : I → X' → (R × X) → K) (b : I → Y' → (R × Y) → K)
    (c : I → Z' → (R × Z) → K)
    (h : ∀ i, Tensor.restrict (a i) (b i) (c i)
      (Tensor.directSum (fun _ : R => T i)) = Q i) :
    ∃ (A : (I × X') → (R × (I × X)) → K)
      (B : (I × Y') → (R × (I × Y)) → K)
      (C : (I × Z') → (R × (I × Z)) → K),
      Tensor.restrict A B C (Tensor.directSum (fun _ : R => Tensor.directSum T)) =
        Tensor.directSum Q := by
  classical
  have hb := restrict_directSum (fun i => Tensor.directSum (fun _ : R => T i)) a b c
  simp_rw [h] at hb
  rw [← swap_replication T, Tensor.pullback_eq_restrict, Tensor.restrict_restrict] at hb
  exact ⟨_, _, _, hb⟩

end MatrixMultiplication.Replication

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

variable (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]

def groupTensor : Tensor ℂ G G G := fun a b c => if a + b = c then 1 else 0

theorem groupTensor_fourier :
    groupTensor G = fun a b c => ∑ χ : AddChar G ℂ,
      Tensor.rankOne (fun a => χ a / (Fintype.card G : ℂ))
        (fun b => χ b) (fun c => χ (-c)) a b c := by
  funext a b c
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    groupTensor G a b c =
        (∑ χ : AddChar G ℂ, χ (a + b - c)) / (Fintype.card G : ℂ) := by
      rw [AddChar.sum_apply_eq_ite]
      by_cases h : a + b = c
      · simp [groupTensor, h, hcard]
      · simp [groupTensor, h, sub_ne_zero.mpr h]
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro χ hχ
      simp only [Tensor.rankOne, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring

theorem groupTensor_rankAtMost : Tensor.RankAtMost (groupTensor G) (Fintype.card G) := by
  rw [groupTensor_fourier]
  simpa only [AddChar.card_eq] using
    Tensor.rankAtMost_sum_rankOne
      (fun χ : AddChar G ℂ => fun a => χ a / (Fintype.card G : ℂ))
      (fun χ : AddChar G ℂ => fun b => χ b)
      (fun χ : AddChar G ℂ => fun c => χ (-c))

end MatrixMultiplication.Foundation

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section Pairing

variable {K U : Type*} [CommSemiring K] [DecidableEq U]

def dotPairing (U : Type*) [DecidableEq U] : Tensor K U U Unit :=
  fun i j _ => if i = j then 1 else 0

@[simp] theorem dotPairing_matching (i : U) :
    dotPairing (K := K) U i i () = 1 := by
  simp [dotPairing]

theorem contract_dotPairing [Fintype U] (a b : U → K) :
    contract (dotPairing (K := K) U) a b () = ∑ i, a i * b i := by
  classical
  simp [contract, dotPairing, ite_mul]

end Pairing

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixAllFields

end OAI
