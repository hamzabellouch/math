import OAI.NumberTheory.TwoPoint.Bounds.SieveModel
import OAI.NumberTheory.TwoPoint.Bounds.ResidueBox

namespace OAI

/-! Exact CRT factorization of the one- and three-variable local sieve
models. The interval/box errors are kept separate in `ResidueBox`. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma FiniteLaw.probability_equiv {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (e : α ≃ β)
    (hweight : ∀ x, μ.weight x = ν.weight (e x)) (E : β → Prop) :
    μ.probability (fun x => E (e x)) = ν.probability E := by
  unfold FiniteLaw.probability FiniteLaw.average
  simp_rw [hweight]
  exact e.sum_comp (fun y => ν.weight y * if E y then 1 else 0)

noncomputable def sieveCubeCRT {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j))) :
    (ZMod (∏ i, s i) × ZMod (∏ i, s i) × ZMod (∏ i, s i)) ≃
      (∀ i, ZMod (s i) × ZMod (s i) × ZMod (s i)) where
  toFun x i := (ZMod.prodEquivPi s hcop x.1 i,
    ZMod.prodEquivPi s hcop x.2.1 i, ZMod.prodEquivPi s hcop x.2.2 i)
  invFun y := ((ZMod.prodEquivPi s hcop).symm (fun i => (y i).1),
    (ZMod.prodEquivPi s hcop).symm (fun i => (y i).2.1),
    (ZMod.prodEquivPi s hcop).symm (fun i => (y i).2.2))
  left_inv x := by
    apply Prod.ext
    · exact (ZMod.prodEquivPi s hcop).symm_apply_apply x.1
    · apply Prod.ext
      · exact (ZMod.prodEquivPi s hcop).symm_apply_apply x.2.1
      · exact (ZMod.prodEquivPi s hcop).symm_apply_apply x.2.2
  right_inv y := by
    funext i
    apply Prod.ext
    · exact congrFun ((ZMod.prodEquivPi s hcop).apply_symm_apply (fun i => (y i).1)) i
    · apply Prod.ext
      · exact congrFun ((ZMod.prodEquivPi s hcop).apply_symm_apply (fun i => (y i).2.1)) i
      · exact congrFun ((ZMod.prodEquivPi s hcop).apply_symm_apply (fun i => (y i).2.2)) i

lemma uniformZModLaw_crt_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j))) (x : ZMod (∏ i, s i)) :
    (uniformZModLaw (∏ i, s i)).weight x =
      (FiniteLaw.dependentIndependent (fun i => uniformZModLaw (s i))).weight
        (ZMod.prodEquivPi s hcop x) := by
  simp [uniformZModLaw, FiniteLaw.dependentIndependent, one_div,
    prod_inv_distrib, Nat.cast_prod]

lemma uniformCube_crt_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (x : ZMod (∏ i, s i) × ZMod (∏ i, s i) × ZMod (∏ i, s i)) :
    (uniformResidueCubeLaw (∏ i, s i)).weight x =
      (FiniteLaw.dependentIndependent (fun i => uniformResidueCubeLaw (s i))).weight
        (sieveCubeCRT s hcop x) := by
  simp only [uniformResidueCubeLaw, FiniteLaw.product, uniformZModLaw,
    FiniteLaw.dependentIndependent, prod_mul_distrib, one_div, prod_inv_distrib, Nat.cast_prod]

/-- CRT evaluates an intersection of one-variable local conditions exactly. -/
theorem sieveCRT_one_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (E : ∀ i, ZMod (s i) → Prop) :
    (uniformZModLaw (∏ i, s i)).probability
      (fun x => ∀ i, E i (ZMod.prodEquivPi s hcop x i)) =
      ∏ i, (uniformZModLaw (s i)).probability (E i) := by
  calc
    _ = (FiniteLaw.dependentIndependent (fun i => uniformZModLaw (s i))).probability
        (fun x => ∀ i, E i (x i)) :=
      FiniteLaw.probability_equiv _ _ (ZMod.prodEquivPi s hcop).toEquiv
        (uniformZModLaw_crt_weight s hcop) (fun x => ∀ i, E i (x i))
    _ = _ := FiniteLaw.dependentIndependent_probability_all
      (fun i => uniformZModLaw (s i)) E

/-- CRT evaluates an intersection of local three-variable conditions
exactly, retaining the dependence among the forms at each individual prime. -/
theorem sieveCRT_cube_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (E : ∀ i, (ZMod (s i) × ZMod (s i) × ZMod (s i)) → Prop) :
    (uniformResidueCubeLaw (∏ i, s i)).probability
      (fun x => ∀ i, E i (sieveCubeCRT s hcop x i)) =
      ∏ i, (uniformResidueCubeLaw (s i)).probability (E i) := by
  calc
    _ = (FiniteLaw.dependentIndependent (fun i => uniformResidueCubeLaw (s i))).probability
        (fun x => ∀ i, E i (x i)) :=
      FiniteLaw.probability_equiv _ _ (sieveCubeCRT s hcop)
        (uniformCube_crt_weight s hcop) (fun x => ∀ i, E i (x i))
    _ = _ := FiniteLaw.dependentIndependent_probability_all
      (fun i => uniformResidueCubeLaw (s i)) E

end TwoPointCorrelations

end OAI
