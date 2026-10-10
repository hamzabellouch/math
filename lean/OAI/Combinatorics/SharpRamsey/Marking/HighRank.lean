import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.ProjectiveTransport
import OAI.Combinatorics.SharpRamsey.Parameters.EndpointScales

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
section

namespace SharpLogRamsey
namespace RichUnion

noncomputable section

open Module MvPolynomial

section LinearAlgebra
variable {K A B C : Type*} [Field K]
  [AddCommGroup A] [Module K A] [FiniteDimensional K A]
  [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]

theorem rank_le_of_ker_le (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (h : LinearMap.ker f ≤ LinearMap.ker g) :
    finrank K (LinearMap.range g) ≤ finrank K (LinearMap.range f) := by
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  have hk := Submodule.finrank_mono h
  omega

theorem finrank_finset_sup_le {ι : Type*} [FiniteDimensional K B]
    (S : Finset ι) (W : ι → Submodule K B) :
    finrank K (S.sup W : Submodule K B) ≤ ∑ i ∈ S, finrank K (W i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

end LinearAlgebra

section Evaluation
variable {K : Type*} [Field K] {n : ℕ}

def evalOn (Z : Finset (Fin n → K)) : MvPolynomial (Fin n) K →ₗ[K] (Z → K) where
  toFun p z := MvPolynomial.eval z.1 p
  map_add' p q := by ext z; simp
  map_smul' a p := by ext z; simp

@[simp] theorem evalOn_apply (Z : Finset (Fin n → K))
    (p : MvPolynomial (Fin n) K) (z : Z) :
    evalOn Z p z = MvPolynomial.eval z.1 p := rfl

def evalSpace (Z : Finset (Fin n → K)) (m : ℕ) : Submodule K (Z → K) :=
  (MvPolynomial.restrictDegree (Fin n) K m).map (evalOn Z)

def diagonal (Z : Finset (Fin n → K)) (e : Fin n →₀ ℕ) : (Z → K) →ₗ[K] (Z → K) where
  toFun v z := (MvPolynomial.eval z.1 (MvPolynomial.monomial e (1 : K))) * v z
  map_add' v w := by ext z; simp [mul_add]
  map_smul' a v := by ext z; simp [mul_comm, mul_assoc]

theorem evalSpace_full [Fintype K] (Z : Finset (Fin n → K)) :
    evalSpace Z (Fintype.card K - 1) = ⊤ := by
  classical
  apply top_unique
  intro f _
  let g : (Fin n → K) → K := fun v => if hv : v ∈ Z then f ⟨v, hv⟩ else 0
  have hg : g ∈ (MvPolynomial.restrictDegree (Fin n) K (Fintype.card K - 1)).map
      (MvPolynomial.evalₗ K (Fin n)) := by
    rw [MvPolynomial.map_restrict_dom_evalₗ]
    trivial
  rcases hg with ⟨p, hp, he⟩
  refine ⟨p, hp, ?_⟩
  ext z
  have hz := congrFun he z.1
  simpa [g, z.property] using hz

theorem evalSpace_box_partition (Z : Finset (Fin n → K)) (a c q : ℕ)
    (ha : 0 < a) (hq : 0 < q) (hqc : q ≤ a*c) :
    evalSpace Z (q-1) ≤
      Finset.univ.sup (fun b : Fin n → Fin c =>
        (evalSpace Z (a-1)).map (diagonal Z
          (Finsupp.equivFunOnFinite.symm (fun i => a * (b i).val)))) := by
  classical
  rw [evalSpace, MvPolynomial.restrictDegree, MvPolynomial.restrictSupport_eq_span,
    Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
  let b : Fin n → Fin c := fun i => ⟨s i / a, by
    apply (Nat.div_lt_iff_lt_mul ha).mpr
    have hi := hs i
    rw [mul_comm]
    omega⟩
  let v : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => a * (b i).val)
  let r : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => s i % a)
  have hsr : s = v + r := by
    ext i
    change s i = a * (s i / a) + s i % a
    simpa [Nat.add_comm] using (Nat.mod_add_div (s i) a).symm
  have hinc : (evalSpace Z (a-1)).map (diagonal Z v) ≤
      Finset.univ.sup (fun b : Fin n → Fin c =>
        (evalSpace Z (a-1)).map (diagonal Z
          (Finsupp.equivFunOnFinite.symm (fun i => a * (b i).val)))) :=
    Finset.le_sup (f := fun b : Fin n → Fin c =>
      (evalSpace Z (a-1)).map (diagonal Z
        (Finsupp.equivFunOnFinite.symm (fun i => a * (b i).val)))) (Finset.mem_univ b)
  apply hinc
  refine Submodule.mem_map.mpr ⟨evalOn Z (MvPolynomial.monomial r 1), ?_, ?_⟩
  · refine Submodule.mem_map.mpr ⟨MvPolynomial.monomial r 1, ?_, rfl⟩
    rw [MvPolynomial.restrictDegree, MvPolynomial.monomial_mem_restrictSupport]
    left
    intro i
    have := Nat.mod_lt (s i) ha
    change s i % a ≤ a-1
    omega
  · ext z
    simp only [diagonal, LinearMap.coe_mk, AddHom.coe_mk, evalOn_apply]
    rw [hsr, ← MvPolynomial.eval_mul, MvPolynomial.monomial_mul_monomial]
    simp

theorem card_le_boxes_mul_eval_rank [Fintype K] (Z : Finset (Fin n → K))
    (a c : ℕ) (ha : 0 < a) (hqc : Fintype.card K ≤ a*c) :
    Z.card ≤ c^n * finrank K (evalSpace Z (a-1)) := by
  classical
  let W : (Fin n → Fin c) → Submodule K (Z → K) := fun b =>
    (evalSpace Z (a-1)).map (diagonal Z
      (Finsupp.equivFunOnFinite.symm (fun i => a * (b i).val)))
  have htop : (⊤ : Submodule K (Z → K)) ≤ Finset.univ.sup W := by
    rw [← evalSpace_full Z]
    exact evalSpace_box_partition Z a c (Fintype.card K) ha Fintype.card_pos hqc
  have hdim := Submodule.finrank_mono htop
  have hsum := finrank_finset_sup_le Finset.univ W
  have hle : (∑ b : Fin n → Fin c, finrank K (W b)) ≤
      c^n * finrank K (evalSpace Z (a-1)) := by
    calc
      _ ≤ ∑ _b : Fin n → Fin c, finrank K (evalSpace Z (a-1)) :=
        Finset.sum_le_sum (fun b _ => Submodule.finrank_map_le _ _)
      _ = _ := by simp
  simpa using hdim.trans (hsum.trans hle)

theorem totalDegree_aeval_linear {r : ℕ}
    (φ : Fin n → MvPolynomial (Fin r) K)
    (hφ : ∀ i, (φ i).totalDegree ≤ 1) (p : MvPolynomial (Fin n) K) :
    (MvPolynomial.aeval φ p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  rw [MvPolynomial.aeval_monomial]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ i ∈ s.support, ((φ i) ^ s i).totalDegree
        ≤ ∑ i ∈ s.support, s i := by
          apply Finset.sum_le_sum
          intro i hi
          exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (s i) (hφ i))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hs

def linearCoordinates {r : ℕ} (f : (Fin r → K) →ₗ[K] (Fin n → K))
    (j : Fin n) : MvPolynomial (Fin r) K :=
  ∑ i : Fin r, MvPolynomial.C (f (Pi.single i 1) j) * MvPolynomial.X i

theorem totalDegree_linearCoordinates {r : ℕ}
    (f : (Fin r → K) →ₗ[K] (Fin n → K)) (j : Fin n) :
    (linearCoordinates f j).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  simpa using MvPolynomial.totalDegree_mul
    (MvPolynomial.C (f (Pi.single i 1) j)) (MvPolynomial.X i)

theorem eval_linearCoordinates {r : ℕ}
    (f : (Fin r → K) →ₗ[K] (Fin n → K)) (x : Fin r → K) (j : Fin n) :
    MvPolynomial.eval x (linearCoordinates f j) = f x j := by
  classical
  have hx : x = ∑ i : Fin r, x i • Pi.single i (1 : K) := by
    ext j
    simp [Pi.single_apply]
  simp only [linearCoordinates, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  conv_rhs => rw [hx]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

theorem eval_aeval_linearCoordinates {r : ℕ}
    (f : (Fin r → K) →ₗ[K] (Fin n → K)) (x : Fin r → K)
    (p : MvPolynomial (Fin n) K) :
    MvPolynomial.eval x (MvPolynomial.aeval (linearCoordinates f) p) =
      MvPolynomial.eval (f x) p := by
  apply MvPolynomial.induction_on p
  · intro a
    simp
  · intro a b ha hb
    simp only [map_add, ha, hb]
  · intro p i hp
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, hp, eval_linearCoordinates]

theorem totalDegree_le_of_restrictDegree (p : MvPolynomial (Fin n) K) (m : ℕ)
    (hp : p ∈ MvPolynomial.restrictDegree (Fin n) K m) :
    p.totalDegree ≤ n*m := by
  classical
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro s hs
  rw [Finsupp.sum_fintype _ _ (by simp)]
  calc
    ∑ i : Fin n, s i ≤ ∑ _i : Fin n, m :=
      Finset.sum_le_sum (fun i _ => (MvPolynomial.mem_restrictDegree _ _ _).mp hp s hs i)
    _ = n*m := by simp

theorem card_roots_mul_le [Fintype K] [DecidableEq K] {r : ℕ} (p : MvPolynomial (Fin r) K)
    (hp : p ≠ 0) :
    (Finset.univ.filter (fun x : Fin r → K => MvPolynomial.eval x p = 0)).card *
      Fintype.card K ≤ p.totalDegree * (Fintype.card K)^r := by
  classical
  have h := MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset K)
  simp only [Finset.card_univ] at h
  simp at h
  have hq : (0 : ℚ≥0) < Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have h' := (div_le_div_iff₀ (pow_pos hq r) hq).mp h
  exact_mod_cast h'

def inSubspace (X : Finset (Fin n → K)) (W : Submodule K (Fin n → K)) :
    Finset (Fin n → K) := by
  classical
  exact X.filter (fun x => x ∈ W)

@[simp] theorem mem_inSubspace (X : Finset (Fin n → K))
    (W : Submodule K (Fin n → K)) (x : Fin n → K) :
    x ∈ inSubspace X W ↔ x ∈ X ∧ x ∈ W := by
  classical
  simp [inSubspace]

theorem vanish_on_rich_subspace [Fintype K]
    (X : Finset (Fin n → K)) (W : Submodule K (Fin n → K)) (m : ℕ)
    (hrich : n*m * Nat.card W < (inSubspace X W).card * Fintype.card K)
    (p : MvPolynomial (Fin n) K) (hp : p ∈ MvPolynomial.restrictDegree (Fin n) K m)
    (hx : ∀ x ∈ X, MvPolynomial.eval x p = 0) :
    ∀ y ∈ W, MvPolynomial.eval y p = 0 := by
  classical
  let r := finrank K W
  let e : (Fin r → K) ≃ₗ[K] W := (Module.finBasis K W).equivFun.symm
  let f : (Fin r → K) →ₗ[K] (Fin n → K) := W.subtype.comp e.toLinearMap
  let P := MvPolynomial.aeval (linearCoordinates f) p
  have hPdeg : P.totalDegree ≤ n*m :=
    (totalDegree_aeval_linear _ (totalDegree_linearCoordinates f) p).trans
      (totalDegree_le_of_restrictDegree p m hp)
  have hcard : Nat.card W = Fintype.card K ^ r := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := W)]
  have hcount : (Finset.univ.filter (fun v : Fin r → K => f v ∈ X)).card =
      (inSubspace X W).card := by
    apply Finset.card_bij (fun v _ => f v)
    · intro v hv
      exact (mem_inSubspace _ _ _).mpr ⟨(Finset.mem_filter.mp hv).2, (e v).property⟩
    · intro v hv w hw h
      exact e.injective (Subtype.ext h)
    · intro y hy
      rcases (mem_inSubspace _ _ _).mp hy with ⟨hyX, hyW⟩
      refine ⟨e.symm ⟨y, hyW⟩, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [f] using hyX
      · simp [f]
  have hP : P = 0 := by
    by_contra hne
    have hSZ := card_roots_mul_le P hne
    have hsub : Finset.univ.filter (fun v : Fin r → K => f v ∈ X) ⊆
        Finset.univ.filter (fun v : Fin r → K => MvPolynomial.eval v P = 0) := by
      intro v hv
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      change MvPolynomial.eval v (MvPolynomial.aeval (linearCoordinates f) p) = 0
      rw [eval_aeval_linearCoordinates]
      exact hx (f v) (Finset.mem_filter.mp hv).2
    have hle := (Nat.mul_le_mul_right (Fintype.card K) (Finset.card_le_card hsub)).trans
      (hSZ.trans (Nat.mul_le_mul_right _ hPdeg))
    rw [hcount, ← hcard] at hle
    exact (not_lt_of_ge hle) hrich
  intro y hy
  have he : f (e.symm ⟨y, hy⟩) = y := by simp [f]
  have hz := eval_aeval_linearCoordinates f (e.symm ⟨y, hy⟩) p
  rw [he] at hz
  rw [← hz]
  change MvPolynomial.eval _ P = 0
  rw [hP, map_zero]

theorem evalSpace_rank_le_of_rich [Fintype K]
    (X Y : Finset (Fin n → K)) (𝓥 : Set (Submodule K (Fin n → K))) (m : ℕ)
    (hrich : ∀ W ∈ 𝓥, n*m * Nat.card W <
      (inSubspace X W).card * Fintype.card K)
    (hcover : ∀ y ∈ Y, ∃ W ∈ 𝓥, y ∈ W) :
    finrank K (evalSpace Y m) ≤ X.card := by
  classical
  let A := MvPolynomial.restrictDegree (Fin n) K m
  let f := (evalOn X).domRestrict A
  let g := (evalOn Y).domRestrict A
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    ext y
    change MvPolynomial.eval y.1 p.1 = 0
    obtain ⟨W, hW, hy⟩ := hcover y.1 y.property
    apply vanish_on_rich_subspace X W m (hrich W hW) p.1 p.property _ y.1 hy
    intro x hx
    exact congrFun hp ⟨x, hx⟩
  have h := rank_le_of_ker_le f g hker
  have hf : finrank K (LinearMap.range f) ≤ X.card := by
    simpa using Submodule.finrank_le (LinearMap.range f)
  apply (le_trans ?_ hf)
  rw [show evalSpace Y m = LinearMap.range g from
    (LinearMap.range_domRestrict A (evalOn Y)).symm]
  exact h

theorem card_union_le_boxes [Fintype K]
    (X Y : Finset (Fin n → K)) (𝓥 : Set (Submodule K (Fin n → K)))
    (a c : ℕ) (ha : 0 < a) (hqc : Fintype.card K ≤ a*c)
    (hrich : ∀ W ∈ 𝓥, n*(a-1) * Nat.card W <
      (inSubspace X W).card * Fintype.card K)
    (hcover : ∀ y ∈ Y, ∃ W ∈ 𝓥, y ∈ W) :
    Y.card ≤ c^n * X.card :=
  (card_le_boxes_mul_eval_rank Y a c ha hqc).trans
    (Nat.mul_le_mul_left _ (evalSpace_rank_le_of_rich X Y 𝓥 (a-1) hrich hcover))

theorem exists_box_parameters (n q : ℕ) (hn : 0 < n) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ a c : ℕ, 0 < a ∧ q ≤ a*c ∧
      (n*(a-1) : ℕ) ≤ δ*q/4 ∧ (c : ℝ) ≤ 5*n/δ := by
  let a := ⌊δ*q/(4*n)⌋₊ + 1
  let c := ⌊4*n/δ⌋₊ + 1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : (0 : ℝ) < 4*n := by positivity
  have ha : 0 < a := Nat.succ_pos _
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hat : δ*q < (4*n)*(a : ℝ) := by
    have h := Nat.lt_floor_add_one (δ*q/(4*n))
    have h : δ*q/(4*n) < (a : ℝ) := by simpa [a] using h
    nlinarith [(div_lt_iff₀ hden).mp h]
  have hct : 4*(n : ℝ) < δ*c := by
    have h := Nat.lt_floor_add_one (4*n/δ)
    have h : 4*n/δ < (c : ℝ) := by simpa [c] using h
    nlinarith [(div_lt_iff₀ hδ).mp h]
  have hqc : q ≤ a*c := by
    have hmul := mul_lt_mul_of_pos_left hct haR
    have h : (q : ℝ) < (a : ℝ)*(c : ℝ) := by nlinarith
    exact_mod_cast h.le
  have had : (n*(a-1) : ℕ) ≤ δ*q/4 := by
    have h := Nat.floor_le (show 0 ≤ δ*(q : ℝ)/(4*n) by positivity)
    have := (le_div_iff₀ hden).mp h
    simp only [a, Nat.add_sub_cancel, Nat.cast_mul]
    nlinarith
  have hc : (c : ℝ) ≤ 5*n/δ := by
    have h := Nat.floor_le (show 0 ≤ 4*(n : ℝ)/δ by positivity)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [c, Nat.cast_add, Nat.cast_one]
    apply (le_div_iff₀ hδ).mpr
    have := (le_div_iff₀ hδ).mp h
    nlinarith
  exact ⟨a, c, ha, hqc, had, hc⟩

theorem rich_union_vector [Fintype K] (hn : 0 < n)
    (X Y : Finset (Fin n → K)) (𝓥 : Set (Submodule K (Fin n → K)))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hne : ∀ W ∈ 𝓥, W ≠ ⊥)
    (hrich : ∀ W ∈ 𝓥, δ*((Nat.card W : ℝ)-1) ≤ (inSubspace X W).card)
    (hcover : ∀ y ∈ Y, ∃ W ∈ 𝓥, y ∈ W) :
    (Y.card : ℝ) ≤ (5*n/δ)^n * X.card := by
  classical
  obtain ⟨a, c, ha, hqc, hdeg, hc⟩ := exists_box_parameters n (Fintype.card K) hn δ hδ hδ1
  have hrich' : ∀ W ∈ 𝓥, n*(a-1) * Nat.card W <
      (inSubspace X W).card * Fintype.card K := by
    intro W hW
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr (hne W hW)
    have hN : (2 : ℝ) ≤ Nat.card W := by
      rw [Nat.card_eq_fintype_card]
      exact_mod_cast Fintype.one_lt_card (α := W)
    have hq : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
    have hlow := hrich W hW
    have hmul := mul_le_mul_of_nonneg_right hlow hq.le
    have hupper := mul_le_mul_of_nonneg_right hdeg (show (0 : ℝ) ≤ Nat.card W by positivity)
    have hstrict : ((n*(a-1) : ℕ) : ℝ) * Nat.card W <
        ((inSubspace X W).card : ℝ) * Fintype.card K := by
      have hpos : 0 < δ*(Fintype.card K : ℝ) := mul_pos hδ hq
      nlinarith
    exact_mod_cast hstrict
  have h := card_union_le_boxes X Y 𝓥 a c ha hqc hrich' hcover
  have hR : (Y.card : ℝ) ≤ (c : ℝ)^n * X.card := by exact_mod_cast h
  exact hR.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hc n) (by positivity))

end Evaluation
end
end RichUnion
end SharpLogRamsey

namespace SharpLogRamsey.RichUnion
noncomputable section
open Module

section ProjectiveLifts
variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

def vectorLifts (X : Finset (Projectivization K (Fin n → K))) : Finset (Fin n → K) := by
  classical
  exact (Finset.univ.filter (fun v : {v : Fin n → K // v ≠ 0} =>
    Projectivization.mk K v.1 v.2 ∈ X)).map (Function.Embedding.subtype _)

@[simp] theorem mem_vectorLifts (X : Finset (Projectivization K (Fin n → K)))
    (v : Fin n → K) : v ∈ vectorLifts X ↔
      ∃ hv : v ≠ 0, Projectivization.mk K v hv ∈ X := by
  classical
  simp only [vectorLifts, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨⟨v, hv⟩, hX, rfl⟩
    exact ⟨hv, hX⟩
  · rintro ⟨hv, hX⟩
    exact ⟨⟨v, hv⟩, hX, rfl⟩

end ProjectiveLifts
end
end SharpLogRamsey.RichUnion
end
end

end OAI
