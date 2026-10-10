import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.ComplexCWPrimitiveDegeneration
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.ComplexCWOriginalWords
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexElementary

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.Foundation.CW75Primitive

open Polynomial
open scoped BigOperators Classical

abbrev Word := Fin 3 → Fin 3

def source : Tensor ℂ Word Word Word := Tensor.power CWBoundary.tensor 3

def hasB (x : Word) : Prop := ∃ i, x i ≠ 0

def hasC (y : Word) : Prop := ∃ i, y i = 2

def allA (z : Word) : Prop := ∀ i, z i ≠ 0

def retained (x y z : Word) : Prop := ¬ (hasB x ∧ hasC y) ∧ ¬ allA z

def tensor : Tensor ℂ Word Word Word :=
  fun x y z => if retained x y z then source x y z else 0

def mixed : Tensor ℂ Word Word Word :=
  fun x y z => if hasB x ∧ hasC y ∧ ¬ allA z then source x y z else 0

theorem boundary_active (x y z : Fin 3) (h : CWBoundary.tensor x y z ≠ 0) :
    z ≠ 0 ↔ x = 0 ∧ y ≠ 2 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [← Fin.val_eq_val, CWBoundary.tensor, CoppersmithWinograd.tensor] at h <;>
      norm_num [← Fin.val_eq_val]

theorem source_factors (x y z : Word) (h : source x y z ≠ 0) (i : Fin 3) :
    CWBoundary.tensor (x i) (y i) (z i) ≠ 0 := by
  unfold source Tensor.power at h
  exact (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)

theorem allA_iff (x y z : Word) (h : source x y z ≠ 0) :
    allA z ↔ ¬ hasB x ∧ ¬ hasC y := by
  have hpoint (i : Fin 3) : z i ≠ 0 ↔ x i = 0 ∧ y i ≠ 2 :=
    boundary_active _ _ _ (source_factors x y z h i)
  simp only [allA, hasB, hasC, not_exists, not_not, hpoint, forall_and]

def leftMap (output input : Word) : Polynomial ℂ :=
  if input = output then (if hasB output then X else 1) else 0

def middleMap (output input : Word) : Polynomial ℂ :=
  if input = output then (if hasC output then X else 1) else 0

def rightMap (output input : Word) : Polynomial ℂ :=
  if input = output ∧ ¬ allA output then 1 else 0

def polynomial : Tensor (Polynomial ℂ) Word Word Word :=
  Tensor.restrict leftMap middleMap rightMap (fun x y z => C (source x y z))

theorem polynomial_apply (x y z : Word) :
    polynomial x y z = if allA z then 0 else
      (if hasB x then X else 1) * (if hasC y then X else 1) * C (source x y z) := by
  by_cases hz : allA z <;>
    simp [polynomial, Tensor.restrict, leftMap, middleMap, rightMap,
      ite_mul, mul_ite, hz]

theorem polynomial_identity (x y z : Word) :
    polynomial x y z = X * C (tensor x y z) + X ^ 2 * C (mixed x y z) := by
  by_cases hs : source x y z = 0
  · simp [polynomial_apply, tensor, mixed, hs]
  · have hA := allA_iff x y z hs
    by_cases hz : allA z <;> by_cases hx : hasB x <;> by_cases hy : hasC y
    all_goals simp_all [polynomial_apply, tensor, mixed, retained, pow_two]

theorem polynomial_coeff (x y z : Word) (j : ℕ) :
    (polynomial x y z).coeff j =
      (if j = 1 then tensor x y z else 0) + (if j = 2 then mixed x y z else 0) := by
  rw [polynomial_identity, Polynomial.coeff_add,
    mul_comm X (C (tensor x y z)), mul_comm (X ^ 2) (C (mixed x y z)),
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]

theorem leftMap_degree (output input : Word) : (leftMap output input).degree ≤ 1 := by
  by_cases heq : input = output <;> by_cases hx : hasB output <;>
    simp [leftMap, heq, hx]

theorem middleMap_degree (output input : Word) : (middleMap output input).degree ≤ 1 := by
  by_cases heq : input = output <;> by_cases hy : hasC output <;>
    simp [middleMap, heq, hy]

theorem rightMap_degree (output input : Word) : (rightMap output input).degree ≤ 0 := by
  by_cases h : input = output ∧ ¬ allA output <;> simp [rightMap, h]

def restriction : Tensor.PolynomialRestrictionDegeneration source tensor 1 1 1 0 where
  leftMap := leftMap
  middleMap := middleMap
  rightMap := rightMap
  left_degree := leftMap_degree
  middle_degree := middleMap_degree
  right_degree := rightMap_degree
  vanishes := by
    intro x y z j hj
    have hcoeff := polynomial_coeff x y z j
    unfold polynomial at hcoeff
    rw [hcoeff]
    have hjzero : j = 0 := by omega
    simp [hjzero]
  leading := by
    intro x y z
    have hcoeff := polynomial_coeff x y z 1
    unfold polynomial at hcoeff
    rw [hcoeff]
    simp

@[simp] theorem restriction_basePolynomial : restriction.basePolynomial = polynomial := rfl

def sourceApproximation : Tensor.PolynomialApproximation source 27 15 45 :=
  CWPrimitiveDegeneration.boundaryApproximation.power 3

def approximation : Tensor.PolynomialApproximation tensor 27 31 92 :=
  restriction.compose sourceApproximation

@[simp] theorem approximation_polynomial :
    approximation.polynomial = Tensor.restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.expand ℂ 2
        (Tensor.power CWPrimitiveDegeneration.boundaryApproximation.polynomial 3 x y z)) := by
  simp only [approximation, Tensor.PolynomialRestrictionDegeneration.compose,
    Tensor.PolynomialRestrictionDegeneration.compositionPolynomial,
    restriction, sourceApproximation, Tensor.PolynomialApproximation.power]

theorem leading (x y z : Word) : (approximation.polynomial x y z).coeff 31 = tensor x y z :=
  approximation.leading x y z

theorem borderRankAtMost : Tensor.BorderRankAtMost tensor 27 := approximation.borderRankAtMost

theorem original_support (x y z : Word) (h : tensor x y z ≠ 0) (i : Fin 3) :
    (x i).val + (y i).val + (z i).val = 2 := by
  have hs : source x y z ≠ 0 := by
    intro hs
    simp [tensor, hs] at h
  have hi := source_factors x y z hs i
  have hcw : CoppersmithWinograd.tensor (x i) (y i) (z i) ≠ 0 := by
    intro hzero
    simp [CWBoundary.tensor, hzero] at hi
  exact (CWOriginalWords.tensor_ne_zero_iff _ _ _).mp hcw

theorem originalWords_decode (x y z : Word) (h : tensor x y z ≠ 0) :
    CWOriginalWords.originalWords (CWOriginalWords.decodeWord x y z) = (x, y, z) :=
  CWOriginalWords.originalWords_decodeWord_of_support x y z (original_support x y z h)

open Elementary

def component : BoundaryTerm → CWOriginalWords.OriginalComponent
  | .a0 => ⟨(0, 0, 2), by decide⟩
  | .a1 => ⟨(0, 1, 1), by decide⟩
  | .b0 => ⟨(2, 0, 0), by decide⟩
  | .b1 => ⟨(1, 1, 0), by decide⟩
  | .c => ⟨(0, 2, 0), by decide⟩

theorem component_injective : Function.Injective component := by
  intro a b h
  have hx := congrArg (fun g => (CWOriginalWords.OriginalComponent.x g).val) h
  have hy := congrArg (fun g => (CWOriginalWords.OriginalComponent.y g).val) h
  have hz := congrArg (fun g => (CWOriginalWords.OriginalComponent.z g).val) h
  cases a <;> cases b <;>
    simp_all [component, CWOriginalWords.OriginalComponent.x,
      CWOriginalWords.OriginalComponent.y, CWOriginalWords.OriginalComponent.z]

def listedWord (w : List BoundaryTerm) : Fin 3 → CWOriginalWords.OriginalComponent :=
  fun i => component (w.getD i.val .a0)

def listedX (w : List BoundaryTerm) : Word := CWOriginalWords.xWord (listedWord w)
def listedY (w : List BoundaryTerm) : Word := CWOriginalWords.yWord (listedWord w)
def listedZ (w : List BoundaryTerm) : Word := CWOriginalWords.zWord (listedWord w)

theorem tensor_on_triple (a b third : BoundaryTerm) :
    tensor (listedX [a, b, third]) (listedY [a, b, third]) (listedZ [a, b, third]) =
      if Elementary.retained [a, b, third] then 1 else 0 := by
  have hboundary (s : BoundaryTerm) :
      CWBoundary.tensor (component s).x (component s).y (component s).z = 1 := by
    cases s <;>
      norm_num [component, CWOriginalWords.OriginalComponent.x,
        CWOriginalWords.OriginalComponent.y, CWOriginalWords.OriginalComponent.z,
        CWBoundary.tensor, CoppersmithWinograd.tensor, ← Fin.val_eq_val]
  have hx (s : BoundaryTerm) : (component s).x.val = s.x := by cases s <;> rfl
  have hy (s : BoundaryTerm) : (component s).y.val = s.y := by cases s <;> rfl
  have hz (s : BoundaryTerm) : (component s).z.val = s.z := by cases s <;> rfl
  simp [tensor, retained, source, Tensor.power,
      hasB, hasC, allA, Fin.exists_fin_succ, Fin.forall_fin_succ,
      listedX, listedY, listedZ, listedWord,
      CWOriginalWords.xWord, CWOriginalWords.yWord, CWOriginalWords.zWord,
      ← Fin.val_eq_val, hboundary, hx, hy, hz,
      Elementary.retained, Elementary.testA, Elementary.testB, Elementary.testC]
  cases a <;> cases b <;> cases third <;>
    norm_num [BoundaryTerm.x, BoundaryTerm.y, BoundaryTerm.z]

theorem mem_triples_shape (w : List BoundaryTerm) (hw : w ∈ Elementary.triples) :
    ∃ a b third, w = [a, b, third] := by
  simp only [Elementary.triples, List.mem_flatMap, List.mem_map] at hw
  rcases hw with ⟨a, _, b, _, third, _, rfl⟩
  exact ⟨a, b, third, rfl⟩

theorem tensor_on_enumeration (w : List BoundaryTerm) (hw : w ∈ Elementary.triples) :
    tensor (listedX w) (listedY w) (listedZ w) =
      if Elementary.retained w then 1 else 0 := by
  rcases mem_triples_shape w hw with ⟨a, b, third, rfl⟩
  exact tensor_on_triple a b third

theorem retained_coefficient_one (w : List BoundaryTerm)
    (hw : w ∈ Elementary.triples.filter Elementary.retained) :
    tensor (listedX w) (listedY w) (listedZ w) = 1 := by
  rw [tensor_on_enumeration w (List.mem_filter.mp hw).1]
  simp [(List.mem_filter.mp hw).2]

theorem listed_coefficient_count :
    (Elementary.triples.filter (fun w =>
      decide (tensor (listedX w) (listedY w) (listedZ w) = 1))).length = 75 := by
  have heq : Elementary.triples.filter (fun w =>
      decide (tensor (listedX w) (listedY w) (listedZ w) = 1)) =
      Elementary.triples.filter Elementary.retained := by
    apply List.filter_congr
    intro w hw
    rw [tensor_on_enumeration w hw]
    cases Elementary.retained w <;> simp
  rw [heq]
  exact Elementary.retained_triples_count

theorem listedWords_injective (w v : List BoundaryTerm)
    (hw : w ∈ Elementary.triples) (hv : v ∈ Elementary.triples)
    (he : CWOriginalWords.originalWords (listedWord w) =
      CWOriginalWords.originalWords (listedWord v)) : w = v := by
  rcases mem_triples_shape w hw with ⟨a, b, third, rfl⟩
  rcases mem_triples_shape v hv with ⟨a', b', c', rfl⟩
  have hword := CWOriginalWords.originalWords_injective he
  have ha := component_injective (by simpa [listedWord] using congrFun hword 0)
  have hb := component_injective (by simpa [listedWord] using congrFun hword 1)
  have hc := component_injective (by simpa [listedWord] using congrFun hword 2)
  simp [ha, hb, hc]

theorem boundary_component_complete (x y z : Fin 3)
    (h : CWBoundary.tensor x y z ≠ 0) :
    ∃ a : BoundaryTerm, (component a).x = x ∧ (component a).y = y ∧
      (component a).z = z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [CWBoundary.tensor, CoppersmithWinograd.tensor] at h
  all_goals first
    | exact ⟨.a0, rfl, rfl, rfl⟩
    | exact ⟨.a1, rfl, rfl, rfl⟩
    | exact ⟨.b0, rfl, rfl, rfl⟩
    | exact ⟨.b1, rfl, rfl, rfl⟩
    | exact ⟨.c, rfl, rfl, rfl⟩

private theorem term_mem_all (a : BoundaryTerm) : a ∈ BoundaryTerm.all := by
  cases a <;> simp [BoundaryTerm.all]

private theorem triple_mem (a b third : BoundaryTerm) : [a, b, third] ∈ Elementary.triples := by
  simp only [Elementary.triples, List.mem_flatMap, List.mem_map]
  exact ⟨a, term_mem_all a, b, term_mem_all b, third, term_mem_all third, rfl⟩

theorem triples_nodup : Elementary.triples.Nodup := by
  decide

theorem support_exhausted (x y z : Word) (h : tensor x y z ≠ 0) :
    ∃ w, w ∈ Elementary.triples.filter Elementary.retained ∧
      (listedX w, listedY w, listedZ w) = (x, y, z) := by
  have hs : source x y z ≠ 0 := by
    intro hs
    simp [tensor, hs] at h
  obtain ⟨a, hax, hay, haz⟩ :=
    boundary_component_complete (x 0) (y 0) (z 0) (source_factors x y z hs 0)
  obtain ⟨b, hbx, hby, hbz⟩ :=
    boundary_component_complete (x 1) (y 1) (z 1) (source_factors x y z hs 1)
  obtain ⟨third, hcx, hcy, hcz⟩ :=
    boundary_component_complete (x 2) (y 2) (z 2) (source_factors x y z hs 2)
  have hx : listedX [a, b, third] = x := by
    funext i
    fin_cases i <;>
      simp [listedX, listedWord, CWOriginalWords.xWord, hax, hbx, hcx]
  have hy : listedY [a, b, third] = y := by
    funext i
    fin_cases i <;>
      simp [listedY, listedWord, CWOriginalWords.yWord, hay, hby, hcy]
  have hz : listedZ [a, b, third] = z := by
    funext i
    fin_cases i <;>
      simp [listedZ, listedWord, CWOriginalWords.zWord, haz, hbz, hcz]
  have hc := tensor_on_triple a b third
  rw [hx, hy, hz] at hc
  have hr : Elementary.retained [a, b, third] = true := by
    cases hret : Elementary.retained [a, b, third] <;> simp_all
  exact ⟨[a, b, third], List.mem_filter.mpr ⟨triple_mem a b third, hr⟩,
    Prod.ext hx (Prod.ext hy hz)⟩

end MatrixMultiplication.Foundation.CW75Primitive

end

end OAI
