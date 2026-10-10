import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Avoids
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MassNonneg

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical

namespace OrdinaryCorrelations.SourceRoughSieveCRT
open Classical Finset
open OrdinaryCorrelations.FiniteResidues OrdinaryCorrelations.SourceRoughSieveLocal
variable {ι : Type*} [Fintype ι] (s : ι → ℕ) [∀ i, NeZero (s i)]

instance product_neZero : NeZero (∏ i, s i) := ⟨(Finset.prod_pos (fun i _ => NeZero.pos (s i))).ne'⟩

def cubeTest (hc : Pairwise (Function.onFun Nat.Coprime s))
    (F : ∀ i, ZMod (s i) → ZMod (s i) → ZMod (s i) → ℝ)
    (x y z : ZMod (∏ i, s i)) : ℝ :=
  ∏ i, F i ((ZMod.prodEquivPi s hc) x i) ((ZMod.prodEquivPi s hc) y i)
    ((ZMod.prodEquivPi s hc) z i)

lemma cubeTest_natCast (s : ι → ℕ) [∀ index, NeZero (s index)]
    (hc : Pairwise (Function.onFun Nat.Coprime s))
    (F : ∀ i, ZMod (s i) → ZMod (s i) → ZMod (s i) → ℝ) (x y z : ℕ) :
    cubeTest s hc F (x : ZMod (∏ i, s i)) (y : ZMod (∏ i, s i)) (z : ZMod (∏ i, s i)) =
      ∏ i, F i (x : ZMod (s i)) (y : ZMod (s i)) (z : ZMod (s i)) := by
  unfold cubeTest
  simp only [map_natCast]
  rfl

lemma cubeTest_abs_le (s : ι → ℕ) [∀ index, NeZero (s index)]
    (hc : Pairwise (Function.onFun Nat.Coprime s))
    (F : ∀ i, ZMod (s i) → ZMod (s i) → ZMod (s i) → ℝ)
    (hF : ∀ i x y z, |F i x y z| ≤ 1) (x y z) : |cubeTest s hc F x y z| ≤ 1 := by
  unfold cubeTest
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i : ι, (1:ℝ) := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun index _ => hF index _ _ _)
    _ = 1 := Finset.prod_const_one

theorem uniform_cube_CRT (hc : Pairwise (Function.onFun Nat.Coprime s))
    (F : ∀ i, ZMod (s i) → ZMod (s i) → ZMod (s i) → ℝ) :
    uniformCubeMean (∏ i, s i) (cubeTest s hc F) =
      ∏ i, uniformCubeMean (s i) (F i) := by
  let e := (ZMod.prodEquivPi s hc).toEquiv
  have hsum : (∑ x, ∑ y, ∑ z, cubeTest s hc F x y z) =
      ∏ i, ∑ x, ∑ y, ∑ z, F i x y z := by
    unfold cubeTest
    change (∑ x, ∑ y, ∑ z, ∏ i, F i (e x i) (e y i) (e z i)) = _
    calc
      _ = ∑ x : ∀ i, ZMod (s i), ∑ y, ∑ z, ∏ i, F i (x i) (e y i) (e z i) :=
        e.sum_comp (fun x => ∑ y, ∑ z, ∏ i, F i (x i) (e y i) (e z i))
      _ = ∑ x : ∀ i, ZMod (s i), ∑ y : ∀ i, ZMod (s i), ∑ z, ∏ i, F i (x i) (y i) (e z i) := by
        apply Finset.sum_congr rfl
        intro x _
        exact e.sum_comp (fun y => ∑ z, ∏ i, F i (x i) (y i) (e z i))
      _ = ∑ x : ∀ i, ZMod (s i), ∑ y : ∀ i, ZMod (s i), ∑ z : ∀ i, ZMod (s i),
          ∏ i, F i (x i) (y i) (z i) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        exact e.sum_comp (fun z => ∏ i, F i (x i) (y i) (z i))
      _ = _ := by
        have hz (x y : ∀ i, ZMod (s i)) :
            (∑ z : ∀ i, ZMod (s i), ∏ i, F i (x i) (y i) (z i)) =
              ∏ i, ∑ z, F i (x i) (y i) z :=
          (Fintype.prod_sum (fun i z => F i (x i) (y i) z)).symm
        have hy (x : ∀ i, ZMod (s i)) :
            (∑ y : ∀ i, ZMod (s i), ∏ i, ∑ z, F i (x i) (y i) z) =
              ∏ i, ∑ y, ∑ z, F i (x i) y z :=
          (Fintype.prod_sum (fun i y => ∑ z, F i (x i) y z)).symm
        simp_rw [hz,hy]
        exact (Fintype.prod_sum (fun i x => ∑ y, ∑ z, F i x y z)).symm
  unfold uniformCubeMean
  rw [hsum]
  have hfactor : (((∏ i, s i : ℕ):ℝ)⁻¹)^3 = ∏ i, ((s i:ℝ)⁻¹)^3 := by
    simp only [Nat.cast_prod,Finset.prod_inv_distrib,Finset.prod_pow]
  rw [hfactor,Finset.prod_mul_distrib]

theorem cube_CRT_boundary (hc : Pairwise (Function.onFun Nat.Coprime s))
    (F : ∀ i, ZMod (s i) → ZMod (s i) → ZMod (s i) → ℝ)
    (hF : ∀ i x y z, |F i x y z| ≤ 1) (a N : ℕ) (hN : 0 < N) :
    |(N:ℝ)⁻¹^3 * (∑ x ∈ range N, ∑ y ∈ range N, ∑ z ∈ range N,
      ∏ i, F i ((a+x : ℕ) : ZMod (s i)) ((a+y : ℕ) : ZMod (s i)) ((a+z : ℕ) : ZMod (s i))) -
      ∏ i, uniformCubeMean (s i) (F i)| ≤ 3 * ((∏ i, s i : ℕ):ℝ) / N := by
  have h := cube_boundary (∏ i, s i) a N hN (cubeTest s hc F) (cubeTest_abs_le s hc F hF)
  rwa [uniform_cube_CRT, cubeMean, show
    (∑ x ∈ range N, ∑ y ∈ range N, ∑ z ∈ range N,
      cubeTest s hc F ((a+x : ℕ) : ZMod (∏ i, s i)) ((a+y : ℕ) : ZMod (∏ i, s i))
        ((a+z : ℕ) : ZMod (∏ i, s i))) =
      (∑ x ∈ range N, ∑ y ∈ range N, ∑ z ∈ range N,
      ∏ i, F i ((a+x : ℕ) : ZMod (s i)) ((a+y : ℕ) : ZMod (s i)) ((a+z : ℕ) : ZMod (s i))) by
        simp only [cubeTest_natCast]] at h

theorem bad_intersection_boundary (hc : Pairwise (Function.onFun Nat.Coprime s))
    (a N : ℕ) (hN : 0 < N) :
    |(N:ℝ)⁻¹^3 * (∑ x ∈ range N, ∑ y ∈ range N, ∑ z ∈ range N,
      ∏ i, if avoids (s i) ((a+x : ℕ) : ZMod (s i)) ((a+y : ℕ) : ZMod (s i))
        ((a+z : ℕ) : ZMod (s i)) then (0:ℝ) else 1) -
      ∏ i, badDensity (s i)| ≤ 3 * ((∏ i, s i : ℕ):ℝ) / N := by
  exact cube_CRT_boundary s hc (fun i x y z => if avoids (s i) x y z then 0 else 1)
    (fun _ _ _ _ => by split_ifs <;> norm_num) a N hN

end OrdinaryCorrelations.SourceRoughSieveCRT

end

end OAI
