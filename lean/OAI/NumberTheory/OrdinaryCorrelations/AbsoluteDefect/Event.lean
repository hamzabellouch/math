import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TruncationComparison
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ProductNeZero

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

namespace OrdinaryCorrelations.SourceBoxSieve
open Classical Finset
open SourceBonferroni SourceRoughSieveLocal SourceRoughSieveCRT
variable {ι : Type*} [Fintype ι] (s : ι → ℕ) [∀ i, NeZero (s i)]

abbrev Box (N : ℕ) := Fin N × Fin N × Fin N

def event (a N : ℕ) (i : ι) (ω : Box N) : Prop :=
  ¬ avoids (s i) ((a+ω.1.val : ℕ) : ZMod (s i)) ((a+ω.2.1.val : ℕ) : ZMod (s i))
    ((a+ω.2.2.val : ℕ) : ZMod (s i))

def weight (N : ℕ) (_ : Box N) : ℝ := (N:ℝ)⁻¹^3

def density (a N : ℕ) : ℝ :=
  survivalMass univ (weight N) univ (event s a N)

omit [Fintype ι] [∀ i, NeZero (s i)] in
lemma joint_eq_product [Fintype ι] [∀ index, NeZero (s index)]
    (a N : ℕ) (t : Finset ι) (ω : Box N) :
    joint (event s a N) t ω =
      ∏ i ∈ t, if avoids (s i) ((a+ω.1.val : ℕ) : ZMod (s i))
        ((a+ω.2.1.val : ℕ) : ZMod (s i)) ((a+ω.2.2.val : ℕ) : ZMod (s i)) then (0:ℝ) else 1 := by
  have he : joint (event s a N) t ω = ∏ i ∈ t, if event s a N i ω then (1:ℝ) else 0 := by
    rw [Finset.prod_boole]
    rfl
  rw [he]
  apply Finset.prod_congr rfl
  intro i _
  unfold event
  split_ifs <;> simp_all

lemma sum_box (N : ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    (∑ x : Fin N, ∑ y : Fin N, ∑ z : Fin N, F x.val y.val z.val) =
      ∑ x ∈ range N, ∑ y ∈ range N, ∑ z ∈ range N, F x y z := by
  rw [Fin.sum_univ_eq_sum_range (fun x => ∑ y : Fin N, ∑ z : Fin N, F x y.val z.val)]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fin.sum_univ_eq_sum_range (fun y => ∑ z : Fin N, F x y z.val)]
  apply Finset.sum_congr rfl
  intro y _
  exact Fin.sum_univ_eq_sum_range (fun z => F x y z) N

lemma intersection_eq_sum (a N : ℕ) (t : Finset ι) :
    intersectionMass univ (weight N) (event s a N) t =
      (N:ℝ)⁻¹^3 * ∑ x ∈ range N, ∑ y ∈ range N, ∑ z ∈ range N,
        ∏ i ∈ t, if avoids (s i) ((a+x : ℕ) : ZMod (s i))
          ((a+y : ℕ) : ZMod (s i)) ((a+z : ℕ) : ZMod (s i)) then (0:ℝ) else 1 := by
  unfold intersectionMass
  simp_rw [joint_eq_product]
  simp only [weight,Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  exact congrArg (fun z : ℝ => (N:ℝ)⁻¹^3 * z) (sum_box N (fun x y z =>
    ∏ i ∈ t, if avoids (s i) ((a+x : ℕ) : ZMod (s i))
      ((a+y : ℕ) : ZMod (s i)) ((a+z : ℕ) : ZMod (s i)) then (0:ℝ) else 1))

theorem intersection_boundary (hc : Pairwise (Function.onFun Nat.Coprime s))
    (a N : ℕ) (hN : 0 < N) (t : Finset ι) :
    |intersectionMass univ (weight N) (event s a N) t - ∏ i ∈ t, badDensity (s i)| ≤
      3 * ((∏ i ∈ t, s i : ℕ):ℝ) / N := by
  have hc' : Pairwise (Function.onFun Nat.Coprime (fun i : t => s i.val)) := by
    intro i j hij
    exact hc (show i.val ≠ j.val from fun hh => hij (Subtype.ext hh))
  have h := bad_intersection_boundary (fun i : t => s i.val) hc' a N hN
  rw [intersection_eq_sum]
  have hp (f : ι → ℝ) : (∏ i : t, f i.val) = ∏ i ∈ t, f i := Finset.prod_coe_sort t f
  have hd : (∏ i : t, badDensity (s i.val)) = ∏ i ∈ t, badDensity (s i) :=
    hp (fun i => badDensity (s i))
  have hf (x y z : ℕ) : (∏ i : t, if avoids (s i.val)
      ((a+x : ℕ) : ZMod (s i.val)) ((a+y : ℕ) : ZMod (s i.val))
      ((a+z : ℕ) : ZMod (s i.val)) then (0:ℝ) else 1) =
      ∏ i ∈ t, if avoids (s i) ((a+x : ℕ) : ZMod (s i))
      ((a+y : ℕ) : ZMod (s i)) ((a+z : ℕ) : ZMod (s i)) then (0:ℝ) else 1 :=
    hp (fun i => if avoids (s i) ((a+x : ℕ) : ZMod (s i))
      ((a+y : ℕ) : ZMod (s i)) ((a+z : ℕ) : ZMod (s i)) then (0:ℝ) else 1)
  simp only [hf,hd,Finset.prod_coe_sort] at h
  exact h

theorem finite_box_sieve (hc : Pairwise (Function.onFun Nat.Coprime s))
    (hs : ∀ i, 2 ≤ s i) (a N : ℕ) (hN : 0 < N) (r : ℕ) :
    density s a N ≤ (∏ i, (1-badDensity (s i))) +
      elementary univ (fun i => badDensity (s i)) (2*r+1) +
      (∑ k ∈ range (2*r+1), ∑ t ∈ (univ : Finset ι).powersetCard k,
        3 * ((∏ i ∈ t, s i : ℕ):ℝ) / N) := by
  have hv (i : ι) : 0 ≤ badDensity (s i) ∧ badDensity (s i) ≤ 1 :=
    ⟨(badDensity_bounds (hs i)).1.le,(badDensity_bounds (hs i)).2.1.le⟩
  have h := finite_upper_sieve univ (weight N) (fun _ _ => by unfold weight; positivity)
    (event s a N) (fun i => badDensity (s i)) hv r
  apply h.trans
  apply _root_.add_le_add le_rfl
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum
  intro t _
  exact intersection_boundary s hc a N hN t

end OrdinaryCorrelations.SourceBoxSieve

end

end OAI
