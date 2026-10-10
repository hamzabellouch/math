import OAI.Analysis.IrrationalRotation.Model.ProductCocycle
import OAI.Analysis.IrrationalRotation.Rotation.FiniteSupportCocycle
import OAI.Analysis.IrrationalRotation.Analysis.InvariantConullCore
import OAI.Analysis.IrrationalRotation.Product.ProductSupport
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

open MeasureTheory Set Function

namespace Invariant233.ProductCocycle

@[simp] theorem rotate_zero {I : Type*} (θ : I → ℝ) (x : Space I) :
    rotate θ 0 x = x := by
  funext i
  simp [rotate]

theorem rotate_add {I : Type*} (θ : I → ℝ) (k n : ℤ) (x : Space I) :
    rotate θ (k + n) x = rotate θ n (rotate θ k x) := by
  funext i
  simp only [rotate, Int.cast_add, add_mul, AddCircle.coe_add, add_assoc]

theorem representative_mem_Ico (x : UnitAddCircle) :
    representative x ∈ Ico (0 : ℝ) 1 := by
  simpa only [representative, zero_add] using (AddCircle.equivIco (1 : ℝ) 0 x).property

@[simp] theorem coe_representative (x : UnitAddCircle) :
    ((representative x : ℝ) : UnitAddCircle) = x :=
  AddCircle.coe_equivIco

theorem representative_add (x : UnitAddCircle) (t : ℝ) :
    representative (x + (t : UnitAddCircle)) = Int.fract (representative x + t) := by
  have hx : x + (t : UnitAddCircle) =
      ((representative x + t : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_add, coe_representative]
  rw [hx]
  change ((AddCircle.equivIco (1 : ℝ) 0
    ((representative x + t : ℝ) : UnitAddCircle)) : ℝ) = _
  simpa only [div_one, mul_one] using
    (AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) (representative x + t))

theorem representative_rotate {I : Type*} (θ : I → ℝ) (k : ℤ)
    (x : Space I) (i : I) :
    representative (rotate θ k x i) =
      Int.fract (representative (x i) + (k : ℝ) * θ i) :=
  representative_add (x i) ((k : ℝ) * θ i)

theorem measurable_representative : Measurable representative :=
  CocycleSupport.measurePreserving_circleRepresentative.measurable

theorem measurable_cocycleVersion {I : Type*} [Countable I]
    (θ c : I → ℝ) (k : ℤ) : Measurable (cocycleVersion θ c k) := by
  apply Real.measurable_exp.comp
  apply Measurable.neg
  apply Measurable.tsum
  intro i
  have hrep : Measurable (fun x : Space I ↦ representative (x i)) :=
    measurable_representative.comp (measurable_pi_apply i)
  exact measurable_const.mul ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
    ((hrep.add_const ((k : ℝ) * θ i)).floor))

theorem cocycleVersion_pos {I : Type*} (θ c : I → ℝ) (k : ℤ) (x : Space I) :
    0 < cocycleVersion θ c k x :=
  Real.exp_pos _

@[simp] theorem cocycleVersion_zero {I : Type*} (θ c : I → ℝ) (x : Space I) :
    cocycleVersion θ c 0 x = 1 := by
  simp only [cocycleVersion, Int.cast_zero, zero_mul, add_zero]
  exact FiniteSupportCocycle.exp_tsum_floor_zero _ c
    (fun i ↦ representative_mem_Ico (x i))

theorem measurePreserving_rotate {I : Type*} (θ : I → ℝ) (k : ℤ) :
    MeasurePreserving (rotate θ k) (haar I) (haar I) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  have hcoord (i : I) : MeasurePreserving
      (fun x : UnitAddCircle ↦ x + (((k : ℝ) * θ i : ℝ) : UnitAddCircle)) volume volume :=
    measurePreserving_add_right volume _
  refine ⟨Measurable.of_eval (fun i ↦ (measurable_pi_apply i).add_const _), ?_⟩
  change (Measure.infinitePi (fun _ : I ↦ (volume : Measure UnitAddCircle))).map
      (fun x i ↦ x i + (((k : ℝ) * θ i : ℝ) : UnitAddCircle)) = _
  rw [Measure.infinitePi_map_pi _ (fun i ↦ (hcoord i).measurable)]
  simp only [(hcoord _).map_eq, haar]

theorem cocycleVersion_add_of_finite_support {I : Type*}
    (θ c : I → ℝ) (k n : ℤ) (x : Space I)
    (hk : HasFiniteSupport
      (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋))
    (hn : HasFiniteSupport
      (fun i ↦ ⌊representative (rotate θ k x i) + (n : ℝ) * θ i⌋)) :
    cocycleVersion θ c (k + n) x =
      cocycleVersion θ c n (rotate θ k x) * cocycleVersion θ c k x := by
  simp only [cocycleVersion, representative_rotate] at hn ⊢
  exact FiniteSupportCocycle.exp_tsum_floor_cocycle _ θ c k n hk hn

theorem cocycleVersion_ratio_le_one {I : Type*}
    (θ c : I → ℝ) (k : ℤ) (x y : Space I)
    (hc : ∀ i, 0 ≤ c i)
    (hxy : ∀ i, representative (x i) ≤ representative (y i))
    (hx : HasFiniteSupport
      (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋))
    (hy : HasFiniteSupport
      (fun i ↦ ⌊representative (y i) + (k : ℝ) * θ i⌋)) :
    cocycleVersion θ c k y / cocycleVersion θ c k x ≤ 1 :=
  FiniteSupportCocycle.exp_tsum_floor_ratio_le_one _ _ θ c k hc hxy hx hy

theorem cocycleVersion_one_le_one {I : Type*} (θ c : I → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Space I) :
    cocycleVersion θ c 1 x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  apply tsum_nonneg
  intro i
  apply mul_nonneg (hc i)
  have hf : (0 : ℤ) ≤ ⌊representative (x i) + (1 : ℝ) * θ i⌋ := by
    apply Int.floor_nonneg.mpr
    simpa only [one_mul] using
      add_nonneg (representative_mem_Ico (x i)).1 (hθ i)
  exact_mod_cast hf

theorem cocycleVersion_eq_finite_sum {I : Type*}
    (θ c : I → ℝ) (k : ℤ) (x : Space I) (s : Finset I)
    (hs : ∀ i ∉ s, ⌊representative (x i) + (k : ℝ) * θ i⌋ = 0) :
    cocycleVersion θ c k x =
      Real.exp (-∑ i ∈ s, c i * (⌊representative (x i) + (k : ℝ) * θ i⌋ : ℝ)) := by
  unfold cocycleVersion
  rw [tsum_eq_sum (s := s) (fun i hi ↦ by rw [hs i hi]; simp)]

theorem exists_finset_cocycleVersion_one {I : Type*}
    (θ c : I → ℝ) (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (x : Space I)
    (hx : HasFiniteSupport (fun i ↦ ⌊representative (x i) + θ i⌋)) :
    ∃ s : Finset I, cocycleVersion θ c 1 x = Real.exp (-∑ i ∈ s, c i) := by
  classical
  let s := hx.toFinset
  have hs : ∀ i ∉ s, ⌊representative (x i) + (1 : ℝ) * θ i⌋ = 0 := by
    intro i hi
    have hnot : i ∉ Function.support (fun j ↦ ⌊representative (x j) + θ j⌋) := by
      exact fun hmem ↦ hi (hx.mem_toFinset.mpr hmem)
    simpa only [Function.mem_support, not_not, one_mul] using hnot
  refine ⟨s, ?_⟩
  rw [cocycleVersion_eq_finite_sum θ c 1 x s (by simpa using hs)]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  have hne : ⌊representative (x i) + θ i⌋ ≠ 0 := by
    exact hx.mem_toFinset.mp hi
  have hzero : ⌊θ i⌋ = 0 := Int.floor_eq_zero_iff.mpr (hθ i)
  have hfloor : ⌊representative (x i) + θ i⌋ = 1 := by
    rw [FloorCocycle.floor_add_eq_indicator (representative_mem_Ico (x i)).1
      (representative_mem_Ico (x i)).2, hzero] at hne ⊢
    split_ifs at hne ⊢ <;> simp_all
  simp only [Int.cast_one, one_mul, hfloor, mul_one]

theorem exists_invariant_cocycle_core {I : Type*} [Countable I]
    (θ : I → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∃ s : Set (Space I), MeasurableSet s ∧ (∀ᵐ x ∂haar I, x ∈ s) ∧
      (∀ k : ℤ, rotate θ k ⁻¹' s = s) ∧
      (∀ x ∈ s, ∀ k : ℤ, HasFiniteSupport
        (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋)) ∧
      (∀ x ∈ s, ∀ (c : I → ℝ) (k n : ℤ),
        cocycleVersion θ c (k + n) x =
          cocycleVersion θ c n (rotate θ k x) * cocycleVersion θ c k x) := by
  have hall : ∀ᵐ x ∂haar I, ∀ k : ℤ, HasFiniteSupport
      (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋) :=
    CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ
  obtain ⟨s, hs, hfull, hprop, hinv⟩ :=
    Invariant233.exists_invariant_conull_forall (rotate θ) (rotate_zero θ)
      (rotate_add θ) (measurePreserving_rotate θ)
      (fun (k : ℤ) (x : Space I) ↦ HasFiniteSupport
        (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋))
      (ae_all_iff.mp hall)
  have hsupport (x : Space I) (hx : x ∈ s) (k : ℤ) :
      HasFiniteSupport (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋) := by
    simpa only [rotate_zero] using hprop x hx 0 k
  refine ⟨s, hs, hfull, hinv, hsupport, ?_⟩
  intro x hx c k n
  exact cocycleVersion_add_of_finite_support θ c k n x
    (hsupport x hx k) (hprop x hx k n)

theorem ae_exists_finset_cocycleVersion_one {I : Type*} [Countable I]
    (θ c : I → ℝ) (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hθ : Summable θ) :
    ∀ᵐ x ∂haar I, ∃ s : Finset I,
      cocycleVersion θ c 1 x = Real.exp (-∑ i ∈ s, c i) := by
  have hall := CocycleSupport.ae_product_all_int_finite_floor_support
    θ (fun i ↦ (hθ01 i).1) hθ
  filter_upwards [hall] with x hx
  apply exists_finset_cocycleVersion_one θ c hθ01 x
  simpa only [HasFiniteSupport, representative, Int.cast_one, one_mul] using hx 1

end Invariant233.ProductCocycle

end OAI
