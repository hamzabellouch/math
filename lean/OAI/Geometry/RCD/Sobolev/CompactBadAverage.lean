import OAI.Geometry.RCD.Sobolev.FiniteDisjointIntegral
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Real

namespace OAI

/-! # The finite Vitali estimate for points with a large ball average

This is the covering step of De Philippis--Gigli (2018), Proposition 3.2,
Step 2.1. The containing region and the radius cutoff remain explicit.
-/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem compact_bad_average (μ : Measure X) {H Ω : Set X} (hH : IsCompact H)
    {f : X → ℝ} (hf : IntegrableOn f Ω μ)
    (hf0 : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ f x)
    (hfin : ∀ x r, μ (ball x r) ≠ ⊤)
    {R D t : ℝ} (hD : 0 ≤ D) (ht : 0 ≤ t)
    (hdoub : ∀ x r, 0 < r → r ≤ R → μ.real (ball x (5*r)) ≤ D*μ.real (ball x r))
    (hbad : ∀ x ∈ H, ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ball x r ⊆ Ω ∧
      t*μ.real (ball x r) ≤ ∫ y in ball x r, f y ∂μ) :
    t*μ.real H ≤ D*∫ y in Ω, f y ∂μ := by
  classical
  choose r hr hR hΩ hav using (fun x : H => hbad x.1 x.2)
  obtain ⟨I,hI⟩ := hH.elim_finite_subcover (fun x : H => ball x.1 (r x))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion_of_mem ⟨x,hx⟩ (mem_ball_self (hr ⟨x,hx⟩)))
  obtain ⟨J,hJI,hdisj,hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    (I : Set H) (fun x => x.1) r R (fun x _ => hR x) 5 (by norm_num)
  have hJ : J.Finite := I.finite_toSet.subset hJI
  let ι := J
  let : Fintype ι := hJ.fintype
  let B : ι → Set X := fun i => ball i.1.1 (r i.1)
  let E : ι → Set X := fun i => ball i.1.1 (5*r i.1)
  have hcov : H ⊆ ⋃ i, E i := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hI hx)
    obtain ⟨j,hj,hij⟩ := hcover i hi
    exact mem_iUnion_of_mem (⟨j,hj⟩ : ι) (hij hxi)
  have hEfin : μ (⋃ i, E i) ≠ ⊤ := by
    simpa only [Set.mem_univ,iUnion_true] using
      (measure_biUnion_ne_top (s := (Set.univ : Set ι)) (Set.toFinite _)
        (fun i _ => hfin i.1.1 (5*r i.1)))
  have hmass : μ.real H ≤ D*∑ i : ι, μ.real (B i) := by
    calc
      _ ≤ μ.real (⋃ i, E i) := measureReal_mono hcov hEfin
      _ ≤ ∑ i, μ.real (E i) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ i : ι, D*μ.real (B i) :=
        Finset.sum_le_sum (fun i _ => hdoub i.1.1 (r i.1) (hr i.1) (hR i.1))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have havsum : t*(∑ i : ι, μ.real (B i)) ≤ ∑ i : ι, ∫ y in B i, f y ∂μ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hav i.1)
  have hisum : (∑ i : ι, ∫ y in B i, f y ∂μ) ≤ ∫ y in Ω, f y ∂μ := by
    apply finite_disjoint_setIntegral_le μ (s := B) hf hf0 (fun _ => measurableSet_ball)
      (fun i : ι => hΩ i.1)
    intro i j hij
    exact hdisj i.2 j.2 (fun h => hij (Subtype.ext h))
  calc
    _ ≤ t*(D*∑ i : ι, μ.real (B i)) := mul_le_mul_of_nonneg_left hmass ht
    _ = D*(t*∑ i : ι, μ.real (B i)) := by ring
    _ ≤ D*∑ i : ι, ∫ y in B i, f y ∂μ := mul_le_mul_of_nonneg_left havsum hD
    _ ≤ _ := mul_le_mul_of_nonneg_left hisum hD

end RegularPointCoordinates

end

end OAI
