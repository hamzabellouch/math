import OAI.Combinatorics.ContingencyTables.Transport.IntegerChildVariance

namespace OAI

/-! # Finite exposure variance with zero-mass children

The exact variance decomposition uses only finite nonnegative weights.
A child of mass zero has zero moment, so its mean can be set to zero.
This is the algebraic decomposition iterated by the small-slot exposure.
-/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical
open CommonBasesFPRAS

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def mean (w H : X → ℝ) : ℝ := (∑ x, w x*H x)/(∑ x, w x)

noncomputable def variance (w H : X → ℝ) : ℝ := ∑ x, w x*(H x-mean w H)^2

omit [Fintype Y] in
lemma zero_mass_weights (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hz : (∑ x, w x)=0) :
    ∀ x, w x=0 := by
  intro x
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hw y)).mp hz x (Finset.mem_univ x)

omit [Fintype Y] in
lemma mean_moment (w H : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x, w x)*mean w H=∑ x, w x*H x := by
  by_cases hz : (∑ x, w x)=0
  · have h := zero_mass_weights w hw hz
    simp only [mean,h,zero_mul,Finset.sum_const_zero]
  · unfold mean
    field_simp

omit [Fintype Y] in
lemma mean_second (w H : X → ℝ) :
    (∑ x, w x)*(mean w H)^2=(∑ x, w x*H x)^2/(∑ x, w x) := by
  by_cases hz : (∑ x, w x)=0
  · simp only [mean,hz,div_zero,zero_mul]
  · unfold mean
    field_simp

omit [Fintype Y] in
/-- The second-moment identity also holds at mass zero. -/
lemma variance_formula (w H : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    variance w H=(∑ x, w x*(H x)^2)-(∑ x, w x*H x)^2/(∑ x, w x) := by
  by_cases hz : (∑ x, w x)=0
  · have h := zero_mass_weights w hw hz
    simp only [variance,h,zero_mul,Finset.sum_const_zero,zero_pow,ne_eq,
      OfNat.ofNat_ne_zero,not_false_eq_true,div_zero,sub_zero]
  · exact finite_center_at_mean Finset.univ w H hz

/-- Exact conditional variance decomposition, allowing arbitrary
zero-mass child fibres and a zero-mass whole space. -/
theorem variance_split (w H : Y → X → ℝ) (hw : ∀ y x, 0 ≤ w y x) :
    variance (fun p : X×Y => w p.2 p.1) (fun p => H p.2 p.1)=
      (∑ y, variance (w y) (H y))+
        variance (fun y => ∑ x, w y x) (fun y => mean (w y) (H y)) := by
  have hmass : (∑ y, ∑ x, w y x)=(∑ p : X×Y, w p.2 p.1) := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
  have hmoment : (∑ y, (∑ x, w y x)*mean (w y) (H y))=
      ∑ p : X×Y, w p.2 p.1*H p.2 p.1 := by
    simp_rw [mean_moment _ _ (hw _)]
    rw [Fintype.sum_prod_type,Finset.sum_comm]
  have hsecond : (∑ y, (∑ x, w y x)*(mean (w y) (H y))^2)=
      ∑ y, (∑ x, w y x*H y x)^2/(∑ x, w y x) := by
    simp_rw [mean_second]
  have hsquares : (∑ y, ∑ x, w y x*(H y x)^2)=
      ∑ p : X×Y, w p.2 p.1*(H p.2 p.1)^2 := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
  rw [variance_formula (fun p : X×Y => w p.2 p.1) (fun p => H p.2 p.1) (fun p => hw p.2 p.1),
    variance_formula (fun y : Y => ∑ x, w y x) (fun y => mean (w y) (H y))
      (fun y => Finset.sum_nonneg (fun x _ => hw y x))]
  have hchild (y : Y) := variance_formula (w y) (H y) (hw y)
  simp_rw [hchild]
  rw [Finset.sum_sub_distrib,hmass,hmoment,hsecond,hsquares]
  ring

omit [Fintype X] [Fintype Y] in
/-- A fixed-depth partition uses each nonnegative edge energy at most
once. The same statement applies to profile contexts and directed edges. -/
theorem sum_context_energy_le {E C : Type*} [Fintype C]
    (edges : Finset E) (energy : E → ℝ) (context : E → C)
    (eligible : E → Prop) (henergy : ∀ e ∈ edges, 0 ≤ energy e) :
    (∑ c : C, ∑ e ∈ edges.filter (fun e => eligible e ∧ context e=c), energy e) ≤
      ∑ e ∈ edges, energy e := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro e he
  by_cases h : eligible e
  · simp only [h,true_and,Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]
    exact le_rfl
  · simpa only [h,false_and,↓reduceIte,Finset.sum_const_zero] using henergy e he

end ContingencyTables.FiniteExposureVariance

end OAI
