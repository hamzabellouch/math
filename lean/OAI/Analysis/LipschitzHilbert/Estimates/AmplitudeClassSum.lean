import OAI.Analysis.LipschitzHilbert.Estimates.DyadicMeasureClass

namespace OAI

/-! The retained amplitude levels cost only the square root of the
number of their dyadic measure classes. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem amplitude_class_sum (I : Finset ℤ) (mass : ℤ → ℝ) (cls : ℤ → ℤ)
    (hlo : ∀ i∈I, (2:ℝ)^(cls i)≤mass i)
    (hhi : ∀ i∈I, mass i≤(2:ℝ)^(cls i+1)) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mass i))≤
      4*Real.sqrt 2*Real.sqrt ((I.image cls).card:ℝ)*
        Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (mass i))^2) := by
  classical
  let a := fun i : ℤ => (2:ℝ)^i*Real.sqrt (mass i)
  let E := fun k : ℤ => ∑ i∈I.filter (fun i => cls i=k), (a i)^2
  have hE (k : ℤ) : 0≤E k := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hclass (k : ℤ) : (∑ i∈I.filter (fun i => cls i=k), a i)≤4*Real.sqrt 2*Real.sqrt (E k) := by
    apply amplitude_class_bound (I.filter (fun i => cls i=k)) mass ((2:ℝ)^k)
    · intro i hi
      obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
      simpa only [he] using hlo i hi
    · intro i hi
      obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
      calc
        _ ≤ (2:ℝ)^(k+1) := by simpa only [he] using hhi i hi
        _ = 2*(2:ℝ)^k := by rw [zpow_add₀ (by norm_num : (2:ℝ)≠0)]; norm_num; ring
  have hfiber : (∑ k∈I.image cls, E k)=∑ i∈I, (a i)^2 :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem cls hi) (fun i => (a i)^2)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (I.image cls) (fun _ => (1:ℝ)) (fun k => Real.sqrt (E k))
  have hcs' : (∑ k∈I.image cls, Real.sqrt (E k))≤
      Real.sqrt ((I.image cls).card:ℝ)*Real.sqrt (∑ i∈I, (a i)^2) := by
    simpa only [one_mul,one_pow,Finset.sum_const,smul_eq_mul,nsmul_eq_mul,Nat.cast_one,mul_one,
      Real.sq_sqrt (hE _),hfiber] using hcs
  calc
    _ = ∑ k∈I.image cls, ∑ i∈I.filter (fun i => cls i=k), a i :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem cls hi) a).symm
    _ ≤ ∑ k∈I.image cls, 4*Real.sqrt 2*Real.sqrt (E k) := Finset.sum_le_sum (fun k _ => hclass k)
    _ = 4*Real.sqrt 2*(∑ k∈I.image cls, Real.sqrt (E k)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcs' (by positivity : 0≤4*Real.sqrt 2)

theorem dyadic_amplitude_class_sum (I : Finset ℤ) (mass : ℤ → ℝ)
    (hm : ∀ i∈I, 0<mass i) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (mass i))≤
      4*Real.sqrt 2*Real.sqrt ((I.image (fun i => dyadicMeasureClass (mass i))).card:ℝ)*
        Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (mass i))^2) :=
  amplitude_class_sum I mass (fun i => dyadicMeasureClass (mass i))
    (fun i hi => (dyadicMeasureClass_bounds (hm i hi)).1)
    (fun i hi => (dyadicMeasureClass_bounds (hm i hi)).2.le)

end LipschitzHilbert

end

end OAI
