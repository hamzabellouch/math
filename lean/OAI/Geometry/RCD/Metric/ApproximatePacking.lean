import OAI.Geometry.RCD.Metric.PowerPacking

namespace OAI

/-! # Dimensional packing in a pointed target of the actual RCD ball -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.approximate_target_packing {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    {Y ι : Type*} [MetricSpace Y] [Fintype ι] {p : X} {q : Y} {ρ d ε : ℝ}
    (hρ : 0 < ρ) (hd : 0 < d) (hd2 : d ≤ 2) (he : ε ≤ d/6)
    (hcurv : -1 ≤ K*(4*ρ)^2) {f : X → Y}
    (hf : IsPointedApproximation p q ρ 1 ε f) (v : ι → Y)
    (hv : ∀ i, dist (v i) q ≤ 1-ε) (hsep : Pairwise (fun i j => d ≤ dist (v i) (v j))) :
    (Fintype.card ι:ℝ)*(d/2)^n ≤ Real.cosh 1^(n-1)*8^n := by
  classical
  have hex (i : ι) : ∃ x : X, dist x p ≤ ρ ∧ dist (f x) (v i) ≤ ε := by
    simpa only [one_mul] using hf.2.2 (v i) (hv i)
  choose x hx hclose using hex
  have hdist (i j : ι) (hij : i ≠ j) : (d/2)*ρ ≤ dist (x i) (x j) := by
    have hh := (abs_le.mp (hf.2.1 (x i) (x j) (by simpa using hx i) (by simpa using hx j))).2
    have ht := dist_triangle (v i) (f (x i)) (v j)
    have ht' := dist_triangle (f (x i)) (f (x j)) (v j)
    have hi := hclose i
    have hj := hclose j
    rw [dist_comm (f (x i)) (v i)] at hi
    have hl := hsep hij
    apply (le_div_iff₀ hρ).mp
    linarith
  have hxin : Function.Injective x := by
    intro i j h
    by_contra hij
    have hh := hdist i j hij
    rw [h,dist_self] at hh
    exact (not_le_of_gt (by positivity : 0 < (d/2)*ρ)) hh
  let S := Finset.univ.image x
  have hScard : S.card = Fintype.card ι := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ hxin,Finset.card_univ]
  have hSnear : ∀ y ∈ S, dist y p ≤ ρ := by
    intro y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
    exact hx i
  have hSsep : (S:Set X).Pairwise (fun y z => (d/2)*ρ ≤ dist y z) := by
    intro y hy z hz hyz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hz
    exact hdist i j (fun h => hyz (congrArg x h))
  have hb := hX.power_packing_bound hn hρ (by positivity : 0 < (d/2)*ρ)
    (by nlinarith) hcurv S hSnear hSsep
  rw [hScard,mul_pow,← mul_assoc] at hb
  exact (mul_le_mul_iff_left₀ (pow_pos hρ n)).mp hb

end RegularPointCoordinates

end

end OAI
