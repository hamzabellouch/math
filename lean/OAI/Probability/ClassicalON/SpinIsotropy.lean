import OAI.Probability.ClassicalON.CoarseExponential

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def coordinateRotation (n : ℕ) (i j : Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

omit [Fintype V] [Fintype E] in
theorem coordinateRotation_apply (n : ℕ) (i j k : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    coordinateRotation n i j v k=v (Equiv.swap i j k) := by
  simp [coordinateRotation,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']

omit [Fintype E] in
theorem freeSpinReference_rotation (n : ℕ) [NeZero n] (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (SpinSystem.rotateConfiguration (fun _ : V => U)) (freeSpinReference n) (freeSpinReference n) :=
  measurePreserving_pi (fun _ : V => sphereProbability n) (fun _ => sphereProbability n)
    (fun _ => spinRotation_preserves_probability U)

omit [Fintype V] in
theorem freeSpinEnergy_rotation (n : ℕ) (left right : E → V) (b : E → ℝ)
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (s : V → Spin n) :
    freeSpinEnergy n left right b (SpinSystem.rotateConfiguration (fun _ : V => U) s)=
      freeSpinEnergy n left right b s := by
  apply Finset.sum_congr rfl
  intro e _
  change b e*⟪U (s (left e)).val,U (s (right e)).val⟫_ℝ=_
  rw [U.inner_map_map]

def coordinateSpinProduct (n : ℕ) (i : Fin n) (x y : V) (s : V → Spin n) : ℝ :=
  (s x).val i*(s y).val i

omit [Fintype V] [Fintype E] in
theorem continuous_coordinateSpinProduct (n : ℕ) (i : Fin n) (x y : V) :
    Continuous (coordinateSpinProduct n i x y) := by
  unfold coordinateSpinProduct
  fun_prop

theorem coordinateSpinMean_eq (n : ℕ) [NeZero n] (left right : E → V) (b : E → ℝ) (i j : Fin n) (x y : V) :
    freeSpinMean n left right b (coordinateSpinProduct n i x y)=
      freeSpinMean n left right b (coordinateSpinProduct n j x y) := by
  let U := coordinateRotation n i j
  have he (s : V → Spin n) :
      coordinateSpinProduct n i x y (SpinSystem.rotateConfiguration (fun _ : V => U) s)=
        coordinateSpinProduct n j x y s := by
    change (U (s x).val) i*(U (s y).val) i=_
    simp only [U,coordinateRotation_apply,Equiv.swap_apply_left,coordinateSpinProduct]
  have hi := (freeSpinReference_rotation (V := V) n U).integral_comp
    (SpinSystem.rotateConfiguration (fun _ : V => U)).measurableEmbedding
    (fun s => Real.exp (freeSpinEnergy n left right b s)*coordinateSpinProduct n i x y s)
  simp_rw [freeSpinEnergy_rotation,he] at hi
  unfold freeSpinMean weightedMean
  rw [hi]

theorem innerSpinMean_eq_coordinate (n : ℕ) [NeZero n] (left right : E → V) (b : E → ℝ)
    (i : Fin n) (x y : V) :
    freeSpinMean n left right b (fun s => ⟪(s x).val,(s y).val⟫_ℝ)=
      n*freeSpinMean n left right b (coordinateSpinProduct n i x y) := by
  have he (s : V → Spin n) : ⟪(s x).val,(s y).val⟫_ℝ=
      ∑ j : Fin n,coordinateSpinProduct n j x y s := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct,coordinateSpinProduct,star_trivial]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hh : freeSpinMean n left right b (fun s => ⟪(s x).val,(s y).val⟫_ℝ)=
      ∑ j : Fin n,freeSpinMean n left right b (coordinateSpinProduct n j x y) := by
    unfold freeSpinMean weightedMean
    simp_rw [he,Finset.mul_sum]
    rw [integral_finsetSum]
    · rw [Finset.sum_div]
    · intro j _
      exact compact_integrable ((continuous_freeSpinEnergy _ _ _ _).rexp.mul
        (continuous_coordinateSpinProduct _ _ _ _))
  rw [hh]
  simp_rw [coordinateSpinMean_eq n left right b _ i x y]
  simp

end ClassicalON

end

end OAI
