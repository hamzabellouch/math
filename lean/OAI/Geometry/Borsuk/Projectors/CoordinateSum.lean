import Mathlib

namespace OAI

namespace BorsukNine
open scoped BigOperators

noncomputable def coordinateSum {ι : Type*} [Fintype ι] : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => ∑ i, x i
      map_add' := by intro x y; simp only [PiLp.add_apply,Finset.sum_add_distrib]
      map_smul' := by intro t x; simp only [PiLp.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply] }

lemma coordinateSum_apply {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    coordinateSum x = ∑ i, x i := rfl

noncomputable def uniformVector (ι : Type*) [Fintype ι] : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun _ => (Fintype.card ι : ℝ)⁻¹)

lemma coordinateSum_uniform (ι : Type*) [Fintype ι] [Nonempty ι] :
    coordinateSum (uniformVector ι) = 1 := by
  simp only [coordinateSum_apply,uniformVector,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt (Fintype.card_pos)))

noncomputable def zeroSumProjection (ι : Type*) [Fintype ι] :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  ContinuousLinearMap.id ℝ _ - coordinateSum.smulRight (uniformVector ι)

noncomputable def simplexProjection {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :=
  zeroSumProjection ι x + uniformVector ι

lemma simplexProjection_sum {ι : Type*} [Fintype ι] [Nonempty ι] (x : EuclideanSpace ℝ ι) :
    coordinateSum (simplexProjection x) = 1 := by
  simp only [simplexProjection,zeroSumProjection,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,map_add,map_sub,map_smul,coordinateSum_uniform,
    smul_eq_mul,mul_one,sub_self,zero_add]

lemma simplexProjection_fixed {ι : Type*} [Fintype ι] {x : EuclideanSpace ℝ ι}
    (hx : coordinateSum x = 1) : simplexProjection x = x := by
  simp only [simplexProjection,zeroSumProjection,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,hx,one_smul,sub_add_cancel]

lemma simplexProjection_sub_fixed {ι : Type*} [Fintype ι] {x y : EuclideanSpace ℝ ι}
    (hy : coordinateSum y = 1) : simplexProjection x - y = zeroSumProjection ι (x-y) := by
  rw [map_sub]
  have hy' := simplexProjection_fixed hy
  change zeroSumProjection ι y + uniformVector ι = y at hy'
  change (zeroSumProjection ι x + uniformVector ι) - y = _
  calc
    _ = (zeroSumProjection ι x + uniformVector ι) -
      (zeroSumProjection ι y + uniformVector ι) := by rw [hy']
    _ = _ := by abel

lemma continuous_simplex_approx {D ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Fintype ι] [Nonempty ι]
    (g : D → EuclideanSpace ℝ ι) (hg : Continuous g)
    {K : Set D} (hK : ∀ x ∈ K, coordinateSum (g x) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : D → EuclideanSpace ℝ ι, ContDiff ℝ (⊤ : ℕ∞) a ∧
      (∀ x, coordinateSum (a x) = 1) ∧ (∀ x ∈ K, ‖a x - g x‖ < ε) := by
  have hp := norm_nonneg (zeroSumProjection ι)
  have hδ : 0 < ε / (‖zeroSumProjection ι‖ + 1) := div_pos hε (by positivity)
  obtain ⟨b,hb,hbg,-⟩ := hg.exists_contDiff_approx (⊤ : ℕ∞)
    (continuous_const : Continuous (fun _ : D => ε / (‖zeroSumProjection ι‖ + 1))) (fun _ => hδ)
  let a := fun x => simplexProjection (b x)
  refine ⟨a,?_,fun x => simplexProjection_sum (b x),?_⟩
  · exact ((zeroSumProjection ι).contDiff.comp hb).add contDiff_const
  · intro x hx
    change ‖simplexProjection (b x) - g x‖ < ε
    rw [simplexProjection_sub_fixed (hK x hx)]
    have hd : ‖b x - g x‖ < ε / (‖zeroSumProjection ι‖ + 1) := by
      simpa only [dist_eq_norm] using hbg x
    calc
      _ ≤ ‖zeroSumProjection ι‖ * ‖b x - g x‖ := (zeroSumProjection ι).le_opNorm _
      _ ≤ ‖zeroSumProjection ι‖ * (ε / (‖zeroSumProjection ι‖ + 1)) := mul_le_mul_of_nonneg_left hd.le hp
      _ < ε := by
        have he : (‖zeroSumProjection ι‖+1) * (ε / (‖zeroSumProjection ι‖+1)) = ε :=
          mul_div_cancel₀ ε (by positivity)
        nlinarith

end BorsukNine

end OAI
