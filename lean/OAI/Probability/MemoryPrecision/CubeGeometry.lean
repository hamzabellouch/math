import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.AmbientGram

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision
open NoiselessRegression
abbrev CubeSet (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  fun (point : EuclideanSpace ℝ (Fin n)) => ∀ index : Fin n,
    @LE.le ℝ Real.instLE
      (@abs ℝ Real.lattice Real.instAddGroup
        (@WithLp.ofLp
          (@OfNat.ofNat ℝ≥0∞ 2
            (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
              (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0))))
          (Fin n → ℝ) point index))
      (@HDiv.hDiv ℝ ℝ ℝ (@instHDiv ℝ Real.instDivInvMonoid.toDiv)
        (@OfNat.ofNat ℝ 1 (@One.toOfNat1 ℝ Real.instOne))
        (@OfNat.ofNat ℝ 2 (@instOfNatAtLeastTwo ℝ 2 Real.commRing.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))))
abbrev Cube (d : ℕ) := CubeSet (d/2)
def CubeLaw (d : ℕ) : Measure (Cube d) :=
  (volume : Measure (Space (d/2))).comap Subtype.val
lemma cube_second_coordinate_lt (d : ℕ) (index : Fin d)
    (lower : ¬index.val < d/2) (upper : index.val < 2*(d/2)) :
    index.val - d/2 < d/2 := by omega

def cubeRaw (d : ℕ) (u : Space (d/2)) : Space d :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  @HSMul.hSMul ℝ (Space d) (Space d)
    (@instHSMul ℝ (Space d) (WithLp.instSMul exponent ℝ (Fin d → ℝ)))
    (Real.sqrt (d/2:ℕ))⁻¹ (WithLp.toLp exponent (fun index : Fin d =>
      if lower : index.val < d/2 then
        @WithLp.ofLp exponent (Fin (d/2) → ℝ) u ⟨index.val, lower⟩
      else if upper : index.val < 2*(d/2) then
        Real.sqrt (1-(@WithLp.ofLp exponent (Fin (d/2) → ℝ) u
          ⟨index.val-d/2, cube_second_coordinate_lt d index lower upper⟩)^2)
      else 0))
def CubeEmbedding (d : ℕ) (u : Cube d) : Space d := cubeRaw d u.val
def CubeBall (d : ℕ) (z : Space (d/2)) (r : ℝ) : Set (Cube d) :=
  {u | dist u.val z ≤ Real.sqrt (d/2:ℕ) * r}
def CubeLocal {d : ℕ} (f : Cube d → ℝ≥0∞) (L : ℝ) : Prop :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  let cubeMeasurable := @Subtype.instMeasurableSpace (Space (d/2)) (CubeSet (d/2))
    (@WithLp.measurableSpace exponent (Fin (d/2) → ℝ) inferInstance)
  ∀ z : Space (d/2), ∀ r : ℝ, 0 < r →
    @MeasureTheory.lintegral (Cube d) cubeMeasurable
      (@Measure.restrict (Cube d) cubeMeasurable (CubeLaw d) (CubeBall d z r)) f ≤
      ENNReal.ofReal (L * r^(
        (@OfNat.ofNat ℝ 3 (@instOfNatAtLeastTwo ℝ 3 Real.commRing.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 1)))) * (d/2:ℕ) /
        (@OfNat.ofNat ℝ 4 (@instOfNatAtLeastTwo ℝ 4 Real.commRing.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 2)))) : ℝ))

lemma cubeSet_closed (n : ℕ) : IsClosed (CubeSet n) := by
  change IsClosed {u : Space n | ∀ i, |u i| ≤ 1/2}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun i => isClosed_le (by fun_prop) continuous_const)

lemma cubeSet_measurable (n : ℕ) : MeasurableSet (CubeSet n) :=
  (cubeSet_closed n).measurableSet

lemma cubeLaw_probability (d : ℕ) : IsProbabilityMeasure (CubeLaw d) := by
  constructor
  rw [CubeLaw, comap_subtype_coe_apply (cubeSet_measurable _), Set.image_univ,
    Subtype.range_coe]
  have he : CubeSet (d/2) = WithLp.ofLp ⁻¹' (Set.univ.pi (fun _ : Fin (d/2) => Icc (-1/2:ℝ) (1/2))) := by
    ext u
    change (∀ i, |u i| ≤ (1/2 : ℝ)) ↔ _
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Icc, abs_le]
    norm_num
  rw [he, (PiLp.volume_preserving_ofLp (Fin (d/2))).measure_preimage (by measurability)]
  rw [volume_pi, Measure.pi_pi]
  norm_num [Real.volume_Icc]

instance (d : ℕ) : IsProbabilityMeasure (CubeLaw d) := cubeLaw_probability d

lemma cubeBall_measurable (d : ℕ) (z : Space (d/2)) (r : ℝ) : MeasurableSet (CubeBall d z r) := by
  exact measurableSet_le (by fun_prop) measurable_const

lemma cubeRaw_continuous (d : ℕ) : Continuous (cubeRaw d) := by
  unfold cubeRaw
  refine Continuous.const_smul (c := (Real.sqrt (d/2:ℕ))⁻¹) ?_
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
  apply continuous_pi
  intro i
  dsimp
  split_ifs <;> fun_prop

lemma cubeEmbedding_continuous (d : ℕ) : Continuous (CubeEmbedding d) :=
  (cubeRaw_continuous d).comp continuous_subtype_val

lemma cubeEmbedding_measurable (d : ℕ) : Measurable (CubeEmbedding d) :=
  (cubeEmbedding_continuous d).measurable

lemma sum_fin_split {n d : ℕ} (hn : n ≤ d) (f : Fin d → ℝ) :
    (∑ i, f i) = (∑ i : Fin n, f ⟨i.val,by omega⟩) +
      ∑ i : Fin (d-n), f ⟨n+i.val,by omega⟩ := by
  let e : Fin (n+(d-n)) ≃ Fin d := finCongr (Nat.add_sub_of_le hn)
  calc
    _ = ∑ i : Fin (n+(d-n)), f (e i) := (Equiv.sum_comp e f).symm
    _ = _ := by rw [Fin.sum_univ_add]; rfl

def cubeCoords (d : ℕ) (u : Space (d/2)) : Space d :=
  let exponent : ℝ≥0∞ := @OfNat.ofNat ℝ≥0∞ 2
    (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
      (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))
  WithLp.toLp exponent (fun index : Fin d =>
    if lower : index.val < d/2 then
      @WithLp.ofLp exponent (Fin (d/2) → ℝ) u ⟨index.val, lower⟩
    else if upper : index.val < 2*(d/2) then
      Real.sqrt (1-(@WithLp.ofLp exponent (Fin (d/2) → ℝ) u
        ⟨index.val-d/2, cube_second_coordinate_lt d index lower upper⟩)^2)
    else 0)

lemma cubeCoords_first (d : ℕ) (u : Space (d/2)) (i : Fin (d/2)) :
    cubeCoords d u ⟨i.val,by omega⟩ = u i := by
  simp [cubeCoords, i.isLt]

lemma cubeCoords_second (d : ℕ) (u : Space (d/2)) (i : Fin (d/2)) :
    cubeCoords d u ⟨d/2+i.val,by omega⟩ = Real.sqrt (1-u i^2) := by
  simp [cubeCoords, show ¬d/2+i.val < d/2 by omega, show d/2+i.val < 2*(d/2) by omega]

lemma cubeCoords_tail (d : ℕ) (u : Space (d/2)) (i : Fin d) (hi : 2*(d/2) ≤ i.val) :
    cubeCoords d u i = 0 := by
  simp [cubeCoords, show ¬i.val < d/2 by omega, show ¬i.val < 2*(d/2) by omega]

lemma cubeCoords_sum (d : ℕ) (u : Space (d/2)) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ i : Fin d, f (cubeCoords d u i)) =
      (∑ i : Fin (d/2), f (u i)) + ∑ i : Fin (d/2), f (Real.sqrt (1-u i^2)) := by
  rw [sum_fin_split (show d/2 ≤ d by omega)]
  simp_rw [cubeCoords_first]
  rw [sum_fin_split (show d/2 ≤ d-d/2 by omega)]
  congr 1
  have h1 : (∑ i : Fin (d/2), f (cubeCoords d u ⟨d/2+i.val,by omega⟩)) =
      ∑ i : Fin (d/2), f (Real.sqrt (1-u i^2)) := by simp_rw [cubeCoords_second]
  rw [h1]
  have h0 : (∑ i : Fin (d-d/2-d/2), f (cubeCoords d u ⟨d/2+(d/2+i.val),by omega⟩)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [cubeCoords_tail d u _ (show 2*(d/2) ≤ d/2+(d/2+i.val) by omega), hf]
  rw [h0, add_zero]

lemma cube_coordinate_square_le {d : ℕ} (u : Cube d) (i : Fin (d/2)) : u.val i^2 ≤ 1/4 := by
  have hu : -(1/2 : ℝ) ≤ u.val i ∧ u.val i ≤ 1/2 := abs_le.mp (u.property i)
  nlinarith [sq_nonneg (u.val i-1/2), sq_nonneg (u.val i+1/2)]

lemma cubeEmbedding_norm {d : ℕ} (hd : 2 ≤ d) (u : Cube d) :
    @Norm.norm (Space d) (PiLp.instNorm
      (p := @OfNat.ofNat ℝ≥0∞ 2
        (@instOfNatAtLeastTwo ℝ≥0∞ 2 ENNReal.instAddCommMonoidWithOne.toNatCast
          (Mathlib.Meta.NormNum.instAtLeastTwo (nat_lit 0)))) (β := fun _ : Fin d => ℝ))
      (CubeEmbedding d u) = (1 : ℝ) := by
  have hs : ‖cubeCoords d u.val‖^2 = (d/2:ℕ) := by
    rw [EuclideanSpace.real_norm_sq_eq, cubeCoords_sum d u.val (fun x => x^2) (by norm_num)]
    have he (i : Fin (d/2)) : Real.sqrt (1-u.val i^2)^2 = 1-u.val i^2 :=
      Real.sq_sqrt (by have := cube_coordinate_square_le u i; linarith)
    simp_rw [he]
    rw [← Finset.sum_add_distrib]
    simp
  have hn : 0 < (d/2:ℕ) := by omega
  have hr : 0 < Real.sqrt (d/2:ℕ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hnorm : ‖cubeCoords d u.val‖ = Real.sqrt (d/2:ℕ) := by
    rw [← Real.sqrt_sq (norm_nonneg _), hs]
  change ‖(Real.sqrt (d/2:ℕ))⁻¹ • cubeCoords d u.val‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, hnorm, inv_mul_cancel₀ hr.ne']

lemma sqrt_pair_lipschitz {a b : ℝ} (ha : |a| ≤ 1/2) (hb : |b| ≤ 1/2) :
    |Real.sqrt (1-a^2) - Real.sqrt (1-b^2)| ≤ |a-b| := by
  have ha2 : a^2 ≤ 1/4 := by rcases abs_le.mp ha with ⟨ha₁,ha₂⟩; nlinarith
  have hb2 : b^2 ≤ 1/4 := by rcases abs_le.mp hb with ⟨hb₁,hb₂⟩; nlinarith
  have hsa := Real.sq_sqrt (show 0 ≤ 1-a^2 by linarith)
  have hsb := Real.sq_sqrt (show 0 ≤ 1-b^2 by linarith)
  have has : 1/2 ≤ Real.sqrt (1-a^2) := by nlinarith [Real.sqrt_nonneg (1-a^2)]
  have hbs : 1/2 ≤ Real.sqrt (1-b^2) := by nlinarith [Real.sqrt_nonneg (1-b^2)]
  have hab : |a+b| ≤ 1 := (abs_add_le a b).trans (by linarith)
  have he : (Real.sqrt (1-a^2)-Real.sqrt (1-b^2)) *
      (Real.sqrt (1-a^2)+Real.sqrt (1-b^2)) = -(a-b)*(a+b) := by nlinarith
  calc
    _ ≤ |Real.sqrt (1-a^2)-Real.sqrt (1-b^2)| *
        |Real.sqrt (1-a^2)+Real.sqrt (1-b^2)| := by
      apply le_mul_of_one_le_right (abs_nonneg _)
      rw [abs_of_nonneg (by positivity)]
      linarith
    _ = |a-b| * |a+b| := by rw [← abs_mul, he, abs_mul, abs_neg]
    _ ≤ |a-b| := mul_le_of_le_one_right (abs_nonneg _) hab

private lemma cubeCoords_sub_norm (d : ℕ) (u v : Cube d) :
    ‖cubeCoords d u.val - cubeCoords d v.val‖ ≤ 2 * ‖u.val-v.val‖ := by
  have hs : ‖cubeCoords d u.val - cubeCoords d v.val‖^2 =
      (∑ i : Fin (d/2), (u.val i-v.val i)^2) +
      ∑ i : Fin (d/2), (Real.sqrt (1-u.val i^2)-Real.sqrt (1-v.val i^2))^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, sum_fin_split (show d/2 ≤ d by omega)]
    simp only [PiLp.sub_apply, cubeCoords_first]
    rw [sum_fin_split (show d/2 ≤ d-d/2 by omega)]
    simp only [cubeCoords_second]
    have hz : (∑ i : Fin (d-d/2-d/2),
      (cubeCoords d u.val ⟨d/2+(d/2+i.val),by omega⟩ -
        cubeCoords d v.val ⟨d/2+(d/2+i.val),by omega⟩)^2) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [cubeCoords_tail d u.val _ (show 2*(d/2) ≤ d/2+(d/2+i.val) by omega),
        cubeCoords_tail d v.val _ (show 2*(d/2) ≤ d/2+(d/2+i.val) by omega)]
      norm_num
    rw [hz, add_zero]
  have hsq : (∑ i : Fin (d/2), (Real.sqrt (1-u.val i^2)-Real.sqrt (1-v.val i^2))^2) ≤
      ∑ i : Fin (d/2), (u.val i-v.val i)^2 := by
    apply Finset.sum_le_sum
    intro i _
    exact (sq_le_sq).2 (sqrt_pair_lipschitz (u.property i) (v.property i))
  have hv : ‖u.val-v.val‖^2 = ∑ i : Fin (d/2), (u.val i-v.val i)^2 := by
    simp [EuclideanSpace.real_norm_sq_eq]
  nlinarith [norm_nonneg (cubeCoords d u.val-cubeCoords d v.val), norm_nonneg (u.val-v.val)]

lemma cubeEmbedding_dist {d : ℕ} (hd : 2 ≤ d) (u v : Cube d) :
    dist (CubeEmbedding d u) (CubeEmbedding d v) ≤
      2 / Real.sqrt (d/2:ℕ) * dist u.val v.val := by
  have hr : 0 < Real.sqrt (d/2:ℕ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d/2 by omega))
  change dist ((Real.sqrt (d/2:ℕ))⁻¹ • cubeCoords d u.val)
    ((Real.sqrt (d/2:ℕ))⁻¹ • cubeCoords d v.val) ≤ _
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, dist_eq_norm]
  calc
    _ ≤ (Real.sqrt (d/2:ℕ))⁻¹ * (2*‖u.val-v.val‖) :=
      mul_le_mul_of_nonneg_left (cubeCoords_sub_norm d u v) (inv_nonneg.mpr hr.le)
    _ = _ := by ring

def cubeProject (d : ℕ) (x : Space d) : Space (d/2) :=
  WithLp.toLp 2 (fun i : Fin (d/2) => x ⟨i.val,by omega⟩)

lemma cubeProject_continuous (d : ℕ) : Continuous (cubeProject d) := by
  unfold cubeProject
  fun_prop

lemma cubeProject_norm (d : ℕ) (x : Space d) : ‖cubeProject d x‖ ≤ ‖x‖ := by
  have h : ‖cubeProject d x‖^2 ≤ ‖x‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      sum_fin_split (show d/2 ≤ d by omega)]
    change (∑ i : Fin (d/2), x ⟨i.val,by omega⟩^2) ≤ _
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  nlinarith [norm_nonneg (cubeProject d x), norm_nonneg x]

lemma cubeProject_sub (d : ℕ) (x y : Space d) : cubeProject d (x-y) = cubeProject d x-cubeProject d y := by
  ext i
  rfl

lemma cubeProject_embedding (d : ℕ) (u : Cube d) :
    cubeProject d (CubeEmbedding d u) = (Real.sqrt (d/2:ℕ))⁻¹ • u.val := by
  ext i
  simp [cubeProject, CubeEmbedding, cubeRaw]

lemma cubeProject_parameter_dist {d : ℕ} (hd : 2 ≤ d) (u : Cube d) (x : Space d) :
    dist u.val (Real.sqrt (d/2:ℕ) • cubeProject d x) ≤
      Real.sqrt (d/2:ℕ) * dist (CubeEmbedding d u) x := by
  have hr : 0 < Real.sqrt (d/2:ℕ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d/2 by omega))
  have he : u.val - Real.sqrt (d/2:ℕ) • cubeProject d x =
      Real.sqrt (d/2:ℕ) • cubeProject d (CubeEmbedding d u-x) := by
    rw [cubeProject_sub, cubeProject_embedding, smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos hr, dist_eq_norm]
  exact mul_le_mul_of_nonneg_left (cubeProject_norm d _) hr.le
end MemoryPrecision


end

end OAI
