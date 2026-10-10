import Mathlib
import OAI.Probability.GaussianRegression.Main
import OAI.Probability.MemoryPrecision.KernelCaps

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter EuclideanGeometry
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

noncomputable section
universe u v


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise
namespace MemoryPrecision.Kernel
open NoiselessRegression
namespace Policy
variable {d M T : ℕ} (K : Policy d M T)

lemma eval_pair_le_one {X : Type*} (w v : ℕ → MemoryPrecision.Kernel.State M → X → ℝ≥0∞)
    (s t : X) (hpair : ∀ n j, w n j s + v n j t ≤ 1)
    (n k : ℕ) (j : MemoryPrecision.Kernel.State M) (obs : Observations d k) :
    K.eval w n k j s obs + K.eval v n k j t obs ≤ 1 := by
  induction k generalizing n j with
  | zero => exact hpair n j
  | succ k ih =>
    simp only [eval, ← Finset.sum_add_distrib, ← mul_add]
    calc
      _ ≤ ∑ a : Action M, K.transition (n+1) j (obs 0) a * 1 := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul' le_rfl
        split_ifs
        · exact hpair _ _
        · exact ih _ _ _
      _ = 1 := by simpa only [mul_one] using K.transition_sum (n+1) j (obs 0)

lemma pathValue_pair_le_one {X : Type*} (w v : ℕ → MemoryPrecision.Kernel.State M → X → ℝ≥0∞)
    (s t : X) (hpair : ∀ n j, w n j s + v n j t ≤ 1) (obs : Observations d T) :
    K.pathValue w s obs + K.pathValue v t obs ≤ 1 := by
  simp only [pathValue, ← Finset.sum_add_distrib, ← mul_add]
  calc
    _ ≤ ∑ a : Action M, K.initial a * 1 := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul' le_rfl
      split_ifs
      · exact hpair _ _
      · exact K.eval_pair_le_one w v s t hpair _ _ _ _
    _ = 1 := by simpa only [mul_one] using K.initial_sum

lemma chord_pair_le_one {ε : ℝ} (hε : ε ≤ 1/10)
    (s t v : MemoryPrecision.Kernel.Sphere d) (hst : 1/5 < dist s.val t.val) :
    chordTest ε (s,v) + chordTest ε (t,v) ≤ 1 := by
  classical
  have hn : ¬(dist v.val s.val ≤ ε ∧ dist v.val t.val ≤ ε) := by
    rintro ⟨hs,ht⟩
    have htri := dist_triangle s.val v.val t.val
    rw [dist_comm s.val v.val] at htri
    linarith
  simp only [chordTest, Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs <;> simp_all

lemma output_chord_pair_le_one {ε : ℝ} (hε : ε ≤ 1/10)
    (s t : MemoryPrecision.Kernel.Sphere d) (hst : 1/5 < dist s.val t.val)
    (n : ℕ) (j : MemoryPrecision.Kernel.State M) :
    K.outputTest (chordTest ε) n j s + K.outputTest (chordTest ε) n j t ≤ 1 := by
  have hm : Measurable (fun v : MemoryPrecision.Kernel.Sphere d => chordTest ε (s,v)) :=
    (measurable_chordTest ε).comp (measurable_const.prodMk measurable_id)
  simp only [outputTest]
  rw [← lintegral_add_left hm]
  exact (lintegral_mono (fun v => chord_pair_le_one hε s t v hst)).trans_eq (by simp)

lemma path_reflection_pair {ε : ℝ} (hε : ε ≤ 1/10)
    (A : Rows d T) (s : MemoryPrecision.Kernel.Sphere d)
    (U : Submodule ℝ (MemoryPrecision.Kernel.Vector d)) (hA : ∀ i, A i ∈ U)
    (hst : 1/5 < dist s.val (U.reflection s.val)) :
    K.pathValue (K.outputTest (chordTest ε)) s (records s A) +
      K.pathValue (K.outputTest (chordTest ε)) (sphereIsometry U.reflection s)
        (records (sphereIsometry U.reflection s) A) ≤ 1 := by
  have he : records (sphereIsometry U.reflection s) A = records s A := by
    funext i
    change (A i, ⟪U.reflection s.val, A i⟫) = (A i, ⟪s.val, A i⟫)
    apply Prod.ext
    · rfl
    · have h := U.reflection.inner_map_map s.val (A i)
      rw [(Submodule.reflection_eq_self_iff (A i)).2 (hA i)] at h
      exact h
  rw [he]
  have hpair : ∀ n j, K.outputTest (chordTest ε) n j s +
      K.outputTest (chordTest ε) n j (sphereIsometry U.reflection s) ≤ 1 :=
    fun n j => K.output_chord_pair_le_one hε s (sphereIsometry U.reflection s) hst n j
  exact K.pathValue_pair_le_one (K.outputTest (chordTest ε))
    (K.outputTest (chordTest ε)) s (sphereIsometry U.reflection s) hpair (records s A)
end Policy

lemma sphere_reflection_function_bound {d : ℕ} [NeZero d]
    (U : Submodule ℝ (MemoryPrecision.Kernel.Vector d)) (hU : 4*Module.finrank ℝ U ≤ d)
    {f : MemoryPrecision.Kernel.Sphere d → ℝ≥0∞} (hf : AEMeasurable f (UniformSphere d))
    (hf1 : ∀ s, f s ≤ 1)
    (hpair : ∀ s, 1/5 < dist s.val (U.reflection s.val) →
      f s + f (sphereIsometry U.reflection s) ≤ 1) :
    (∫⁻ s, f s ∂UniformSphere d) ≤ ENNReal.ofReal (21/32:ℝ) := by
  let R := sphereIsometry U.reflection
  let B : Set (MemoryPrecision.Kernel.Sphere d) := {s | (4/5:ℝ) ≤ ‖U.orthogonalProjectionOnto s.val‖^2}
  have hB : MeasurableSet B := by dsimp [B]; exact measurableSet_le measurable_const (by fun_prop)
  have hp : MeasurePreserving R (UniformSphere d) (UniformSphere d) := sphereIsometry_preserving U.reflection
  have he : (∫⁻ s, f (R s) ∂UniformSphere d) = ∫⁻ s, f s ∂UniformSphere d := by
    calc
      _ = ∫⁻ s, f s ∂(UniformSphere d).map R :=
        (lintegral_map' (by simpa only [hp.map_eq] using hf) hp.measurable.aemeasurable).symm
      _ = _ := by rw [hp.map_eq]
  have hb : UniformSphere d B ≤ ENNReal.ofReal (5/16:ℝ) :=
    sphere_projection_large U (by simpa using hU)
  have hsum : ∀ s, f s + f (R s) ≤ 1 + B.indicator (fun _ => 1) s := by
    intro s
    classical
    by_cases hs : s ∈ B
    · simpa [hs] using add_le_add (hf1 s) (hf1 (R s))
    · have hst : 1/5 < dist s.val (U.reflection s.val) := by
        by_contra hn
        have hd : dist s.val (U.reflection s.val) ≤ 1/5 := le_of_not_gt hn
        rw [reflection_dist] at hd
        have hn := U.norm_sq_eq_add_norm_sq_starProjection s.val
        rw [mem_sphere_zero_iff_norm.mp s.property] at hn
        have he : ‖U.starProjection s.val‖ = ‖U.orthogonalProjectionOnto s.val‖ := rfl
        rw [he] at hn
        apply hs
        change (4/5:ℝ) ≤ ‖U.orthogonalProjectionOnto s.val‖^2
        nlinarith [norm_nonneg (Uᗮ.starProjection s.val)]
      simpa [hs] using hpair s hst
  have hi : (∫⁻ s, f s ∂UniformSphere d) + (∫⁻ s, f s ∂UniformSphere d) ≤
      1 + ENNReal.ofReal (5/16:ℝ) := by
    calc
      _ = (∫⁻ s, f s ∂UniformSphere d) + (∫⁻ s, f (R s) ∂UniformSphere d) := by rw [he]
      _ = ∫⁻ s, f s + f (R s) ∂UniformSphere d := (lintegral_add_left' hf _).symm
      _ ≤ ∫⁻ s, 1 + B.indicator (fun _ => (1:ℝ≥0∞)) s ∂UniformSphere d := lintegral_mono hsum
      _ = 1 + UniformSphere d B := by rw [lintegral_add_left measurable_const]; simp [lintegral_indicator_const hB]
      _ ≤ _ := add_le_add le_rfl hb
  calc
    _ = ENNReal.ofReal (1/2:ℝ) * ((∫⁻ s, f s ∂UniformSphere d) +
      (∫⁻ s, f s ∂UniformSphere d)) := by
      rw [← two_mul, ← mul_assoc]
      have hc : ENNReal.ofReal (1/2:ℝ) * 2 = 1 := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
        norm_num
      rw [hc, one_mul]
    _ ≤ ENNReal.ofReal (1/2:ℝ) * (1 + ENNReal.ofReal (5/16:ℝ)) := mul_le_mul' le_rfl hi
    _ = ENNReal.ofReal (21/32:ℝ) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1)
        (by norm_num : (0:ℝ) ≤ 5/16),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
      norm_num

namespace Policy
lemma source_linear_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Ω → Policy d M T) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 0 < d) (hT : 4*T ≤ d) {ε : ℝ} (hε : ε ≤ 1/10)
    (hL : Admissible L ρ (UniformSphere d)) :
    Success L ρ (UniformSphere d) ε ≤ ENNReal.ofReal (21/32:ℝ) := by
  let : NeZero d := ⟨hd.ne'⟩
  apply (success_le_chord L ρ (UniformSphere d) ε).trans
  have hm := hL.experiment (chordTest ε) (measurable_chordTest ε) (chordTest_le_one ε)
  unfold ChordSuccess
  rw [lintegral_prod_symm _ hm]
  apply le_trans (b := ∫⁻ _z : Ω × Rows d T, ENNReal.ofReal (21/32:ℝ)
    ∂ρ.prod (RowLaw d T)) ?_ (by simp)
  apply lintegral_mono_ae
  filter_upwards [ae_fiber_aemeasurable hm] with z hz
  let U : Submodule ℝ (MemoryPrecision.Kernel.Vector d) := Submodule.span ℝ (Set.range z.2)
  have hdim : Module.finrank ℝ U ≤ T := by
    have h := finrank_span_le_card (R := ℝ) (Set.range z.2)
    apply h.trans
    rw [Set.toFinset_range]
    exact (Finset.card_image_le).trans_eq (by simp)
  apply sphere_reflection_function_bound U ((Nat.mul_le_mul_left 4 hdim).trans hT) hz
  · intro s
    exact (L z.1).pathValue_le_one _ ((L z.1).outputTest_le_one (chordTest_le_one ε)) _ _
  · intro s hs
    exact (L z.1).path_reflection_pair hε z.2 s U
      (fun i => Submodule.subset_span (Set.mem_range_self i)) hs
end Policy
end MemoryPrecision.Kernel


end

end OAI
