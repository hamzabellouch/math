import OAI.Probability.GaussianReplacement.StreamSphere
import OAI.Probability.GaussianRegression.Blocks

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
universe u
namespace NoiselessRegression
open InnerProductSpace
open scoped Pointwise

namespace Learner
lemma run_congr_labels {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s t : UnitSphere d) (ω : Ω) (x : Samples d T)
    (h : ∀ i, ⟪x i,s.val⟫ = ⟪x i,t.val⟫) (n : ℕ) :
    L.run s ω x n = L.run t ω x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    split
    · rfl
    · split
      · rw [h]
      · rfl

lemma estimate_congr_labels {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s t : UnitSphere d) (ω : Ω) (x : Samples d T)
    (h : ∀ i, ⟪x i,s.val⟫ = ⟪x i,t.val⟫) : L.estimate s ω x = L.estimate t ω x := by
  simp only [estimate, terminal, run_congr_labels L s t ω x h]

lemma angularSuccess_nullMeasurable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (hL : L.Admissible ρ) :
    NullMeasurableSet {z : UnitSphere d × (Ω × Samples d T) |
      angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := by
  apply nullMeasurableSet_le _ aemeasurable_const
  exact Real.continuous_arccos.measurable.comp_aemeasurable
    ((measurable_subtype_coe.comp_aemeasurable hL.uniform_experiment).inner
      (measurable_subtype_coe.comp measurable_fst).aemeasurable)

lemma linear_success_bound {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hd : 0 < d) (hT : 4*T ≤ d) {ε : ℝ} (hε : ε ≤ 1/10) (hL : L.Admissible ρ) :
    L.uniformSuccess ρ ε ≤ ENNReal.ofReal (21/32 : ℝ) := by
  classical
  let : NeZero d := ⟨hd.ne'⟩
  have hmeas := ae_fiber_aemeasurable hL.uniform_experiment
  unfold uniformSuccess
  refine (prod_null_set_bound (L.angularSuccess_nullMeasurable ρ ε hL)
    (c := ENNReal.ofReal (21/32 : ℝ)) ?_).trans_eq (by simp)
  filter_upwards [hmeas] with z hz
  let U : Submodule ℝ (Vector d) := Submodule.span ℝ (Set.range z.2)
  have hdim : Module.finrank ℝ U ≤ T := by
    have h := finrank_span_le_card (R := ℝ) (Set.range z.2)
    apply h.trans
    rw [Set.toFinset_range]
    exact (Finset.card_image_le).trans_eq (by simp)
  have hU : 4 * Module.finrank ℝ U ≤ Module.finrank ℝ (Vector d) := by
    simpa only [Vector, finrank_euclideanSpace_fin] using (Nat.mul_le_mul_left 4 hdim).trans hT
  change sphereLaw {s : UnitSphere d | angularError s (L.estimate s z.1 z.2) ≤ ε} ≤ _
  apply sphere_reflection_success_bound U hU
  · exact nullMeasurableSet_le
      (Real.continuous_arccos.measurable.comp_aemeasurable
        ((measurable_subtype_coe.comp_aemeasurable hz).inner measurable_subtype_coe.aemeasurable))
      aemeasurable_const
  · intro s hs ht
    let t := sphereIsometry U.reflection s
    have he : L.estimate s z.1 z.2 = L.estimate t z.1 z.2 := by
      apply L.estimate_congr_labels
      intro i
      have hi : z.2 i ∈ U := Submodule.subset_span (Set.mem_range_self i)
      have he := U.reflection.inner_map_map (z.2 i) s.val
      rw [(Submodule.reflection_eq_self_iff (z.2 i)).2 hi] at he
      exact he.symm
    have hs' : dist s.val (L.estimate s z.1 z.2).val ≤ ε := by
      apply (chord_le_arccos s (L.estimate s z.1 z.2)).trans
      simpa only [Set.mem_ofPred_eq, angularError, real_inner_comm] using hs
    have ht' : dist t.val (L.estimate t z.1 z.2).val ≤ ε := by
      apply (chord_le_arccos t (L.estimate t z.1 z.2)).trans
      simpa only [Set.mem_ofPred_eq, angularError, real_inner_comm] using ht
    calc
      _ = dist s.val t.val := rfl
      _ ≤ dist s.val (L.estimate s z.1 z.2).val + dist (L.estimate s z.1 z.2).val t.val := dist_triangle _ _ _
      _ ≤ ε + ε := by rw [he, dist_comm (L.estimate t z.1 z.2).val t.val] at *; exact add_le_add hs' ht'
      _ ≤ 1/5 := by linarith
end Learner

section Block
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [borelSpaceE : BorelSpace E]

omit borelSpaceE in
lemma blockValue_le_one_no_borel {J : Type*} [Fintype J] {m : ℕ} {h : J → E → ℝ≥0∞}
    (hh : ∀ j s, h j s ≤ 1) (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (s : E) :
    blockValue h φ s ≤ 1 := by
  exact (lintegral_mono (fun A => hh _ s)).trans_eq (by simp)

end Block

end NoiselessRegression

end

end OAI
