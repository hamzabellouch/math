import Mathlib
import OAI.Analysis.Conductivity.Scalarization.ScalarRelationLpStrongClosed
import OAI.Analysis.Conductivity.Variational.DenseWeakStrongContinuityPoints

namespace OAI

section
noncomputable section
open MeasureTheory
open scoped ENNReal
noncomputable section
open Matrix Filter Topology
namespace ScalarConductivity
open Filter Topology Set TopologicalSpace

lemma tendstoInMeasure_of_small_exceptional_sets
    {X V : Type*} [MeasurableSpace X] [SeminormedAddCommGroup V]
    (μ : Measure X) (f : ℕ → X → V) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, μ {x | ε n ≤ ‖f n x‖} ≤ ENNReal.ofReal (ε n)) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro δ hδ
  simp only [sub_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hε)
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [(tendsto_order.1 hε).2 δ hδ] with n hn
    exact (measure_mono (fun x hx => hn.le.trans hx)).trans (hbound n)

def ApproxScalar {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure X) (a b ε : ℝ) (Z : Lp V 2 μ × Lp V 2 μ) : Prop :=
  ∃ s : X → ℝ, Measurable s ∧
    (∀ᵐ x ∂μ, s x ∈ Icc a b) ∧
    μ {x | ε ≤ ‖Z.2 x - s x • Z.1 x‖} ≤ ENNReal.ofReal ε

theorem exact_scalar_of_weak_density
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] (μ : Measure X)
    [SeparableSpace (Lp V 2 μ)] {a b : ℝ} (hab : a ≤ b)
    (K : Set (WeakSpace ℝ (Lp V 2 μ × Lp V 2 μ)))
    (hK : IsCompact K) (hKn : K.Nonempty)
    (hdense : ∀ ε > 0, Dense {z : K | ApproxScalar μ a b ε
      ((toWeakSpace ℝ (Lp V 2 μ × Lp V 2 μ)).symm z.val)}) :
    ∃ (Z : Lp V 2 μ × Lp V 2 μ) (s : X → ℝ),
      toWeakSpace ℝ (Lp V 2 μ × Lp V 2 μ) Z ∈ K ∧ Measurable s ∧
      (∀ᵐ x ∂μ, s x ∈ Icc a b ∧ Z.2 x = s x • Z.1 x) := by
  classical
  let : Nonempty K := hKn.to_subtype
  let φ : K → Lp V 2 μ × Lp V 2 μ :=
    fun z => (toWeakSpace ℝ (Lp V 2 μ × Lp V 2 μ)).symm z.val
  obtain ⟨z, hz⟩ := (dense_weakToStrong_continuityPoints K hK).nonempty
  change ContinuousAt φ z at hz
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεp : ∀ n, 0 < ε n := fun n => div_pos zero_lt_one (Nat.cast_add_one_pos n)
  have hεt : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hn : ∀ n, ∃ w : K, ApproxScalar μ a b (ε n) (φ w) ∧ dist (φ w) (φ z) < ε n := by
    intro n
    have hnbr : {w : K | dist (φ w) (φ z) < ε n} ∈ 𝓝 z :=
      hz.preimage_mem_nhds (Metric.ball_mem_nhds _ (hεp n))
    obtain ⟨w, hw, hw'⟩ := (hdense (ε n) (hεp n)).inter_nhds_nonempty hnbr
    exact ⟨w, hw, hw'⟩
  choose w hw hd using hn
  have hwt : Tendsto (fun n => φ (w n)) atTop (𝓝 (φ z)) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hd n).le) hεt
  choose s hsm hsb hsr using hw
  obtain ⟨σ, hσm, hσ⟩ := scalar_relation_Lp_strong_closed hab hsb
    (continuous_fst.tendsto _ |>.comp hwt) (continuous_snd.tendsto _ |>.comp hwt)
    (tendstoInMeasure_of_small_exceptional_sets μ
      (fun n x => (φ (w n)).2 x - s n x • (φ (w n)).1 x) ε hεt hsr)
  refine ⟨φ z, σ, ?_, hσm, hσ⟩
  simpa only [φ, LinearEquiv.apply_symm_apply] using z.property

end ScalarConductivity

end
end
end

end OAI
