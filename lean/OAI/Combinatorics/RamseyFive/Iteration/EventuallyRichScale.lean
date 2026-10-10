import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.Beta

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace SharpRamseyFive.RichRegime
open Filter ParameterHierarchy
open scoped Topology

theorem eventually_rich_scale {η : ℝ} (hη : 0 < η) (hη' : η < 1/10) :
    ∀ᶠ σ : ℝ in atTop, 1000 ≤ σ ∧ ∀ D R g : ℝ,
      Range η σ D R → P η σ D R / 10000 ≤ g → 100000000 ≤ g := by
  have hg := (tendsto_rpow_atTop (mul_pos (by norm_num : (0:ℝ)<10) (beta_pos hη))).eventually
    (eventually_ge_atTop (1000000000000:ℝ))
  filter_upwards [eventually_ge_atTop (1000:ℝ),hg] with σ hσ hp
  refine ⟨hσ,?_⟩
  intro D R g h hpg
  have hh := (finite_bounds hη hη' (by linarith) h).2.2.2.2.2.1
  linarith

lemma source_size_identity {q : ℝ} (hq : 0 < q) (v : ℝ) :
    Real.exp (3*Real.log q/2+(v-1/2)*Real.log q) = q ^ (1+v) := by
  rw [Real.rpow_def_of_pos hq]
  congr 1
  ring

end SharpRamseyFive.RichRegime

end

end OAI
