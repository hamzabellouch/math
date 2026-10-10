import Mathlib
import OAI.Geometry.HyperbolicGroups.DiagonalSampling

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate

namespace SamplingStage
variable {δ : ℕ → ℝ} (s : ∀ m, SamplingStage m (δ m))
abbrev Alphabet (m : ℕ) := SymmetricAlphabet (s m).size
abbrev Matches (m : ℕ) := StarModel.Matches rowSupport (s m).master
instance (m : ℕ) : Nonempty ((Matches s) m) := (s m).nonempty

def label (m : ℕ) (a : (Matches s) m) : Field → (Alphabet s) m := a.val

lemma size_tendsto : Tendsto (fun m => (s m).size) atTop atTop :=
  tendsto_atTop_mono (fun m => (s m).large) tendsto_id

/-- The genuine pure combinatorial sampling sequence, obtained by diagonalizing
actual finite table realizations. The laws in its conclusion are not hypotheses. -/
theorem samplingSequence : SamplingSequence Field Admissible (Alphabet s) (Matches s) (label s) where
  singleton e := by
    have hh : ∀ m, (((FiniteLaw.uniform : FiniteLaw ((Matches s) m)).map
        (fun a => (label s) m a e)).totalVariation FiniteLaw.uniform) ≤ 2*stageError m := by
      intro m
      exact ((ConditionalTest.singleton_bound e ((s m).tests (singletonData e) 0 (Nat.zero_le _))).choose_spec)
    exact squeeze_zero (fun m => FiniteLaw.totalVariation_nonneg _ _) hh
      (by simpa using stageError_tendsto.const_mul 2)
  star I e he ha k := by
    let p : ConditionalData := ⟨(I,e),he,ha⟩
    refine ⟨stageError,stageError_tendsto,?_⟩
    filter_upwards [eventually_ge_atTop k] with m hm
    obtain ⟨hne,κ,hb,hl⟩ := (s m).tests p k hm
    exact ⟨κ,hb,hl⟩

end SamplingStage

/-- One admissible positive parameter sequence. Later diagram restrictions may
be imposed by choosing smaller parameters before each finite selection. -/
def samplingParameter (m : ℕ) : ℝ := 1 / (1000*(m+1:ℝ))
lemma samplingParameter_pos (m : ℕ) : 0 < samplingParameter m := by unfold samplingParameter; positivity
lemma samplingParameter_lt_one (m : ℕ) : samplingParameter m < 1 := by
  unfold samplingParameter
  rw [div_lt_one (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) m]
lemma samplingParameter_small (m : ℕ) : (m+1:ℝ)*(98*samplingParameter m) ≤ 1/2 := by
  unfold samplingParameter
  have hp : (m+1:ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [Nat.cast_nonneg (α := ℝ) m]
lemma samplingParameter_tendsto : Tendsto samplingParameter atTop (𝓝 0) := by
  have hh := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hf : samplingParameter = fun n : ℕ => (1/1000:ℝ) * (1 / (n+1:ℝ)) := by
    funext n
    simp only [samplingParameter,div_eq_mul_inv,mul_inv_rev,one_mul]
    ring
  rw [hf]
  simpa using hh.const_mul (1/1000:ℝ)

def actualSamplingStage (m : ℕ) : SamplingStage m (samplingParameter m) :=
  Classical.choice (exists_samplingStage m (samplingParameter_pos m)
    (samplingParameter_lt_one m) (samplingParameter_small m))

/-- An unconditional table sampling producer. Asphericity and filling still
require the separate diagram event on these same tables. -/
theorem actualSamplingSequence : SamplingSequence Field Admissible
    (SamplingStage.Alphabet actualSamplingStage) (SamplingStage.Matches actualSamplingStage)
    (SamplingStage.label actualSamplingStage) := SamplingStage.samplingSequence actualSamplingStage

end IncidenceTemplate
end HyperbolicObstruction
end
end

section

end
end

end OAI
