import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledProfiles
import Mathlib.Topology.CompactOpen
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

namespace OAI

/-! # Continuous dependence of actual profiles on their sheet parameters -/

noncomputable section
namespace PolycyclicRecognition

variable {G W Z A : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [TopologicalSpace Z] [TopologicalSpace A]

/-- The actual rescaled profile as a continuous function of the chart point. -/
def rescaledContinuousProfile (J : G → W) (hJ : Continuous J)
    (x k : G) (r : ℝ) (φ : Z → G) (hφ : Continuous φ) : C(Z, W) :=
  ⟨rescaledMapProfile J x k r φ, continuous_rescaledMapProfile hJ x k r hφ⟩

/-- At a fixed scale the full profile varies continuously with its suffix,
for the topology of uniform convergence on compact chart sets. -/
theorem continuous_rescaledContinuousProfile
    (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (φ : Z → G) (hφ : Continuous φ) :
    Continuous (fun k => rescaledContinuousProfile J hJ x k r φ hφ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_const.smul
    ((hJ.comp ((continuous_const.mul continuous_fst).mul (hφ.comp continuous_snd))).sub
      continuous_const)

/-- Restricting to a compact profile family preserves the continuity of
actual sheet sampling. The membership proof does not choose a new profile. -/
theorem continuous_sampled_profile_subtype
    (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (φ : Z → G) (hφ : Continuous φ) (suffix : A → G) (hsuffix : Continuous suffix)
    (S : Set C(Z, W))
    (hmem : ∀ a, rescaledContinuousProfile J hJ x (suffix a) r φ hφ ∈ S) :
    Continuous (fun a => (⟨rescaledContinuousProfile J hJ x (suffix a) r φ hφ,
      hmem a⟩ : S)) :=
  ((continuous_rescaledContinuousProfile J hJ x r φ hφ).comp hsuffix).subtype_mk hmem

/-- Profiles are extended measurably off the sampling cell. Their source
formula is required only on that cell, where compact containment is known. -/
theorem exists_measurable_sampled_profile
    [MeasurableSpace A] [BorelSpace A]
    (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (φ : Z → G) (hφ : Continuous φ) (suffix : A → G) (hsuffix : Continuous suffix)
    (C : Set A) (hC : MeasurableSet C) (hne : C.Nonempty)
    (S : Set C(Z, W)) [MeasurableSpace S] [BorelSpace S]
    (hmem : ∀ a ∈ C, rescaledContinuousProfile J hJ x (suffix a) r φ hφ ∈ S) :
    ∃ profile : A → S, Measurable profile ∧ ∀ a ∈ C, ∀ z,
      (profile a).val z = rescaledMapProfile J x (suffix a) r φ z := by
  classical
  let F : C → S := fun a =>
    ⟨rescaledContinuousProfile J hJ x (suffix a.val) r φ hφ, hmem a.val a.property⟩
  have hF : Continuous F :=
    (((continuous_rescaledContinuousProfile J hJ x r φ hφ).comp hsuffix).comp
      continuous_subtype_val).subtype_mk _
  obtain ⟨a₀, ha₀⟩ := hne
  obtain ⟨profile, hp, heq⟩ := (MeasurableEmbedding.subtype_coe hC).exists_measurable_extend
    hF.measurable (fun _ => ⟨F ⟨a₀, ha₀⟩⟩)
  refine ⟨profile, hp, ?_⟩
  intro a ha z
  exact congrArg (fun f : S => f.val z) (congrFun heq ⟨a, ha⟩)

/-- A finite family of actual sheet suffixes gives measurable profile
chains on a carrying cell. All choices remain exact on that cell. -/
theorem exists_measurable_profile_chain
    [MeasurableSpace A] [BorelSpace A] {N : ℕ}
    (J : ℕ → G → W) (hJ : ∀ n, Continuous (J n)) (x : ℕ → G) (r : ℕ → ℝ)
    (φ : ℕ → Z → G) (hφ : ∀ n, Continuous (φ n))
    (suffix : ℕ → Fin (N + 1) → A → G) (hsuffix : ∀ n j, Continuous (suffix n j))
    (C : Set A) (hC : MeasurableSet C) (hne : C.Nonempty)
    (S : Set C(Z, W)) [MeasurableSpace S] [BorelSpace S]
    (hmem : ∀ n j a, a ∈ C → ∃ f ∈ S, ∀ z,
      f z = rescaledMapProfile (J n) (x n) (suffix n j a) (r n) (φ n) z) :
    ∃ profile : ℕ → A → Fin (N + 1) → S, (∀ n, Measurable (profile n)) ∧
      ∀ n a j, a ∈ C → ∀ z,
      (profile n a j).val z = rescaledMapProfile (J n) (x n) (suffix n j a) (r n) (φ n) z := by
  have hm (n : ℕ) (j : Fin (N + 1)) (a : A) (ha : a ∈ C) :
      rescaledContinuousProfile (J n) (hJ n) (x n) (suffix n j a) (r n) (φ n) (hφ n) ∈ S := by
    obtain ⟨f, hf, he⟩ := hmem n j a ha
    have heq : rescaledContinuousProfile (J n) (hJ n) (x n) (suffix n j a)
        (r n) (φ n) (hφ n) = f := by ext z; exact (he z).symm
    rwa [heq]
  have hex (n : ℕ) (j : Fin (N + 1)) := exists_measurable_sampled_profile
    (J n) (hJ n) (x n) (r n) (φ n) (hφ n) (suffix n j) (hsuffix n j)
    C hC hne S (hm n j)
  choose F hF hactual using hex
  exact ⟨fun n a j => F n j a, fun n => Measurable.of_eval (hF n),
    fun n a j ha z => hactual n j a ha z⟩

end PolycyclicRecognition

end

end OAI
