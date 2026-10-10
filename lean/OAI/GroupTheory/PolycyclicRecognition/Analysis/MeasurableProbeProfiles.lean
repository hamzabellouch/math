import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProfileParameterContinuity

namespace OAI

/-! # Measurable profiles of the Borel-selected probe chains -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {G W Z : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [TopologicalSpace Z]
  [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)]

/-- A Borel suffix selector gives a Borel profile in the fixed compact
profile family, with the actual formula on the carrying sample cell. -/
theorem exists_measurable_borel_sampled_profile
    {A : Type*} [MeasurableSpace A]
    (J : G → W) (hJ : Continuous J) (x : G) (r : ℝ)
    (φ : Z → G) (hφ : Continuous φ) (suffix : A → G) (hsuffix : Measurable suffix)
    (C : Set A) (hC : MeasurableSet C) (hne : C.Nonempty)
    (S : Set C(Z, W))
    (hmem : ∀ a ∈ C, rescaledContinuousProfile J hJ x (suffix a) r φ hφ ∈ S) :
    ∃ profile : A → S, Measurable profile ∧ ∀ a ∈ C, ∀ z,
      (profile a).val z = rescaledMapProfile J x (suffix a) r φ z := by
  classical
  let F : C → S := fun a =>
    ⟨rescaledContinuousProfile J hJ x (suffix a.val) r φ hφ, hmem a.val a.property⟩
  have hF : Measurable F :=
    (((continuous_rescaledContinuousProfile J hJ x r φ hφ).measurable.comp hsuffix).comp
      measurable_subtype_coe).subtype_mk
  obtain ⟨a₀, ha₀⟩ := hne
  obtain ⟨profile, hp, heq⟩ := (MeasurableEmbedding.subtype_coe hC).exists_measurable_extend
    hF (fun _ => ⟨F ⟨a₀, ha₀⟩⟩)
  refine ⟨profile, hp, ?_⟩
  intro a ha z
  exact congrArg (fun f : S => f.val z) (congrFun heq ⟨a, ha⟩)

/-- At every scale, finitely many Borel-selected prefixes have measurable
representatives in the same profile family. The probe spaces may vary
with the ideal box; no continuity of the tile selector is required. -/
theorem exists_measurable_probe_profile_chain
    {A : ℕ → Type*} [∀ n, MeasurableSpace (A n)] {N : ℕ}
    (J : ℕ → G → W) (hJ : ∀ n, Continuous (J n)) (x : ℕ → G) (r : ℕ → ℝ)
    (φ : ℕ → Z → G) (hφ : ∀ n, Continuous (φ n))
    (suffix : ∀ n, Fin (N + 1) → A n → G) (hsuffix : ∀ n j, Measurable (suffix n j))
    (C : ∀ n, Set (A n)) (hC : ∀ n, MeasurableSet (C n)) (hne : ∀ n, (C n).Nonempty)
    (S : Set C(Z, W))
    (hmem : ∀ n j a, a ∈ C n → ∃ f ∈ S, ∀ z,
      f z = rescaledMapProfile (J n) (x n) (suffix n j a) (r n) (φ n) z) :
    ∃ profile : ∀ n, A n → Fin (N + 1) → S, (∀ n, Measurable (profile n)) ∧
      ∀ n a j, a ∈ C n → ∀ z,
      (profile n a j).val z = rescaledMapProfile (J n) (x n) (suffix n j a) (r n) (φ n) z := by
  have hm (n : ℕ) (j : Fin (N + 1)) (a : A n) (ha : a ∈ C n) :
      rescaledContinuousProfile (J n) (hJ n) (x n) (suffix n j a) (r n) (φ n) (hφ n) ∈ S := by
    obtain ⟨f, hf, he⟩ := hmem n j a ha
    have heq : rescaledContinuousProfile (J n) (hJ n) (x n) (suffix n j a)
        (r n) (φ n) (hφ n) = f := by ext z; exact (he z).symm
    rwa [heq]
  have hex (n : ℕ) (j : Fin (N + 1)) := exists_measurable_borel_sampled_profile
    (J n) (hJ n) (x n) (r n) (φ n) (hφ n) (suffix n j) (hsuffix n j)
    (C n) (hC n) (hne n) S (hm n j)
  choose F hF hactual using hex
  exact ⟨fun n a j => F n j a, fun n => Measurable.of_eval (hF n),
    fun n a j ha z => hactual n j a ha z⟩

end PolycyclicRecognition

end

end OAI
