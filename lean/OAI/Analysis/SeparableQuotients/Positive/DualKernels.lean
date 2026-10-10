import Mathlib

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields
variable {𝕜 : Type*} [RCLike 𝕜] {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]



lemma infiniteDimensional_ker_to_finite (T : V →L[𝕜] W) [FiniteDimensional 𝕜 W]
    (hV : ¬ FiniteDimensional 𝕜 V) : ¬ FiniteDimensional 𝕜 T.ker := by
  intro hker
  let := hker
  have htop : FiniteDimensional 𝕜 ((⊤ : Submodule 𝕜 W).comap T.toLinearMap) := inferInstance
  let := htop
  let J : V →ₗ[𝕜] ((⊤ : Submodule 𝕜 W).comap T.toLinearMap) :=
    (LinearMap.id : V →ₗ[𝕜] V).codRestrict _ (fun _ => Submodule.mem_top)
  exact hV (FiniteDimensional.of_injective J (fun a b h => congrArg Subtype.val h))

lemma exists_unit_of_infiniteDimensional (hV : ¬ FiniteDimensional 𝕜 V) :
    ∃ v : V, ‖v‖ = 1 := by
  have : Nontrivial V := by
    by_contra hh
    have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hh
    exact hV inferInstance
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨(‖v‖ : 𝕜)⁻¹ • v, norm_smul_inv_norm hv⟩

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
local instance kernelDualSubmoduleNormedGroup (F : Submodule 𝕜 (StrongDual 𝕜 X)) :
    NormedAddCommGroup F := Submodule.normedAddCommGroup F
local instance kernelDualSubmoduleNormedSpace (F : Submodule 𝕜 (StrongDual 𝕜 X)) :
    NormedSpace 𝕜 F := Submodule.normedSpace F

lemma exists_unit_annihilating_finite
    (F : Submodule 𝕜 (StrongDual 𝕜 X)) (hF : ¬ FiniteDimensional 𝕜 F) (D : Finset X) :
    ∃ f : F, ‖f‖ = 1 ∧ ∀ d ∈ D, (f : StrongDual 𝕜 X) d = 0 := by
  let T : F →L[𝕜] (D → 𝕜) := ContinuousLinearMap.pi (fun d => F.subtypeL.flip d.val)
  have hinf := infiniteDimensional_ker_to_finite T hF
  obtain ⟨f, hf⟩ := exists_unit_of_infiniteDimensional hinf
  refine ⟨f.val, hf, ?_⟩
  intro d hd
  have hh := congrFun f.property (⟨d, hd⟩ : D)
  exact hh
end SeparableQuotient.Positive.Fields

end

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields
variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
local instance scalarDualSubmoduleNormedGroup (F : Submodule 𝕜 (StrongDual 𝕜 X)) :
    NormedAddCommGroup F := Submodule.normedAddCommGroup F
local instance scalarDualSubmoduleNormedSpace (F : Submodule 𝕜 (StrongDual 𝕜 X)) :
    NormedSpace 𝕜 F := Submodule.normedSpace F

theorem exists_finite_half_normers_scalar (F : Submodule 𝕜 (StrongDual 𝕜 X))
    [FiniteDimensional 𝕜 F] :
    ∃ D : Finset X, (∀ x ∈ D, ‖x‖ ≤ 1) ∧
      ∀ f ∈ F, ∃ x ∈ D, ‖f‖ ≤ 2 * ‖f x‖ := by
  classical
  let U : {x : X // ‖x‖ ≤ 1} → Set F := fun x => {f | (1:ℝ)/2 < ‖f.val x.val‖}
  have ho (x : {x : X // ‖x‖ ≤ 1}) : IsOpen (U x) :=
    isOpen_lt continuous_const ((F.subtypeL.flip x.val).continuous.norm)
  have hcover : sphere (0 : F) 1 ⊆ ⋃ x, U x := by
    intro f hf
    have hn : ‖f.val‖ = 1 := by simpa only [mem_sphere, dist_zero_right, Submodule.norm_coe] using hf
    obtain ⟨x, hx, hfx⟩ := f.val.exists_lt_apply_of_lt_opNorm (show (1:ℝ)/2 < ‖f.val‖ by rw [hn]; norm_num)
    exact mem_iUnion.mpr ⟨⟨x, hx.le⟩, hfx⟩
  obtain ⟨D₀, hD₀⟩ := (isCompact_sphere (0 : F) 1).elim_finite_subcover U ho hcover
  let D := insert 0 (D₀.image Subtype.val)
  refine ⟨D, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp
    · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      exact y.property
  · intro f hf
    by_cases hh : f = 0
    · exact ⟨0, Finset.mem_insert_self _ _, by simp [hh]⟩
    let v : F := ⟨f, hf⟩
    have hv : v ≠ 0 := by intro h; exact hh (congrArg Subtype.val h)
    let g : F := (‖f‖ : 𝕜)⁻¹ • v
    have hg : g ∈ sphere (0 : F) 1 := by
      rw [mem_sphere, dist_zero_right]
      change ‖(‖v‖ : 𝕜)⁻¹ • v‖ = 1
      exact norm_smul_inv_norm hv
    obtain ⟨x, hx⟩ := mem_iUnion.mp (hD₀ hg)
    obtain ⟨hxD, hxg⟩ := mem_iUnion.mp hx
    refine ⟨x.val, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hxD, rfl⟩), ?_⟩
    have he : (1:ℝ)/2 < ‖f‖⁻¹ * ‖f x.val‖ := by
      simpa only [U, mem_ofPred_eq, g, Submodule.coe_smul, smul_apply, norm_smul,
        norm_inv, RCLike.norm_ofReal, Real.norm_eq_abs, abs_norm, v] using hxg
    have hn : 0 < ‖f‖ := norm_pos_iff.mpr hh
    have hv' := mul_lt_mul_of_pos_left he hn
    field_simp at hv'
    linarith

lemma exists_prefix_half_normers (f : ℕ → StrongDual 𝕜 X) (n : ℕ) :
    ∃ D : Finset X, (∀ x ∈ D, ‖x‖ ≤ 1) ∧
      ∀ v ∈ Submodule.span 𝕜 (f '' (Finset.range n : Set ℕ)),
        ∃ x ∈ D, ‖v‖ ≤ 2 * ‖v x‖ := by
  have : FiniteDimensional 𝕜 (Submodule.span 𝕜 (f '' (Finset.range n : Set ℕ))) :=
    (Submodule.fg_iff_finiteDimensional _).mp (Submodule.fg_span ((Finset.finite_toSet _).image _))
  exact exists_finite_half_normers_scalar _

def chosenPrefixNormers (f : ℕ → StrongDual 𝕜 X) (n : ℕ) : Finset X :=
  (exists_prefix_half_normers f n).choose

lemma chosenPrefixNormers_spec (f : ℕ → StrongDual 𝕜 X) (n : ℕ) :
    (∀ x ∈ chosenPrefixNormers f n, ‖x‖ ≤ 1) ∧
      ∀ v ∈ Submodule.span 𝕜 (f '' (Finset.range n : Set ℕ)),
        ∃ x ∈ chosenPrefixNormers f n, ‖v‖ ≤ 2 * ‖v x‖ :=
  (exists_prefix_half_normers f n).choose_spec
end SeparableQuotient.Positive.Fields

end

end

end OAI
