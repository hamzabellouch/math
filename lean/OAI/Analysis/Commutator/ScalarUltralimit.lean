import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter

namespace Kadison.ScalarUltralimit

variable {ι : Type*}

lemma exists_limit (ω : Ultrafilter ι) (f : ι → ℂ) (C : ℝ)
    (hf : ∀ i, ‖f i‖≤C) : ∃ z : ℂ, ‖z‖≤C ∧ Tendsto f (ω : Filter ι) (𝓝 z) := by
  obtain ⟨z,hz,hl⟩ := (isCompact_closedBall (0 : ℂ) C).ultrafilter_le_nhds
    (ω.map f) (by
      rw [Ultrafilter.coe_map,Filter.map_le_iff_le_comap,Filter.comap_principal]
      exact Filter.le_principal_iff.mpr (Filter.Eventually.of_forall (fun i => by
        simpa only [Metric.mem_closedBall,dist_zero_right] using hf i)))
  exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using hz,hl⟩

def limit (ω : Ultrafilter ι) (f : ι → ℂ) (hf : ∃ C : ℝ, ∀ i, ‖f i‖≤C) : ℂ :=
  (exists_limit ω f hf.choose hf.choose_spec).choose

lemma tendsto_limit (ω : Ultrafilter ι) (f : ι → ℂ) (hf : ∃ C : ℝ, ∀ i, ‖f i‖≤C) :
    Tendsto f (ω : Filter ι) (𝓝 (limit ω f hf)) :=
  (exists_limit ω f hf.choose hf.choose_spec).choose_spec.2

lemma norm_limit_le (ω : Ultrafilter ι) (f : ι → ℂ) (hf : ∃ C : ℝ, ∀ i, ‖f i‖≤C)
    (C : ℝ) (hC : ∀ᶠ i in (ω : Filter ι), ‖f i‖≤C) : ‖limit ω f hf‖≤C :=
  le_of_tendsto (tendsto_limit ω f hf).norm hC

lemma limit_eq_of_tendsto (ω : Ultrafilter ι) (f : ι → ℂ)
    (hf : ∃ C : ℝ, ∀ i, ‖f i‖≤C) {z : ℂ} (hz : Tendsto f (ω : Filter ι) (𝓝 z)) :
    limit ω f hf=z := tendsto_nhds_unique (tendsto_limit ω f hf) hz

variable (ω : Ultrafilter ι)

variable [TopologicalSpace ι]

def value (f : ι →ᵇ ℂ) : ℂ := limit ω f ⟨‖f‖,fun i => f.norm_coe_le_norm i⟩

lemma tendsto_value (f : ι →ᵇ ℂ) : Tendsto f (ω : Filter ι) (𝓝 (value ω f)) :=
  tendsto_limit ω f _

lemma value_add (f g : ι →ᵇ ℂ) : value ω (f+g)=value ω f+value ω g := by
  exact tendsto_nhds_unique (tendsto_value ω _) ((tendsto_value ω f).add (tendsto_value ω g))

lemma value_mul (f g : ι →ᵇ ℂ) : value ω (f*g)=value ω f*value ω g := by
  exact tendsto_nhds_unique (tendsto_value ω _) ((tendsto_value ω f).mul (tendsto_value ω g))

lemma value_smul (a : ℂ) (f : ι →ᵇ ℂ) : value ω (a • f)=a • value ω f := by
  exact tendsto_nhds_unique (tendsto_value ω _) (tendsto_const_nhds.smul (tendsto_value ω f))

lemma value_star (f : ι →ᵇ ℂ) : value ω (star f)=star (value ω f) := by
  exact tendsto_nhds_unique (tendsto_value ω _) (tendsto_value ω f).star

lemma value_const (a : ℂ) : value ω (BoundedContinuousFunction.const ι a)=a := by
  exact tendsto_nhds_unique (tendsto_value ω _) tendsto_const_nhds

lemma value_norm_le (f : ι →ᵇ ℂ) : ‖value ω f‖≤‖f‖ :=
  norm_limit_le ω _ _ _ (Filter.Eventually.of_forall (fun i => f.norm_coe_le_norm i))

def hom : (ι →ᵇ ℂ) →⋆ₐ[ℂ] ℂ where
  toFun := value ω
  map_one' := value_const ω 1
  map_zero' := value_const ω 0
  map_add' := value_add ω
  map_mul' := value_mul ω
  commutes' := fun a => value_const ω a
  map_star' := value_star ω

lemma nonneg_value_re (f : ι →ᵇ ℂ) (hf : ∀ᶠ i in (ω : Filter ι), 0≤(f i).re) :
    0≤(value ω f).re := ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp (tendsto_value ω f)) hf

end Kadison.ScalarUltralimit

end

end
end

end OAI
