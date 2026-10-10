import OAI.Combinatorics.SparsestCut.LatticeDensity

namespace OAI

universe u1 u2 u3 u4

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ProductSlice
open MeasureTheory Set
open scoped BigOperators
noncomputable section
variable {Z : Type u1} {I : Type u2} {K : Type u3} {A : Type u4} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure]
  [Fintype I] [Fintype K] [Fintype A] [DecidableEq I] [DecidableEq K]

def jump (B : I → Z →L[ℝ] ℝ) (q : I → K → ℝ) (F : Finset (I × K) → A → ℝ)
    (θ : ℝ × Z) (i : I) (k : K) (z : Z) (α : A) : ℝ :=
  F (Finset.univ.filter (fun p => form (B p.1) θ+B p.1 z+q p.1 p.2 ≤ form (B i) θ+B i z+q i k)) α-
  F (Finset.univ.filter (fun p => form (B p.1) θ+B p.1 z+q p.1 p.2 < form (B i) θ+B i z+q i k)) α
omit [FiniteDimensional ℝ Z] [(volume : Measure Z).IsAddHaarMeasure] [Fintype A] in
lemma jump_measurable (B : I → Z →L[ℝ] ℝ) (q : I → K → ℝ) (F : Finset (I × K) → A → ℝ)
    (θ : ℝ × Z) (i : I) (k : K) (α : A) : Measurable (fun z => jump B q F θ i k z α) := by
  unfold jump
  apply Measurable.sub
  · apply InterfaceStep.measurable_filter_apply Finset.univ _ _ (fun a => F a α)
    intro p
    exact measurableSet_le ((measurable_const.add (B p.1).measurable).add_const _)
      ((measurable_const.add (B i).measurable).add_const _)
  · apply InterfaceStep.measurable_filter_apply Finset.univ _ _ (fun a => F a α)
    intro p
    exact measurableSet_lt ((measurable_const.add (B p.1).measurable).add_const _)
      ((measurable_const.add (B i).measurable).add_const _)

omit [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [Fintype A] [DecidableEq I] [DecidableEq K] in
lemma jump_bound (B : I → Z →L[ℝ] ℝ) (q : I → K → ℝ) (F : Finset (I × K) → A → ℝ)
    {M : ℝ} (hM : ∀ a α, |F a α|≤M) (θ : ℝ × Z) (i : I) (k : K) (z : Z) (α : A) :
    |jump B q F θ i k z α|≤2*M := by
  unfold jump
  exact (abs_sub _ _).trans (add_le_add (hM _ α) (hM _ α) |>.trans (by ring_nf; rfl))

omit [FiniteDimensional ℝ Z] [(volume : Measure Z).IsAddHaarMeasure] in

lemma common_coefficient_budget (B : I → Z →L[ℝ] ℝ) (s : Finset ℤ)
    (pivot : I → ℝ) (hp : ∀ i, pivot i≠0) {τ : ℝ} (hτ : 0<τ)
    (F : Finset (I × s) → A → ℝ) {M C J : ℝ}
    (_hM0 : 0≤M) (hC : 0≤C) (hJ : 0≤J) (hM : ∀ a α, |F a α|≤M)
    {φ φ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt φ (φ' t) t) (hn : ∀ t, 0≤φ t)
    (hi : Integrable φ) (hi' : Integrable φ') (h1 : ∫ t, φ t=1) (hφC : ∀ t, |φ t|≤C)
    {ψ : Z → ℝ} (hmψ : Measurable ψ) (hnψ : ∀ z, 0≤ψ z) (hiψ : Integrable ψ) (hψ1 : ∫ z, ψ z=1)
    (θ : ℝ × Z) (i : I)
    (hj : ∀ᵐ z ∂law ψ volume, ∀ k : s,
      φ (form (B i) θ+B i z-(k:ℤ)*τ/pivot i)≠0 →
        (∑ α, |jump B (fun i (k : s) => -((k:ℤ)*τ/pivot i)) F θ i k z α|)≤J)
    (hsmall : τ/|pivot i| *(∫ t, |φ' t|)≤1) :
    (∑ α, |(pivot i)⁻¹ * ∑ k : s, ∫ z,
      -(φ (form (B i) θ+B i z-(k:ℤ)*τ/pivot i)*
        jump B (fun i (k : s) => -((k:ℤ)*τ/pivot i)) F θ i k z α) ∂law ψ volume|) ≤ 2*J/τ := by
  let μ := law ψ volume
  let q : I → s → ℝ := fun i (k : s) => -((k:ℤ)*τ/pivot i)
  let w : s → Z → ℝ := fun k z => φ (form (B i) θ+B i z-(k:ℤ)*τ/pivot i)
  have : IsProbabilityMeasure μ := law_probability hmψ hnψ volume hiψ hψ1
  have hcφ : Continuous φ := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hw (k : s) : Measurable (w k) :=
    hcφ.measurable.comp ((measurable_const.add (B i).measurable).sub_const _)
  have hiw (k : s) : Integrable (w k) μ :=
    (integrable_const C).mono' (hw k).aestronglyMeasurable (ae_of_all _ (fun z => hφC _))
  have hid (k : s) (α : A) : Integrable (fun z => w k z*jump B q F θ i k z α) μ := by
    apply (integrable_const (C*(2*M))).mono' ((hw k).mul (jump_measurable B q F θ i k α)).aestronglyMeasurable
    filter_upwards with z
    simp only [Pi.mul_apply, Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hφC _) (jump_bound B q F hM θ i k z α) (abs_nonneg _) hC
  have hs (z : Z) : (∑ k : s, w k z)≤2*|pivot i|/τ := by
    have h := LatticeDensity.affine_lattice_bound hd hn hi hi' h1 hτ (hp i) (form (B i) θ+B i z) s
    rw [← Finset.sum_coe_sort] at h
    have hp0 : 0 < |pivot i| := abs_pos.mpr (hp i)
    have hmul : τ/|pivot i| *(∑ k : s, w k z)≤2 := by exact h.trans (by linarith)
    apply (le_div_iff₀ hτ).mpr
    have hh := mul_le_mul_of_nonneg_right hmul hp0.le
    have he : (τ/|pivot i| *(∑ k : s, w k z))*|pivot i| = (∑ k : s, w k z)*τ := by
      field_simp
    rwa [he] at hh
  have hb := SliceCoefficients.coefficient_budget μ w (jump B q F θ i) hJ
    (fun k z => hn _) hiw hid hj (ae_of_all _ hs)
  simp_rw [abs_mul,abs_inv,← Finset.mul_sum]
  calc
    _ ≤ |pivot i|⁻¹*(J*(2*|pivot i|/τ)) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg _))
    _ = _ := by field_simp [abs_ne_zero.mpr (hp i)]

end
end UniformSparsestCut.ProductSlice

end

end OAI
