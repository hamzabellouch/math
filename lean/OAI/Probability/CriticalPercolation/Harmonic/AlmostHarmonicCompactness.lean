import Mathlib
import OAI.Probability.CriticalPercolation.Growth.WordLengthGeometry
import OAI.Probability.CriticalPercolation.Harmonic.CayleyCaccioppoli
import OAI.Probability.CriticalPercolation.Harmonic.ProjectedWalkFunctions
import OAI.Probability.CriticalPercolation.Harmonic.WalkAlmostHarmonic

namespace OAI

section
noncomputable section
open Set Function Filter
open scoped Classical Pointwise BigOperators Topology

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

include W in
lemma countable_group : Countable A := by
  apply Set.countable_univ_iff.mp
  have hc : (⋃ n:ℕ, (W.ball n:Set A)).Countable :=
    Set.countable_iUnion (fun n => (W.ball n).finite_toSet.countable)
  apply hc.mono
  intro a _
  obtain ⟨n,hn⟩ := W.exists_mem_ball a
  exact Set.mem_iUnion.mpr ⟨n,hn⟩

lemma exists_projected_approximation [Infinite A] (d : ℕ)
    (hg : SparseGrowth.HasDegree W.generators d) (δ : ℝ) (hδ : 0<δ) :
    ∃ u : A → ℝ, u 1=0 ∧ (∀ x, |u x|≤(W.length x:ℝ)) ∧
      (∀ x s, s∈W.generators → |u (x*s)-u x|≤1) ∧
      (W.generators.card:ℝ)⁻¹^2≤∑ s∈W.generators, (u s)^2 ∧
      ∀ x, |∑ s∈W.generators, (u x-u (x*s))|≤δ := by
  have hc : (0:ℝ)<W.generators.card := by exact_mod_cast W.generators_card_pos
  obtain ⟨n,hE,hres⟩ := W.exists_walk_small_relative_residual d hg
    (δ^2/(W.generators.card:ℝ)) (div_pos (sq_pos_of_pos hδ) hc)
  let f := W.walkState n
  obtain ⟨t,ht,hlarge⟩ := W.exists_large_generator_gradient f
  let u := W.projectedFunction f t
  have hlow := W.projectedFunction_generator_lower f hE t hlarge
  refine ⟨u,W.projectedFunction_one f t,W.projectedFunction_length_bound f hE t ht,
    W.projectedFunction_edge_bound f hE t ht,?_,?_⟩
  · have hs : (W.generators.card:ℝ)⁻¹^2≤(u t)^2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hc.le) hlow 2
    exact hs.trans (Finset.single_le_sum (fun s hs => sq_nonneg (u s)) ht)
  · intro x
    have h := W.projectedFunction_residual_sq f hE t ht x
    have hb : (W.generators.card:ℝ)*‖f-W.lazyWalk f‖^2/W.walkEnergy f≤δ^2 := by
      apply (div_le_iff₀ hE).mpr
      have hh := mul_le_mul_of_nonneg_left hres hc.le
      have he : (W.generators.card:ℝ)*(δ^2/(W.generators.card:ℝ)*W.walkEnergy f)=δ^2*W.walkEnergy f := by
        field_simp
      rw [he] at hh
      exact hh
    have hh : (∑ s∈W.generators, (u x-u (x*s)))^2≤δ^2 := h.trans hb
    nlinarith [sq_abs (∑ s∈W.generators, (u x-u (x*s))),abs_nonneg (∑ s∈W.generators, (u x-u (x*s)))]

theorem exists_nonconstant_lipschitz_harmonic [Infinite A] (d : ℕ)
    (hg : SparseGrowth.HasDegree W.generators d) :
    ∃ u : A → ℝ, W.IsHarmonic u ∧ u 1=0 ∧
      (∀ x, |u x|≤(W.length x:ℝ)) ∧
      (∀ x s, s∈W.generators → |u (x*s)-u x|≤1) ∧
      ∃ s∈W.generators, u s≠0 := by
  let _ : Countable A := W.countable_group
  have hδ (n:ℕ) : (0:ℝ)<1/((n:ℝ)+1) := by positivity
  choose v hv1 hvbound hvedge hvgrad hvres using
    (fun n : ℕ => W.exists_projected_approximation d hg (1/((n:ℝ)+1)) (hδ n))
  let K : Set (A → ℝ) := Set.pi Set.univ (fun x => Set.Icc (-(W.length x:ℝ)) (W.length x:ℝ))
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hvK (n:ℕ) : v n∈K := by
    intro x hx
    exact abs_le.mp (hvbound n x)
  obtain ⟨u,huK,φ,hφ,hlim⟩ := hK.tendsto_subseq hvK
  have hxlim (x:A) : Tendsto (fun n => v (φ n) x) atTop (𝓝 (u x)) :=
    (continuous_apply x).continuousAt.tendsto.comp hlim
  have hu1 : u 1=0 := by
    have hh : Tendsto (fun n => v (φ n) 1) atTop (𝓝 0) := by
      simpa only [hv1] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique (hxlim 1) hh
  have hbound (x:A) : |u x|≤(W.length x:ℝ) := abs_le.mpr (huK x (Set.mem_univ x))
  have hedge (x s:A) (hs:s∈W.generators) : |u (x*s)-u x|≤1 :=
    le_of_tendsto ((hxlim (x*s)).sub (hxlim x)).abs (Filter.Eventually.of_forall (fun n => hvedge (φ n) x s hs))
  have hgrad : (W.generators.card:ℝ)⁻¹^2≤∑ s∈W.generators, (u s)^2 := by
    have hl := tendsto_finsetSum W.generators (fun s hs => (hxlim s).pow 2)
    exact ge_of_tendsto hl (Filter.Eventually.of_forall (fun n => hvgrad (φ n)))
  have hharm : W.IsHarmonic u := by
    intro x
    have hl := tendsto_finsetSum W.generators (fun s hs => (hxlim x).sub (hxlim (x*s)))
    have hz : Tendsto (fun n : ℕ => 1/((φ n:ℝ)+1)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
    have hnonneg : (0:ℝ)≤ |∑ s∈W.generators, (u x-u (x*s))| := abs_nonneg _
    have hle : |∑ s∈W.generators, (u x-u (x*s))|≤0 :=
      le_of_tendsto_of_tendsto hl.abs hz (Filter.Eventually.of_forall (fun n => hvres (φ n) x))
    exact abs_eq_zero.mp (le_antisymm hle hnonneg)
  refine ⟨u,hharm,hu1,hbound,hedge,?_⟩
  by_contra! hn
  have hz : (∑ s∈W.generators, (u s)^2)=0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rw [hn s hs]
    norm_num
  rw [hz] at hgrad
  have hc : (0:ℝ)<W.generators.card := by exact_mod_cast W.generators_card_pos
  have hp := sq_pos_of_pos (inv_pos.mpr hc)
  linarith

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
