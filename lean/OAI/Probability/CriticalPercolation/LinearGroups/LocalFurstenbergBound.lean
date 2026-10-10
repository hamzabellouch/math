import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.LocalPositiveSubspaceOrbit
import OAI.Probability.CriticalPercolation.LinearGroups.LocalFurstenbergConcentration

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory NormedSpace Module Metric TopologicalSpace
open scoped Classical Topology ENNReal

namespace CriticalPercolation.LocalProjective
variable {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]

lemma equiv_operator_ne_zero [Nontrivial V] (a : V ≃L[K] V) :
    a.toContinuousLinearMap≠0 := by
  intro he
  obtain ⟨x,hx⟩ := exists_ne (0:V)
  apply hx
  apply a.injective
  have hh := congrArg (fun f : V →L[K] V => f x) he
  exact hh.trans a.map_zero.symm

variable (t : K) (ht : 1<‖t‖)
include ht
lemma exists_shell_scalar {U : Type*} [NormedAddCommGroup U] [NormedSpace K U]
    (x : U) (hx : x≠0) : ∃ c : K, c≠0 ∧ 1/‖t‖≤‖c • x‖ ∧ ‖c • x‖≤1 := by
  obtain ⟨c,hc,hlt,hle,_⟩ := rescale_to_shell ht zero_lt_one hx
  exact ⟨c,hc,hle,hlt.le⟩

noncomputable def shellScalar {U : Type*} [NormedAddCommGroup U] [NormedSpace K U]
    (x : U) (hx : x≠0) : K := Classical.choose (exists_shell_scalar t ht x hx)
lemma shellScalar_spec {U : Type*} [NormedAddCommGroup U] [NormedSpace K U]
    (x : U) (hx : x≠0) : shellScalar t ht x hx≠0 ∧
      1/‖t‖≤‖shellScalar t ht x hx • x‖ ∧ ‖shellScalar t ht x hx • x‖≤1 :=
  Classical.choose_spec (exists_shell_scalar t ht x hx)

variable [Nontrivial V]
def normalized (a : V ≃L[K] V) : V →L[K] V :=
  shellScalar t ht a.toContinuousLinearMap (equiv_operator_ne_zero a) • a.toContinuousLinearMap

def shell (U : Type*) [NormedAddCommGroup U] : Set U := {x | 1/‖t‖≤‖x‖ ∧ ‖x‖≤1}

omit ht in
lemma compact_shell {U : Type*} [NormedAddCommGroup U] [ProperSpace U] : IsCompact (shell t U) := by
  have he : shell t U=closedBall (0:U) 1 ∩ {x | 1/‖t‖≤‖x‖} := by
    ext x
    simp only [shell,mem_ofPred_eq,mem_inter_iff,mem_closedBall,dist_zero_right,and_comm]
  rw [he]
  exact (isCompact_closedBall (0:U) 1).inter_right (isClosed_le continuous_const continuous_norm)

lemma normalized_mem (a : V ≃L[K] V) : normalized t ht a∈shell t (V →L[K] V) :=
  (shellScalar_spec t ht _ (equiv_operator_ne_zero a)).2

variable [ProperSpace K] [FiniteDimensional K V]
variable {G : Type*} [Group G]
lemma normalizedClosure_compact (ρ : G →* (V ≃L[K] V)) :
    IsCompact (closure (Set.range (fun g => normalized t ht (ρ g)))) := by
  let : ProperSpace (V →L[K] V) := FiniteDimensional.proper K _
  apply (compact_shell t).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (compact_shell t).isClosed
  rintro A ⟨g,rfl⟩
  exact normalized_mem t ht _

lemma normalizedClosure_injective (ρ : G →* (V ≃L[K] V))
    (μ : Measure (Space K V)) [IsProbabilityMeasure μ]
    (hn : ∀ W : Submodule K V, W≠⊤ → μ (subspace W)=0)
    (hμ : ∀ g, Measure.map (action (ρ g)) μ=μ)
    (A : V →L[K] V) (hA : A∈closure (Set.range (fun g => normalized t ht (ρ g)))) :
    Injective A := by
  let : ProperSpace (V →L[K] V) := FiniteDimensional.proper K _
  obtain ⟨B,hB,hlim⟩ := mem_closure_iff_seq_limit.mp hA
  choose g hg using hB
  have hnorm : A∈shell t (V →L[K] V) := by
    apply closure_minimal _ (compact_shell t).isClosed hA
    rintro B ⟨g,rfl⟩
    exact normalized_mem t ht _
  have hne : A≠0 := by
    intro he
    have hp : 0<1/‖t‖ := div_pos zero_lt_one (lt_trans zero_lt_one ht)
    have hh := hnorm.1
    rw [he,norm_zero] at hh
    exact hp.not_ge hh
  apply injective_of_nonzero_projective_limit μ hn (fun n => ρ (g n))
    (fun n => shellScalar t ht _ (equiv_operator_ne_zero (ρ (g n))))
    (fun n => (shellScalar_spec t ht _ (equiv_operator_ne_zero _)).1) A hne _ (fun n => hμ _)
  change Tendsto (fun n => normalized t ht (ρ (g n))) atTop (𝓝 A)
  convert hlim using 1
  funext n
  exact hg n

lemma projective_lower_bound_of_null_subspaces
    (ρ : G →* (V ≃L[K] V)) (μ : Measure (Space K V)) [IsProbabilityMeasure μ]
    (hn : ∀ W : Submodule K V, W≠⊤ → μ (subspace W)=0)
    (hμ : ∀ g, Measure.map (action (ρ g)) μ=μ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ g : G, ∀ x : V,
      δ*‖(ρ g).toContinuousLinearMap‖*‖x‖≤‖ρ g x‖ := by
  let : ProperSpace V := FiniteDimensional.proper K V
  let : ProperSpace (V →L[K] V) := FiniteDimensional.proper K _
  let C := closure (Set.range (fun g => normalized t ht (ρ g)))
  have hC : IsCompact C := normalizedClosure_compact t ht ρ
  obtain ⟨v,hv⟩ := exists_ne (0:V)
  have hne : (C×ˢshell t V).Nonempty :=
    ⟨(normalized t ht (ρ 1),shellScalar t ht v hv • v),subset_closure ⟨1,rfl⟩,
      (shellScalar_spec t ht v hv).2⟩
  have hcont : Continuous (fun z : (V →L[K] V)×V => ‖z.1 z.2‖) :=
    (continuous_fst.clm_apply continuous_snd).norm
  obtain ⟨z,hz,hmin⟩ := (hC.prod (compact_shell t)).exists_isMinOn hne hcont.continuousOn
  have hzinj : Injective z.1 := normalizedClosure_injective t ht ρ μ hn hμ z.1 hz.1
  have hz2 : z.2≠0 := by
    intro he
    have hh := hz.2.1
    rw [he,norm_zero] at hh
    exact (div_pos zero_lt_one (lt_trans zero_lt_one ht)).not_ge hh
  have hδ : 0<‖z.1 z.2‖ := norm_pos_iff.mpr
    (fun he => hz2 (hzinj (he.trans z.1.map_zero.symm)))
  refine ⟨‖z.1 z.2‖,hδ,?_⟩
  intro g x
  by_cases hx : x=0
  · simp [hx]
  let b := shellScalar t ht _ (equiv_operator_ne_zero (ρ g))
  let c := shellScalar t ht x hx
  have hb := (shellScalar_spec t ht _ (equiv_operator_ne_zero (ρ g))).2.2
  have hc := (shellScalar_spec t ht x hx).2.2
  have hsmall := hmin (a := (normalized t ht (ρ g), c • x))
    ⟨subset_closure ⟨g,rfl⟩,(shellScalar_spec t ht x hx).2⟩
  change ‖z.1 z.2‖≤‖(b • (ρ g).toContinuousLinearMap) (c • x)‖ at hsmall
  simp only [smul_apply,map_smul,norm_smul] at hsmall
  change ‖b • (ρ g).toContinuousLinearMap‖≤1 at hb
  change ‖c • x‖≤1 at hc
  rw [norm_smul] at hb hc
  have hp := mul_le_mul hb hc (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
  have hh := mul_le_mul_of_nonneg_right hsmall (mul_nonneg (norm_nonneg (ρ g).toContinuousLinearMap) (norm_nonneg x))
  calc
    _ = ‖z.1 z.2‖ * (‖(ρ g).toContinuousLinearMap‖*‖x‖) := by ring
    _ ≤ _ := hh
    _ = (‖b‖*‖(ρ g).toContinuousLinearMap‖*(‖c‖*‖x‖))*‖ρ g x‖ := by
      change ‖c‖ * (‖b‖ * ‖ρ g x‖) * (‖(ρ g).toContinuousLinearMap‖*‖x‖) = _
      ring
    _ ≤ 1*‖ρ g x‖ := mul_le_mul_of_nonneg_right (by simpa only [one_mul] using hp) (norm_nonneg _)
    _ = _ := one_mul _

omit ht in
lemma sparse_local_furstenberg_alternative [DecidableEq G]
    (ρ : G →* (V ≃L[K] V)) (S : Finset G)
    (h1 : (1:G)∈S) (hgen : Subgroup.closure (S:Set G)=⊤)
    (d : ℕ) (hg : SparseGrowth.HasDegree S d) :
    (∃ W : Submodule K V, W≠⊥ ∧ W≠⊤ ∧
      (Set.range (fun g => W.map (ρ g).toLinearEquiv.toLinearMap)).Finite) ∨
    (∃ δ : ℝ, 0<δ ∧ ∀ g : G, ∀ x : V,
      δ*‖(ρ g).toContinuousLinearMap‖*‖x‖≤‖ρ g x‖) := by
  obtain ⟨t,ht⟩ := NormedField.exists_one_lt_norm K
  obtain ⟨μ,hprob,hμ⟩ := exists_invariant_measure ρ S h1 hgen d hg
  let : IsProbabilityMeasure μ := hprob
  by_cases hn : ∀ W : Submodule K V, W≠⊤ → μ (subspace W)=0
  · exact Or.inr (projective_lower_bound_of_null_subspaces t ht ρ μ hn hμ)
  · push Not at hn
    exact Or.inl (exists_finite_positive_subspace_orbit ρ μ hμ hn)

end CriticalPercolation.LocalProjective
end
end

end OAI
