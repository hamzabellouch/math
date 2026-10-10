import Mathlib
import OAI.Analysis.HardSphere.Comparison.PermutationPullbackComp

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere

attribute [local instance] scalarL2_addCommMonoid scalarL2_module scalarL2_completeSpace

def optionJetEquiv (N : ℕ) (L : Length) :
    (Option (Direction N) → ScalarL2 N L) ≃L[ℂ] Jet N L where
  toLinearEquiv := LinearEquiv.piOptionEquivProd ℂ
  continuous_toFun := (continuous_apply none).prodMk
    (continuous_pi fun i ↦ continuous_apply (some i))
  continuous_invFun := continuous_pi fun i ↦ by
    cases i with
    | none => exact continuous_fst
    | some p => exact (continuous_apply p).comp continuous_snd

def hilbertJetEquiv (N : ℕ) (L : Length) : HilbertJet N L ≃L[ℂ] Jet N L :=
  (PiLp.continuousLinearEquiv _ ℂ _).trans (optionJetEquiv N L)

@[simp] lemma hilbertJetEquiv_fst {N : ℕ} {L : Length} (u : HilbertJet N L) :
    (hilbertJetEquiv N L u).1 = u.ofLp none := rfl
@[simp] lemma hilbertJetEquiv_snd {N : ℕ} {L : Length} (u : HilbertJet N L) (p : Direction N) :
    (hilbertJetEquiv N L u).2 p = u.ofLp (some p) := rfl

lemma hilbertJet_inner {N : ℕ} {L : Length} (u v : HilbertJet N L) :
    inner ℂ u v = inner ℂ (hilbertJetEquiv N L u).1 (hilbertJetEquiv N L v).1 +
      ∑ p : Direction N, inner ℂ ((hilbertJetEquiv N L u).2 p) ((hilbertJetEquiv N L v).2 p) := by
  rw [PiLp.inner_apply,Fintype.sum_option]
  rfl

lemma hilbertJet_norm_sq {N : ℕ} {L : Length} (u : HilbertJet N L) :
    ‖u‖^2 = ‖(hilbertJetEquiv N L u).1‖^2 + energy (hilbertJetEquiv N L u) := by
  rw [PiLp.norm_sq_eq_of_L2,Fintype.sum_option]
  rfl

def hilbertDomain (N : ℕ) (L : Length) (a : ℝ) : Submodule ℂ (HilbertJet N L) :=
  (dirichletSubmodule N L a).comap (hilbertJetEquiv N L).toLinearMap

instance hilbertDomain_closed (N : ℕ) (L : Length) (a : ℝ) :
    IsClosed (hilbertDomain N L a : Set (HilbertJet N L)) :=
  (Submodule.isClosed_topologicalClosure _).preimage (hilbertJetEquiv N L).continuous
instance hilbertDomain_complete (N : ℕ) (L : Length) (a : ℝ) :
    CompleteSpace (hilbertDomain N L a) := IsClosed.completeSpace_coe

def scalarEmbedding (N : ℕ) (L : Length) (a : ℝ) :
    (hilbertDomain N L a) →L[ℂ] ScalarL2 N L :=
  (PiLp.proj _ _ none).comp (hilbertDomain N L a).subtypeL

lemma scalarEmbedding_norm_le (N : ℕ) (L : Length) (a : ℝ) : ‖scalarEmbedding N L a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa [scalarEmbedding] using PiLp.norm_apply_le (u : HilbertJet N L) none

def formResolvent (N : ℕ) (L : Length) (a : ℝ) : ScalarL2 N L →L[ℂ] ScalarL2 N L :=
  (scalarEmbedding N L a).comp (scalarEmbedding N L a).adjoint

lemma formResolvent_isPositive (N : ℕ) (L : Length) (a : ℝ) :
    (formResolvent N L a).IsPositive := by
  simpa [formResolvent] using
    ContinuousLinearMap.isPositive_adjoint_comp_self (scalarEmbedding N L a).adjoint

lemma formResolvent_norm_le_one (N : ℕ) (L : Length) (a : ℝ) :
    ‖formResolvent N L a‖ ≤ 1 := by
  have ha : ‖(scalarEmbedding N L a).adjoint‖ = ‖scalarEmbedding N L a‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  have hadj : ‖(scalarEmbedding N L a).adjoint‖ ≤ 1 := by
    rw [ha]
    exact scalarEmbedding_norm_le N L a
  calc
    _ ≤ ‖scalarEmbedding N L a‖ * ‖(scalarEmbedding N L a).adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*1 := mul_le_mul (scalarEmbedding_norm_le N L a)
      hadj (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma resolvent_weak_equation {N : ℕ} {L : Length} {a : ℝ} (f : ScalarL2 N L)
    (v : hilbertDomain N L a) :
    let u : Jet N L := hilbertJetEquiv N L ((scalarEmbedding N L a).adjoint f : HilbertJet N L)
    inner ℂ u.1 (hilbertJetEquiv N L (v : HilbertJet N L)).1 +
      ∑ p : Direction N, inner ℂ (u.2 p) ((hilbertJetEquiv N L (v : HilbertJet N L)).2 p) =
      inner ℂ f (scalarEmbedding N L a v) := by
  exact (hilbertJet_inner _ _).symm.trans
    (ContinuousLinearMap.adjoint_inner_left (scalarEmbedding N L a) v f)

lemma IsGroundVector.resolvent_eigenvector {N : ℕ} {L : Length} {a : ℝ}
    {u : Jet N L} (hu : IsGroundVector N L a u) :
    formResolvent N L a u.1 = ((1+(energy u:ℂ))⁻¹) • u.1 := by
  let ug : hilbertDomain N L a := ⟨(hilbertJetEquiv N L).symm u, by
    change hilbertJetEquiv N L ((hilbertJetEquiv N L).symm u) ∈ dirichletSubmodule N L a
    simpa using hu.1⟩
  have hE : 0 ≤ energy u := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hne : 1+(energy u:ℂ) ≠ 0 := by
    have hreal : (1:ℝ)+energy u ≠ 0 := ne_of_gt (by linarith)
    exact_mod_cast hreal
  have heq : (scalarEmbedding N L a).adjoint u.1 = ((1+(energy u:ℂ))⁻¹) • ug := by
    apply ext_inner_right ℂ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left]
    rw [inner_smul_left ug v ((1+(energy u:ℂ))⁻¹)]
    have hv : hilbertJetEquiv N L (v : HilbertJet N L) ∈ dirichletDomain N L a := v.property
    have hg : inner ℂ ug v = (1+(energy u:ℂ))*inner ℂ u.1 (scalarEmbedding N L a v) := by
      change inner ℂ (ug : HilbertJet N L) (v : HilbertJet N L) = _
      rw [hilbertJet_inner]
      have hgu : hilbertJetEquiv N L (ug : HilbertJet N L) = u := by simp [ug]
      rw [hgu,hu.full_first_variation _ hv]
      change inner ℂ u.1 (scalarEmbedding N L a v) + (energy u:ℂ)*inner ℂ u.1 (scalarEmbedding N L a v) = _
      ring
    rw [hg]
    simp only [map_inv₀,map_add,map_one,Complex.conj_ofReal]
    rw [← mul_assoc,inv_mul_cancel₀ hne,one_mul]
  change scalarEmbedding N L a ((scalarEmbedding N L a).adjoint u.1) = _
  rw [heq,map_smul]
  congr 1

lemma strong_projection_limit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (K : Submodule ℂ E) (Kseq : ℕ → Submodule ℂ E)
    [K.HasOrthogonalProjection] [∀ n, (Kseq n).HasOrthogonalProjection]
    (hmono : Monotone Kseq) (hle : ∀ n, Kseq n ≤ K)
    (hdense : closure (⋃ n, (Kseq n : Set E)) = K) (x : E) :
    Tendsto (fun n ↦ (Kseq n).starProjection x) atTop (𝓝 (K.starProjection x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hy : K.starProjection x ∈ closure (⋃ n, (Kseq n : Set E)) := by
    rw [hdense]
    exact K.starProjection_apply_mem x
  obtain ⟨v, hv, hdist⟩ := Metric.mem_closure_iff.mp hy (ε/2) (half_pos hε)
  obtain ⟨m, hm⟩ := mem_iUnion.mp hv
  refine ⟨m, fun n hn ↦ ?_⟩
  have hvn : (Kseq n).starProjection v = v :=
    (Kseq n).starProjection_eq_self_iff.mpr (hmono hn hm)
  have hcomp : (Kseq n).starProjection (K.starProjection x) = (Kseq n).starProjection x :=
    DFunLike.congr_fun (Submodule.starProjection_comp_starProjection_of_le (hle n)) x
  have hnorm := (Kseq n).norm_starProjection_apply_le (K.starProjection x - v)
  rw [map_sub, hcomp, hvn] at hnorm
  calc
    dist ((Kseq n).starProjection x) (K.starProjection x) =
        ‖(Kseq n).starProjection x - K.starProjection x‖ := dist_eq_norm _ _
    _ ≤ ‖(Kseq n).starProjection x - v‖ + ‖v - K.starProjection x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖K.starProjection x - v‖ + ‖v - K.starProjection x‖ := add_le_add hnorm le_rfl
    _ < ε := by rw [norm_sub_rev v]; rw [dist_eq_norm] at hdist; linarith

lemma scalarAdjoint_eq_projection {N : ℕ} {L : Length} {a : ℝ} (f : ScalarL2 N L) :
    ((scalarEmbedding N L a).adjoint f : HilbertJet N L) =
      (hilbertDomain N L a).starProjection (PiLp.single 2 none f) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ((scalarEmbedding N L a).adjoint f).property
  · intro v hv
    rw [inner_sub_left]
    have hleft : inner ℂ (PiLp.single 2 none f : HilbertJet N L) v = inner ℂ f (v.ofLp none) := by
      rw [PiLp.inner_apply, Fintype.sum_option]
      simp
    rw [hleft]
    have hh := ContinuousLinearMap.adjoint_inner_left (scalarEmbedding N L a) ⟨v,hv⟩ f
    change inner ℂ ((scalarEmbedding N L a).adjoint f : HilbertJet N L) v = _ at hh
    rw [hh]
    change inner ℂ f (v.ofLp none) - inner ℂ f (v.ofLp none) = 0
    exact sub_self _

lemma formResolvent_eq_projection {N : ℕ} {L : Length} {a : ℝ} (f : ScalarL2 N L) :
    formResolvent N L a f =
      ((hilbertDomain N L a).starProjection (PiLp.single 2 none f)).ofLp none := by
  change (((scalarEmbedding N L a).adjoint f : HilbertJet N L)).ofLp none = _
  rw [scalarAdjoint_eq_projection]

lemma continuous_torusDistance (L : Length) : Continuous (fun p : Torus L × Torus L ↦ torusDistance L p.1 p.2) := by
  unfold torusDistance
  fun_prop

lemma isOpen_allowed (N : ℕ) (L : Length) (a : ℝ) : IsOpen (allowed N L a) := by
  let P := {p : Fin N × Fin N // p.1 < p.2}
  have heq : allowed N L a = ⋂ p : P, {X : Configuration N L | a < torusDistance L (X p.1.1) (X p.1.2)} := by
    ext X
    simp only [allowed, mem_ofPred_eq, mem_iInter]
    exact ⟨fun h p ↦ h _ _ p.2, fun h i j hij ↦ h ⟨(i,j),hij⟩⟩
  rw [heq]
  apply isOpen_iInter_of_finite
  intro p
  have hc : Continuous (fun X : Configuration N L ↦ torusDistance L (X p.1.1) (X p.1.2)) := by
    unfold torusDistance
    fun_prop
  exact isOpen_lt continuous_const hc

lemma allowed_antitone (N : ℕ) (L : Length) : Antitone (allowed N L) := by
  intro a b hab X hX i j hij
  exact lt_of_le_of_lt hab (hX i j hij)

def innerRadius (a : ℝ) (n : ℕ) : ℝ := a + 1 / ((n:ℝ)+1)

lemma innerRadius_gt (a : ℝ) (n : ℕ) : a < innerRadius a n := by
  unfold innerRadius
  have : 0 < 1 / ((n:ℝ)+1) := by positivity
  linarith

lemma innerRadius_antitone (a : ℝ) : Antitone (innerRadius a) := by
  intro m n hmn
  unfold innerRadius
  apply add_le_add le_rfl
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hmn 1

lemma innerRadius_tendsto (a : ℝ) : Tendsto (innerRadius a) atTop (𝓝 a) := by
  change Tendsto (fun n : ℕ ↦ a + 1 / ((n:ℝ)+1)) atTop (𝓝 a)
  simpa only [add_zero] using (tendsto_const_nhds (x := a)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma iUnion_allowed_innerRadius (N : ℕ) (L : Length) (a : ℝ) :
    (⋃ n, allowed N L (innerRadius a n)) = allowed N L a := by
  apply Subset.antisymm
  · exact iUnion_subset fun n ↦ allowed_antitone N L (innerRadius_gt a n).le
  · intro X hX
    have h : ∀ i j : Fin N, ∀ᶠ n in atTop, i < j → innerRadius a n < torusDistance L (X i) (X j) := by
      intro i j
      by_cases hij : i < j
      · exact ((innerRadius_tendsto a).eventually (gt_mem_nhds (hX i j hij))).mono fun _ hn _ ↦ hn
      · exact Filter.Eventually.of_forall fun _ h ↦ (hij h).elim
    have hh : ∀ᶠ n in atTop, ∀ i j : Fin N, i < j → innerRadius a n < torusDistance L (X i) (X j) := by
      exact Filter.eventually_all.mpr fun i ↦ Filter.eventually_all.mpr (h i)
    obtain ⟨n, hn⟩ := hh.exists
    exact mem_iUnion.mpr ⟨n,hn⟩

lemma SmoothTest.exists_innerRadius {N : ℕ} {L : Length} {a : ℝ} (f : SmoothTest N L a) :
    ∃ n, tsupport f.toFun ⊆ allowed N L (innerRadius a n) := by
  apply f.compact.isCompact.elim_directed_cover (fun n ↦ allowed N L (innerRadius a n))
  · exact fun n ↦ isOpen_allowed _ _ _
  · rw [iUnion_allowed_innerRadius]
    exact f.support_allowed
  · intro m n
    exact ⟨max m n, allowed_antitone N L (innerRadius_antitone a (le_max_left _ _)),
      allowed_antitone N L (innerRadius_antitone a (le_max_right _ _))⟩

lemma dirichletDomain_antitone (N : ℕ) (L : Length) : Antitone (dirichletDomain N L) := by
  intro a b hab
  apply closure_mono
  rintro _ ⟨f,rfl⟩
  let g : SmoothTest N L a := {f with support_allowed := fun X hX ↦ allowed_antitone N L hab (f.support_allowed hX)}
  exact ⟨g,rfl⟩

lemma hilbertDomain_antitone (N : ℕ) (L : Length) : Antitone (hilbertDomain N L) := by
  intro a b hab u hu
  exact dirichletDomain_antitone N L hab hu

lemma hilbertDomain_exhaustion (N : ℕ) (L : Length) (a : ℝ) :
    closure (⋃ n, (hilbertDomain N L (innerRadius a n) : Set (HilbertJet N L))) = hilbertDomain N L a := by
  apply Subset.antisymm
  · apply closure_minimal
    · exact iUnion_subset fun n ↦ hilbertDomain_antitone N L (innerRadius_gt a n).le
    · exact hilbertDomain_closed N L a
  · intro u hu
    let S := closure (⋃ n, (hilbertDomain N L (innerRadius a n) : Set (HilbertJet N L)))
    have hclosed : IsClosed ((hilbertJetEquiv N L).symm ⁻¹' S) :=
      isClosed_closure.preimage (hilbertJetEquiv N L).symm.continuous
    have hsub : dirichletDomain N L a ⊆ (hilbertJetEquiv N L).symm ⁻¹' S := by
      apply closure_minimal _ hclosed
      rintro _ ⟨f,rfl⟩
      obtain ⟨n, hn⟩ := f.exists_innerRadius
      let g : SmoothTest N L (innerRadius a n) := {f with support_allowed := hn}
      apply subset_closure
      apply mem_iUnion.mpr
      refine ⟨n,?_⟩
      change hilbertJetEquiv N L ((hilbertJetEquiv N L).symm f.jet) ∈ dirichletDomain N L (innerRadius a n)
      simp only [ContinuousLinearEquiv.apply_symm_apply]
      exact subset_closure ⟨g,rfl⟩
    have hx := hsub hu
    change (hilbertJetEquiv N L).symm (hilbertJetEquiv N L u) ∈ S at hx
    rwa [ContinuousLinearEquiv.symm_apply_apply] at hx

lemma formResolvent_innerRadius_tendsto (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    Tendsto (fun n ↦ formResolvent N L (innerRadius a n) f) atTop (𝓝 (formResolvent N L a f)) := by
  simp only [formResolvent_eq_projection]
  apply (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Option (Direction N) ↦ ScalarL2 N L) none).continuous.tendsto _ |>.comp
  apply strong_projection_limit
  · exact fun m n hmn ↦ hilbertDomain_antitone N L (innerRadius_antitone a hmn)
  · exact fun n ↦ hilbertDomain_antitone N L (innerRadius_gt a n).le
  · exact hilbertDomain_exhaustion N L a

end HardSphere

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

end
end
end
end
end

end OAI
