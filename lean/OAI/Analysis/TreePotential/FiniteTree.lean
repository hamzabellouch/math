import OAI.Analysis.TreePotential.LinearCost

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section FiniteHeightTrees

/-- The countably branching, finite-height, root-inclusive tree. -/
abbrev Tree (n : ℕ) := {s : List ℕ // s.length ≤ n}
abbrev TreeHilbert (n : ℕ) := lp (fun _ : Tree n => ℝ) 2

def root (n : ℕ) : Tree n := ⟨[], Nat.zero_le n⟩
instance (n : ℕ) : Inhabited (Tree n) := ⟨root n⟩

def prefixNode {n : ℕ} (s : Tree n) (k : Fin (s.val.length + 1)) : Tree n :=
  ⟨s.val.take k, (List.length_take.le.trans (min_le_right _ _)).trans s.property⟩

lemma prefixNode_length {n : ℕ} (s : Tree n) (k : Fin (s.val.length + 1)) :
    (prefixNode s k).val.length = k.val := by
  simp only [prefixNode, List.length_take]
  exact min_eq_left (Nat.le_of_lt_succ k.isLt)

lemma prefixNode_injective {n : ℕ} (s : Tree n) : Function.Injective (prefixNode s) := by
  intro i j hij
  apply Fin.ext
  have := congrArg (fun t : Tree n => t.val.length) hij
  simpa only [prefixNode_length] using this

def pathNodes {n : ℕ} (s : Tree n) : Finset (Tree n) :=
  Finset.univ.image (prefixNode s)

lemma pathNodes_card {n : ℕ} (s : Tree n) : (pathNodes s).card = s.val.length + 1 := by
  rw [pathNodes, Finset.card_image_of_injective _ (prefixNode_injective s)]
  simp

lemma mem_pathNodes_iff {n : ℕ} (s t : Tree n) : t ∈ pathNodes s ↔ t.val <+: s.val := by
  constructor
  · intro ht
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
    exact List.take_prefix k s.val
  · intro ht
    apply Finset.mem_image.mpr
    refine ⟨⟨t.val.length, Nat.lt_succ_of_le ht.length_le⟩, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact (List.prefix_iff_eq_take.mp ht).symm

@[simp] lemma self_mem_pathNodes {n : ℕ} (s : Tree n) : s ∈ pathNodes s :=
  (mem_pathNodes_iff s s).mpr ⟨[], by simp⟩

@[simp] lemma root_mem_pathNodes {n : ℕ} (s : Tree n) : root n ∈ pathNodes s := by
  rw [mem_pathNodes_iff]
  exact List.nil_prefix

/-- The root occurs in every path vector, including the root's own path. -/
def rootPath {n : ℕ} (s : Tree n) : TreeHilbert n :=
  ∑ r ∈ pathNodes s, lp.single 2 r (1 : ℝ)

def pathPotential {n : ℕ} (f : TreeHilbert n) (s : Tree n) : ℝ :=
  ∑ r ∈ pathNodes s, f r

lemma rootPath_apply {n : ℕ} (s t : Tree n) :
    rootPath s t = if t ∈ pathNodes s then 1 else 0 := by
  simp only [rootPath, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]

lemma rootPath_norm_sq {n : ℕ} (s : Tree n) : ‖rootPath s‖ ^ 2 = (s.val.length + 1 : ℕ) := by
  simpa [rootPath, pathNodes_card, Real.rpow_two] using
    (lp.norm_sum_single (p := 2) (by norm_num) (fun _ : Tree n => (1 : ℝ)) (pathNodes s))

lemma rootPath_norm_bound {n : ℕ} (s : Tree n) : ‖rootPath s‖ ≤ Real.sqrt (n + 1) := by
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  rw [rootPath_norm_sq]
  exact_mod_cast Nat.add_le_add_right s.property 1

lemma inner_rootPath {n : ℕ} (f : TreeHilbert n) (s : Tree n) :
    inner ℝ f (rootPath s) = pathPotential f s := by
  simp [rootPath, pathPotential, inner_sum, lp.inner_single_right, RCLike.inner_apply]

/-- The map B_n is exactly the absolutely convergent signed sum of root paths. -/
def pathSynthesis (n : ℕ) : L1Mass (Tree n) →L[ℝ] TreeHilbert n :=
  atomSynthesis rootPath rootPath_norm_bound

@[simp] lemma pathSynthesis_apply (n : ℕ) (μ : L1Mass (Tree n)) :
    pathSynthesis n μ = ∑' s, μ s • rootPath s := rfl

lemma pathSynthesis_bound (n : ℕ) (μ : L1Mass (Tree n)) :
    ‖pathSynthesis n μ‖ ≤ Real.sqrt (n + 1) * ‖μ‖ :=
  atom_tsum_norm_le rootPath rootPath_norm_bound μ

/-- L_n, not Q_n: the two costs are added, not squared. -/
def linearBlockCost (n : ℕ) (x : TreeHilbert n) : ℝ := linearCost (pathSynthesis n) x

def linearPolar (n : ℕ) (f : TreeHilbert n) : ℝ :=
  max ‖f‖ (⨆ s : Tree n, |pathPotential f s|)

lemma pathPotential_bound {n : ℕ} (f : TreeHilbert n) (s : Tree n) :
    |pathPotential f s| ≤ ‖f‖ * Real.sqrt (n + 1) := by
  rw [← inner_rootPath]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (rootPath_norm_bound s) (norm_nonneg f))

lemma pathPotential_bddAbove {n : ℕ} (f : TreeHilbert n) :
    BddAbove (range fun s => |pathPotential f s|) :=
  ⟨‖f‖ * Real.sqrt (n + 1), by rintro _ ⟨s, rfl⟩; exact pathPotential_bound f s⟩

lemma linearPolar_le_one_iff {n : ℕ} (f : TreeHilbert n) :
    linearPolar n f ≤ 1 ↔ ‖f‖ ≤ 1 ∧ ∀ s, |pathPotential f s| ≤ 1 := by
  rw [linearPolar, max_le_iff]
  exact and_congr_right fun _ => ciSup_le_iff (pathPotential_bddAbove f)

/-- Exact linear-cost duality with the root-potential norming set. -/
theorem linearBlockCost_duality (n : ℕ) (x : TreeHilbert n) :
    linearBlockCost n x = sSup {r : ℝ | ∃ f : TreeHilbert n,
      linearPolar n f ≤ 1 ∧ r = inner ℝ f x} := by
  rw [linearBlockCost, pathSynthesis, linearCost_atom_duality]
  congr 1
  ext r
  simp only [mem_ofPred_eq, linearPolar_le_one_iff, inner_rootPath]
  aesop

/-- Both exact linear-cost norm comparison constants. -/
theorem linearBlockCost_comparison (n : ℕ) (x : TreeHilbert n) :
    ‖x‖ / Real.sqrt (n + 1) ≤ linearBlockCost n x ∧ linearBlockCost n x ≤ ‖x‖ := by
  refine ⟨?_, linearCost_le_norm _ _⟩
  have hK : 1 ≤ Real.sqrt (n + 1 : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    norm_num
  rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hK), mul_comm]
  exact norm_le_mul_linearCost (pathSynthesis n) hK (pathSynthesis_bound n) x

lemma singleton_pathPotential {n : ℕ} (s t : Tree n) :
    pathPotential (lp.single 2 s (1 : ℝ)) t = if s ∈ pathNodes t then 1 else 0 := by
  rw [← inner_rootPath, lp.inner_single_left, RCLike.inner_apply, rootPath_apply]
  simp

lemma singleton_polar_le_one {n : ℕ} (s : Tree n) :
    linearPolar n (lp.single 2 s (1 : ℝ)) ≤ 1 := by
  rw [linearPolar_le_one_iff]
  constructor
  · simp only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one, le_refl]
  · intro t
    rw [singleton_pathPotential]
    split_ifs <;> norm_num

lemma linearBlockCost_eval_le {n : ℕ} {f : TreeHilbert n}
    (hf : linearPolar n f ≤ 1) (x : TreeHilbert n) :
    inner ℝ f x ≤ linearBlockCost n x := by
  obtain ⟨hf, hp⟩ := linearPolar_le_one_iff f |>.mp hf
  apply inner_le_linearCost (pathSynthesis n) hf
  apply atom_pairing_bound
  intro s
  simpa only [inner_rootPath] using hp s

lemma linearBlockCost_abs_eval_le {n : ℕ} {f : TreeHilbert n}
    (hf : linearPolar n f ≤ 1) (x : TreeHilbert n) :
    |inner ℝ f x| ≤ linearBlockCost n x := by
  rw [abs_le]
  constructor
  · have hneg : linearPolar n (-f) ≤ 1 := by
      rw [linearPolar_le_one_iff] at hf ⊢
      constructor
      · simpa using hf.1
      · intro s
        simpa only [← inner_rootPath, inner_neg_left, abs_neg] using hf.2 s
    have h := linearBlockCost_eval_le hneg x
    rw [inner_neg_left] at h
    linarith
  · exact linearBlockCost_eval_le hf x

/-- Every coordinate of a finite-height block is norm continuous, with bound 1. -/
theorem coordinate_le_linearBlockCost {n : ℕ} (x : TreeHilbert n) (s : Tree n) :
    |x s| ≤ linearBlockCost n x := by
  have h := linearBlockCost_abs_eval_le (singleton_polar_le_one s) x
  simpa [lp.inner_single_left, RCLike.inner_apply] using h

@[simp] theorem linearBlockCost_singleton {n : ℕ} (s : Tree n) :
    linearBlockCost n (lp.single 2 s (1 : ℝ)) = 1 := by
  apply le_antisymm
  · exact (linearCost_le_norm _ _).trans_eq (by simp [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)])
  · simpa using coordinate_le_linearBlockCost (lp.single 2 s (1 : ℝ)) s

@[simp] theorem linearBlockCost_rootPath {n : ℕ} (s : Tree n) :
    linearBlockCost n (rootPath s) = 1 := by
  apply le_antisymm
  · have h := linearCost_synthesis_le (pathSynthesis n) (lp.single 1 s (1 : ℝ))
    change linearCost (atomSynthesis rootPath rootPath_norm_bound)
      (atomSynthesis rootPath rootPath_norm_bound (lp.single 1 s (1 : ℝ))) ≤ _ at h
    rw [atomSynthesis_single, one_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)] at h
    simpa [linearBlockCost, pathSynthesis] using h
  · simpa [rootPath_apply] using coordinate_le_linearBlockCost (rootPath s) s

/-- A separate type is used for the infimal-cost norm. It is not silently
    identified with the original Hilbert norm. -/
def LinearBlock (n : ℕ) := TreeHilbert n
instance (n : ℕ) : AddCommGroup (LinearBlock n) := inferInstanceAs (AddCommGroup (TreeHilbert n))
instance (n : ℕ) : Module ℝ (LinearBlock n) := inferInstanceAs (Module ℝ (TreeHilbert n))
def linearBlockEquiv (n : ℕ) : LinearBlock n ≃ₗ[ℝ] TreeHilbert n :=
  { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

instance (n : ℕ) : Norm (LinearBlock n) := ⟨fun x => linearBlockCost n x⟩

theorem linearBlockCore (n : ℕ) : NormedSpace.Core ℝ (LinearBlock n) where
  norm_nonneg := linearCost_nonneg (pathSynthesis n)
  norm_smul c x := map_smul_eq_mul (linearCostSeminorm (pathSynthesis n)) c x
  norm_triangle := linearCost_add_le (pathSynthesis n)
  norm_eq_zero_iff x := by
    constructor
    · intro hx
      have h := (linearBlockCost_comparison n (linearBlockEquiv n x)).1
      change linearBlockCost n (linearBlockEquiv n x) = 0 at hx
      rw [hx] at h
      have hk : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
      have hxnorm : ‖linearBlockEquiv n x‖ ≤ 0 := by
        have := (div_le_iff₀ hk).mp h
        simpa only [zero_mul] using this
      apply (linearBlockEquiv n).injective
      rw [map_zero]
      exact norm_eq_zero.mp (le_antisymm hxnorm (norm_nonneg _))
    · rintro rfl
      exact linearCost_zero (pathSynthesis n)

instance (n : ℕ) : NormedAddCommGroup (LinearBlock n) := NormedAddCommGroup.ofCore (linearBlockCore n)
instance (n : ℕ) : NormedSpace ℝ (LinearBlock n) := NormedSpace.ofCore (linearBlockCore n)

@[simp] lemma norm_LinearBlock (n : ℕ) (x : LinearBlock n) : ‖x‖ = linearBlockCost n x := rfl

/-- Completeness is transported by equivalence of norms, with exactly the
    finite-height comparison constant sqrt(n+1). -/
def linearBlockHilbertEquiv (n : ℕ) : LinearBlock n ≃L[ℝ] TreeHilbert n :=
  (linearBlockEquiv n).toContinuousLinearEquivOfBounds (Real.sqrt (n + 1)) 1
    (fun x => by
      have hk : 0 < Real.sqrt (n + 1 : ℝ) := by positivity
      exact (mul_comm _ _).ge.trans' ((div_le_iff₀ hk).mp (linearBlockCost_comparison n x).1))
    (fun x => by
      change linearBlockCost n x ≤ 1 * ‖x‖
      simpa only [one_mul] using (linearBlockCost_comparison n x).2)

def linearBlockUniformEquiv (n : ℕ) : LinearBlock n ≃ᵤ TreeHilbert n :=
  { toEquiv := (linearBlockHilbertEquiv n).toLinearEquiv.toEquiv
    uniformContinuous_toFun := (linearBlockHilbertEquiv n).toContinuousLinearMap.uniformContinuous
    uniformContinuous_invFun := (linearBlockHilbertEquiv n).symm.toContinuousLinearMap.uniformContinuous }

instance (n : ℕ) : CompleteSpace (LinearBlock n) :=
  (linearBlockUniformEquiv n).completeSpace_iff.mpr inferInstance

lemma linearPolar_nonneg {n : ℕ} (f : TreeHilbert n) : 0 ≤ linearPolar n f :=
  (norm_nonneg f).trans (le_max_left _ _)

lemma norm_le_linearPolar {n : ℕ} (f : TreeHilbert n) : ‖f‖ ≤ linearPolar n f := le_max_left _ _

lemma path_le_linearPolar {n : ℕ} (f : TreeHilbert n) (s : Tree n) :
    |pathPotential f s| ≤ linearPolar n f :=
  (le_ciSup (pathPotential_bddAbove f) s).trans (le_max_right _ _)

lemma pathPotential_smul {n : ℕ} (a : ℝ) (f : TreeHilbert n) (s : Tree n) :
    pathPotential (a • f) s = a * pathPotential f s := by
  simp only [← inner_rootPath, real_inner_smul_left]

lemma linearBlockCost_abs_eval_scaled {n : ℕ} (f x : TreeHilbert n) :
    |inner ℝ f x| ≤ linearPolar n f * linearBlockCost n x := by
  by_cases hp : linearPolar n f = 0
  · have hf : f = 0 := norm_eq_zero.mp (le_antisymm (hp ▸ norm_le_linearPolar f) (norm_nonneg f))
    rw [hp, hf, inner_zero_left, abs_zero, zero_mul]
  · have hp0 : 0 < linearPolar n f := lt_of_le_of_ne (linearPolar_nonneg f) (Ne.symm hp)
    have htest : linearPolar n ((linearPolar n f)⁻¹ • f) ≤ 1 := by
      rw [linearPolar_le_one_iff]
      constructor
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp0)]
        calc
          (linearPolar n f)⁻¹ * ‖f‖ ≤ (linearPolar n f)⁻¹ * linearPolar n f :=
            mul_le_mul_of_nonneg_left (norm_le_linearPolar f) (inv_nonneg.mpr hp0.le)
          _ = 1 := inv_mul_cancel₀ hp
      · intro s
        rw [pathPotential_smul, abs_mul, abs_of_pos (inv_pos.mpr hp0)]
        calc
          (linearPolar n f)⁻¹ * |pathPotential f s| ≤ (linearPolar n f)⁻¹ * linearPolar n f :=
            mul_le_mul_of_nonneg_left (path_le_linearPolar f s) (inv_nonneg.mpr hp0.le)
          _ = 1 := inv_mul_cancel₀ hp
    have h := linearBlockCost_abs_eval_le htest x
    rw [real_inner_smul_left, abs_mul, abs_of_pos (inv_pos.mpr hp0), ← div_eq_inv_mul] at h
    exact (mul_comm _ _).ge.trans' ((div_le_iff₀ hp0).mp h)

/-- The functional with Hilbert coefficients f, acting on the L_n block. -/
def blockFunctional (n : ℕ) (f : TreeHilbert n) : LinearBlock n →L[ℝ] ℝ :=
  (innerSL ℝ f).comp (linearBlockHilbertEquiv n).toContinuousLinearMap

@[simp] lemma blockFunctional_apply (n : ℕ) (f : TreeHilbert n) (x : LinearBlock n) :
    blockFunctional n f x = inner ℝ f (linearBlockEquiv n x) := rfl

lemma block_inv_norm_le (n : ℕ) :
    ‖(linearBlockHilbertEquiv n).symm.toContinuousLinearMap‖ ≤ 1 := by
  refine ((linearBlockHilbertEquiv n).symm.toContinuousLinearMap).opNorm_le_bound (by norm_num) ?_
  intro x
  change linearBlockCost n x ≤ 1 * ‖x‖
  simpa only [one_mul] using (linearBlockCost_comparison n x).2

/-- The exact continuous-dual norm, not merely an equivalent norm. -/
theorem blockFunctional_norm (n : ℕ) (f : TreeHilbert n) :
    ‖blockFunctional n f‖ = linearPolar n f := by
  apply le_antisymm
  · refine (blockFunctional n f).opNorm_le_bound (linearPolar_nonneg f) ?_
    intro x
    change |inner ℝ f (linearBlockEquiv n x)| ≤ _
    exact linearBlockCost_abs_eval_scaled f (linearBlockEquiv n x)
  · apply max_le
    · have hh : (blockFunctional n f).comp (linearBlockHilbertEquiv n).symm.toContinuousLinearMap =
          innerSL ℝ f := by
        ext x
        simp only [blockFunctional, ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
      calc
        ‖f‖ = ‖innerSL ℝ f‖ := (innerSL_apply_norm ℝ f).symm
        _ = ‖(blockFunctional n f).comp (linearBlockHilbertEquiv n).symm.toContinuousLinearMap‖ := by rw [hh]
        _ ≤ ‖blockFunctional n f‖ * ‖(linearBlockHilbertEquiv n).symm.toContinuousLinearMap‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖blockFunctional n f‖ * 1 :=
          mul_le_mul_of_nonneg_left (block_inv_norm_le n) (norm_nonneg _)
        _ = ‖blockFunctional n f‖ := mul_one _
    · apply ciSup_le
      intro s
      have h := (blockFunctional n f).le_opNorm ((linearBlockHilbertEquiv n).symm (rootPath s))
      change |inner ℝ f (rootPath s)| ≤ ‖blockFunctional n f‖ * linearBlockCost n (rootPath s) at h
      simpa only [inner_rootPath, linearBlockCost_rootPath, mul_one] using h

/-- Every bounded linear functional on X_n has Hilbert coefficients. -/
theorem blockFunctional_surjective (n : ℕ) : Function.Surjective (blockFunctional n) := by
  intro φ
  let ψ : TreeHilbert n →L[ℝ] ℝ := φ.comp (linearBlockHilbertEquiv n).symm.toContinuousLinearMap
  let f := (InnerProductSpace.toDual ℝ (TreeHilbert n)).symm ψ
  refine ⟨f, ?_⟩
  ext x
  rw [blockFunctional_apply]
  change inner ℝ ((InnerProductSpace.toDual ℝ (TreeHilbert n)).symm ψ)
      ((linearBlockHilbertEquiv n) x) = φ x
  rw [InnerProductSpace.toDual_symm_apply]
  simp only [ψ, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

end FiniteHeightTrees


end BoundedTreePotentials

end

end OAI
