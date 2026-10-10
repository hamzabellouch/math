import OAI.Analysis.TreePotential.HilbertSum

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section QuadraticCost
variable {H M : Type*} [NormedAddCommGroup H] [spaceH : NormedSpace ℝ H]
  [NormedAddCommGroup M] [spaceM : NormedSpace ℝ M]

lemma dot_two_le_sqrt (a b c d : ℝ) :
    a*c + b*d ≤ Real.sqrt (a^2+b^2) * Real.sqrt (c^2+d^2) := by
  have he : (Real.sqrt (a^2+b^2) * Real.sqrt (c^2+d^2))^2 =
      (a^2+b^2)*(c^2+d^2) := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  nlinarith [sq_nonneg (a*d-b*c),
    mul_nonneg (Real.sqrt_nonneg (a^2+b^2)) (Real.sqrt_nonneg (c^2+d^2))]

def pairCost (h : H) (μ : M) : ℝ := Real.sqrt (‖h‖^2 + ‖μ‖^2)

lemma pairCost_eq_norm {H M : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup M] [NormedSpace ℝ M] (h : H) (μ : M) :
    pairCost h μ = ‖WithLp.toLp 2 (h, μ)‖ := by
  rw [WithLp.prod_norm_eq_of_L2]
  rfl

lemma pairCost_add_le (h k : H) (μ ν : M) :
    pairCost (h+k) (μ+ν) ≤ pairCost h μ + pairCost k ν := by
  simp only [pairCost_eq_norm]
  exact norm_add_le (WithLp.toLp 2 (h, μ)) (WithLp.toLp 2 (k, ν))

lemma pairCost_smul (a : ℝ) (h : H) (μ : M) :
    pairCost (a • h) (a • μ) = ‖a‖ * pairCost h μ := by
  simp only [pairCost_eq_norm]
  exact norm_smul a (WithLp.toLp 2 (h, μ))

@[simp] lemma pairCost_zero_right {H M : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup M] [NormedSpace ℝ M] (h : H) : pairCost h (0 : M) = ‖h‖ := by
  simp [pairCost, Real.sqrt_sq]

@[simp] lemma pairCost_zero_left {H M : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup M] [NormedSpace ℝ M] (μ : M) : pairCost (0 : H) μ = ‖μ‖ := by
  simp [pairCost, Real.sqrt_sq]

/-- The exact quadratic path cost. -/
def quadraticCost (B : M →L[ℝ] H) (x : H) : ℝ :=
  ⨅ μ : M, pairCost (x - B μ) μ

lemma quadraticCost_bddBelow (B : M →L[ℝ] H) (x : H) :
    BddBelow (range fun μ : M => pairCost (x - B μ) μ) :=
  ⟨0, by rintro _ ⟨μ, rfl⟩; exact Real.sqrt_nonneg _⟩

lemma quadraticCost_nonneg (B : M →L[ℝ] H) (x : H) : 0 ≤ quadraticCost B x :=
  le_ciInf (fun _ => Real.sqrt_nonneg _)

lemma quadraticCost_le (B : M →L[ℝ] H) (x : H) (μ : M) :
    quadraticCost B x ≤ pairCost (x - B μ) μ := ciInf_le (quadraticCost_bddBelow B x) μ

lemma quadraticCost_le_norm (B : M →L[ℝ] H) (x : H) : quadraticCost B x ≤ ‖x‖ := by
  simpa using quadraticCost_le B x 0

@[simp] lemma quadraticCost_zero (B : M →L[ℝ] H) : quadraticCost B 0 = 0 :=
  le_antisymm (by simpa using quadraticCost_le_norm B 0) (quadraticCost_nonneg B 0)

lemma quadraticCost_synthesis_le (B : M →L[ℝ] H) (μ : M) :
    quadraticCost B (B μ) ≤ ‖μ‖ := by simpa using quadraticCost_le B (B μ) μ

lemma quadraticCost_representation_le (B : M →L[ℝ] H) (h : H) (μ : M) :
    quadraticCost B (h + B μ) ≤ pairCost h μ := by
  simpa using quadraticCost_le B (h+B μ) μ

lemma quadraticCost_add_le (B : M →L[ℝ] H) (x y : H) :
    quadraticCost B (x+y) ≤ quadraticCost B x + quadraticCost B y := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  obtain ⟨μ, hμ⟩ := (ciInf_lt_iff (quadraticCost_bddBelow B x)).mp
    (show quadraticCost B x < r - quadraticCost B y by linarith)
  obtain ⟨ν, hν⟩ := (ciInf_lt_iff (quadraticCost_bddBelow B y)).mp
    (show quadraticCost B y < r - pairCost (x-B μ) μ by linarith)
  calc
    quadraticCost B (x+y) ≤ pairCost (x+y-B (μ+ν)) (μ+ν) := quadraticCost_le _ _ _
    _ = pairCost ((x-B μ)+(y-B ν)) (μ+ν) := by rw [map_add]; congr 1; abel
    _ ≤ pairCost (x-B μ) μ + pairCost (y-B ν) ν := pairCost_add_le _ _ _ _
    _ ≤ r := by linarith

lemma quadraticCost_smul_le (B : M →L[ℝ] H) (a : ℝ) (x : H) :
    quadraticCost B (a • x) ≤ ‖a‖ * quadraticCost B x := by
  change quadraticCost B (a • x) ≤ ‖a‖ * (⨅ μ : M, pairCost (x-B μ) μ)
  rw [Real.mul_iInf_of_nonneg (norm_nonneg a)]
  apply le_ciInf
  intro μ
  calc
    quadraticCost B (a • x) ≤ pairCost (a • x-B (a • μ)) (a • μ) := quadraticCost_le _ _ _
    _ = ‖a‖ * pairCost (x-B μ) μ := by rw [map_smul, ← smul_sub, pairCost_smul]

def quadraticCostSeminorm (B : M →L[ℝ] H) : Seminorm ℝ H :=
  Seminorm.ofSMulLE (quadraticCost B) (quadraticCost_zero B)
    (quadraticCost_add_le B) (quadraticCost_smul_le B)

lemma quadraticCost_exists_norming (B : M →L[ℝ] H) (x : H) :
    ∃ φ : H →L[ℝ] ℝ, ‖φ‖ ≤ 1 ∧ φ x = quadraticCost B x ∧
      ∀ z : H, |φ z| ≤ quadraticCost B z := by
  obtain ⟨ψ, hx, hψ⟩ := exists_linear_norming (quadraticCostSeminorm B) x
  have hb : ∀ z : H, ‖ψ z‖ ≤ 1 * ‖z‖ := fun z => by
    simpa using (hψ z).trans (quadraticCost_le_norm B z)
  let φ : H →L[ℝ] ℝ := ψ.mkContinuous 1 hb
  exact ⟨φ, φ.opNorm_le_bound (by norm_num) hb, hx, hψ⟩

lemma norm_le_mul_quadraticCost (B : M →L[ℝ] H) {K : ℝ}
    (hB : ∀ μ : M, ‖B μ‖ ≤ K * ‖μ‖) (x : H) :
    ‖x‖ ≤ Real.sqrt (1+K^2) * quadraticCost B x := by
  have hK : 0 < Real.sqrt (1+K^2) := by positivity
  rw [mul_comm]
  apply (div_le_iff₀ hK).mp
  apply le_ciInf
  intro μ
  apply (div_le_iff₀ hK).mpr
  calc
    ‖x‖ = ‖(x-B μ)+B μ‖ := by rw [sub_add_cancel]
    _ ≤ ‖x-B μ‖ + ‖B μ‖ := norm_add_le _ _
    _ ≤ ‖x-B μ‖ + K*‖μ‖ := add_le_add le_rfl (hB μ)
    _ ≤ pairCost (x-B μ) μ * Real.sqrt (1+K^2) := by
      simpa only [one_pow, one_mul, pairCost, mul_comm] using
        dot_two_le_sqrt 1 K ‖x-B μ‖ ‖μ‖

end QuadraticCost

/-- Z_n uses the same rooted tree and synthesis, but a genuinely different norm. -/
def quadraticBlockCost (n : ℕ) (x : TreeHilbert n) := quadraticCost (pathSynthesis n) x

theorem quadraticBlockCost_comparison (n : ℕ) (x : TreeHilbert n) :
    ‖x‖ / Real.sqrt (n+2) ≤ quadraticBlockCost n x ∧ quadraticBlockCost n x ≤ ‖x‖ := by
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < Real.sqrt (n+2 : ℝ))).mpr
    have h := norm_le_mul_quadraticCost (pathSynthesis n) (pathSynthesis_bound n) x
    have he : (1 : ℝ) + (Real.sqrt (n+1 : ℝ))^2 = n+2 := by
      rw [Real.sq_sqrt (by positivity)]
      ring
    rw [he] at h
    simpa only [quadraticBlockCost, mul_comm] using h
  · exact quadraticCost_le_norm _ _

def QuadraticBlock (n : ℕ) := TreeHilbert n
instance (n : ℕ) : AddCommGroup (QuadraticBlock n) := inferInstanceAs (AddCommGroup (TreeHilbert n))
instance (n : ℕ) : Module ℝ (QuadraticBlock n) := inferInstanceAs (Module ℝ (TreeHilbert n))
def quadraticBlockEquiv (n : ℕ) : QuadraticBlock n ≃ₗ[ℝ] TreeHilbert n :=
  { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
instance (n : ℕ) : Norm (QuadraticBlock n) := ⟨fun x => quadraticBlockCost n x⟩

theorem quadraticBlockCore (n : ℕ) : NormedSpace.Core ℝ (QuadraticBlock n) where
  norm_nonneg := quadraticCost_nonneg (pathSynthesis n)
  norm_smul c x := map_smul_eq_mul (quadraticCostSeminorm (pathSynthesis n)) c x
  norm_triangle := quadraticCost_add_le (pathSynthesis n)
  norm_eq_zero_iff x := by
    constructor
    · intro hx
      have h := (quadraticBlockCost_comparison n (quadraticBlockEquiv n x)).1
      change quadraticBlockCost n (quadraticBlockEquiv n x) = 0 at hx
      rw [hx] at h
      have hk : 0 < Real.sqrt (n+2 : ℝ) := by positivity
      have hxnorm : ‖quadraticBlockEquiv n x‖ ≤ 0 := by
        have := (div_le_iff₀ hk).mp h
        simpa only [zero_mul] using this
      apply (quadraticBlockEquiv n).injective
      rw [map_zero]
      exact norm_eq_zero.mp (le_antisymm hxnorm (norm_nonneg _))
    · rintro rfl
      exact quadraticCost_zero (pathSynthesis n)
instance (n : ℕ) : NormedAddCommGroup (QuadraticBlock n) := NormedAddCommGroup.ofCore (quadraticBlockCore n)
instance (n : ℕ) : NormedSpace ℝ (QuadraticBlock n) := NormedSpace.ofCore (quadraticBlockCore n)

@[simp] lemma norm_QuadraticBlock (n : ℕ) (x : QuadraticBlock n) : ‖x‖ = quadraticBlockCost n x := rfl

def quadraticBlockHilbertEquiv (n : ℕ) : QuadraticBlock n ≃L[ℝ] TreeHilbert n :=
  (quadraticBlockEquiv n).toContinuousLinearEquivOfBounds (Real.sqrt (n+2)) 1
    (fun x => by
      have hk : 0 < Real.sqrt (n+2 : ℝ) := by positivity
      exact (mul_comm _ _).ge.trans' ((div_le_iff₀ hk).mp (quadraticBlockCost_comparison n x).1))
    (fun x => by
      change quadraticBlockCost n x ≤ 1 * ‖x‖
      simpa only [one_mul] using (quadraticBlockCost_comparison n x).2)

def quadraticBlockUniformEquiv (n : ℕ) : QuadraticBlock n ≃ᵤ TreeHilbert n :=
  { toEquiv := (quadraticBlockHilbertEquiv n).toLinearEquiv.toEquiv
    uniformContinuous_toFun := (quadraticBlockHilbertEquiv n).toContinuousLinearMap.uniformContinuous
    uniformContinuous_invFun := (quadraticBlockHilbertEquiv n).symm.toContinuousLinearMap.uniformContinuous }
instance (n : ℕ) : CompleteSpace (QuadraticBlock n) :=
  (quadraticBlockUniformEquiv n).completeSpace_iff.mpr inferInstance

lemma quadraticBlock_reflexive (n : ℕ) : IsReflexive (QuadraticBlock n) :=
  reflexive_equiv (quadraticBlockHilbertEquiv n) hilbert_reflexive

abbrev QuadraticOuter := HilbertSum (fun n : ℕ => QuadraticBlock (n+1))
theorem quadraticOuter_reflexive : IsReflexive QuadraticOuter :=
  hilbertSum_reflexive _ (fun _ => quadraticBlock_reflexive _)


section QuadraticDuality

abbrev pathBound {n : ℕ} (f : TreeHilbert n) : ℝ := ⨆ s : Tree n, |pathPotential f s|

lemma path_le_pathBound {n : ℕ} (f : TreeHilbert n) (s : Tree n) :
    |pathPotential f s| ≤ pathBound f := le_ciSup (pathPotential_bddAbove f) s

lemma pathBound_nonneg {n : ℕ} (f : TreeHilbert n) : 0 ≤ pathBound f :=
  (abs_nonneg _).trans (path_le_pathBound f (root n))

def quadraticPolar (n : ℕ) (f : TreeHilbert n) : ℝ :=
  Real.sqrt (‖f‖^2 + (pathBound f)^2)

lemma quadraticPolar_nonneg {n : ℕ} (f : TreeHilbert n) : 0 ≤ quadraticPolar n f :=
  Real.sqrt_nonneg _

lemma quadraticPolar_sq {n : ℕ} (f : TreeHilbert n) :
    (quadraticPolar n f)^2 = ‖f‖^2 + (pathBound f)^2 := Real.sq_sqrt (by positivity)

lemma quadraticPolar_le_iff {n : ℕ} (f : TreeHilbert n) {C : ℝ} (hC : 0 ≤ C) :
    quadraticPolar n f ≤ C ↔ ∀ s, ‖f‖^2 + (pathPotential f s)^2 ≤ C^2 := by
  constructor
  · intro h s
    have hp := path_le_pathBound f s
    have hpn := pathBound_nonneg f
    have he := quadraticPolar_sq f
    have hqn := quadraticPolar_nonneg f
    nlinarith [sq_abs (pathPotential f s), abs_nonneg (pathPotential f s)]
  · intro h
    have hn : 0 ≤ C^2-‖f‖^2 := by nlinarith [sq_nonneg (pathPotential f (root n)), h (root n)]
    have hp : pathBound f ≤ Real.sqrt (C^2-‖f‖^2) := by
      apply ciSup_le
      intro s
      apply (Real.le_sqrt (abs_nonneg _) hn).mpr
      nlinarith [sq_abs (pathPotential f s), h s]
    have he := quadraticPolar_sq f
    have hs := Real.sq_sqrt hn
    have hpn := pathBound_nonneg f
    have hsn := Real.sqrt_nonneg (C^2-‖f‖^2)
    have hqn := quadraticPolar_nonneg f
    nlinarith

lemma atom_pairing_scaled {I E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : I → E) {K : ℝ} (hb : ∀ i, ‖b i‖ ≤ K) {f : E} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ i, |inner ℝ f (b i)| ≤ C) (μ : L1Mass I) :
    |inner ℝ f (atomSynthesis b hb μ)| ≤ C * ‖μ‖ := by
  have heq : inner ℝ f (atomSynthesis b hb μ) = ∑' i, μ i * inner ℝ f (b i) := by
    simpa only [atomSynthesis_apply, innerSL_apply_apply, real_inner_smul_right] using
      (innerSL ℝ f).map_tsum (atom_summable b hb μ)
  have hpoint : ∀ i, ‖μ i * inner ℝ f (b i)‖ ≤ C * ‖μ i‖ := by
    intro i
    rw [norm_mul, Real.norm_eq_abs (inner ℝ f (b i))]
    simpa only [mul_comm] using mul_le_mul (hf i) (le_refl ‖μ i‖) (norm_nonneg _) hC
  have hsm := ((l1_hasSum_norm μ).summable.mul_left C)
  have hs : Summable (fun i => ‖μ i * inner ℝ f (b i)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint hsm
  rw [heq, ← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hs).trans
    ((Summable.tsum_le_tsum hpoint hs hsm).trans_eq ((l1_hasSum_norm μ).mul_left C).tsum_eq)

lemma path_pairing_bound {n : ℕ} (f : TreeHilbert n) (μ : L1Mass (Tree n)) :
    |inner ℝ f (pathSynthesis n μ)| ≤ pathBound f * ‖μ‖ :=
  atom_pairing_scaled rootPath rootPath_norm_bound (pathBound_nonneg f)
    (fun s => by simpa only [inner_rootPath] using path_le_pathBound f s) μ

lemma quadraticBlockCost_abs_eval_scaled {n : ℕ} (f x : TreeHilbert n) :
    |inner ℝ f x| ≤ quadraticPolar n f * quadraticBlockCost n x := by
  change |inner ℝ f x| ≤ quadraticPolar n f * (⨅ μ : L1Mass (Tree n), pairCost (x-pathSynthesis n μ) μ)
  rw [Real.mul_iInf_of_nonneg (quadraticPolar_nonneg f)]
  apply le_ciInf
  intro μ
  calc
    |inner ℝ f x| = |inner ℝ f (x-pathSynthesis n μ) + inner ℝ f (pathSynthesis n μ)| := by
      rw [← inner_add_right, sub_add_cancel]
    _ ≤ |inner ℝ f (x-pathSynthesis n μ)| + |inner ℝ f (pathSynthesis n μ)| := abs_add_le _ _
    _ ≤ ‖f‖ * ‖x-pathSynthesis n μ‖ + pathBound f * ‖μ‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (path_pairing_bound f μ)
    _ ≤ quadraticPolar n f * pairCost (x-pathSynthesis n μ) μ :=
      dot_two_le_sqrt ‖f‖ (pathBound f) ‖x-pathSynthesis n μ‖ ‖μ‖

@[simp] lemma pathSynthesis_single {n : ℕ} (s : Tree n) (c : ℝ) :
    pathSynthesis n (lp.single 1 s c) = c • rootPath s :=
  atomSynthesis_single rootPath rootPath_norm_bound s c

def quadraticFunctional (n : ℕ) (f : TreeHilbert n) : QuadraticBlock n →L[ℝ] ℝ :=
  (innerSL ℝ f).comp (quadraticBlockHilbertEquiv n).toContinuousLinearMap

@[simp] lemma quadraticFunctional_apply (n : ℕ) (f : TreeHilbert n) (x : QuadraticBlock n) :
    quadraticFunctional n f x = inner ℝ f (quadraticBlockEquiv n x) := rfl

/-- Exact quadratic dual norm, with a sum rather than a maximum. -/
theorem quadraticFunctional_norm (n : ℕ) (f : TreeHilbert n) :
    ‖quadraticFunctional n f‖ = quadraticPolar n f := by
  apply le_antisymm
  · refine (quadraticFunctional n f).opNorm_le_bound (quadraticPolar_nonneg f) ?_
    intro x
    change |inner ℝ f (quadraticBlockEquiv n x)| ≤ _
    exact quadraticBlockCost_abs_eval_scaled f (quadraticBlockEquiv n x)
  · apply (quadraticPolar_le_iff f (norm_nonneg _)).mpr
    intro s
    let c := pathPotential f s
    let z := f + pathSynthesis n (lp.single 1 s c)
    have he : inner ℝ f z = ‖f‖^2+c^2 := by
      simp only [z, inner_add_right, pathSynthesis_single, real_inner_smul_right,
        inner_rootPath, real_inner_self_eq_norm_sq]
      change ‖f‖^2 + c*c = ‖f‖^2+c^2
      ring
    have hb : quadraticBlockCost n z ≤ Real.sqrt (‖f‖^2+c^2) := by
      have h := quadraticCost_representation_le (pathSynthesis n) f (lp.single 1 s c)
      simpa only [quadraticBlockCost, z, pairCost, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1), Real.norm_eq_abs, sq_abs] using h
    have h := (quadraticFunctional n f).le_opNorm ((quadraticBlockHilbertEquiv n).symm z)
    change |inner ℝ f z| ≤ ‖quadraticFunctional n f‖ * quadraticBlockCost n z at h
    rw [he, abs_of_nonneg (by positivity)] at h
    have hp := h.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    have hs : (Real.sqrt (‖f‖^2+c^2))^2 = ‖f‖^2+c^2 := Real.sq_sqrt (by positivity)
    have hk : Real.sqrt (‖f‖^2+c^2) ≤ ‖quadraticFunctional n f‖ := by
      by_cases hz : Real.sqrt (‖f‖^2+c^2) = 0
      · rw [hz]; exact norm_nonneg _
      have ht : 0 < Real.sqrt (‖f‖^2+c^2) := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
      apply (mul_le_mul_iff_right₀ ht).mp
      nlinarith
    nlinarith [norm_nonneg (quadraticFunctional n f), Real.sqrt_nonneg (‖f‖^2+c^2)]

theorem quadraticFunctional_surjective (n : ℕ) : Function.Surjective (quadraticFunctional n) := by
  intro φ
  let ψ : TreeHilbert n →L[ℝ] ℝ := φ.comp (quadraticBlockHilbertEquiv n).symm.toContinuousLinearMap
  let f := (InnerProductSpace.toDual ℝ (TreeHilbert n)).symm ψ
  refine ⟨f, ?_⟩
  ext x
  rw [quadraticFunctional_apply]
  change inner ℝ ((InnerProductSpace.toDual ℝ (TreeHilbert n)).symm ψ)
    ((quadraticBlockHilbertEquiv n) x) = φ x
  rw [InnerProductSpace.toDual_symm_apply]
  simp only [ψ, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

lemma quadraticBlockCost_norming (n : ℕ) (x : TreeHilbert n) :
    ∃ f : TreeHilbert n, quadraticPolar n f ≤ 1 ∧ inner ℝ f x = quadraticBlockCost n x := by
  obtain ⟨φ, hφ, hφx⟩ := exists_dual_vector'' ℝ ((quadraticBlockHilbertEquiv n).symm x)
  obtain ⟨f, rfl⟩ := quadraticFunctional_surjective n φ
  refine ⟨f, ?_, hφx⟩
  rwa [quadraticFunctional_norm] at hφ

theorem quadraticBlockCost_duality (n : ℕ) (x : TreeHilbert n) :
    quadraticBlockCost n x = sSup {r : ℝ | ∃ f : TreeHilbert n,
      quadraticPolar n f ≤ 1 ∧ r = inner ℝ f x} := by
  have hb : ∀ f : TreeHilbert n, quadraticPolar n f ≤ 1 → inner ℝ f x ≤ quadraticBlockCost n x := by
    intro f hf
    exact (le_abs_self _).trans ((quadraticBlockCost_abs_eval_scaled f x).trans
      (by simpa only [quadraticBlockCost, one_mul] using mul_le_mul_of_nonneg_right hf (quadraticCost_nonneg (pathSynthesis n) x)))
  have hbd : BddAbove {r : ℝ | ∃ f : TreeHilbert n, quadraticPolar n f ≤ 1 ∧ r = inner ℝ f x} :=
    ⟨quadraticBlockCost n x, by rintro r ⟨f, hf, rfl⟩; exact hb f hf⟩
  obtain ⟨f, hf, hx⟩ := quadraticBlockCost_norming n x
  exact le_antisymm (le_csSup hbd ⟨f, hf, hx.symm⟩)
    (csSup_le ⟨_, f, hf, rfl⟩ (by rintro r ⟨g, hg, rfl⟩; exact hb g hg))

lemma pathBound_single {n : ℕ} (s : Tree n) : pathBound (lp.single 2 s (1 : ℝ)) = 1 := by
  apply le_antisymm
  · apply ciSup_le
    intro t
    rw [singleton_pathPotential]
    split_ifs <;> norm_num
  · have h := path_le_pathBound (lp.single 2 s (1 : ℝ)) s
    simpa only [singleton_pathPotential, self_mem_pathNodes, ite_true, abs_one] using h

lemma quadraticPolar_single {n : ℕ} (s : Tree n) :
    quadraticPolar n (lp.single 2 s (1 : ℝ)) = Real.sqrt 2 := by
  norm_num [quadraticPolar, pathBound_single, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

lemma coordinate_le_quadraticBlockCost {n : ℕ} (x : TreeHilbert n) (s : Tree n) :
    |x s| ≤ Real.sqrt 2 * quadraticBlockCost n x := by
  have h := quadraticBlockCost_abs_eval_scaled (lp.single 2 s (1 : ℝ)) x
  simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, one_mul, mul_one,
    quadraticPolar_single] using h

lemma quadraticBlockCost_single_bounds {n : ℕ} (s : Tree n) :
    1 / Real.sqrt 2 ≤ quadraticBlockCost n (lp.single 2 s (1 : ℝ)) ∧
    quadraticBlockCost n (lp.single 2 s (1 : ℝ)) ≤ 1 := by
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < Real.sqrt (2 : ℝ))).mpr
    have h := coordinate_le_quadraticBlockCost (lp.single 2 s (1 : ℝ)) s
    simpa [mul_comm] using h
  · have h := quadraticCost_le_norm (pathSynthesis n) (lp.single 2 s (1 : ℝ))
    simpa [quadraticBlockCost, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] using h

lemma quadraticBlockCost_path_bounds {n : ℕ} (s : Tree n) :
    1 / Real.sqrt 2 ≤ quadraticBlockCost n (rootPath s) ∧ quadraticBlockCost n (rootPath s) ≤ 1 := by
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < Real.sqrt (2 : ℝ))).mpr
    have h := coordinate_le_quadraticBlockCost (rootPath s) s
    simpa [rootPath_apply, mul_comm] using h
  · have h := quadraticCost_synthesis_le (pathSynthesis n) (lp.single 1 s (1 : ℝ))
    simpa only [quadraticBlockCost, pathSynthesis_single, one_smul,
      lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1), norm_one] using h

end QuadraticDuality


end BoundedTreePotentials

end

end OAI
