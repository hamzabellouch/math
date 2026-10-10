import OAI.MathematicalPhysics.AlternatingFlow.Model

namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Spatial

noncomputable def d {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (F : Space → E) (x : Space) : E := fderiv ℝ F x (e i)

lemma coord_smooth (i : Fin 3) : ContDiff ℝ ∞ (fun x : Space => x i) :=
  (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff

lemma coord_hasFDeriv (i : Fin 3) (x : Space) :
    HasFDerivAt (fun x : Space => x i) (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i) x :=
  (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt

lemma e_apply (i j : Fin 3) : e i j = if j = i then 1 else 0 := by
  simp [e, EuclideanSpace.single, PiLp.single_apply]

lemma d_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (F : Space → E) (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (d i F) := by
  exact (hF.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))).clm_apply contDiff_const

lemma d_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (F : Space → E) : tsupport (d i F) ⊆ tsupport F :=
  tsupport_fderiv_apply_subset ℝ (e i)

lemma d_comm (i j : Fin 3) (F : Space → ℝ) (hF : ContDiff ℝ ∞ F) :
    d i (d j F) = d j (d i F) := by
  ext x
  have hd := (hF.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))).differentiable (by simp)
  have heq (a b : Fin 3) : d a (d b F) x = fderiv ℝ (fderiv ℝ F) x (e a) (e b) := by
    unfold d
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  rw [heq, heq]
  exact hF.contDiffAt.isSymmSndFDerivAt (by norm_num) _ _

noncomputable def curl (i j : Fin 3) (φ : Space → ℝ) (x : Space) : Space :=
  d j φ x • e i - d i φ x • e j

lemma curl_smooth (i j : Fin 3) (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (curl i j φ) :=
  ((d_smooth j φ hφ).smul contDiff_const).sub ((d_smooth i φ hφ).smul contDiff_const)

lemma curl_tsupport (i j : Fin 3) (φ : Space → ℝ) : tsupport (curl i j φ) ⊆ tsupport φ := by
  apply (tsupport_sub _ _).trans
  apply Set.union_subset
  · exact (tsupport_smul_subset_left _ _).trans (d_tsupport j φ)
  · exact (tsupport_smul_subset_left _ _).trans (d_tsupport i φ)

lemma curl_div (i j : Fin 3) (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) (x : Space) :
    (∑ k : Fin 3, d k (curl i j φ) x k) = 0 := by
  have hd (k : Fin 3) := (d_smooth k φ hφ).differentiable (by simp)
  have hc (k : Fin 3) : d k (curl i j φ) x k =
      d k (d j φ) x * (if k = i then 1 else 0) -
        d k (d i φ) x * (if k = j then 1 else 0) := by
    change (fderiv ℝ ((fun y => d j φ y • e i) - (fun y => d i φ y • e j)) x (e k)) k = _
    rw [fderiv_sub ((hd j x).smul_const _) ((hd i x).smul_const _),
      fderiv_smul_const (hd j x), fderiv_smul_const (hd i x)]
    simp [e_apply, d]
  simp_rw [hc]
  rw [Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [d_comm i j φ hφ, sub_self]

def box : Set Space := {x | ∀ i : Fin 3, |x i| ≤ 3}

def plateau : Set Space := {x | ∀ i : Fin 3, |x i| < 2}

noncomputable def cutoff (x : Space) : ℝ :=
  letI := threeAtLeastTwo
  ∏ i : Fin 3, Real.smoothTransition (3 - x i) * Real.smoothTransition (3 + x i)

lemma cutoff_smooth : ContDiff ℝ ∞ cutoff := by
  unfold cutoff
  apply contDiff_prod
  intro i _
  have hi := coord_smooth i
  fun_prop

lemma isClosed_box : IsClosed box := by
  have heq : box = ⋂ i : Fin 3, {x : Space | |x i| ≤ 3} := by ext; simp [box]
  rw [heq]
  exact isClosed_iInter (fun i => isClosed_le (coord_smooth i).continuous.abs continuous_const)

lemma box_compact : IsCompact box := by
  apply (isCompact_closedBall (0 : Space) 9).of_isClosed_subset isClosed_box
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  calc
    ∑ i : Fin 3, ‖x i‖ ^ 2 ≤ ∑ _i : Fin 3, (3 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (hx i) 2
    _ ≤ 9 ^ 2 := by norm_num

lemma plateau_open : IsOpen plateau := by
  have heq : plateau = ⋂ i : Fin 3, {x : Space | |x i| < 2} := by ext; simp [plateau]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt (coord_smooth i).continuous.abs continuous_const)

lemma cutoff_one (x : Space) (hx : x ∈ plateau) : cutoff x = 1 := by
  apply Finset.prod_eq_one
  intro i _
  have hi := abs_lt.1 (hx i)
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 - x i),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 + x i), one_mul]

lemma cutoff_one_near (x : Space) (hx : x ∈ plateau) :
    cutoff =ᶠ[𝓝 x] (fun _ => 1) :=
  Filter.eventually_of_mem (plateau_open.mem_nhds hx) (fun y hy => cutoff_one y hy)

lemma cutoff_support : tsupport cutoff ⊆ box := by
  apply closure_minimal _ isClosed_box
  intro x hx i
  by_contra hi
  have hn : 3 < |x i| := lt_of_not_ge hi
  have hz : Real.smoothTransition (3 - x i) * Real.smoothTransition (3 + x i) = 0 := by
    rcases (lt_abs.1 hn) with hn | hn
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 - x i ≤ 0), zero_mul]
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 + x i ≤ 0), mul_zero]
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

noncomputable def shearPotential (d i j : Fin 3) (L E : ℝ → ℝ) (x : Space) : ℝ :=
  x j * L (x d) - x i * E (x d)

noncomputable def localizedShear (d i j : Fin 3) (L E : ℝ → ℝ) : Space → Space :=
  curl i j (fun x => cutoff x * shearPotential d i j L E x)

lemma shearPotential_smooth (d i j : Fin 3) (L E : ℝ → ℝ)
    (hL : ContDiff ℝ ∞ L) (hE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ (shearPotential d i j L E) :=
  ((coord_smooth j).mul (hL.comp (coord_smooth d))).sub
    ((coord_smooth i).mul (hE.comp (coord_smooth d)))

lemma localizedShear_smooth (d i j : Fin 3) (L E : ℝ → ℝ)
    (hL : ContDiff ℝ ∞ L) (hE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ (localizedShear d i j L E) :=
  curl_smooth i j _ (cutoff_smooth.mul (shearPotential_smooth d i j L E hL hE))

lemma localizedShear_support (d i j : Fin 3) (L E : ℝ → ℝ) :
    tsupport (localizedShear d i j L E) ⊆ box :=
  (curl_tsupport _ _ _).trans (tsupport_mul_subset_left.trans cutoff_support)

lemma localizedShear_div (d i j : Fin 3) (L E : ℝ → ℝ)
    (hL : ContDiff ℝ ∞ L) (hE : ContDiff ℝ ∞ E) (x : Space) :
    (∑ k : Fin 3, Spatial.d k (localizedShear d i j L E) x k) = 0 :=
  curl_div i j _ (cutoff_smooth.mul (shearPotential_smooth d i j L E hL hE)) x

lemma localizedShear_plateau (d i j : Fin 3) (hij : i ≠ j) (hdi : d ≠ i) (hdj : d ≠ j)
    (L E : ℝ → ℝ) (hL : ContDiff ℝ ∞ L) (hE : ContDiff ℝ ∞ E)
    (x : Space) (hx : x ∈ plateau) :
    localizedShear d i j L E x = L (x d) • e i + E (x d) • e j := by
  have heq : (fun y => cutoff y * shearPotential d i j L E y) =ᶠ[𝓝 x]
      shearPotential d i j L E := by
    filter_upwards [cutoff_one_near x hx] with y hy
    rw [hy, one_mul]
  have hL' := ((hL.differentiable (by simp)) (x d)).hasFDerivAt.comp x (coord_hasFDeriv d x)
  have hE' := ((hE.differentiable (by simp)) (x d)).hasFDerivAt.comp x (coord_hasFDeriv d x)
  have hφ := ((coord_hasFDeriv j x).mul hL').sub ((coord_hasFDeriv i x).mul hE')
  have hφeq := hφ.fderiv
  change fderiv ℝ (shearPotential d i j L E) x = _ at hφeq
  simp only [localizedShear, curl, Spatial.d, heq.fderiv_eq, hφeq]
  simp [ContinuousLinearMap.comp_apply, PiLp.proj_apply, e_apply, hij, hij.symm, hdi,
    hdj, sub_eq_add_neg]

end Spatial
end AlternatingNS

end OAI
