import OAI.Analysis.TreePotential.Clipping

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section WeightedMidpoints
variable {I : Type*} {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
  [spaceE : ∀ i, NormedSpace ℝ (E i)]

lemma lp_hasSum_sq {I : Type*} {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] (x : HilbertSum E) :
    HasSum (fun i => ‖x i‖^2) (‖x‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using lp.hasSum_norm (by norm_num) x

lemma lp_midpoint_sq (x z u v : HilbertSum E)
    (h : ∀ i, ‖x i‖^2+‖z i‖^2/16 ≤ ((‖u i‖+‖v i‖)/2)^2) :
    ‖x‖^2+‖z‖^2/16 ≤ ((‖u‖+‖v‖)/2)^2 := by
  let w : lp (fun _ : I => ℝ) 2 := (1/2 : ℝ) • (lp.toNorm u+lp.toNorm v)
  have hws : HasSum (fun i => ((‖u i‖+‖v i‖)/2)^2) (‖w‖^2) := by
    have he := lp_hasSum_sq w
    convert he using 1
    funext i
    change ((‖u i‖+‖v i‖)/2)^2 = ‖(1/2 : ℝ)*(‖u i‖+‖v i‖)‖^2
    rw [Real.norm_eq_abs, sq_abs]
    ring
  have hxs := (lp_hasSum_sq x).add ((lp_hasSum_sq z).div_const 16)
  have hh := hxs.summable.tsum_le_tsum h hws.summable
  rw [hxs.tsum_eq, hws.tsum_eq] at hh
  have hw : ‖w‖ ≤ (‖u‖+‖v‖)/2 := by
    dsimp [w]
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    have ht := norm_add_le (lp.toNorm u) (lp.toNorm v)
    rw [lp.norm_toNorm, lp.norm_toNorm] at ht
    nlinarith
  nlinarith [norm_nonneg w]

end WeightedMidpoints

/-- A finite ancestral subset of the disjoint union of the finite-height trees. -/
structure FiniteOuterHead where
  nodes : ℕ → Set TreeCalculus.Node
  initial : ∀ n, TreeCalculus.Initial (nodes n)
  finite_nodes : {s : (n : ℕ) × Tree (n+1) | s.2.val ∈ nodes s.1}.Finite

namespace CostHeads
open BlockCalculus
open TreeCalculus
open scoped Classical

def linearHead (n : ℕ) (D : Set Node) (hD : Initial D) : LinearBlock n →L[ℝ] LinearBlock n :=
  (((linearBlockEquiv n).symm.toLinearMap.comp (headLM D)).comp (linearBlockEquiv n).toLinearMap).mkContinuous
    1 (by
      intro x
      change linearBlockCost n (head D (linearBlockEquiv n x)) ≤ 1*linearBlockCost n (linearBlockEquiv n x)
      simpa only [one_mul] using head_linearCost_le hD (linearBlockEquiv n x))

@[simp] lemma linearHead_equiv (n : ℕ) (D : Set Node) (hD : Initial D) (x : LinearBlock n) :
    linearBlockEquiv n (linearHead n D hD x) = head D (linearBlockEquiv n x) := rfl

lemma linearHead_norm (n : ℕ) (D : Set Node) (hD : Initial D) : ‖linearHead n D hD‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change linearBlockCost n (head D (linearBlockEquiv n x)) ≤ 1*linearBlockCost n (linearBlockEquiv n x)
  simpa only [one_mul] using head_linearCost_le hD (linearBlockEquiv n x)

def linearOuterHead (D : ℕ → Set Node) (hD : ∀ n, Initial (D n)) : LinearOuter →L[ℝ] LinearOuter :=
  lp.mapCLM 2 (fun n => linearHead (n+1) (D n) (hD n)) zero_le_one
    (fun n => linearHead_norm (n+1) (D n) (hD n))

@[simp] lemma linearOuterHead_apply (D : ℕ → Set Node) (hD : ∀ n, Initial (D n))
    (x : LinearOuter) (n : ℕ) :
    linearOuterHead D hD x n = linearHead (n+1) (D n) (hD n) (x n) := rfl

lemma linearOuterHead_contract (D : ℕ → Set Node) (hD : ∀ n, Initial (D n)) (x : LinearOuter) :
    ‖linearOuterHead D hD x‖ ≤ ‖x‖ := by
  have hb : ‖linearOuterHead D hD‖ ≤ 1 :=
    lp.norm_mapCLM_le 2 _ zero_le_one (fun n => linearHead_norm (n+1) (D n) (hD n))
  simpa only [one_mul] using (linearOuterHead D hD).le_of_opNorm_le hb x

lemma linearOuterHead_idem (D : ℕ → Set Node) (hD : ∀ n, Initial (D n)) (x : LinearOuter) :
    linearOuterHead D hD (linearOuterHead D hD x) = linearOuterHead D hD x := by
  apply Subtype.ext
  funext n
  apply (linearBlockEquiv (n+1)).injective
  simp only [linearOuterHead_apply, linearHead_equiv, head_idem]

lemma linearOuterTail_bound (D : ℕ → Set Node) (hD : ∀ n, Initial (D n)) (x : LinearOuter) :
    ‖x-linearOuterHead D hD x‖ ≤ 2*‖x‖ :=
  (norm_sub_le _ _).trans (by linarith [linearOuterHead_contract D hD x])

/-- Paired estimates permit arbitrary old-head motion in the displacement. -/
theorem linearOuter_midpoint_sq (D : ℕ → Set Node) (hD : ∀ n, Initial (D n))
    (x y : LinearOuter) (hx : linearOuterHead D hD x = x) :
    ‖x‖^2+‖y-linearOuterHead D hD y‖^2/16 ≤ ((‖x+y‖+‖x-y‖)/2)^2 := by
  apply lp_midpoint_sq
  intro n
  have hxn : head (D n) (linearBlockEquiv (n+1) (x n)) = linearBlockEquiv (n+1) (x n) := by
    have he := congrArg (fun z : LinearOuter => linearBlockEquiv (n+1) (z n)) hx
    simpa only [linearOuterHead_apply, linearHead_equiv] using he
  have he := linear_midpoint_tail (hD n) (linearBlockEquiv (n+1) (x n))
    (linearBlockEquiv (n+1) (y n)) hxn
  change Real.sqrt (‖x n‖^2+‖(y-linearOuterHead D hD y) n‖^2/16) ≤
    (‖(x+y) n‖+‖(x-y) n‖)/2 at he
  have hs := Real.sq_sqrt (show 0 ≤ ‖x n‖^2+‖(y-linearOuterHead D hD y) n‖^2/16 by positivity)
  have hn := Real.sqrt_nonneg (‖x n‖^2+‖(y-linearOuterHead D hD y) n‖^2/16)
  nlinarith [norm_nonneg ((x+y) n), norm_nonneg ((x-y) n)]

theorem linearOuter_midpoint (D : ℕ → Set Node) (hD : ∀ n, Initial (D n))
    (x y : LinearOuter) (hx : linearOuterHead D hD x = x) :
    Real.sqrt (‖x‖^2+‖y-linearOuterHead D hD y‖^2/16) ≤ (‖x+y‖+‖x-y‖)/2 := by
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by positivity, linearOuter_midpoint_sq D hD x y hx⟩

theorem linearOuter_tail_four (A : FiniteOuterHead) (x y : LinearOuter)
    (hx : linearOuterHead A.nodes A.initial x = x) {R : ℝ} (hR : 0 ≤ R)
    (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖y-linearOuterHead A.nodes A.initial y‖ ≤ 4*Real.sqrt (R^2-‖x‖^2) := by
  have he := linearOuter_midpoint_sq A.nodes A.initial x y hx
  have hb : ‖x‖^2+‖y-linearOuterHead A.nodes A.initial y‖^2/16 ≤ R^2 := by
    nlinarith [norm_nonneg (x+y), norm_nonneg (x-y)]
  have hd : 0 ≤ R^2-‖x‖^2 := by nlinarith [sq_nonneg ‖y-linearOuterHead A.nodes A.initial y‖]
  have hs := Real.sq_sqrt hd
  have hsn := Real.sqrt_nonneg (R^2-‖x‖^2)
  nlinarith [norm_nonneg (y-linearOuterHead A.nodes A.initial y)]

def quadraticHead (n : ℕ) (D : Set Node) (hD : Initial D) : QuadraticBlock n →L[ℝ] QuadraticBlock n :=
  (((quadraticBlockEquiv n).symm.toLinearMap.comp (headLM D)).comp (quadraticBlockEquiv n).toLinearMap).mkContinuous
    1 (by
      intro x
      change quadraticBlockCost n (head D (quadraticBlockEquiv n x)) ≤ 1*quadraticBlockCost n (quadraticBlockEquiv n x)
      simpa only [one_mul] using head_quadraticCost_le hD (quadraticBlockEquiv n x))

@[simp] lemma quadraticHead_equiv (n : ℕ) (D : Set Node) (hD : Initial D) (x : QuadraticBlock n) :
    quadraticBlockEquiv n (quadraticHead n D hD x) = head D (quadraticBlockEquiv n x) := rfl

lemma quadraticHead_norm (n : ℕ) (D : Set Node) (hD : Initial D) : ‖quadraticHead n D hD‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change quadraticBlockCost n (head D (quadraticBlockEquiv n x)) ≤ 1*quadraticBlockCost n (quadraticBlockEquiv n x)
  simpa only [one_mul] using head_quadraticCost_le hD (quadraticBlockEquiv n x)

def quadraticOuterHead (D : ℕ → Set Node) (hD : ∀ n, Initial (D n)) : QuadraticOuter →L[ℝ] QuadraticOuter :=
  lp.mapCLM 2 (fun n => quadraticHead (n+1) (D n) (hD n)) zero_le_one
    (fun n => quadraticHead_norm (n+1) (D n) (hD n))

@[simp] lemma quadraticOuterHead_apply (D : ℕ → Set Node) (hD : ∀ n, Initial (D n))
    (x : QuadraticOuter) (n : ℕ) :
    quadraticOuterHead D hD x n = quadraticHead (n+1) (D n) (hD n) (x n) := rfl

lemma quadraticOuterHead_contract (D : ℕ → Set Node) (hD : ∀ n, Initial (D n)) (x : QuadraticOuter) :
    ‖quadraticOuterHead D hD x‖ ≤ ‖x‖ := by
  have hb : ‖quadraticOuterHead D hD‖ ≤ 1 :=
    lp.norm_mapCLM_le 2 _ zero_le_one (fun n => quadraticHead_norm (n+1) (D n) (hD n))
  simpa only [one_mul] using (quadraticOuterHead D hD).le_of_opNorm_le hb x

lemma quadraticOuterHead_idem (D : ℕ → Set Node) (hD : ∀ n, Initial (D n)) (x : QuadraticOuter) :
    quadraticOuterHead D hD (quadraticOuterHead D hD x) = quadraticOuterHead D hD x := by
  apply Subtype.ext
  funext n
  apply (quadraticBlockEquiv (n+1)).injective
  simp only [quadraticOuterHead_apply, quadraticHead_equiv, head_idem]

lemma quadraticOuterTail_bound (D : ℕ → Set Node) (hD : ∀ n, Initial (D n)) (x : QuadraticOuter) :
    ‖x-quadraticOuterHead D hD x‖ ≤ 2*‖x‖ :=
  (norm_sub_le _ _).trans (by linarith [quadraticOuterHead_contract D hD x])

/-- Paired estimates permit arbitrary old-head motion in the displacement. -/
theorem quadraticOuter_midpoint_sq (D : ℕ → Set Node) (hD : ∀ n, Initial (D n))
    (x y : QuadraticOuter) (hx : quadraticOuterHead D hD x = x) :
    ‖x‖^2+‖y-quadraticOuterHead D hD y‖^2/16 ≤ ((‖x+y‖+‖x-y‖)/2)^2 := by
  apply lp_midpoint_sq
  intro n
  have hxn : head (D n) (quadraticBlockEquiv (n+1) (x n)) = quadraticBlockEquiv (n+1) (x n) := by
    have he := congrArg (fun z : QuadraticOuter => quadraticBlockEquiv (n+1) (z n)) hx
    simpa only [quadraticOuterHead_apply, quadraticHead_equiv] using he
  have he := quadratic_midpoint_tail (hD n) (quadraticBlockEquiv (n+1) (x n))
    (quadraticBlockEquiv (n+1) (y n)) hxn
  change Real.sqrt (‖x n‖^2+‖(y-quadraticOuterHead D hD y) n‖^2/16) ≤
    (‖(x+y) n‖+‖(x-y) n‖)/2 at he
  have hs := Real.sq_sqrt (show 0 ≤ ‖x n‖^2+‖(y-quadraticOuterHead D hD y) n‖^2/16 by positivity)
  have hn := Real.sqrt_nonneg (‖x n‖^2+‖(y-quadraticOuterHead D hD y) n‖^2/16)
  nlinarith [norm_nonneg ((x+y) n), norm_nonneg ((x-y) n)]

theorem quadraticOuter_midpoint (D : ℕ → Set Node) (hD : ∀ n, Initial (D n))
    (x y : QuadraticOuter) (hx : quadraticOuterHead D hD x = x) :
    Real.sqrt (‖x‖^2+‖y-quadraticOuterHead D hD y‖^2/16) ≤ (‖x+y‖+‖x-y‖)/2 := by
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by positivity, quadraticOuter_midpoint_sq D hD x y hx⟩

theorem quadraticOuter_tail_four (A : FiniteOuterHead) (x y : QuadraticOuter)
    (hx : quadraticOuterHead A.nodes A.initial x = x) {R : ℝ} (hR : 0 ≤ R)
    (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖y-quadraticOuterHead A.nodes A.initial y‖ ≤ 4*Real.sqrt (R^2-‖x‖^2) := by
  have he := quadraticOuter_midpoint_sq A.nodes A.initial x y hx
  have hb : ‖x‖^2+‖y-quadraticOuterHead A.nodes A.initial y‖^2/16 ≤ R^2 := by
    nlinarith [norm_nonneg (x+y), norm_nonneg (x-y)]
  have hd : 0 ≤ R^2-‖x‖^2 := by nlinarith [sq_nonneg ‖y-quadraticOuterHead A.nodes A.initial y‖]
  have hs := Real.sq_sqrt hd
  have hsn := Real.sqrt_nonneg (R^2-‖x‖^2)
  nlinarith [norm_nonneg (y-quadraticOuterHead A.nodes A.initial y)]

/-- The coefficient-seven tail bound without a head-zero hypothesis on displacement. The inward inequality gives the stronger coefficient four. -/

theorem quadratic_tail_seven (A : FiniteOuterHead) (x y : QuadraticOuter)
    (hx : quadraticOuterHead A.nodes A.initial x = x) {R : ℝ} (hR : 0 ≤ R)
    (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖y-quadraticOuterHead A.nodes A.initial y‖ ≤ 7*Real.sqrt (R^2-‖x‖^2) := by
  have he := quadraticOuter_tail_four A x y hx hR hp hm
  nlinarith [Real.sqrt_nonneg (R^2-‖x‖^2)]

theorem quadratic_tail_eight (A : FiniteOuterHead) (x y : QuadraticOuter)
    (hx : quadraticOuterHead A.nodes A.initial x = x) {R : ℝ} (hR : 0 ≤ R)
    (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖y-quadraticOuterHead A.nodes A.initial y‖ ≤ 8*Real.sqrt (R^2-‖x‖^2) := by
  have he := quadratic_tail_seven A x y hx hR hp hm
  nlinarith [Real.sqrt_nonneg (R^2-‖x‖^2)]

end CostHeads

section ScalarConsequences
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_displacement_le_avg (x y : E) : ‖y‖ ≤ (‖x+y‖+‖x-y‖)/2 := by
  have he : (2:ℝ) • y = (x+y)-(x-y) := by module
  have ht := norm_sub_le (x+y) (x-y)
  rw [← he, norm_smul] at ht
  norm_num at ht
  linarith

lemma norm_center_le_avg (x y : E) : ‖x‖ ≤ (‖x+y‖+‖x-y‖)/2 := by
  have he : (2:ℝ) • x = (x+y)+(x-y) := by module
  have ht := norm_add_le (x+y) (x-y)
  rw [← he, norm_smul] at ht
  norm_num at ht
  linarith

lemma scalar_avg_sq_le {p q R : ℝ} (hp0 : 0 ≤ p) (hq0 : 0 ≤ q)
    (hp : p ≤ R) (hq : q ≤ R) : ((p+q)/2)^2 ≤ R^2 := by
  have hr : 0 ≤ R := hp0.trans hp
  have h1 : 0 ≤ R-(p+q)/2 := by linarith
  have h2 : 0 ≤ R+(p+q)/2 := by positivity
  nlinarith [mul_nonneg h1 h2]

lemma scalar_midpoint_energy {r s p q : ℝ}
    (h : r^2+s^2/16 ≤ ((p+q)/2)^2) :
    s^2 ≤ 16*((p^2+q^2)/2-r^2) := by
  nlinarith [sq_nonneg (p-q)]

lemma scalar_clipping_family {r s R c : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hR : 0 ≤ R) (hc : 0 < c) (h : r^2+s^2/16 ≤ R^2) :
    (r+c*s/2)/Real.sqrt (1+4*c^2) ≤ R := by
  have hd : 0 < Real.sqrt (1+4*c^2) := Real.sqrt_pos.mpr (by positivity)
  apply (div_le_iff₀ hd).mpr
  have he := Real.sq_sqrt (show 0 ≤ 1+4*c^2 by positivity)
  have hp : (r+c*s/2)^2 ≤ R^2*(1+4*c^2) := by
    nlinarith [sq_nonneg (2*c*r-s/4),
      mul_le_mul_of_nonneg_right h (show 0 ≤ 1+4*c^2 by positivity)]
  have hmul : (R*Real.sqrt (1+4*c^2))^2 = R^2*(1+4*c^2) := by rw [mul_pow, he]
  exact (sq_le_sq₀ (add_nonneg hr (div_nonneg (mul_nonneg hc.le hs) (by norm_num)))
    (mul_nonneg hR hd.le)).mp (hp.trans_eq hmul.symm)

lemma scalar_positive_scaled {r s β : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hβ : 0 ≤ β) (h : r^2+s^2/16 ≤ β^2) :
    s^2 ≤ (6*(Real.sqrt 2+1))^2*β*(β-r) ∧
    (6*(Real.sqrt 2+1))^2*β*(β-r) ≤ (6*(Real.sqrt 2+1))^2*(β^2-r^2) := by
  have hrβ : r ≤ β := (sq_le_sq₀ hr hβ).mp
    ((le_add_of_nonneg_right (div_nonneg (pow_nonneg hs 2) (by norm_num))).trans h)
  have hc : (32:ℝ) ≤ (6*(Real.sqrt 2+1))^2 := by
    nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hg : 0 ≤ β*(β-r) := mul_nonneg hβ (sub_nonneg.mpr hrβ)
  have hh : s^2 ≤ 32*(β*(β-r)) := by nlinarith [sq_nonneg (β-r)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hc hg]
  · have he : β*(β-r) ≤ β^2-r^2 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hrβ)]
    nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg (6*(Real.sqrt 2+1)))]

end ScalarConsequences

namespace CostHeads
open TreeCalculus BlockCalculus

theorem linear_head_tail_clipping (A : FiniteOuterHead) (x y : LinearOuter)
    (hx : linearOuterHead A.nodes A.initial x = x)
    (hy : linearOuterHead A.nodes A.initial y = 0) {c : ℝ} (hc : 0 < c) :
    (‖x‖+c*‖y‖/2)/Real.sqrt (1+4*c^2) ≤ max ‖x+y‖ ‖x-y‖ := by
  have he := linearOuter_midpoint_sq A.nodes A.initial x y hx
  rw [hy, sub_zero] at he
  apply scalar_clipping_family (norm_nonneg _) (norm_nonneg _)
    ((norm_nonneg (x+y)).trans (le_max_left _ _)) hc
  have h1 := le_max_left ‖x+y‖ ‖x-y‖
  have h2 := le_max_right ‖x+y‖ ‖x-y‖
  nlinarith [norm_nonneg (x+y), norm_nonneg (x-y)]

theorem linear_fresh_energy_sixteen (A : FiniteOuterHead) (x y : LinearOuter)
    (hx : linearOuterHead A.nodes A.initial x = x) :
    ‖y-linearOuterHead A.nodes A.initial y‖^2 ≤
      16*((‖x+y‖^2+‖x-y‖^2)/2-‖x‖^2) :=
  scalar_midpoint_energy (linearOuter_midpoint_sq A.nodes A.initial x y hx)

theorem linear_fresh_layer_400 (A B : FiniteOuterHead)
    (_hAB : ∀ n, A.nodes n ⊆ B.nodes n) (x y : LinearOuter)
    (hx : linearOuterHead A.nodes A.initial x = x)
    (hy : linearOuterHead B.nodes B.initial y = y) :
    ‖linearOuterHead B.nodes B.initial y-linearOuterHead A.nodes A.initial y‖^2 ≤
      400*((‖x+y‖^2+‖x-y‖^2)/2-‖x‖^2) := by
  rw [hy]
  have he := linear_fresh_energy_sixteen A x y hx
  nlinarith [sq_nonneg ‖y-linearOuterHead A.nodes A.initial y‖]

theorem linear_trimming_242 (A : FiniteOuterHead) (x y : LinearOuter)
    (hx : linearOuterHead A.nodes A.initial x = x)
    (hy : linearOuterHead A.nodes A.initial y = 0) :
    ‖y‖^2 ≤ 242*(‖x+y‖^2+‖x-y‖^2-2*‖x‖^2) := by
  have he := linear_fresh_energy_sixteen A x y hx
  rw [hy, sub_zero] at he
  nlinarith [sq_nonneg ‖y‖]

theorem linear_positive_outer (A : FiniteOuterHead) (x y : LinearOuter)
    (hx : linearOuterHead A.nodes A.initial x = x)
    (hy : linearOuterHead A.nodes A.initial y = 0) :
    ‖y‖^2 ≤ (6*(Real.sqrt 2+1))^2*(‖x+y‖^2+‖x-y‖^2-2*‖x‖^2) := by
  have he := linear_fresh_energy_sixteen A x y hx
  rw [hy, sub_zero] at he
  have hg : 0 ≤ ‖x+y‖^2+‖x-y‖^2-2*‖x‖^2 := by nlinarith [sq_nonneg ‖y‖]
  have hc : (8:ℝ) ≤ (6*(Real.sqrt 2+1))^2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  nlinarith [mul_le_mul_of_nonneg_right hc hg]

theorem quadratic_symmetric_twelve (A : FiniteOuterHead) (x y : QuadraticOuter)
    (hx : quadraticOuterHead A.nodes A.initial x = x)
    (hy : quadraticOuterHead A.nodes A.initial y = 0) :
    ‖x‖^2+‖y‖^2/144 ≤ (‖x+y‖^2+‖x-y‖^2)/2 := by
  have he := scalar_midpoint_energy (quadraticOuter_midpoint_sq A.nodes A.initial x y hx)
  rw [hy, sub_zero] at he
  nlinarith [sq_nonneg ‖y‖]

theorem quadratic_tail_nine (A : FiniteOuterHead) (x y : QuadraticOuter)
    (hx : quadraticOuterHead A.nodes A.initial x = x) {R : ℝ} (hR : 0 ≤ R)
    (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖y-quadraticOuterHead A.nodes A.initial y‖ ≤ 9*Real.sqrt (R^2-‖x‖^2) := by
  have he := quadratic_tail_seven A x y hx hR hp hm
  nlinarith [Real.sqrt_nonneg (R^2-‖x‖^2)]

end CostHeads

namespace BlockCalculus
open TreeCalculus

lemma linear_block_midpoint_sq {n : ℕ} {D : Set Node} (hD : Initial D) (x y : TreeHilbert n)
    (hx : head D x = x) :
    (linearBlockCost n x)^2+(linearBlockCost n (y-head D y))^2/16 ≤
      ((linearBlockCost n (x+y)+linearBlockCost n (x-y))/2)^2 := by
  have he := linear_midpoint_tail hD x y hx
  have hs := Real.sq_sqrt (show 0 ≤ (linearBlockCost n x)^2+(linearBlockCost n (y-head D y))^2/16 by positivity)
  have hn := Real.sqrt_nonneg ((linearBlockCost n x)^2+(linearBlockCost n (y-head D y))^2/16)
  nlinarith [linearCost_nonneg (pathSynthesis n) (x+y), linearCost_nonneg (pathSynthesis n) (x-y)]

theorem linear_positive_scaled {n : ℕ} {D : Set Node} (hD : Initial D) (x y : TreeHilbert n)
    (hx : head D x = x) (hy : head D y = 0) :
    let β := max (linearBlockCost n (x+y)) (linearBlockCost n (x-y))
    (linearBlockCost n y)^2 ≤ (6*(Real.sqrt 2+1))^2*β*(β-linearBlockCost n x) ∧
      (6*(Real.sqrt 2+1))^2*β*(β-linearBlockCost n x) ≤
      (6*(Real.sqrt 2+1))^2*(β^2-(linearBlockCost n x)^2) := by
  dsimp only
  apply scalar_positive_scaled (linearCost_nonneg _ _) (linearCost_nonneg _ _)
    ((linearCost_nonneg _ _).trans (le_max_left _ _))
  have he := linear_block_midpoint_sq hD x y hx
  rw [hy, sub_zero] at he
  have hp := le_max_left (linearBlockCost n (x+y)) (linearBlockCost n (x-y))
  have hm := le_max_right (linearBlockCost n (x+y)) (linearBlockCost n (x-y))
  exact he.trans (scalar_avg_sq_le (linearCost_nonneg _ _) (linearCost_nonneg _ _) hp hm)

theorem linear_positive_unit {n : ℕ} {D : Set Node} (hD : Initial D) (x y : TreeHilbert n)
    (hx : head D x = x) (hy : head D y = 0)
    (hp : linearBlockCost n (x+y) ≤ 1) (hm : linearBlockCost n (x-y) ≤ 1) :
    linearBlockCost n y ≤ 6*(Real.sqrt 2+1)*Real.sqrt (1-linearBlockCost n x) := by
  have he := linear_block_midpoint_sq hD x y hx
  rw [hy, sub_zero] at he
  have hav := scalar_avg_sq_le (linearCost_nonneg (pathSynthesis n) (x+y)) (linearCost_nonneg (pathSynthesis n) (x-y)) hp hm
  change ((linearBlockCost n (x+y)+linearBlockCost n (x-y))/2)^2 ≤ (1:ℝ)^2 at hav
  have hr : 0 ≤ linearBlockCost n x := linearCost_nonneg (pathSynthesis n) x
  have hs : 0 ≤ linearBlockCost n y := linearCost_nonneg (pathSynthesis n) y
  have hr1 : linearBlockCost n x ≤ 1 := by
    nlinarith [linearCost_nonneg (pathSynthesis n) (x+y), linearCost_nonneg (pathSynthesis n) (x-y), sq_nonneg (linearBlockCost n y)]
  have hgap : (linearBlockCost n y)^2 ≤ 32*(1-linearBlockCost n x) := by
    nlinarith [sq_nonneg (1-linearBlockCost n x), linearCost_nonneg (pathSynthesis n) (x+y), linearCost_nonneg (pathSynthesis n) (x-y)]
  have hc : (32:ℝ) ≤ (6*(Real.sqrt 2+1))^2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hd := Real.sq_sqrt (sub_nonneg.mpr hr1)
  have hn := Real.sqrt_nonneg (1-linearBlockCost n x)
  have hmul := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hr1)
  have hsq : (6*(Real.sqrt 2+1)*Real.sqrt (1-linearBlockCost n x))^2 ≥ (linearBlockCost n y)^2 := by
    rw [mul_pow, hd]; nlinarith
  nlinarith [mul_nonneg (show 0 ≤ 6*(Real.sqrt 2+1) by positivity) hn]

theorem linear_bottom_up_tail {n : ℕ} {D : Set Node} (hD : Initial D) (x y : TreeHilbert n)
    (hx : head D x = x) (hy : head D y = 0) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hp : linearBlockCost n (x+y) ≤ 1) (hm : linearBlockCost n (x-y) ≤ 1)
    (hr : 1-ε ≤ linearBlockCost n x) :
    linearBlockCost n y ≤ 3*Real.sqrt (2*ε)+8*ε := by
  have hav := scalar_avg_sq_le (linearCost_nonneg (pathSynthesis n) (x+y)) (linearCost_nonneg (pathSynthesis n) (x-y)) hp hm
  change ((linearBlockCost n (x+y)+linearBlockCost n (x-y))/2)^2 ≤ (1:ℝ)^2 at hav
  have hy0 : 0 ≤ linearBlockCost n y := linearCost_nonneg (pathSynthesis n) y
  have hx0 : 0 ≤ linearBlockCost n x := linearCost_nonneg (pathSynthesis n) x
  have hs := Real.sq_sqrt hε
  have hs0 := Real.sqrt_nonneg ε
  have ht := Real.sq_sqrt (show 0 ≤ 2*ε by positivity)
  have ht0 := Real.sqrt_nonneg (2*ε)
  by_cases hz : ε = 0
  · have he := linear_block_midpoint_sq hD x y hx
    rw [hy, sub_zero] at he
    rw [hz] at hr ⊢
    norm_num
    nlinarith [linearCost_nonneg (pathSynthesis n) (x+y), linearCost_nonneg (pathSynthesis n) (x-y)]
  by_cases hsmall : ε ≤ 1/4
  · have hsp : 0 < Real.sqrt ε := Real.sqrt_pos.mpr (lt_of_le_of_ne hε (Ne.symm hz))
    have he := linear_paired_unit hD x y hx (a := 1-ε) (b := Real.sqrt ε)
      (by linarith) (by linarith) hs0 (by nlinarith) (by nlinarith)
    rw [hy, sub_zero] at he
    have hrr : (1-ε)^2 ≤ (1-ε)*linearBlockCost n x := by
      nlinarith [mul_le_mul_of_nonneg_left hr (show 0 ≤ 1-ε by linarith)]
    have hy4 : linearBlockCost n y ≤ 4*Real.sqrt ε := by nlinarith [sq_nonneg ε]
    have hfour : 4*Real.sqrt ε ≤ 3*Real.sqrt (2*ε) := by nlinarith
    linarith
  · have he := norm_displacement_le_avg ((linearBlockEquiv n).symm x) ((linearBlockEquiv n).symm y)
    change linearBlockCost n y ≤ (linearBlockCost n (x+y)+linearBlockCost n (x-y))/2 at he
    linarith

end BlockCalculus


end BoundedTreePotentials

end

end OAI
