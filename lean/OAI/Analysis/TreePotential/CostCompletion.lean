import OAI.Analysis.TreePotential.Coordinates

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

namespace CostHeads
open TreeCalculus BlockCalculus ForestCoordinates Filter Topology
open scoped Classical

lemma linear_coefficient_head (A : FiniteOuterHead) (x : LinearOuter) (s : ForestNode) :
    coefficient (fun n => linearBlockHilbertEquiv (n+1)) (linearOuterHead A.nodes A.initial x) s =
    if s.2.val ∈ A.nodes s.1 then coefficient (fun n => linearBlockHilbertEquiv (n+1)) x s else 0 := rfl

lemma linear_head_eq_self_iff (A : FiniteOuterHead) (x : LinearOuter) :
    linearOuterHead A.nodes A.initial x = x ↔ ∀ s : ForestNode,
      s.2.val ∉ A.nodes s.1 → coefficient (fun n => linearBlockHilbertEquiv (n+1)) x s = 0 := by
  constructor
  · intro h s hs
    have he := congrArg (fun z => coefficient (fun n => linearBlockHilbertEquiv (n+1)) z s) h
    rw [linear_coefficient_head, ite_eq_right hs] at he
    exact he.symm
  · intro h
    apply coefficient_ext (fun n => linearBlockHilbertEquiv (n+1))
    intro s
    rw [linear_coefficient_head]
    split_ifs with hs
    · rfl
    · exact (h s hs).symm

lemma linear_head_eq_zero_iff (A : FiniteOuterHead) (x : LinearOuter) :
    linearOuterHead A.nodes A.initial x = 0 ↔ ∀ s : ForestNode,
      s.2.val ∈ A.nodes s.1 → coefficient (fun n => linearBlockHilbertEquiv (n+1)) x s = 0 := by
  constructor
  · intro h s hs
    have he := congrArg (fun z => coefficient (fun n => linearBlockHilbertEquiv (n+1)) z s) h
    rw [linear_coefficient_head, ite_eq_left hs, coefficient_zero] at he
    exact he
  · intro h
    apply coefficient_ext (fun n => linearBlockHilbertEquiv (n+1))
    intro s
    rw [linear_coefficient_head, coefficient_zero]
    split_ifs with hs
    · exact h s hs
    · rfl

lemma linear_finite_head_approx (x : LinearOuter) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : LinearOuter, ∃ A : FiniteOuterHead, ‖x-p‖ < ε ∧ linearOuterHead A.nodes A.initial p = p := by
  obtain ⟨p,A,hd,hp⟩ := exists_finite_head_approx (fun n => linearBlockHilbertEquiv (n+1)) x hε
  exact ⟨p,A,hd,(linear_head_eq_self_iff A p).mpr hp⟩

def linearCoordinateTail (A : FiniteOuterHead) : ClosedFiniteCodim LinearOuter :=
  ForestCoordinates.coordinateTail (fun n => linearBlockHilbertEquiv (n+1)) A

lemma mem_linearCoordinateTail (A : FiniteOuterHead) (x : LinearOuter) :
    x ∈ (linearCoordinateTail A).space ↔ linearOuterHead A.nodes A.initial x = 0 := by
  exact (ForestCoordinates.mem_coordinateTail (fun n => linearBlockHilbertEquiv (n+1)) A x).trans
    (linear_head_eq_zero_iff A x).symm

lemma linear_head_ker (A : FiniteOuterHead) :
    (linearOuterHead A.nodes A.initial).ker = (linearCoordinateTail A).space := by
  ext x
  exact (mem_linearCoordinateTail A x).symm

instance linear_head_finiteRank (A : FiniteOuterHead) :
    Module.Finite ℝ (linearOuterHead A.nodes A.initial).range := by
  have h : Module.Finite ℝ (LinearOuter ⧸ (linearOuterHead A.nodes A.initial).ker) := by
    rw [linear_head_ker]
    exact (linearCoordinateTail A).finiteCodim
  let := h
  exact Module.Finite.equiv (linearOuterHead A.nodes A.initial).toLinearMap.quotKerEquivRange

lemma linear_head_weaklyNull {y : ℕ → LinearOuter} (hy : WeaklyNull y) (A : FiniteOuterHead) :
    Tendsto (fun j => ‖linearOuterHead A.nodes A.initial (y j)‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he := hy.approximable (linearCoordinateTail A) hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N, ?_⟩
  intro j hj
  obtain ⟨w,hw,hd⟩ := hN j hj
  have hw0 := (mem_linearCoordinateTail A w).mp hw
  have hh := linearOuterHead_contract A.nodes A.initial (y j-w)
  rw [map_sub, hw0, sub_zero] at hh
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_norm] using hh.trans_lt hd

lemma quadratic_coefficient_head (A : FiniteOuterHead) (x : QuadraticOuter) (s : ForestNode) :
    coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) (quadraticOuterHead A.nodes A.initial x) s =
    if s.2.val ∈ A.nodes s.1 then coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) x s else 0 := rfl

lemma quadratic_head_eq_self_iff (A : FiniteOuterHead) (x : QuadraticOuter) :
    quadraticOuterHead A.nodes A.initial x = x ↔ ∀ s : ForestNode,
      s.2.val ∉ A.nodes s.1 → coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) x s = 0 := by
  constructor
  · intro h s hs
    have he := congrArg (fun z => coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) z s) h
    rw [quadratic_coefficient_head, ite_eq_right hs] at he
    exact he.symm
  · intro h
    apply coefficient_ext (fun n => quadraticBlockHilbertEquiv (n+1))
    intro s
    rw [quadratic_coefficient_head]
    split_ifs with hs
    · rfl
    · exact (h s hs).symm

lemma quadratic_head_eq_zero_iff (A : FiniteOuterHead) (x : QuadraticOuter) :
    quadraticOuterHead A.nodes A.initial x = 0 ↔ ∀ s : ForestNode,
      s.2.val ∈ A.nodes s.1 → coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) x s = 0 := by
  constructor
  · intro h s hs
    have he := congrArg (fun z => coefficient (fun n => quadraticBlockHilbertEquiv (n+1)) z s) h
    rw [quadratic_coefficient_head, ite_eq_left hs, coefficient_zero] at he
    exact he
  · intro h
    apply coefficient_ext (fun n => quadraticBlockHilbertEquiv (n+1))
    intro s
    rw [quadratic_coefficient_head, coefficient_zero]
    split_ifs with hs
    · exact h s hs
    · rfl

lemma quadratic_finite_head_approx (x : QuadraticOuter) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : QuadraticOuter, ∃ A : FiniteOuterHead, ‖x-p‖ < ε ∧ quadraticOuterHead A.nodes A.initial p = p := by
  obtain ⟨p,A,hd,hp⟩ := exists_finite_head_approx (fun n => quadraticBlockHilbertEquiv (n+1)) x hε
  exact ⟨p,A,hd,(quadratic_head_eq_self_iff A p).mpr hp⟩

def quadraticCoordinateTail (A : FiniteOuterHead) : ClosedFiniteCodim QuadraticOuter :=
  ForestCoordinates.coordinateTail (fun n => quadraticBlockHilbertEquiv (n+1)) A

lemma mem_quadraticCoordinateTail (A : FiniteOuterHead) (x : QuadraticOuter) :
    x ∈ (quadraticCoordinateTail A).space ↔ quadraticOuterHead A.nodes A.initial x = 0 := by
  exact (ForestCoordinates.mem_coordinateTail (fun n => quadraticBlockHilbertEquiv (n+1)) A x).trans
    (quadratic_head_eq_zero_iff A x).symm

lemma quadratic_head_ker (A : FiniteOuterHead) :
    (quadraticOuterHead A.nodes A.initial).ker = (quadraticCoordinateTail A).space := by
  ext x
  exact (mem_quadraticCoordinateTail A x).symm

instance quadratic_head_finiteRank (A : FiniteOuterHead) :
    Module.Finite ℝ (quadraticOuterHead A.nodes A.initial).range := by
  have h : Module.Finite ℝ (QuadraticOuter ⧸ (quadraticOuterHead A.nodes A.initial).ker) := by
    rw [quadratic_head_ker]
    exact (quadraticCoordinateTail A).finiteCodim
  let := h
  exact Module.Finite.equiv (quadraticOuterHead A.nodes A.initial).toLinearMap.quotKerEquivRange

lemma quadratic_head_weaklyNull {y : ℕ → QuadraticOuter} (hy : WeaklyNull y) (A : FiniteOuterHead) :
    Tendsto (fun j => ‖quadraticOuterHead A.nodes A.initial (y j)‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he := hy.approximable (quadraticCoordinateTail A) hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N, ?_⟩
  intro j hj
  obtain ⟨w,hw,hd⟩ := hN j hj
  have hw0 := (mem_quadraticCoordinateTail A w).mp hw
  have hh := quadraticOuterHead_contract A.nodes A.initial (y j-w)
  rw [map_sub, hw0, sub_zero] at hh
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_norm] using hh.trans_lt hd

end CostHeads

lemma sqrt_shift {r R d c : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) (hd : 0 ≤ d)
    (hc : 0 ≤ c) (hh : r ≤ R+d) :
    Real.sqrt (r^2+c) ≤ Real.sqrt (R^2+c)+d := by
  have hs := Real.sq_sqrt (show 0 ≤ R^2+c by positivity)
  have hn := Real.sqrt_nonneg (R^2+c)
  have hRT : R ≤ Real.sqrt (R^2+c) := by nlinarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hrhs : r^2 ≤ (R+d)^2 := by nlinarith [mul_nonneg (show 0 ≤ R+d-r by linarith) (show 0 ≤ R+d+r by positivity)]
  nlinarith [mul_nonneg hd (sub_nonneg.mpr hRT)]

section FiniteRankCompactness
open Filter Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma finiteRank_close_pair (P : E →L[ℝ] F) [Module.Finite ℝ P.range]
    (y : ℕ → E) {R ε : ℝ} (hR : ∀ j, ‖y j‖ ≤ R) (hε : 0 < ε) :
    ∃ i j : ℕ, i ≠ j ∧ ‖P (y i)-P (y j)‖ < ε := by
  let z : ℕ → P.range := fun j => ⟨P (y j), ⟨y j,rfl⟩⟩
  have hz : ∀ j, z j ∈ Metric.closedBall (0 : P.range) (‖P‖*R) := by
    intro j
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hR j) (norm_nonneg P))
  obtain ⟨a,ha,φ,hφ,hlim⟩ := (isCompact_closedBall (0 : P.range) (‖P‖*R)).tendsto_subseq hz
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim (ε/2) (by positivity)
  refine ⟨φ N, φ (N+1), (hφ (Nat.lt_succ_self N)).ne, ?_⟩
  have h1 := hN N le_rfl
  have h2 := hN (N+1) (Nat.le_succ N)
  have ht := dist_triangle (z (φ N)) a (z (φ (N+1)))
  rw [dist_comm a] at ht
  rw [dist_eq_norm] at ht
  change ‖P (y (φ N))-P (y (φ (N+1)))‖ ≤ _ at ht
  change dist (z (φ N)) a < ε/2 at h1
  change dist (z (φ (N+1))) a < ε/2 at h2
  linarith

end FiniteRankCompactness

namespace CostHeads
open TreeCalculus BlockCalculus ForestCoordinates Filter Topology
open scoped Classical

/-- Transfer from finite centers to arbitrary completed centers, uniformly on
an entire closed finite-codimensional tail. -/
theorem linear_completed_tail_bound (x : LinearOuter) (hx : ‖x‖ = 1)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∃ F : ClosedFiniteCodim LinearOuter, ∀ y, y ∈ F.space → 1 ≤ ‖y‖ →
      Real.sqrt (1+t^2/16)-1-ε ≤ (‖x+t • y‖+‖x-t • y‖)/2-1 := by
  obtain ⟨p,A,hp,hA⟩ := linear_finite_head_approx x (show 0 < ε/2 by positivity)
  refine ⟨linearCoordinateTail A, ?_⟩
  intro y hy hyn
  have hy0 := (mem_linearCoordinateTail A y).mp hy
  have he := linearOuter_midpoint A.nodes A.initial p (t • y) hA
  rw [map_smul, hy0, smul_zero, sub_zero, norm_smul, Real.norm_of_nonneg ht.le] at he
  have hnorm : 1 ≤ ‖p‖+‖x-p‖ := by
    have hh := norm_sub_norm_le x p
    rw [hx] at hh
    linarith
  have hs := sqrt_shift zero_le_one (norm_nonneg p) (norm_nonneg (x-p))
    (show 0 ≤ t^2/16 by positivity) hnorm
  norm_num only [one_pow] at hs
  have hyb : Real.sqrt (‖p‖^2+t^2/16) ≤ Real.sqrt (‖p‖^2+(t*‖y‖)^2/16) := by
    apply Real.sqrt_le_sqrt
    have hh : t ≤ t*‖y‖ := by nlinarith
    nlinarith [norm_nonneg y]
  have hppert := midpoint_center_perturbation x p y t
  rw [norm_sub_rev p x] at hppert
  linarith

theorem linear_averaged_modulus {t : ℝ} (ht : 0 < t) :
    ((Real.sqrt (1+t^2/16)-1 : ℝ) : EReal) ≤ averagedModulus LinearOuter t := by
  apply averagedModulus_lower_bound
  intro x hx ε hε
  exact linear_completed_tail_bound x hx ht hε

/-- Transfer from finite centers to arbitrary completed centers, uniformly on
an entire closed finite-codimensional tail. -/
theorem quadratic_completed_tail_bound (x : QuadraticOuter) (hx : ‖x‖ = 1)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∃ F : ClosedFiniteCodim QuadraticOuter, ∀ y, y ∈ F.space → 1 ≤ ‖y‖ →
      Real.sqrt (1+t^2/16)-1-ε ≤ (‖x+t • y‖+‖x-t • y‖)/2-1 := by
  obtain ⟨p,A,hp,hA⟩ := quadratic_finite_head_approx x (show 0 < ε/2 by positivity)
  refine ⟨quadraticCoordinateTail A, ?_⟩
  intro y hy hyn
  have hy0 := (mem_quadraticCoordinateTail A y).mp hy
  have he := quadraticOuter_midpoint A.nodes A.initial p (t • y) hA
  rw [map_smul, hy0, smul_zero, sub_zero, norm_smul, Real.norm_of_nonneg ht.le] at he
  have hnorm : 1 ≤ ‖p‖+‖x-p‖ := by
    have hh := norm_sub_norm_le x p
    rw [hx] at hh
    linarith
  have hs := sqrt_shift zero_le_one (norm_nonneg p) (norm_nonneg (x-p))
    (show 0 ≤ t^2/16 by positivity) hnorm
  norm_num only [one_pow] at hs
  have hyb : Real.sqrt (‖p‖^2+t^2/16) ≤ Real.sqrt (‖p‖^2+(t*‖y‖)^2/16) := by
    apply Real.sqrt_le_sqrt
    have hh : t ≤ t*‖y‖ := by nlinarith
    nlinarith [norm_nonneg y]
  have hppert := midpoint_center_perturbation x p y t
  rw [norm_sub_rev p x] at hppert
  linarith

theorem quadratic_averaged_modulus {t : ℝ} (ht : 0 < t) :
    ((Real.sqrt (1+t^2/16)-1 : ℝ) : EReal) ≤ averagedModulus QuadraticOuter t := by
  apply averagedModulus_lower_bound
  intro x hx ε hε
  exact quadratic_completed_tail_bound x hx ht hε

end CostHeads


end BoundedTreePotentials

end

end OAI
