import OAI.Analysis.FreeGroupFactor.GlobalODE

namespace OAI

noncomputable section

universe uA uι

open Set Metric
open scoped NNReal Topology BigOperators

open scoped BigOperators ContDiff
namespace FreeGroupFactorMain
namespace PolynomialFlow

section

variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def wordList (w : List (ι × Bool)) (X : ι → A) : A :=
  (w.map (fun ib => if ib.2 then X ib.1 else star (X ib.1))).prod

def word (g : FreeGroup ι) (X : ι → A) : A := wordList g.toWord X

def hamiltonian (S : A) (h : FreeGroup ι →₀ ℝ) (X : ι → A) : A :=
  h.sum (fun g c => (c : ℂ) • (word g X * S * star (word g X)))

def field (S : A) (h : ι → FreeGroup ι →₀ ℝ) (X : ι → A) : ι → A :=
  fun j => Complex.I • (hamiltonian S (h j) X * X j)

 omit [DecidableEq ι] in
 theorem smooth_wordList (w : List (ι × Bool)) :
    ContDiff ℝ ∞ (wordList (A := A) w) := by
  induction w with
  | nil =>
    change ContDiff ℝ ∞ (fun _ : ι → A => (1 : A))
    exact contDiff_const
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    cases b
    · change ContDiff ℝ ∞ (fun X : ι → A => star (X i) * wordList w X)
      exact ((starL ℝ (A := A)).contDiff.comp (contDiff_apply ℝ A i)).mul ih
    · change ContDiff ℝ ∞ (fun X : ι → A => X i * wordList w X)
      exact (contDiff_apply ℝ A i).mul ih

 theorem smooth_word (g : FreeGroup ι) : ContDiff ℝ ∞ (word (A := A) g) :=
  smooth_wordList _

 theorem smooth_hamiltonian (S : A) (h : FreeGroup ι →₀ ℝ) :
    ContDiff ℝ ∞ (hamiltonian S h) := by
  classical
  unfold hamiltonian Finsupp.sum
  apply ContDiff.sum
  intro g hg
  exact (contDiff_const (c := (h g : ℂ))).smul
    (((smooth_word (A := A) g).mul (contDiff_const (c := S))).mul
      ((starL ℝ (A := A)).contDiff.comp (smooth_word (A := A) g)))

 theorem smooth_field (S : A) (h : ι → FreeGroup ι →₀ ℝ) :
    ContDiff ℝ ∞ (field S h) := by
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_const (c := Complex.I)).smul
    ((smooth_hamiltonian S (h j)).mul (contDiff_apply ℝ A j))

 omit [Fintype ι] in
 theorem selfAdjoint_hamiltonian (S : A) (hS : IsSelfAdjoint S)
    (h : FreeGroup ι →₀ ℝ) (X : ι → A) : IsSelfAdjoint (hamiltonian S h X) := by
  classical
  unfold hamiltonian Finsupp.sum
  change star (∑ g ∈ h.support, (h g : ℂ) • (word g X * S * star (word g X))) = _
  simp only [star_sum, star_smul, Complex.star_def, Complex.conj_ofReal, star_mul, star_star, hS.star_eq, mul_assoc]

 theorem local_solution (S : A) (h : ι → FreeGroup ι →₀ ℝ)
    (V : ι → A) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ X : ℝ → ι → A, X t₀ = V ∧
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), HasDerivAt X (field S h (X t)) t := by
  obtain ⟨X, hX, ε, hε, hd⟩ :=
    ((smooth_field S h).of_le (show (1 : WithTop ℕ∞) ≤ ∞ from by simp)).contDiffAt
      (x := V) |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  exact ⟨ε, hε, X, hX, hd⟩

omit [Fintype ι] in

 theorem tangent_star_mul (S : A) (hS : IsSelfAdjoint S)
    (h : ι → FreeGroup ι →₀ ℝ) (X : ι → A) (j : ι) :
    star (field S h X j) * X j + star (X j) * field S h X j = 0 := by
  simp only [field, star_smul, star_mul, (selfAdjoint_hamiltonian S hS (h j) X).star_eq,
    Complex.star_def, Complex.conj_I, neg_smul, neg_mul, smul_mul_assoc,
    mul_smul_comm, mul_assoc]
  exact neg_add_cancel _

 omit [Fintype ι] in
 theorem solution_star_mul_derivative (S : A) (hS : IsSelfAdjoint S)
    (h : ι → FreeGroup ι →₀ ℝ) {X : ℝ → ι → A} {t : ℝ}
    (hX : HasDerivAt X (field S h (X t)) t) (j : ι) :
    HasDerivAt (fun u => star (X u j) * X u j) 0 t := by
  have hj := hasDerivAt_pi.mp hX j
  convert! hj.star.mul hj using 1
  exact (tangent_star_mul S hS h (X t) j).symm

 omit [Fintype ι] in
 theorem solution_star_mul_constant (S : A) (hS : IsSelfAdjoint S)
    (h : ι → FreeGroup ι →₀ ℝ) {X : ℝ → ι → A} {a b : ℝ}
    (hX : ∀ t ∈ Set.Ioo a b, HasDerivAt X (field S h (X t)) t)
    {t u : ℝ} (ht : t ∈ Set.Ioo a b) (hu : u ∈ Set.Ioo a b) (j : ι) :
    star (X t j) * X t j = star (X u j) * X u j := by
  have hd (v : ℝ) (hv : v ∈ Set.Ioo a b) :=
    solution_star_mul_derivative S hS h (hX v hv) j
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun v hv => (hd v hv).differentiableAt.differentiableWithinAt)
    (fun v hv => (hd v hv).deriv) ht hu

theorem local_unitary_solution (S : A) (hS : IsSelfAdjoint S)
    (h : ι → FreeGroup ι →₀ ℝ) (V : ι → A)
    (hV : ∀ j, V j ∈ unitary A) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ X : ℝ → ι → A, X t₀ = V ∧
      (∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), HasDerivAt X (field S h (X t)) t) ∧
      (∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), ∀ j, X t j ∈ unitary A) := by
  obtain ⟨ε, hε, X, hX₀, hX⟩ := local_solution S h V t₀
  have ht₀ : t₀ ∈ Set.Ioo (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
  have hinv : ∀ᶠ t in nhds t₀, ∀ j, IsUnit (X t j) := by
    rw [Filter.eventually_all]
    intro j
    have hj := (hasDerivAt_pi.mp (hX t₀ ht₀) j).continuousAt
    apply hj.eventually
    apply Units.isOpen.mem_nhds
    change IsUnit (X t₀ j)
    rw [hX₀]
    exact Unitary.isUnit_coe (U := ⟨V j, hV j⟩)
  obtain ⟨ρ, hρ, hinv⟩ := Metric.eventually_nhds_iff.mp hinv
  refine ⟨min ε ρ, lt_min hε hρ, X, hX₀, ?_, ?_⟩
  · intro t ht
    apply hX t
    constructor <;> have := min_le_left ε ρ <;> rcases ht with ⟨htl, htr⟩ <;> linarith
  · intro t ht j
    have htε : t ∈ Set.Ioo (t₀ - ε) (t₀ + ε) := by
      constructor <;> have := min_le_left ε ρ <;> rcases ht with ⟨htl, htr⟩ <;> linarith
    have hdist : dist t t₀ < ρ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> have := min_le_right ε ρ <;> rcases ht with ⟨htl, htr⟩ <;> linarith
    apply (hinv hdist j).mem_unitary_of_star_mul_self
    rw [solution_star_mul_constant S hS h hX htε ht₀ j, hX₀]
    exact (Unitary.mem_iff.mp (hV j)).1

end

section
open scoped NNReal BigOperators
variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem boundedLip_clip_coordinate (j : ι) :
    BoundedLip (fun X : ι → A => radialClip X j) := by
  refine ⟨1, 2, by positivity, by positivity, ?_, ?_⟩
  · intro X
    exact (norm_le_pi_norm (radialClip X) j).trans (norm_radialClip_le X)
  · intro X Y
    exact (norm_le_pi_norm (radialClip X - radialClip Y) j).trans
      (by simpa only [dist_eq_norm, NNReal.coe_ofNat] using radialClip_lipschitz.dist_le_mul X Y)

omit [DecidableEq ι] in
theorem boundedLip_clip_wordList (w : List (ι × Bool)) :
    BoundedLip (fun X : ι → A => wordList w (radialClip X)) := by
  induction w with
  | nil => exact BoundedLip.const 1
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    cases b
    · exact (boundedLip_clip_coordinate i).star.mul ih
    · exact (boundedLip_clip_coordinate i).mul ih

theorem boundedLip_clip_word (g : FreeGroup ι) :
    BoundedLip (fun X : ι → A => word g (radialClip X)) :=
  boundedLip_clip_wordList _

theorem boundedLip_clip_hamiltonian (S : A) (h : FreeGroup ι →₀ ℝ) :
    BoundedLip (fun X : ι → A => hamiltonian S h (radialClip X)) := by
  classical
  unfold hamiltonian Finsupp.sum
  apply BoundedLip.sum
  intro g hg
  exact ((boundedLip_clip_word g).mul (BoundedLip.const S) |>.mul
    (boundedLip_clip_word g).star).smul (h g : ℂ)

theorem boundedLip_clip_field (S : A) (h : ι → FreeGroup ι →₀ ℝ) :
    BoundedLip (fun X => field S h (radialClip X)) := by
  apply BoundedLip.pi
  intro j
  exact ((boundedLip_clip_hamiltonian S (h j)).mul
    (boundedLip_clip_coordinate j)).smul Complex.I

theorem tangent_clipped (S : A) (hS : IsSelfAdjoint S)
    (h : ι → FreeGroup ι →₀ ℝ) (X : ι → A) (j : ι) :
    star (field S h (radialClip X) j) * X j +
      star (X j) * field S h (radialClip X) j = 0 := by
  let r : ℝ := (max 1 ‖X‖)⁻¹
  have he : radialClip X j = r • X j := rfl
  simp only [field, he, mul_smul_comm, smul_comm Complex.I r, star_smul,
    star_trivial, star_mul, (selfAdjoint_hamiltonian S hS (h j) (radialClip X)).star_eq,
    Complex.star_def, Complex.conj_I, neg_smul, neg_mul, smul_mul_assoc,
    mul_assoc]
  module

theorem global_unitary_solution [Nontrivial A]
    (S : A) (hS : IsSelfAdjoint S) (h : ι → FreeGroup ι →₀ ℝ)
    (V : ι → A) (hV : ∀ j, V j ∈ unitary A) :
    ∃ X : ℝ → ι → A, X 0 = V ∧
      (∀ t, HasDerivAt X (field S h (X t)) t) ∧
      ∀ t j, X t j ∈ unitary A := by
  obtain ⟨M, K, hb, hl⟩ := (boundedLip_clip_field S h).to_bounds
  obtain ⟨X, hX₀, hX⟩ := global_solution_of_bounded_lipschitz
    (fun X => field S h (radialClip X)) K M hl hb V
  have hd (j : ι) (t : ℝ) :
      HasDerivAt (fun u => star (X u j) * X u j) 0 t := by
    have hj := hasDerivAt_pi.mp (hX t) j
    convert! hj.star.mul hj using 1
    exact (tangent_clipped S hS h (X t) j).symm
  have hisom (t : ℝ) (j : ι) : star (X t j) * X t j = 1 := by
    have he := is_const_of_deriv_eq_zero (fun u => (hd j u).differentiableAt)
      (fun u => (hd j u).deriv) t 0
    rw [he, hX₀]
    exact (Unitary.mem_iff.mp (hV j)).1
  have hn (t : ℝ) : ‖X t‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    have he := congrArg norm (hisom t j)
    rw [CStarRing.norm_star_mul_self, norm_one] at he
    nlinarith [norm_nonneg (X t j)]
  have hder (t : ℝ) : HasDerivAt X (field S h (X t)) t := by
    simpa only [radialClip_eq (hn t)] using hX t
  refine ⟨X, hX₀, hder, ?_⟩
  intro t j
  have hc : Continuous (fun u => X u j) :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_pi.mp (hder u) j).continuousAt
  have hset : {u | X u j ∈ unitary A} = {u | IsUnit (X u j)} := by
    ext u
    constructor
    · intro hu
      exact Unitary.isUnit_coe (U := ⟨X u j, hu⟩)
    · exact fun hu => hu.mem_unitary_of_star_mul_self (hisom u j)
  have hcl : IsClosed {u | X u j ∈ unitary A} := isClosed_unitary.preimage hc
  have hop : IsOpen {u | X u j ∈ unitary A} := by
    rw [hset]
    exact Units.isOpen.preimage hc
  have hall := (IsClopen.eq_univ ⟨hcl, hop⟩ ⟨0, by change X 0 j ∈ unitary A; rw [hX₀]; exact hV j⟩)
  exact (show t ∈ {u | X u j ∈ unitary A} from by rw [hall]; trivial)

end

variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

theorem smooth_solution (S : A) (h : ι → FreeGroup ι →₀ ℝ)
    (X : ℝ → ι → A) (hX : ∀ t, HasDerivAt X (field S h (X t)) t) :
    ContDiff ℝ ∞ X := by
  have hdiff : Differentiable ℝ X := fun t => (hX t).differentiableAt
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hdiff.continuous
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨hdiff, by simp, ?_⟩
    have heq : deriv X = fun t => field S h (X t) := funext fun t => (hX t).deriv
    rw [heq]
    exact (contDiff_infty.mp (smooth_field S h) n).comp ih

omit [DecidableEq ι] in
theorem norm_unitary_tuple_le [Nontrivial A] (V : ι → A)
    (hV : ∀ j, V j ∈ unitary A) : ‖V‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  exact (CStarRing.norm_of_mem_unitary (hV j)).le

theorem unitary_solutions_unique [Nontrivial A]
    (S : A) (h : ι → FreeGroup ι →₀ ℝ) (X Y : ℝ → ι → A)
    (hX : ∀ t, HasDerivAt X (field S h (X t)) t)
    (hY : ∀ t, HasDerivAt Y (field S h (Y t)) t)
    (hUX : ∀ t j, X t j ∈ unitary A) (hUY : ∀ t j, Y t j ∈ unitary A)
    (t₀ : ℝ) (hinit : X t₀ = Y t₀) : X = Y := by
  obtain ⟨M, K, _hb, hl⟩ := (boundedLip_clip_field S h).to_bounds
  funext t
  let R := |t| + |t₀| + 1
  have ht : t ∈ Set.Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [neg_abs_le t, le_abs_self t, abs_nonneg t₀]
  have ht₀ : t₀ ∈ Set.Ioo (-R) R := by
    dsimp [R]
    constructor <;> linarith [neg_abs_le t₀, le_abs_self t₀, abs_nonneg t]
  have heq : Set.EqOn X Y (Set.Ioo (-R) R) := by
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun _ Z => field S h (radialClip Z)) (s := fun _ => Set.univ) (t₀ := t₀)
      (fun _ _ => hl.lipschitzOnWith) ht₀ _ _ hinit
    · intro u _
      rw [radialClip_eq (norm_unitary_tuple_le _ (hUX u))]
      exact ⟨hX u, Set.mem_univ _⟩
    · intro u _
      rw [radialClip_eq (norm_unitary_tuple_le _ (hUY u))]
      exact ⟨hY u, Set.mem_univ _⟩
  exact heq ht

end PolynomialFlow
end FreeGroupFactorMain

end

end OAI
