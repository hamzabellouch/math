import Mathlib
import OAI.Probability.CoordinateSweeps.Induction
import OAI.RepresentationTheory.Young.Entropy
import OAI.Probability.CoordinateSweeps.Scales

namespace OAI

/-!
Work on the genuinely missing main statements of the pinned manuscript.
All definitions are finite and use the source's ordinary probability and trace
normalizations. No result of the manuscript is assumed.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.UnitaryIrrep

variable {Γ : Type*} [Group Γ] (ρ : UnitaryIrrep Γ)

lemma orbit_span_top (v : Fin ρ.dimension → ℂ) (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range (fun g => (ρ.matrix g).mulVec v)) = ⊤ := by
  let S := Submodule.span ℂ (Set.range (fun g => (ρ.matrix g).mulVec v))
  have hvS : v ∈ S := by
    have h := Submodule.subset_span (R := ℂ) (s := Set.range (fun g => (ρ.matrix g).mulVec v))
      (Set.mem_range_self (1 : Γ))
    simpa using h
  have hne : S ≠ ⊥ := by
    intro he; rw [he,Submodule.mem_bot] at hvS; exact hv hvS
  apply (ρ.irreducible S ?_).resolve_left hne
  intro g w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k,rfl⟩ := hw
    rw [Matrix.mulVec_mulVec,← map_mul]
    exact Submodule.subset_span (Set.mem_range_self (g*k))
  | zero => simp
  | add x y hx hy hix hiy => simpa only [Matrix.mulVec_add] using S.add_mem hix hiy
  | smul c x hx hi => simpa only [Matrix.mulVec_smul] using S.smul_mem c hi

/- Elementary irreducible dimension bound needed for the finite base case;
no partition classification has been assumed. -/
theorem dimension_le_card [Fintype Γ] : ρ.dimension ≤ Fintype.card Γ := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  obtain ⟨v,hv⟩ := exists_ne (0 : Fin ρ.dimension → ℂ)
  have h := finrank_le_of_span_eq_top (ρ.orbit_span_top v hv)
  simpa using h

def fixed : Submodule ℂ (Fin ρ.dimension → ℂ) where
  carrier := {v | ∀ g, (ρ.matrix g).mulVec v=v}
  zero_mem' := by simp
  add_mem' hu hv := by intro g; simp only [Matrix.mulVec_add,hu g,hv g]
  smul_mem' c v hv := by intro g; simp only [Matrix.mulVec_smul,hv g]

lemma fixed_eq_bot_or_trivial : ρ.fixed = ⊥ ∨ ∀ g, ρ.matrix g = 1 := by
  have hi := ρ.irreducible ρ.fixed (by
    intro g v hv
    change ∀ k, (ρ.matrix k).mulVec ((ρ.matrix g).mulVec v)=(ρ.matrix g).mulVec v
    change ∀ k, (ρ.matrix k).mulVec v=v at hv
    rw [hv g]
    exact hv)
  rcases hi with h | h
  · exact Or.inl h
  · right
    intro g
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    have hv : v ∈ ρ.fixed := by rw [h]; trivial
    simpa using hv g

/- The exact zero of a uniform group average in every nontrivial irreducible.
This is the strict moment bound at z=0 used in06's b=1 base case. -/
theorem uniform_average_eq_zero [Fintype Γ]
    (hρ : ¬ ∀ g, ρ.matrix g=1) :
    (∑ g, (FiniteLaw.uniform Γ g : ℂ) • ρ.matrix g) = 0 := by
  have hfix : ρ.fixed = ⊥ := ρ.fixed_eq_bot_or_trivial.resolve_right hρ
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [Matrix.zero_mulVec]
  have hmem : (∑ g, (FiniteLaw.uniform Γ g : ℂ) • ρ.matrix g).mulVec v ∈ ρ.fixed := by
    intro k
    simp only [Matrix.sum_mulVec,Matrix.smul_mulVec,Matrix.mulVec_sum,Matrix.mulVec_smul,
      Matrix.mulVec_mulVec,← map_mul,FiniteLaw.uniform_apply]
    exact Equiv.sum_comp (Equiv.mulLeft k)
      (fun g => Complex.ofReal ((Fintype.card Γ : ℝ)⁻¹) • (ρ.matrix g).mulVec v)
  rwa [hfix,Submodule.mem_bot] at hmem

end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.UnitaryIrrep

variable {Γ : Type*} [Group Γ] [Fintype Γ] (ρ : UnitaryIrrep Γ)

lemma sum_matrix_eq_zero (hρ : ¬ ∀ g, ρ.matrix g=1) : ∑ g, ρ.matrix g=0 := by
  have h := ρ.uniform_average_eq_zero hρ
  simp only [FiniteLaw.uniform_apply,← Finset.smul_sum] at h
  exact (smul_eq_zero.mp h).resolve_left (by
    simp [Fintype.card_ne_zero])

/- Uniform-in-the-irrep quantitative form of the finite one-block base
perturbation in06. A conditional coset has precisely these affine weights,
with u=1/m! and 0≤w≤1. No classification, finiteness of a chosen list of
representations, or continuity assumption is needed. -/
theorem affine_average_norm_le (hρ : ¬ ∀ g, ρ.matrix g=1)
    (u : ℝ) (hu : 0 < u) (w : Γ → ℝ)
    (hw : ∀ g, 0 ≤ w g) (hw1 : ∀ g, w g ≤ 1)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1/2) :
    ‖((∑ g, ((1-z)*u+z*w g) : ℝ) : ℂ)⁻¹ •
       ∑ g, (((1-z)*u+z*w g : ℝ) : ℂ) • ρ.matrix g‖ ≤ 2*z/u := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  let Z : ℝ := ∑ g, ((1-z)*u+z*w g)
  have hN : (0 : ℝ) < Fintype.card Γ := Nat.cast_pos.mpr Fintype.card_pos
  have hZ : (Fintype.card Γ : ℝ)*(u/2) ≤ Z := by
    calc
      _ = ∑ _ : Γ, u/2 := by simp
      _ ≤ Z := Finset.sum_le_sum (fun g _ => by
        have hh := mul_nonneg hz (hw g)
        nlinarith)
  have hZp : 0 < Z := lt_of_lt_of_le (mul_pos hN (by positivity)) hZ
  have hsum : (∑ g, (((1-z)*u+z*w g : ℝ) : ℂ) • ρ.matrix g) =
      (z : ℂ) • ∑ g, (w g : ℂ) • ρ.matrix g := by
    simp only [Complex.ofReal_add,Complex.ofReal_mul,add_smul,mul_smul,
      Finset.sum_add_distrib,← Finset.smul_sum,ρ.sum_matrix_eq_zero hρ,
      smul_zero,zero_add]
  have hn : ‖∑ g, (w g : ℂ) • ρ.matrix g‖ ≤ Fintype.card Γ := by
    calc
      _ ≤ ∑ g, ‖(w g : ℂ) • ρ.matrix g‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Γ, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro g _
        rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw g)]
        exact (mul_le_of_le_one_right (hw g)
          (matrix_unitary_norm_le _ (ρ.unitary g))).trans (hw1 g)
      _ = Fintype.card Γ := by simp
  change ‖(Z : ℂ)⁻¹ • _‖ ≤ _
  rw [hsum,norm_smul,norm_smul,norm_inv,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hZp,abs_of_nonneg hz]
  calc
    Z⁻¹ * (z * ‖∑ g, (w g : ℂ) • ρ.matrix g‖) ≤
        Z⁻¹ * (z * Fintype.card Γ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn hz) (inv_nonneg.mpr hZp.le)
    _ ≤ 2*z/u := by
      rw [inv_mul_eq_div,div_le_iff₀ hZp]
      have hmult := mul_le_mul_of_nonneg_left hZ (show 0 ≤ 2*z/u by positivity)
      have he : 2*z/u * ((Fintype.card Γ : ℝ)*(u/2)) = z*Fintype.card Γ := by
        field_simp
      rw [he] at hmult
      exact hmult

end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.Grid

/- A one-coordinate grid, the base of06's induction. -/
abbrev single (d : ℕ) : Grid := ⟨1,by decide,fun _ => d⟩

instance single_line_unique (d : ℕ) (j : Fin (single d).b) :
    Unique ((single d).Line j) := by
  have he : IsEmpty {k : Fin (single d).b // k ≠ j} :=
    ⟨fun k => k.property (Subsingleton.elim _ _)⟩
  exact Pi.uniqueOfIsEmpty _

/- The single coordinate slot identification is explicit. -/
def singleSlot (d : ℕ) : (single d).Slot ≃ Cube d :=
  Equiv.piUnique (fun _ : Fin 1 => Cube d)

@[simp] theorem singleSlot_apply (d : ℕ) (x : (single d).Slot) :
    singleSlot d x = x 0 := rfl

@[simp] theorem singleSlot_symm_apply (d : ℕ) (x : Cube d) (j : Fin 1) :
    (singleSlot d).symm x j=x := rfl

/- Every line-choice array in a one-coordinate grid is one permutation. -/
def singleChoice (d : ℕ) : (single d).Choices ≃ Equiv.Perm (Cube d) where
  toFun ω := ω 0 default
  invFun σ _ _ := σ
  left_inv ω := by
    funext j L
    have hj : j=0 := Subsingleton.elim _ _
    subst j
    exact congrArg (ω 0) (Subsingleton.elim _ _)
  right_inv σ := rfl

lemma single_stage_apply (d : ℕ) (ω : (single d).Choices) (x : (single d).Slot) :
    (single d).stage ω 0 x 0=singleChoice d ω (x 0) := by
  have hs : (single d).stage ω 0 x 0=ω 0 (fun k => x k) (x 0) := by
    simp [stage,fiberPerm,Equiv.piSplitAt_apply,Equiv.piSplitAt_symm_apply]
  rw [hs]
  change ω 0 (fun k => x k) (x 0)=ω 0 default (x 0)
  exact congrArg (fun L => ω 0 L (x 0)) (Subsingleton.elim _ _)

lemma single_sweep (d : ℕ) (ω : (single d).Choices) :
    (single d).sweep ω=(singleSlot d).symm.permCongr (singleChoice d ω) := by
  apply Equiv.ext
  intro x
  funext j
  have hj : j=0 := Subsingleton.elim _ _
  subst j
  change (single d).boundary ω 1 x 0=_
  simp only [boundary,List.ofFn_succ,List.ofFn_zero,List.take_succ_cons,List.take_zero,
    List.reverse_cons,List.reverse_nil,List.nil_append,List.prod_cons,List.prod_nil,mul_one]
  exact single_stage_apply d ω x

/- No hidden fibers in the one-block base: all permutations are possible,
and each one determines the unique line-choice array. -/
def singleSweepEquiv (d : ℕ) : (single d).Choices ≃ Equiv.Perm (single d).Slot :=
  (singleChoice d).trans (Equiv.permCongr (singleSlot d).symm)

@[simp] lemma singleSweepEquiv_apply (d : ℕ) (ω : (single d).Choices) :
    singleSweepEquiv d ω=(single d).sweep ω := (single_sweep d ω).symm

lemma single_choiceWeight (d : ℕ) (z : ℝ) (ω : (single d).Choices) :
    (single d).choiceWeight z ω=
      (1-z)*(Fintype.card (Equiv.Perm (Cube d)) : ℝ)⁻¹+
        z*binaryLaw d (singleChoice d ω) := by
  unfold choiceWeight
  rw [Fin.prod_univ_one]
  rw [Fintype.prod_subsingleton _ (default : (single d).Line 0)]
  rfl

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid.Holes
variable {d h : ℕ} (H : (Grid.single d).Holes h)

lemma single_compatible_iff (ω : (Grid.single d).Choices) :
    H.Compatible ω ↔ ∀ i, (Grid.single d).sweep ω (H.path i 0)=H.path i 1 := by
  constructor
  · intro hω i
    exact hω i 1
  · intro hω i t
    fin_cases t
    · simp [Grid.boundary]
    · exact hω i

/- Exact bijection of conditioned one-block choices with the remaining
symmetric group, not an assumption of uniformity of that residual law. -/
def singleResidualEquiv (hf : H.Feasible) :
    {ω : (Grid.single d).Choices // H.Compatible ω} ≃ H.stabilizer where
  toFun := H.residual hf
  invFun g := ⟨(Grid.singleSweepEquiv d).symm
      ((Grid.single d).sweep (H.reference hf)*g.val), by
    apply (H.single_compatible_iff _).mpr
    intro i
    rw [← Grid.singleSweepEquiv_apply,Equiv.apply_symm_apply]
    change (Grid.single d).sweep (H.reference hf) (g.val (H.path i 0))=H.path i 1
    rw [g.property i]
    exact H.reference_compatible hf i 1⟩
  left_inv ω := by
    apply Subtype.ext
    apply (Grid.singleSweepEquiv d).injective
    simp only [Equiv.apply_symm_apply,Grid.singleSweepEquiv_apply,residual,
      mul_inv_cancel_left]
  right_inv g := by
    apply Subtype.ext
    change ((Grid.single d).sweep (H.reference hf))⁻¹ *
      (Grid.single d).sweep ((Grid.singleSweepEquiv d).symm
        ((Grid.single d).sweep (H.reference hf)*g.val))=g.val
    rw [← Grid.singleSweepEquiv_apply d ((Grid.singleSweepEquiv d).symm
      ((Grid.single d).sweep (H.reference hf)*g.val)),
      Equiv.apply_symm_apply,inv_mul_cancel_left]

lemma single_probability (hf : H.Feasible) (z : ℝ) :
    H.probability z = ∑ g : H.stabilizer,
      (Grid.single d).choiceWeight z ((H.singleResidualEquiv hf).symm g).val :=
  ((H.singleResidualEquiv hf).symm.sum_comp _).symm

lemma single_conditionalAverage (hf : H.Feasible) (z : ℝ)
    (ρ : UnitaryIrrep H.stabilizer) :
    H.conditionalAverage hf z ρ =
      ((∑ g : H.stabilizer, (Grid.single d).choiceWeight z
        ((H.singleResidualEquiv hf).symm g).val : ℝ) : ℂ)⁻¹ •
      ∑ g : H.stabilizer, ((Grid.single d).choiceWeight z
        ((H.singleResidualEquiv hf).symm g).val : ℂ) • ρ.matrix g := by
  unfold conditionalAverage
  rw [H.single_probability hf z]
  congr 1
  rw [← (H.singleResidualEquiv hf).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro g _
  congr 2
  exact (H.singleResidualEquiv hf).apply_symm_apply g

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {d h : ℕ} (H : (Grid.single d).Holes h)

/- Actual conditioned single-coordinate operator, uniform in the hole family,
reference bijection, irrep, and representation realization. -/
theorem single_conditional_norm_le (hf : H.Feasible)
    (ρ : UnitaryIrrep H.stabilizer) (hρ : ¬ ∀ g, ρ.matrix g=1)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1/2) :
    ‖H.conditionalAverage hf z ρ‖ ≤
      2*z*(Fintype.card (Equiv.Perm (Cube d)) : ℝ) := by
  rw [H.single_conditionalAverage hf z ρ]
  simp only [Grid.single_choiceWeight]
  simpa only [div_inv_eq_mul] using
    ρ.affine_average_norm_le hρ
      ((Fintype.card (Equiv.Perm (Cube d)) : ℝ)⁻¹)
      (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
      (fun g => binaryLaw d (Grid.singleChoice d ((H.singleResidualEquiv hf).symm g).val))
      (fun g => (binaryLaw d).nonneg _) (fun g => (binaryLaw d).mass_le_one _) hz hz1

lemma single_dimension_le (ρ : UnitaryIrrep H.stabilizer) :
    ρ.dimension ≤ Fintype.card (Equiv.Perm (Cube d)) := by
  apply ρ.dimension_le_card.trans
  have hc : Fintype.card H.stabilizer ≤ Fintype.card (Equiv.Perm (Grid.single d).Slot) :=
    Fintype.card_subtype_le _
  rwa [Fintype.card_congr (Equiv.permCongr (Grid.singleSlot d))] at hc

/- Exact one-block moment bound before choosing the absolute real interval. -/
theorem single_conditional_moment_le (hf : H.Feasible)
    (ρ : UnitaryIrrep H.stabilizer) (hρ : ¬ ∀ g, ρ.matrix g=1)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1/2) (q : ℕ) :
    schattenMoment q (H.conditionalAverage hf z ρ) ≤
      (Fintype.card (Equiv.Perm (Cube d)) : ℝ) *
        (2*z*(Fintype.card (Equiv.Perm (Cube d)) : ℝ))^(2*q) := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  exact (trace_moment_le _ q).trans (mul_le_mul
    (by exact_mod_cast H.single_dimension_le ρ)
    (pow_le_pow_left₀ (norm_nonneg _) (H.single_conditional_norm_le hf ρ hρ hz hz1) _)
    (by positivity) (by positivity))

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps

lemma e0_pos : 0 < e0 := by norm_num [e0,a]
lemma c0_eq_e0 : c0=e0 := rfl
lemma c0_small : 2*c0 < 1 := by norm_num [c0,a]

namespace Grid

lemma log_size_lower_one (G : Grid) {r : ℕ} (hG : G.Allowed r) :
    (r : ℝ)*Real.log 2 ≤ Real.log G.size := by
  apply le_trans _ (G.log_size_lower hG)
  have hb : (1 : ℝ) ≤ G.b := by exact_mod_cast G.positive
  exact le_mul_of_one_le_left (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))) hb

end Grid

/- Exactly the two largeness requirements stated at the start of06, converted
from log R to bit exponent r. Both constants remain the source constants. -/
def ScaleLarge (r : ℕ) : Prop :=
  1 ≤ r ∧ (2/e0)^2 ≤ (r : ℝ)*Real.log 2 ∧ 4/e0 ≤ (r : ℝ)*Real.log 2

lemma exists_scaleLarge : ∃ r, ScaleLarge r := by
  let B : ℝ := max ((2/e0)^2) (4/e0)
  obtain ⟨r,hr⟩ := exists_nat_gt (max 1 (B/Real.log 2))
  have hr1 : (1 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hr
  have hrB : B/Real.log 2 < r := lt_of_le_of_lt (le_max_right _ _) hr
  have hh : B ≤ (r : ℝ)*Real.log 2 :=
    ((div_lt_iff₀ (Real.log_pos (by norm_num))).mp hrB).le
  refine ⟨r,?_,?_,?_⟩
  · have hnat : 1 < r := by exact_mod_cast hr1
    omega
  · exact (le_max_left _ _).trans hh
  · exact (le_max_right _ _).trans hh

lemma scale_coefficients {r : ℕ} (hr : ScaleLarge r) (G : Grid) (hG : G.Allowed r) :
    0 < Real.log G.size ∧ c G.size ≤ 2*c0 ∧ e0/2 ≤ e G.size ∧
    (G.b : ℝ) ≤ (e0/4)*Real.log G.size := by
  have he := e0_pos
  have hroot : (2/e0)^2 ≤ Real.log G.size := hr.2.1.trans (G.log_size_lower_one hG)
  have hlog : 0 < Real.log G.size := lt_of_lt_of_le (by positivity) hroot
  have hs : 2/e0 ≤ Real.sqrt (Real.log G.size) :=
    (Real.le_sqrt (by positivity) hlog.le).mpr hroot
  have hspos : 0 < Real.sqrt (Real.log G.size) := Real.sqrt_pos.mpr hlog
  have hi : 1/Real.sqrt (Real.log G.size) ≤ e0/2 := by
    apply (div_le_iff₀ hspos).mpr
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ e0/2 by positivity)
    field_simp at hh ⊢
    nlinarith
  have hb : (G.b : ℝ)*(4/e0) ≤ Real.log G.size :=
    (mul_le_mul_of_nonneg_left hr.2.2 (Nat.cast_nonneg _)).trans (G.log_size_lower hG)
  refine ⟨hlog,?_,?_,?_⟩
  · unfold c
    rw [c0_eq_e0]
    linarith
  · unfold e
    linarith
  · have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ e0/4 by positivity)
    field_simp at hh
    nlinarith

namespace Grid.Holes
variable {G : Grid} {h : ℕ} (H : G.Holes h)

/- Exact source nonnegative allowance, including h=0 and the empty type. -/
theorem allowance_lower {r : ℕ} (hr : ScaleLarge r) (hG : G.Allowed r) :
    (e0/4) * h * Real.log G.size ≤ e G.size * h * Real.log G.size - H.cost := by
  obtain ⟨hlog,hc,he,hb⟩ := scale_coefficients hr G hG
  have h1 := mul_le_mul_of_nonneg_right he (show 0 ≤ (h : ℝ)*Real.log G.size by positivity)
  have h2 := H.cost_le.trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg h))
  nlinarith

lemma allowance_nonneg {r : ℕ} (hr : ScaleLarge r) (hG : G.Allowed r) :
    0 ≤ e G.size * h * Real.log G.size - H.cost :=
  (mul_nonneg (mul_nonneg (div_nonneg e0_pos.le (by norm_num)) (Nat.cast_nonneg _))
    (scale_coefficients hr G hG).1.le).trans (H.allowance_lower hr hG)

end Grid.Holes

lemma logMoment_le_of_le {t u : ℝ} (ht : 0 ≤ t) (hu : 0 < u) (htu : t ≤ u) :
    logMoment t ≤ (Real.log u : EReal) := by
  by_cases ht0 : t=0
  · simp [logMoment,ht0]
  · rw [logMoment,ite_eq_right ht0]
    exact_mod_cast (Real.log_le_log_iff (lt_of_le_of_ne ht (Ne.symm ht0)) hu).mpr htu

namespace Grid.Holes
variable {G : Grid} {h : ℕ} (H : G.Holes h)

/- Entire automatic branch06 eq16, with no representation type omitted. -/
theorem conditional_automatic (hf : H.Feasible) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (ρ : UnitaryIrrep H.stabilizer) (q : ℕ)
    (ha : (1+c G.size)*Real.log ρ.dimension ≤
      e G.size*h*Real.log G.size-H.cost) :
    logMoment (schattenMoment q (H.conditionalAverage hf z ρ)) ≤
      ((-c G.size*Real.log ρ.dimension+e G.size*h*Real.log G.size-H.cost : ℝ) : EReal) := by
  apply (logMoment_le_of_le (H.conditionalMoment_nonneg hf z ρ q)
    (Nat.cast_pos.mpr ρ.positive) (H.conditionalMoment_le_dimension hf hz hz1 ρ q)).trans
  exact_mod_cast (show Real.log ρ.dimension ≤
    -c G.size*Real.log ρ.dimension+e G.size*h*Real.log G.size-H.cost by nlinarith)

/- All one-dimensional types (trivial, sign, empty, and M=1), as required
explicitly in the statement and the first branch of the main induction. -/
theorem conditional_dimension_one {r : ℕ} (hr : ScaleLarge r) (hG : G.Allowed r)
    (hf : H.Feasible) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (ρ : UnitaryIrrep H.stabilizer) (hρ : ρ.dimension=1) (q : ℕ) :
    logMoment (schattenMoment q (H.conditionalAverage hf z ρ)) ≤
      ((-c G.size*Real.log ρ.dimension+e G.size*h*Real.log G.size-H.cost : ℝ) : EReal) := by
  apply H.conditional_automatic hf hz hz1 ρ q
  simpa [hρ] using H.allowance_nonneg hr hG

end Grid.Holes
end CoordinateSweeps

namespace CoordinateSweeps
namespace UnitaryIrrep
variable {Γ : Type*} [Group Γ] (ρ : UnitaryIrrep Γ)

lemma dimension_one_of_trivial (hρ : ∀ g, ρ.matrix g=1) : ρ.dimension=1 := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  obtain ⟨v,hv⟩ := exists_ne (0 : Fin ρ.dimension → ℂ)
  have hs := ρ.orbit_span_top v hv
  simp only [hρ,Matrix.one_mulVec,Set.range_const] at hs
  have hf := finrank_span_singleton (K := ℂ) hv
  rw [hs] at hf
  simpa using hf

end UnitaryIrrep

/- An explicit uniform base interval, so06's finiteness perturbation requires
no choice of a finite list of representation realizations. -/
def baseWidth (r : ℕ) : ℝ := ((2^(2*r)).factorial : ℕ)
def baseZeta (r : ℕ) : ℝ := 1/(4*(baseWidth r)^2)

lemma baseWidth_one_le (r : ℕ) : 1 ≤ baseWidth r := by
  unfold baseWidth
  exact_mod_cast (show 1 ≤ (2^(2*r)).factorial from Nat.factorial_pos _)

lemma baseZeta_pos (r : ℕ) : 0 < baseZeta r := by
  have h := baseWidth_one_le r
  unfold baseZeta
  positivity

lemma baseZeta_le_half (r : ℕ) : baseZeta r ≤ 1/2 := by
  have h := baseWidth_one_le r
  unfold baseZeta
  apply (div_le_iff₀ (by positivity : 0 < 4*(baseWidth r)^2)).mpr
  nlinarith

lemma single_card_le_baseWidth {r d : ℕ} (hd : d ≤ 2*r) :
    (Fintype.card (Equiv.Perm (Cube d)) : ℝ) ≤ baseWidth r := by
  simp only [Fintype.card_perm,Cube,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
  unfold baseWidth
  exact_mod_cast Nat.factorial_le (Nat.pow_le_pow_right (by norm_num : 0 < 2) hd)

namespace Grid.Holes
variable {d h : ℕ} (H : (Grid.single d).Holes h)

theorem single_base_norm {r : ℕ} (hd : d ≤ 2*r) (hf : H.Feasible)
    (ρ : UnitaryIrrep H.stabilizer) (hρ : ρ.dimension ≠ 1)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ baseZeta r) :
    ‖H.conditionalAverage hf z ρ‖ ≤ (baseWidth r)⁻¹ := by
  have hB := baseWidth_one_le r
  have hc := single_card_le_baseWidth hd
  have hZ := baseZeta_pos r
  have hnt : ¬ ∀ g, ρ.matrix g=1 := fun hh => hρ (ρ.dimension_one_of_trivial hh)
  apply (H.single_conditional_norm_le hf ρ hnt hz
    (hz'.trans (baseZeta_le_half r))).trans
  calc
    2*z*(Fintype.card (Equiv.Perm (Cube d)) : ℝ) ≤ 2*baseZeta r*baseWidth r :=
      mul_le_mul (mul_le_mul_of_nonneg_left hz' (by norm_num)) hc
        (Nat.cast_nonneg _) (by positivity)
    _ ≤ (baseWidth r)⁻¹ := by
      unfold baseZeta
      field_simp
      nlinarith

/- A quantitative strict base estimate for all nontrivial irreducibles. -/
theorem single_base_moment {r : ℕ} (hd : d ≤ 2*r) (hf : H.Feasible)
    (ρ : UnitaryIrrep H.stabilizer) (hρ : ρ.dimension ≠ 1)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ baseZeta r)
    {q : ℕ} (hq : 1 ≤ q) :
    schattenMoment q (H.conditionalAverage hf z ρ) ≤ (ρ.dimension : ℝ)⁻¹ := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  have hB := baseWidth_one_le r
  have hBp : 0 < baseWidth r := lt_of_lt_of_le (by norm_num) hB
  have hBi : (baseWidth r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hB
  have hD : (ρ.dimension : ℝ) ≤ baseWidth r :=
    (show (ρ.dimension : ℝ) ≤ (Fintype.card (Equiv.Perm (Cube d)) : ℝ) by
      exact_mod_cast H.single_dimension_le ρ).trans (single_card_le_baseWidth hd)
  have hnorm := H.single_base_norm hd hf ρ hρ hz hz'
  calc
    _ ≤ (ρ.dimension : ℝ)*‖H.conditionalAverage hf z ρ‖^(2*q) := trace_moment_le _ q
    _ ≤ baseWidth r*((baseWidth r)⁻¹)^(2*q) :=
      mul_le_mul hD (pow_le_pow_left₀ (norm_nonneg _) hnorm _)
        (by positivity) (by positivity)
    _ ≤ baseWidth r*((baseWidth r)⁻¹)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) hBi (by omega)) hBp.le
    _ = (baseWidth r)⁻¹ := by field_simp
    _ ≤ (ρ.dimension : ℝ)⁻¹ := (inv_le_inv₀ hBp (by exact_mod_cast ρ.positive)).mpr hD

/- The full06 one-coordinate base with the manuscript's precise c,e and cost. -/
theorem single_conditional_main {r : ℕ} (hr : ScaleLarge r)
    (hG : (Grid.single d).Allowed r) (hf : H.Feasible)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ baseZeta r)
    (ρ : UnitaryIrrep H.stabilizer) {q : ℕ} (hq : 1 ≤ q) :
    logMoment (schattenMoment q (H.conditionalAverage hf z ρ)) ≤
      ((-c (Grid.single d).size*Real.log ρ.dimension+
        e (Grid.single d).size*h*Real.log (Grid.single d).size-H.cost : ℝ) : EReal) := by
  have hz1 : z < 1 := lt_of_le_of_lt (hz'.trans (baseZeta_le_half r)) (by norm_num)
  by_cases hρ : ρ.dimension=1
  · exact H.conditional_dimension_one hr hG hf hz hz1 ρ hρ q
  have hm := H.single_base_moment (hG 0).2 hf ρ hρ hz hz' hq
  have hl := logMoment_le_of_le (H.conditionalMoment_nonneg hf z ρ q)
    (inv_pos.mpr (Nat.cast_pos.mpr ρ.positive)) hm
  rw [Real.log_inv] at hl
  apply hl.trans
  have hc : c (Grid.single d).size ≤ 1 :=
    (scale_coefficients hr _ hG).2.1.trans c0_small.le
  have hfnonneg : 0 ≤ Real.log ρ.dimension :=
    Real.log_nonneg (by exact_mod_cast ρ.positive)
  have ha := H.allowance_nonneg hr hG
  exact_mod_cast (show -Real.log ρ.dimension ≤
    -c (Grid.single d).size*Real.log ρ.dimension+
      e (Grid.single d).size*h*Real.log (Grid.single d).size-H.cost by nlinarith)

end Grid.Holes
end CoordinateSweeps

namespace CoordinateSweeps.Grid
lemma eq_single_of_b_one (G : Grid) (hb : G.b=1) : ∃ d, G=single d := by
  rcases G with ⟨b,hpos,bits⟩
  dsimp at hb
  subst b
  refine ⟨bits 0,?_⟩
  congr
  funext i
  exact congrArg bits (Subsingleton.elim i 0)

/- Full base branch for every allowed one-coordinate grid, not only a chosen
canonical coordinate presentation. -/
theorem conditional_main_b_one {r : ℕ} (hr : ScaleLarge r)
    (G : Grid) (hb : G.b=1) (hG : G.Allowed r)
    {h : ℕ} (H : G.Holes h) (hf : H.Feasible)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ baseZeta r)
    (ρ : UnitaryIrrep H.stabilizer) {q : ℕ} (hq : 1 ≤ q) :
    logMoment (schattenMoment q (H.conditionalAverage hf z ρ)) ≤
      ((-c G.size*Real.log ρ.dimension+e G.size*h*Real.log G.size-H.cost : ℝ) : EReal) := by
  obtain ⟨d,rfl⟩ := G.eq_single_of_b_one hb
  exact H.single_conditional_main hr hG hf hz hz' ρ hq
end CoordinateSweeps.Grid
end

namespace CoordinateSweeps.Grid.Holes
open UnitaryIrrep YoungCorner
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)
/- The unswept free sites and the literal occupied junction board are
identified by the actual reference first-half sweep. -/
noncomputable def initialJunctionFree (hf : H.Feasible) : H.FreeAt 0 ≃ H.JunctionFree :=
  Marked.freeEquiv (fun i => H.path i 0) (fun i => H.path i (suffixTime A B 0))
    (H.rowAction (H.refPair hf).1) (H.rowAction_marked hf (H.refPair hf).1)
lemma initialJunction_conj (hf : H.Feasible) (g : H.stabilizer) :
    H.junctionFreeEquiv (H.junctionEquiv hf g)=
      (H.initialJunctionFree hf).permCongrHom (H.stabilizerFreeEquiv g) := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rfl
lemma junctionChart_symm_boxes (hf : H.Feasible)
    (eF : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (μ : YoungDiagram) (eB : H.FreeAt 0 ≃ Boxes μ)
    (g : Equiv.Perm (Fin (Fintype.card H.JunctionFree))) :
    (H.junctionChart hf eF).symm g=
      H.boxesChart μ eB ((eF.trans ((H.initialJunctionFree hf).symm.trans eB)).permCongrHom g) := by
  apply (H.junctionChart hf eF).injective
  rw [MulEquiv.apply_symm_apply]
  change g=eF.symm.permCongrHom (H.junctionFreeEquiv (H.junctionEquiv hf
    (H.boxesChart μ eB ((eF.trans ((H.initialJunctionFree hf).symm.trans eB)).permCongrHom g))))
  rw [H.initialJunction_conj]
  change g=eF.symm.permCongrHom ((H.initialJunctionFree hf).permCongrHom
    (H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm (eB.symm.permCongrHom
      ((eF.trans ((H.initialJunctionFree hf).symm.trans eB)).permCongrHom g)))))
  rw [MulEquiv.apply_symm_apply]
  apply Equiv.ext
  intro x
  simp [Equiv.permCongrHom,Equiv.permCongr]
lemma junction_hasShape (hf : H.Feasible)
    (eF : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (μ : YoungDiagram) (eB : H.FreeAt 0 ≃ Boxes μ)
    (σ : UnitaryIrrep H.stabilizer)
    (hσ : hasShape μ (Equiv.refl _) (σ.pullback (H.boxesChart μ eB)).asRepresentation) :
    hasShape μ (eF.trans ((H.initialJunctionFree hf).symm.trans eB))
      (σ.pullback (H.junctionChart hf eF).symm).asRepresentation := by
  let t := eF.trans ((H.initialJunctionFree hf).symm.trans eB)
  have he : (σ.pullback (H.junctionChart hf eF).symm).asRepresentation=
      (σ.pullback (H.boxesChart μ eB)).asRepresentation.comp t.permCongrHom := by
    apply MonoidHom.ext
    intro g
    change Matrix.toLinAlgEquiv' (σ.matrix ((H.junctionChart hf eF).symm g))=
      Matrix.toLinAlgEquiv' (σ.matrix (H.boxesChart μ eB (t.permCongrHom g)))
    rw [H.junctionChart_symm_boxes]
  rw [he]
  change hasShape μ t ((σ.pullback (H.boxesChart μ eB)).asRepresentation.comp t.permCongrHom)
  simpa only [Equiv.trans_refl] using (hasShape_reparam μ t (Equiv.refl _) _).mpr hσ
lemma conditionalAverage_cancelChart (hf : H.Feasible)
    (eF : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (σ : UnitaryIrrep H.stabilizer) (z : ℝ) :
    H.conditionalAverage hf z ((σ.pullback (H.junctionChart hf eF).symm).pullback (H.junctionChart hf eF))=
      H.conditionalAverage hf z σ := by
  rw [H.conditionalAverage_eq_sum,H.conditionalAverage_eq_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  change (_:ℂ) • σ.matrix ((H.junctionChart hf eF).symm (H.junctionChart hf eF (H.residual hf ω)))=_
  rw [MulEquiv.symm_apply_apply]
/- Exact hooked-main estimate for the actual stabilizer representation and
its literal initial-site Young labeling, with arbitrary feasible holes. -/
theorem actual_hook_bound (p : ℕ) (hp : 0<p) (hf : H.Feasible)
    (z : ℝ) (q : ℕ) (hq : 0<q) (c e : ℝ) (hc : 0≤c) (hcq : c≤q)
    (s : ℕ) (hpS : p≤ s) (hAS : A.size≤ s) (hBS : B.size≤ s)
    (σ : UnitaryIrrep H.stabilizer)
    (hR : ∀ y : B.Slot, ∀ τ : UnitaryIrrep (H.rowHoles y).stabilizer,
      schattenMoment q ((H.rowHoles y).conditionalAverage (H.rowHoles y).feasible_of_disjoint z τ) ≤
        Real.exp (-c*Real.log τ.dimension+e*H.rowCount y*Real.log A.size-(H.rowHoles y).cost))
    (hC : ∀ x : A.Slot, ∀ τ : UnitaryIrrep (H.columnHoles x).stabilizer,
      schattenMoment q ((H.columnHoles x).conditionalAverage (H.columnHoles x).feasible_of_disjoint z τ) ≤
        Real.exp (-c*Real.log τ.dimension+e*H.columnCount x*Real.log B.size-(H.columnHoles x).cost))
    (μ : YoungDiagram) (eB : H.FreeAt 0 ≃ Boxes μ)
    (hσ : hasShape μ (Equiv.refl _) (σ.pullback (H.boxesChart μ eB)).asRepresentation) (hhook : Hook μ p) :
    schattenMoment q (H.conditionalAverage hf z σ) ≤
      Real.exp (-c*Real.log σ.dimension+e*h*(Real.log A.size+Real.log B.size)-H.cost+c*h+
        (((2*q+1:ℕ):ℝ)*((A.size+B.size)*((2*p)*(2*p)):ℕ)+
          c*((A.size+B.size)*(41*p^2):ℕ))*Real.log (s+1:ℕ)) := by
  let eF := (Fintype.equivFin H.JunctionFree).symm
  have hh := H.grid_conditional_hook_bound p hp eF hf z q hq c e hc hcq s hpS hAS hBS
    (σ.pullback (H.junctionChart hf eF).symm) hR hC μ
    (eF.trans ((H.initialJunctionFree hf).symm.trans eB)) (H.junction_hasShape hf eF μ eB σ hσ) hhook
  rw [H.conditionalAverage_cancelChart] at hh
  exact hh
end CoordinateSweeps.Grid.Holes

open scoped Matrix.Norms.L2Operator

end OAI
