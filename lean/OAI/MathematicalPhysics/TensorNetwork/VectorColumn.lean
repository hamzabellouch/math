import Mathlib

namespace OAI

 

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open WithLp

namespace PolynomialPEPS

abbrev Vertex (L : ℕ) := Fin L × Fin L

 

abbrev Edge (L : ℕ) :=
  {p : Vertex L × Vertex L //
    (p.1.1.val + 1 = p.2.1.val ∧ p.1.2 = p.2.2) ∨
    (p.1.1 = p.2.1 ∧ p.1.2.val + 1 = p.2.2.val)}

abbrev IncidentEdge (L : ℕ) (v : Vertex L) :=
  {e : Edge L // e.val.1 = v ∨ e.val.2 = v}

abbrev Configuration (q L : ℕ) := Vertex L → Fin q
abbrev State (q L : ℕ) := EuclideanSpace ℂ (Configuration q L)
abbrev Operator (q L : ℕ) := Matrix (Configuration q L) (Configuration q L) ℂ

 

def SupportedOn {q L : ℕ} (A : Operator q L) (S : Finset (Vertex L)) : Prop := by
  classical
  exact ∃ K : Matrix ({v : Vertex L // v ∈ S} → Fin q)
      ({v : Vertex L // v ∈ S} → Fin q) ℂ,
    ∀ x y : Configuration q L,
      A x y = if ∀ v, v ∉ S → x v = y v then
        K (fun v => x v.val) (fun v => y v.val) else 0

 
def outer {q L : ℕ} (x : State q L) : Operator q L :=
  fun i j => x i * star (x j)

 
def act {q L : ℕ} (A : Operator q L) (x : State q L) : State q L :=
  toLp 2 (A.mulVec (ofLp x))

def phase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

def normalized {q L : ℕ} (x : State q L) : State q L :=
  (‖x‖ : ℂ)⁻¹ • x

 
def UniqueGroundVector {q L : ℕ} (H : Operator q L) (E₀ : ℝ)
    (Ω : State q L) : Prop :=
  ‖Ω‖ = 1 ∧ act H Ω = (E₀ : ℂ) • Ω ∧
    (H - (E₀ : ℂ) • (1 : Operator q L)).PosSemidef ∧
    ∀ ψ : State q L, ‖ψ‖ = 1 → act H ψ = (E₀ : ℂ) • ψ →
      ∃ θ : ℝ, ψ = phase θ • Ω

 
def GlobalGap {q L : ℕ} (H : Operator q L) (E₀ Δ : ℝ)
    (Ω : State q L) : Prop :=
  (H - (E₀ : ℂ) • (1 : Operator q L) -
    (Δ : ℂ) • ((1 : Operator q L) - outer Ω)).PosSemidef

 

structure PEPS (q L : ℕ) where
  bondDim : Edge L → ℕ
  bondDim_pos : ∀ e, 0 < bondDim e
  tensor : ∀ v : Vertex L,
    ((e : IncidentEdge L v) → Fin (bondDim e.val)) → Fin q → ℂ

namespace PEPS

 

def contract {q L : ℕ} (P : PEPS q L) : State q L := by
  classical
  exact toLp 2 (fun x => ∑ a : (e : Edge L) → Fin (P.bondDim e),
    ∏ v : Vertex L, P.tensor v (fun e => a e.val) (x v))

def maxBondDim {q L : ℕ} (P : PEPS q L) : ℕ := by
  classical
  exact Finset.univ.sup P.bondDim

end PEPS

 

def PhaseErrorAtMost {q L : ℕ} (x Ω : State q L) (ε : ℝ) : Prop :=
  ∃ θ : ℝ,
    (∀ φ : ℝ, ‖normalized x - phase θ • Ω‖ ≤ ‖normalized x - phase φ • Ω‖) ∧
    ‖normalized x - phase θ • Ω‖ ≤ ε



@[simp] theorem norm_phase (θ : ℝ) : ‖phase θ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

@[simp] theorem phase_neg_mul (θ : ℝ) : phase (-θ) * phase θ = 1 := by
  simp only [phase, ← Complex.exp_add, Complex.ofReal_neg, neg_mul, neg_add_cancel,
    Complex.exp_zero]

theorem phase_arg_mul (z : ℂ) : phase (-z.arg) * z = (‖z‖ : ℂ) := by
  have hz : (‖z‖ : ℂ) * phase z.arg = z := Complex.norm_mul_exp_arg_mul_I z
  calc
    phase (-z.arg) * z = phase (-z.arg) * ((‖z‖ : ℂ) * phase z.arg) :=
      congrArg (phase (-z.arg) * ·) hz.symm
    _ = (‖z‖ : ℂ) * (phase (-z.arg) * phase z.arg) := by ring
    _ = (‖z‖ : ℂ) := by rw [phase_neg_mul, mul_one]

 
theorem exists_phase_minimizer {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (x y : E) :
    ∃ θ : ℝ,
      (∀ φ : ℝ, ‖x - phase θ • y‖ ≤ ‖x - phase φ • y‖) ∧
      ‖x - phase θ • y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * ‖inner ℂ x y‖ := by
  have hdist (φ : ℝ) : ‖x - phase φ • y‖ ^ 2 =
      ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (phase φ * inner ℂ x y).re := by
    rw [norm_sub_sq (𝕜 := ℂ), norm_smul, norm_phase, one_mul, inner_smul_right]
    change ‖x‖ ^ 2 - 2 * (phase φ * inner ℂ x y).re + ‖y‖ ^ 2 = _
    ring
  refine ⟨-(inner ℂ x y).arg, ?_, ?_⟩
  · intro φ
    have hreal : (phase φ * inner ℂ x y).re ≤ ‖inner ℂ x y‖ := by
      calc
        _ ≤ ‖phase φ * inner ℂ x y‖ := Complex.re_le_norm _
        _ = ‖inner ℂ x y‖ := by rw [norm_mul, norm_phase, one_mul]
    have hmin := hdist (-(inner ℂ x y).arg)
    rw [phase_arg_mul, Complex.ofReal_re] at hmin
    have hφ := hdist φ
    nlinarith [norm_nonneg (x - phase (-(inner ℂ x y).arg) • y),
      norm_nonneg (x - phase φ • y)]
  · rw [hdist, phase_arg_mul, Complex.ofReal_re]

@[simp] theorem norm_normalized {q L : ℕ} {x : State q L} (hx : x ≠ 0) :
    ‖normalized x‖ = 1 := by
  rw [normalized, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

@[simp] theorem act_sub {q L : ℕ} (A B : Operator q L) (x : State q L) :
    act (A - B) x = act A x - act B x := by
  ext i
  simp [act, Matrix.sub_mulVec]

@[simp] theorem act_smul {q L : ℕ} (a : ℂ) (A : Operator q L) (x : State q L) :
    act (a • A) x = a • act A x := by
  ext i
  simp [act, Matrix.smul_mulVec]

@[simp] theorem act_one {q L : ℕ} (x : State q L) :
    act (1 : Operator q L) x = x := by
  ext i
  simp [act]

@[simp] theorem act_outer {q L : ℕ} (x y : State q L) :
    act (outer x) y = inner ℂ x y • x := by
  ext i
  simp only [act, outer, Matrix.mulVec, dotProduct, PiLp.smul_apply,
    smul_eq_mul, PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

 
def expectation {q L : ℕ} (A : Operator q L) (x : State q L) : ℝ :=
  (inner ℂ x (act A x)).re

theorem expectation_nonneg {q L : ℕ} {A : Operator q L} (hA : A.PosSemidef)
    (x : State q L) : 0 ≤ expectation A x := by
  simpa only [expectation, EuclideanSpace.inner_eq_star_dotProduct, act, ofLp_toLp,
    RCLike.re_to_complex, dotProduct_comm]
    using hA.re_dotProduct_nonneg (ofLp x)

theorem globalGap_expectation {q L : ℕ} {H : Operator q L} {E₀ Δ : ℝ}
    {Ω : State q L} (hgap : GlobalGap H E₀ Δ Ω) (ψ : State q L) :
    Δ * (‖ψ‖ ^ 2 - ‖inner ℂ Ω ψ‖ ^ 2) ≤
      expectation (H - (E₀ : ℂ) • (1 : Operator q L)) ψ := by
  have h := expectation_nonneg hgap ψ
  unfold expectation at h ⊢
  simp only [act_sub, act_smul, act_one, act_outer, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K] at h ⊢
  have hin : inner ℂ ψ Ω = (starRingEnd ℂ) (inner ℂ Ω ψ) := by
    rw [← inner_conj_symm]
  rw [hin, RCLike.mul_conj] at h
  simp only [RCLike.ofReal_eq_complex_ofReal, Complex.sub_re, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re,
    ← Complex.ofReal_sub] at h ⊢
  linarith

 

theorem energy_vector {q L : ℕ} {H : Operator q L} {E₀ Δ : ℝ}
    {Ω ψ : State q L} (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (hψ : ‖ψ‖ = 1)
    (hgap : GlobalGap H E₀ Δ Ω) :
    ∃ θ : ℝ,
      (∀ φ : ℝ, ‖ψ - phase θ • Ω‖ ≤ ‖ψ - phase φ • Ω‖) ∧
      ‖ψ - phase θ • Ω‖ ^ 2 ≤ 2 / Δ *
        expectation (H - (E₀ : ℂ) • (1 : Operator q L)) ψ := by
  obtain ⟨θ, hmin, heq⟩ := exists_phase_minimizer ψ Ω
  refine ⟨θ, hmin, ?_⟩
  have hsym : ‖inner ℂ ψ Ω‖ = ‖inner ℂ Ω ψ‖ := norm_inner_symm ψ Ω
  rw [hψ, hΩ, hsym] at heq
  have hr1 : ‖inner ℂ Ω ψ‖ ≤ 1 := by
    simpa [hΩ, hψ] using norm_inner_le_norm (𝕜 := ℂ) Ω ψ
  have hr0 := norm_nonneg (inner ℂ Ω ψ)
  have hr2 : ‖inner ℂ Ω ψ‖ ^ 2 ≤ ‖inner ℂ Ω ψ‖ := by nlinarith
  have hg := globalGap_expectation hgap ψ
  rw [hψ, one_pow] at hg
  have hle : Δ * (1 - ‖inner ℂ Ω ψ‖) ≤
      expectation (H - (E₀ : ℂ) • (1 : Operator q L)) ψ :=
    (mul_le_mul_of_nonneg_left (by linarith :
      1 - ‖inner ℂ Ω ψ‖ ≤ 1 - ‖inner ℂ Ω ψ‖ ^ 2) hΔ.le).trans hg
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hΔ).mpr
  calc
    _ = 2 * (Δ * (1 - ‖inner ℂ Ω ψ‖)) := by rw [heq]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (by norm_num)



 

theorem phaseErrorAtMost_iff_exists {q L : ℕ} (x Ω : State q L) (ε : ℝ) :
    PhaseErrorAtMost x Ω ε ↔ ∃ θ : ℝ, ‖normalized x - phase θ • Ω‖ ≤ ε := by
  constructor
  · rintro ⟨θ, _, hθ⟩
    exact ⟨θ, hθ⟩
  · rintro ⟨θ, hθ⟩
    obtain ⟨φ, hmin, _⟩ := exists_phase_minimizer (normalized x) Ω
    exact ⟨φ, hmin, (hmin θ).trans hθ⟩

 
def productState {q L : ℕ} (b : Vertex L → Fin q → ℂ) : State q L :=
  toLp 2 (fun x => ∏ v : Vertex L, b v (x v))

 
def productPEPS {q L : ℕ} (b : Vertex L → Fin q → ℂ) : PEPS q L where
  bondDim := fun _ => 1
  bondDim_pos := fun _ => Nat.zero_lt_one
  tensor := fun v _ a => b v a

@[simp] theorem productPEPS_contract {q L : ℕ} (b : Vertex L → Fin q → ℂ) :
    (productPEPS b).contract = productState b := by
  classical
  ext x
  change (∑ _a : Edge L → Fin 1, ∏ v : Vertex L, b v (x v)) =
    ∏ v : Vertex L, b v (x v)
  simp

theorem maxBondDim_le_iff {q L : ℕ} (P : PEPS q L) (D : ℕ) :
    P.maxBondDim ≤ D ↔ ∀ e, P.bondDim e ≤ D := by
  classical
  simp [PEPS.maxBondDim, Finset.sup_le_iff]

theorem productPEPS_bond_bound {q L : ℕ} (b : Vertex L → Fin q → ℂ) :
    (productPEPS b).maxBondDim ≤ 1 := by
  rw [maxBondDim_le_iff]
  exact fun _ => le_rfl



 

theorem normalized_dist_le {q L : ℕ} {x y : State q L}
    (hx : x ≠ 0) (hy : ‖y‖ = 1) :
    ‖normalized x - y‖ ≤ 2 * ‖x - y‖ := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hself : ‖normalized x - x‖ = |1 - ‖x‖| := by
    have heq : normalized x - x = (((‖x‖ : ℂ)⁻¹ - 1) : ℂ) • x := by
      simp [normalized, sub_smul]
    rw [heq, norm_smul]
    have hscalar : ‖(‖x‖ : ℂ)⁻¹ - 1‖ = |‖x‖⁻¹ - 1| := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hscalar, ← abs_of_nonneg (norm_nonneg x), ← abs_mul]
    congr 1
    rw [abs_of_nonneg (norm_nonneg x), sub_mul, inv_mul_cancel₀ hn, one_mul]
  have hrev : |1 - ‖x‖| ≤ ‖x - y‖ := by
    simpa only [hy, norm_sub_rev] using abs_norm_sub_norm_le y x
  calc
    ‖normalized x - y‖ = ‖(normalized x - x) + (x - y)‖ := by
      congr 1
      abel
    _ ≤ ‖normalized x - x‖ + ‖x - y‖ := norm_add_le _ _
    _ = |1 - ‖x‖| + ‖x - y‖ := by rw [hself]
    _ ≤ ‖x - y‖ + ‖x - y‖ := by linarith
    _ = _ := by ring

theorem normalized_smul_phase {q L : ℕ} (x : State q L) {a : ℂ} (ha : a ≠ 0) :
    normalized (a • x) = phase a.arg • normalized x := by
  have hna : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr ha)
  have hpolar : (‖a‖ : ℂ) * phase a.arg = a := Complex.norm_mul_exp_arg_mul_I a
  have hquot : (‖a‖ : ℂ)⁻¹ * a = phase a.arg := by
    calc
      (‖a‖ : ℂ)⁻¹ * a = (‖a‖ : ℂ)⁻¹ * ((‖a‖ : ℂ) * phase a.arg) :=
        congrArg ((‖a‖ : ℂ)⁻¹ * ·) hpolar.symm
      _ = phase a.arg := by rw [← mul_assoc, inv_mul_cancel₀ hna, one_mul]
  unfold normalized
  rw [norm_smul, Complex.ofReal_mul, mul_inv, smul_smul, smul_smul]
  congr 1
  calc
    (‖a‖ : ℂ)⁻¹ * (‖x‖ : ℂ)⁻¹ * a = (‖x‖ : ℂ)⁻¹ * ((‖a‖ : ℂ)⁻¹ * a) := by ring
    _ = phase a.arg * (‖x‖ : ℂ)⁻¹ := by rw [hquot]; ring

 

theorem column_of_relative_error {q L : ℕ} {v Ω : State q L} {a : ℂ} {η : ℝ}
    (hΩ : ‖Ω‖ = 1) (hη1 : η < 1) (ha : a ≠ 0)
    (herr : ‖v - a • Ω‖ ≤ η * ‖a‖) :
    v ≠ 0 ∧ PhaseErrorAtMost v Ω (2 * η) := by
  let w : State q L := a⁻¹ • v
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hscale : w - Ω = a⁻¹ • (v - a • Ω) := by
    simp [w, smul_sub, smul_smul, inv_mul_cancel₀ ha]
  have hwerr : ‖w - Ω‖ ≤ η := by
    rw [hscale, norm_smul, norm_inv]
    calc
      ‖a‖⁻¹ * ‖v - a • Ω‖ ≤ ‖a‖⁻¹ * (η * ‖a‖) :=
        mul_le_mul_of_nonneg_left herr (inv_nonneg.mpr (norm_nonneg a))
      _ = η := by rw [mul_left_comm, inv_mul_cancel₀ hna, mul_one]
  have hw : w ≠ 0 := by
    intro heq
    have : (1 : ℝ) ≤ η := by simpa [heq, hΩ] using hwerr
    linarith
  have hv : v ≠ 0 := by
    intro hv
    apply hw
    simp [w, hv]
  refine ⟨hv, (phaseErrorAtMost_iff_exists v Ω _).mpr ⟨a.arg, ?_⟩⟩
  have hcv : a • w = v := by simp [w, smul_smul, mul_inv_cancel₀ ha]
  have heq : normalized v = phase a.arg • normalized w := by
    rw [← hcv, normalized_smul_phase w ha]
  calc
    ‖normalized v - phase a.arg • Ω‖ = ‖normalized w - Ω‖ := by
      rw [heq, ← smul_sub, norm_smul, norm_phase, one_mul]
    _ ≤ 2 * ‖w - Ω‖ := normalized_dist_le hw hΩ
    _ ≤ 2 * η := mul_le_mul_of_nonneg_left hwerr (by norm_num)



 

theorem column_from_sum_sq_error {ι : Type*} [Fintype ι] {q L : ℕ}
    (v : ι → State q L) (a : ι → ℂ) (Ω : State q L) {η : ℝ}
    (hΩ : ‖Ω‖ = 1) (hη : 0 ≤ η) (hη1 : η < 1)
    (ha : ∑ j : ι, ‖a j‖ ^ 2 = 1)
    (herr : ∑ j : ι, ‖v j - a j • Ω‖ ^ 2 ≤ η ^ 2) :
    ∃ j : ι, v j ≠ 0 ∧ PhaseErrorAtMost (v j) Ω (2 * η) := by
  classical
  have hgood : ∃ j : ι, a j ≠ 0 ∧ ‖v j - a j • Ω‖ ≤ η * ‖a j‖ := by
    by_contra hbad
    push Not at hbad
    have hstrict (j : ι) (hj : a j ≠ 0) :
        η ^ 2 * ‖a j‖ ^ 2 < ‖v j - a j • Ω‖ ^ 2 := by
      rw [← mul_pow]
      exact (sq_lt_sq₀ (mul_nonneg hη (norm_nonneg _))
        (norm_nonneg _)).mpr (hbad j hj)
    have hle (j : ι) : η ^ 2 * ‖a j‖ ^ 2 ≤ ‖v j - a j • Ω‖ ^ 2 := by
      by_cases hj : a j = 0
      · simp only [hj, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
        exact sq_nonneg _
      · exact (hstrict j hj).le
    have hnz : ∃ j : ι, a j ≠ 0 := by
      by_contra hnz
      push Not at hnz
      simp [hnz] at ha
    obtain ⟨j, hj⟩ := hnz
    have hsumlt := Finset.sum_lt_sum (s := Finset.univ) (fun i _ => hle i)
      ⟨j, Finset.mem_univ _, hstrict j hj⟩
    rw [← Finset.mul_sum, ha, mul_one] at hsumlt
    exact (not_lt_of_ge herr) hsumlt
  obtain ⟨j, hj, hrel⟩ := hgood
  exact ⟨j, column_of_relative_error hΩ hη1 hj hrel⟩

end PolynomialPEPS

end

end OAI
