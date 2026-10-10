import OAI.Geometry.Arnold.Obstruction

namespace OAI

noncomputable section
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff

namespace ArnoldCounterexample
namespace ThreePoints

abbrev R3 := Fin 3 → ℝ
abbrev Pair := R3 × R3

def sqNorm (x : R3) : ℝ := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2

def sphereProduct : Set Pair := {q | sqNorm q.1 = 1 ∧ sqNorm q.2 = 1}

def pole : R3 := ![0, 0, 1]
def east : R3 := ![1, 0, 0]

/-- A polynomial with three constrained critical points. -/
def f (q : Pair) : ℝ :=
  q.1 0 + q.1 0 * q.2 0 + q.1 1 * q.2 1 + (q.1 2 - 1) * q.2 2

/-- The constrained critical equations of the polynomial. -/
def MultiplierCritical (q : Pair) : Prop :=
  q ∈ sphereProduct ∧ ∃ lam μ : ℝ,
    1 + q.2 0 = lam * q.1 0 ∧ q.2 1 = lam * q.1 1 ∧ q.2 2 = lam * q.1 2 ∧
    q.1 0 = μ * q.2 0 ∧ q.1 1 = μ * q.2 1 ∧ q.1 2 - 1 = μ * q.2 2

def qzero : Pair := (pole, -east)
def qplus : Pair := (![Real.sqrt 3 / 2, 0, -1/2], ![1/2, 0, -Real.sqrt 3 / 2])
def qminus : Pair := (![-Real.sqrt 3 / 2, 0, -1/2], ![1/2, 0, Real.sqrt 3 / 2])

/-- Algebraic elimination of every solution, without a nondegeneracy assumption.
We eliminate using μ instead of t=|x-p|; μ²=t², so the remaining factor is μ²=3. -/
lemma classify_coordinates
    {x₀ x₁ x₂ y₀ y₁ y₂ lam μ : ℝ}
    (hx : x₀^2 + x₁^2 + x₂^2 = 1)
    (hy : y₀^2 + y₁^2 + y₂^2 = 1)
    (h₀ : 1 + y₀ = lam * x₀) (h₁ : y₁ = lam * x₁) (h₂ : y₂ = lam * x₂)
    (g₀ : x₀ = μ * y₀) (g₁ : x₁ = μ * y₁) (g₂ : x₂ - 1 = μ * y₂) :
    (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 1 ∧ y₀ = -1 ∧ y₁ = 0 ∧ y₂ = 0) ∨
    (μ^2 = 3 ∧ x₀ = μ/2 ∧ x₁ = 0 ∧ x₂ = -1/2 ∧
      y₀ = 1/2 ∧ y₁ = 0 ∧ y₂ = -μ/2) := by
  by_cases hμ : μ = 0
  · left
    have hx₀ : x₀ = 0 := by simpa [hμ] using g₀
    have hx₁ : x₁ = 0 := by simpa [hμ] using g₁
    have hx₂ : x₂ = 1 := by simp [hμ] at g₂; linarith
    have hy₀ : y₀ = -1 := by rw [hx₀] at h₀; linarith
    have hy₁ : y₁ = 0 := by nlinarith [sq_nonneg y₂]
    have hy₂ : y₂ = 0 := by nlinarith [sq_nonneg y₁]
    exact ⟨hx₀, hx₁, hx₂, hy₀, hy₁, hy₂⟩
  · right
    have gx₂ : x₂ = 1 + μ * y₂ := by linarith
    have hn : μ * (μ + 2 * y₂) = 0 := by
      have he : μ^2 * (y₀^2 + y₁^2 + y₂^2 - 1) + μ * (μ + 2 * y₂) =
          x₀^2 + x₁^2 + x₂^2 - 1 := by
        rw [g₀, g₁, gx₂]
        ring
      simpa [hx, hy] using he
    have hμy : μ + 2 * y₂ = 0 := (mul_eq_zero.mp hn).resolve_left hμ
    have hy₂ : y₂ = -μ/2 := by linarith
    have hc₀ : (1 - lam * μ) * y₀ = -1 := by rw [g₀] at h₀; nlinarith
    have hc₁ : (1 - lam * μ) * y₁ = 0 := by rw [g₁] at h₁; nlinarith
    have hc : 1 - lam * μ ≠ 0 := by intro h; rw [h] at hc₀; norm_num at hc₀
    have hy₁ : y₁ = 0 := (mul_eq_zero.mp hc₁).resolve_left hc
    have hlam : lam ≠ 0 := by
      intro h
      rw [h] at h₂
      simp only [zero_mul] at h₂
      exact hμ (by linarith)
    have hdot : y₀ + 1 = lam * (μ + y₂) := by
      calc
        y₀ + 1 = (1 + y₀) * y₀ + y₁ * y₁ + y₂ * y₂ := by nlinarith [hy]
        _ = (lam * x₀) * y₀ + (lam * x₁) * y₁ + (lam * x₂) * y₂ := by
          rw [← h₀, ← h₁, ← h₂]
        _ = lam * (μ * (y₀^2 + y₁^2 + y₂^2) + y₂) := by rw [g₀, g₁, gx₂]; ring
        _ = lam * (μ + y₂) := by rw [hy]; ring
    have he : (lam * μ) * (2 * y₀ - 1) = 0 := by
      rw [g₀] at h₀
      rw [hy₂] at hdot
      nlinarith only [h₀, hdot]
    have hy₀ : y₀ = 1/2 := by
      have := (mul_eq_zero.mp he).resolve_left (mul_ne_zero hlam hμ)
      linarith
    have hμsq : μ^2 = 3 := by rw [hy₀, hy₁, hy₂] at hy; nlinarith only [hy]
    refine ⟨hμsq, ?_, ?_, ?_, hy₀, hy₁, hy₂⟩
    · rw [g₀, hy₀]; ring
    · rw [g₁, hy₁]; ring
    · rw [gx₂, hy₂]; nlinarith only [hμsq]

lemma qzero_critical : MultiplierCritical qzero := by
  refine ⟨⟨?_, ?_⟩, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [sqNorm, qzero, pole, east, Matrix.cons_val_two]

lemma qplus_critical : MultiplierCritical qplus := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨⟨?_, ?_⟩, Real.sqrt 3, Real.sqrt 3, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [sqNorm, qplus, Matrix.cons_val_two] <;> nlinarith only [hs]

lemma qminus_critical : MultiplierCritical qminus := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨⟨?_, ?_⟩, -Real.sqrt 3, -Real.sqrt 3, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [sqNorm, qminus, Matrix.cons_val_two] <;> nlinarith only [hs]

/-- Exhaustiveness includes the isolated degenerate point. -/
theorem multiplierCritical_iff (q : Pair) :
    MultiplierCritical q ↔ q = qzero ∨ q = qplus ∨ q = qminus := by
  constructor
  · rintro ⟨⟨hx, hy⟩, lam, μ, h₀, h₁, h₂, g₀, g₁, g₂⟩
    rcases classify_coordinates hx hy h₀ h₁ h₂ g₀ g₁ g₂ with h | h
    · left
      rcases h with ⟨hx₀, hx₁, hx₂, hy₀, hy₁, hy₂⟩
      apply Prod.ext <;> ext i <;> fin_cases i <;> simp [qzero, pole, east, hx₀, hx₁, hx₂, hy₀, hy₁, hy₂]
    · rcases h with ⟨hμ, hx₀, hx₁, hx₂, hy₀, hy₁, hy₂⟩
      have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have hm : μ = Real.sqrt 3 ∨ μ = -Real.sqrt 3 :=
        sq_eq_sq_iff_eq_or_eq_neg.mp (hμ.trans hs.symm)
      rcases hm with hm | hm
      · right; left
        apply Prod.ext <;> ext i <;> fin_cases i <;> simp [qplus, hx₀, hx₁, hx₂, hy₀, hy₁, hy₂, hm]
      · right; right
        apply Prod.ext <;> ext i <;> fin_cases i <;> simp [qminus, hx₀, hx₁, hx₂, hy₀, hy₁, hy₂, hm]
  · rintro (rfl | rfl | rfl)
    · exact qzero_critical
    · exact qplus_critical
    · exact qminus_critical

lemma qzero_ne_qplus : qzero ≠ qplus := by
  intro h
  have := congrArg (fun q : Pair => q.2 0) h
  norm_num [qzero, pole, east, qplus] at this

lemma qzero_ne_qminus : qzero ≠ qminus := by
  intro h
  have := congrArg (fun q : Pair => q.2 0) h
  norm_num [qzero, pole, east, qminus] at this

lemma qplus_ne_qminus : qplus ≠ qminus := by
  intro h
  have he := congrArg (fun q : Pair => q.1 0) h
  have hp : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  norm_num [qplus, qminus] at he
  linarith

theorem multiplierCritical_set : {q : Pair | MultiplierCritical q} =
    {qzero, qplus, qminus} := by
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    multiplierCritical_iff]

/-- A finite cardinality assertion, not ncard's default zero for infinite sets. -/
theorem multiplierCritical_encard : {q : Pair | MultiplierCritical q}.encard = 3 := by
  rw [multiplierCritical_set, Set.encard_insert_of_notMem]
  · rw [Set.encard_pair qplus_ne_qminus]
    norm_num
  · simp [qzero_ne_qplus, qzero_ne_qminus]

lemma f_qzero : f qzero = 0 := by norm_num [f, qzero, pole, east, Matrix.cons_val_two]
lemma f_qplus : f qplus = 3 * Real.sqrt 3 / 2 := by norm_num [f, qplus, Matrix.cons_val_two]; ring
lemma f_qminus : f qminus = -(3 * Real.sqrt 3 / 2) := by norm_num [f, qminus, Matrix.cons_val_two]; ring

/-- Smoothness of the actual ambient polynomial, so its restriction is smooth. -/
theorem f_contDiff : ContDiff ℝ ∞ f := by unfold f; fun_prop

open scoped Matrix

lemma dot_self (x : R3) : x ⬝ᵥ x = sqNorm x := by
  simp [dotProduct, Fin.sum_univ_succ, sqNorm, pow_two]
  ring

/-- The elementary tangent-annihilator lemma supplies (rather than assumes)
  the Lagrange multipliers. -/
lemma annihilator_sphere {x a : R3} (hx : sqNorm x = 1) :
    (∀ u : R3, x ⬝ᵥ u = 0 → a ⬝ᵥ u = 0) ↔ ∃ lam : ℝ, a = lam • x := by
  constructor
  · intro h
    let lam : ℝ := x ⬝ᵥ a
    let u : R3 := a - lam • x
    have hxu : x ⬝ᵥ u = 0 := by
      dsimp [u]
      rw [dotProduct_sub, dotProduct_smul, dot_self, hx]
      simp [lam]
    have hau : a ⬝ᵥ u = 0 := h u hxu
    have huu : u ⬝ᵥ u = 0 := by
      change (a - lam • x) ⬝ᵥ u = 0
      rw [sub_dotProduct, smul_dotProduct, hau, hxu, smul_zero, sub_zero]
    exact ⟨lam, sub_eq_zero.mp (dotProduct_self_eq_zero.mp huu)⟩
  · rintro ⟨lam, rfl⟩ u hu
    rw [smul_dotProduct, hu, smul_zero]

def firstCoord (i : Fin 3) : Pair →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ R3 R3)

def secondCoord (i : Fin 3) : Pair →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ R3 R3)

/-- The ambient differential of the polynomial. -/
def df (q : Pair) : Pair →L[ℝ] ℝ :=
  (1 + q.2 0) • firstCoord 0 + q.2 1 • firstCoord 1 + q.2 2 • firstCoord 2 +
  q.1 0 • secondCoord 0 + q.1 1 • secondCoord 1 + (q.1 2 - 1) • secondCoord 2

lemma df_apply (q r : Pair) : df q r =
    (east + q.2) ⬝ᵥ r.1 + (q.1 - pole) ⬝ᵥ r.2 := by
  simp [df, east, pole, firstCoord, secondCoord, dotProduct, Fin.sum_univ_succ]
  ring

lemma f_hasFDerivAt (q : Pair) : HasFDerivAt f (df q) q := by
  have h₀ := (firstCoord 0).hasFDerivAt (x := q)
  have h₁ := (firstCoord 1).hasFDerivAt (x := q)
  have h₂ := (firstCoord 2).hasFDerivAt (x := q)
  have k₀ := (secondCoord 0).hasFDerivAt (x := q)
  have k₁ := (secondCoord 1).hasFDerivAt (x := q)
  have k₂ := (secondCoord 2).hasFDerivAt (x := q)
  convert! ((h₀.add (h₀.mul k₀)).add (h₁.mul k₁)).add ((h₂.sub_const 1).mul k₂) using 1
  apply ContinuousLinearMap.ext
  intro r
  simp [df, firstCoord, secondCoord]
  ring

/-- dh vanishes on the full constrained tangent of S² × S². -/
def TangentCritical (q : Pair) : Prop :=
  q ∈ sphereProduct ∧ ∀ u v : R3,
    q.1 ⬝ᵥ u = 0 → q.2 ⬝ᵥ v = 0 → fderiv ℝ f q (u, v) = 0

lemma tangentCritical_iff_multiplierCritical (q : Pair) :
    TangentCritical q ↔ MultiplierCritical q := by
  have hd : fderiv ℝ f q = df q := (f_hasFDerivAt q).fderiv
  constructor
  · rintro ⟨hq, h⟩
    have ha : ∀ u : R3, q.1 ⬝ᵥ u = 0 → (east + q.2) ⬝ᵥ u = 0 := by
      intro u hu
      have := h u 0 hu (dotProduct_zero _)
      simpa [hd, df_apply] using this
    have hb : ∀ v : R3, q.2 ⬝ᵥ v = 0 → (q.1 - pole) ⬝ᵥ v = 0 := by
      intro v hv
      have := h 0 v (dotProduct_zero _) hv
      simpa [hd, df_apply] using this
    obtain ⟨lam, hlam⟩ := (annihilator_sphere hq.1).mp ha
    obtain ⟨μ, hμ⟩ := (annihilator_sphere hq.2).mp hb
    refine ⟨hq, lam, μ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [east] using congrFun hlam 0
    · simpa [east] using congrFun hlam 1
    · simpa [east] using congrFun hlam 2
    · simpa [pole] using congrFun hμ 0
    · simpa [pole] using congrFun hμ 1
    · simpa [pole] using congrFun hμ 2
  · rintro ⟨hq, lam, μ, h₀, h₁, h₂, g₀, g₁, g₂⟩
    have ha : east + q.2 = lam • q.1 := by
      ext i; fin_cases i <;> simp [east, h₀, h₁, h₂]
    have hb : q.1 - pole = μ • q.2 := by
      ext i; fin_cases i <;> simp [pole, g₀, g₁, g₂]
    refine ⟨hq, ?_⟩
    intro u v hu hv
    rw [hd, df_apply, ha, hb, smul_dotProduct, smul_dotProduct, hu, hv]
    simp

/-- The complete critical-point calculation in constrained tangent form. -/
theorem tangentCritical_iff (q : Pair) :
    TangentCritical q ↔ q = qzero ∨ q = qplus ∨ q = qminus := by
  rw [tangentCritical_iff_multiplierCritical, multiplierCritical_iff]

theorem tangentCritical_encard : {q : Pair | TangentCritical q}.encard = 3 := by
  simpa only [tangentCritical_iff_multiplierCritical] using multiplierCritical_encard

end ThreePoints
end ArnoldCounterexample

end

end OAI
