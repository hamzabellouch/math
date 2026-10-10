import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem exists_variational_DN
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : Submodule ℝ V) [hK : IsClosed (K : Set V)]
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hcoer : IsCoercive (((B.comp K.subtypeL).flip.comp K.subtypeL).flip)) :
    ∃ Λ : (V ⧸ K) →L[ℝ] (V ⧸ K) →L[ℝ] ℝ,
    ∀ f : V ⧸ K, ∃ u : V,
      K.mkQ u = f ∧ (∀ h ∈ K, B u h = 0) ∧
      (∀ u', K.mkQ u' = f → (∀ h ∈ K, B u' h = 0) → u' = u) ∧
      ∀ v : V, Λ f (K.mkQ v) = B u v := by
  let R : (V ⧸ K) →L[ℝ] V :=
    K.orthogonal.subtypeL.comp K.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hR (f : V ⧸ K) : K.mkQ (R f) = f := by
    change Submodule.Quotient.mk (K.quotientEquivOrthogonal f).val = f
    rw [← K.quotientEquivOrthogonal_symm_eq_mk]
    exact K.quotientEquivOrthogonal.symm_apply_apply f
  let A : K →L[ℝ] K →L[ℝ] ℝ := ((B.comp K.subtypeL).flip.comp K.subtypeL).flip
  let S : V →L[ℝ] K →L[ℝ] ℝ := (B.flip.comp K.subtypeL).flip
  let W : V →L[ℝ] K :=
    hcoer.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
      ((InnerProductSpace.toDual ℝ K).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp S)
  have hW (v : V) (h : K) : B (W v).val h.val = B v h.val := by
    change A (W v) h = S v h
    rw [← hcoer.continuousLinearEquivOfBilin_apply]
    change inner ℝ (hcoer.continuousLinearEquivOfBilin
      (hcoer.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ K).symm (S v)))) h = _
    rw [hcoer.continuousLinearEquivOfBilin.apply_symm_apply]
    exact congrArg (fun g : K →L[ℝ] ℝ => g h)
      ((InnerProductSpace.toDual ℝ K).apply_symm_apply (S v))
  let E : (V ⧸ K) →L[ℝ] V := R - K.subtypeL.comp (W.comp R)
  have hEtrace (f : V ⧸ K) : K.mkQ (E f) = f := by
    change K.mkQ (R f - (W (R f)).val) = f
    rw [map_sub, hR]
    simp
  have hEharm (f : V ⧸ K) (h : V) (hh : h ∈ K) : B (E f) h = 0 := by
    change B (R f - (W (R f)).val) h = 0
    rw [map_sub, sub_apply, hW (R f) ⟨h, hh⟩, sub_self]
  have huniq (f : V ⧸ K) (u : V) (hu : K.mkQ u = f)
      (huh : ∀ h ∈ K, B u h = 0) : u = E f := by
    have hdmem : u - E f ∈ K := (Submodule.Quotient.eq K).mp (hu.trans (hEtrace f).symm)
    let d : K := ⟨u - E f, hdmem⟩
    have hd : A d d = 0 := by
      change B (u - E f) (u - E f) = 0
      rw [map_sub B u (E f)]
      change B u (u - E f) - B (E f) (u - E f) = 0
      rw [huh _ hdmem, hEharm _ _ hdmem, sub_self]
    obtain ⟨c, hc, hbound⟩ := hcoer
    have hz : ‖d‖ = 0 := by
      have hb := hbound d
      rw [hd] at hb
      by_contra hn
      have hp : 0 < ‖d‖ := (norm_nonneg d).lt_of_ne (Ne.symm hn)
      exact (not_lt_of_ge hb) (mul_pos (mul_pos hc hp) hp)
    have heq : d = 0 := norm_eq_zero.mp hz
    exact sub_eq_zero.mp (congrArg (fun x : K => x.val) heq)
  let Λ : (V ⧸ K) →L[ℝ] (V ⧸ K) →L[ℝ] ℝ := ((B.comp E).flip.comp R).flip
  refine ⟨Λ, fun f => ⟨E f, hEtrace f, hEharm f, fun u hu huh => huniq f u hu huh, ?_⟩⟩
  intro v
  change B (E f) (R (K.mkQ v)) = B (E f) v
  have hmem : v - R (K.mkQ v) ∈ K := (Submodule.Quotient.eq K).mp (hR (K.mkQ v)).symm
  have hh := hEharm f _ hmem
  rw [map_sub] at hh
  exact (sub_eq_zero.mp hh).symm

abbrev DiagonalTriple := Fin 3 → ℝ

def coordinateJoin (i : Fin 3) (θ : ℝ) (α β : DiagonalTriple) : DiagonalTriple :=
  fun j => if j = i then (θ / α j + (1 - θ) / β j)⁻¹
    else θ * α j + (1 - θ) * β j

inductive IsFiniteLaminate (a b : ℝ) : DiagonalTriple → Prop
  | scalar (s : ℝ) (ha : a < s) (hb : s < b) : IsFiniteLaminate a b (fun _ => s)
  | join (i : Fin 3) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
      {α β : DiagonalTriple} (hα : IsFiniteLaminate a b α)
      (hβ : IsFiniteLaminate a b β) : IsFiniteLaminate a b (coordinateJoin i θ α β)

lemma convexComb_lt {θ η x y z : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hsum : θ + η = 1) (hx : x < z) (hy : y < z) : θ * x + η * y < z := by
  rcases eq_or_lt_of_le hθ with h | h
  · subst θ
    have : η = 1 := by simpa using hsum
    simpa [this] using hy
  · calc
      θ * x + η * y < θ * z + η * z :=
        add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx h)
          (mul_le_mul_of_nonneg_left hy.le hη)
      _ = z := by rw [← add_mul, hsum, one_mul]

lemma lt_convexComb {θ η x y z : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hsum : θ + η = 1) (hx : z < x) (hy : z < y) : z < θ * x + η * y := by
  have hh := convexComb_lt hθ hη hsum (neg_lt_neg hx) (neg_lt_neg hy)
  nlinarith

lemma harmonic_mean_bounds {a b x y θ : ℝ} (ha : 0 < a)
    (hx : a < x ∧ x < b) (hy : a < y ∧ y < b) (hθ : 0 ≤ θ ∧ θ ≤ 1) :
    a < (θ / x + (1 - θ) / y)⁻¹ ∧ (θ / x + (1 - θ) / y)⁻¹ < b := by
  have hx0 : 0 < x := lt_trans ha hx.1
  have hy0 : 0 < y := lt_trans ha hy.1
  have hb : 0 < b := lt_trans hx0 hx.2
  have hs : 0 < θ / x + (1 - θ) / y := by
    rcases lt_or_eq_of_le hθ.1 with hθ0 | rfl
    · exact add_pos_of_pos_of_nonneg (div_pos hθ0 hx0) (div_nonneg (sub_nonneg.mpr hθ.2) hy0.le)
    · simp [hy0]
  have hl : θ / x + (1 - θ) / y < a⁻¹ := by
    have hxi : x⁻¹ < a⁻¹ := (inv_lt_inv₀ hx0 ha).2 hx.1
    have hyi : y⁻¹ < a⁻¹ := (inv_lt_inv₀ hy0 ha).2 hy.1
    have he := convexComb_lt hθ.1 (sub_nonneg.mpr hθ.2) (by ring : θ + (1-θ) = 1) hxi hyi
    simpa [div_eq_mul_inv] using he
  have hu : b⁻¹ < θ / x + (1 - θ) / y := by
    have hxi : b⁻¹ < x⁻¹ := (inv_lt_inv₀ hb hx0).2 hx.2
    have hyi : b⁻¹ < y⁻¹ := (inv_lt_inv₀ hb hy0).2 hy.2
    have he := lt_convexComb hθ.1 (sub_nonneg.mpr hθ.2) (by ring : θ + (1-θ) = 1) hxi hyi
    simpa [div_eq_mul_inv] using he
  constructor
  · have hh := (inv_lt_inv₀ (inv_pos.mpr ha) hs).2 hl
    simpa using hh
  · have hh := (inv_lt_inv₀ hs (inv_pos.mpr hb)).2 hu
    simpa using hh

lemma coordinateJoin_bounds {a b : ℝ} (ha : 0 < a) {α β : DiagonalTriple}
    (hα : ∀ j, a < α j ∧ α j < b) (hβ : ∀ j, a < β j ∧ β j < b)
    (i : Fin 3) {θ : ℝ} (hθ : 0 ≤ θ ∧ θ ≤ 1) :
    ∀ j, a < coordinateJoin i θ α β j ∧ coordinateJoin i θ α β j < b := by
  intro j
  by_cases hji : j = i
  · simpa [coordinateJoin, hji] using harmonic_mean_bounds ha (hα j) (hβ j) hθ
  · simp only [coordinateJoin, ite_eq_right hji]
    constructor
    · have he := lt_convexComb hθ.1 (sub_nonneg.mpr hθ.2)
        (by ring : θ + (1-θ) = 1) (hα j).1 (hβ j).1
      simpa using he
    · have he := convexComb_lt hθ.1 (sub_nonneg.mpr hθ.2)
        (by ring : θ + (1-θ) = 1) (hα j).2 (hβ j).2
      simpa using he

lemma IsFiniteLaminate.bounds {a b : ℝ} (ha : 0 < a) {α : DiagonalTriple}
    (h : IsFiniteLaminate a b α) : ∀ j, a < α j ∧ α j < b := by
  induction h with
  | scalar s has hsb => exact fun _ => ⟨has, hsb⟩
  | join i θ hθ₀ hθ₁ hα hβ ihα ihβ =>
    exact coordinateJoin_bounds ha ihα ihβ i ⟨hθ₀, hθ₁⟩

lemma half_harmonic_eq_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y = 2) : ((1 / 2 : ℝ) / x + (1 - 1 / 2) / y)⁻¹ = x * y := by
  have h : (1 / 2 : ℝ) / x + (1 - 1 / 2) / y = (x * y)⁻¹ := by
    field_simp
    nlinarith
  rw [h, inv_inv]

lemma coordinateJoin_half_smul (i : Fin 3) (v : DiagonalTriple) {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y = 2) :
    coordinateJoin i (1/2) (x • v) (y • v) =
      fun j => if j = i then x * y * v j else v j := by
  ext j
  by_cases hji : j = i
  · simp only [coordinateJoin, hji, ite_true, Pi.smul_apply, smul_eq_mul]
    have hden : (1 / 2 : ℝ) / (x * v j) + (1 - 1 / 2) / (y * v j) =
        ((1 / 2 : ℝ) / x + (1 - 1 / 2) / y) / v j := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hji] at hden
    rw [hden, div_eq_mul_inv, mul_inv_rev, inv_inv, half_harmonic_eq_mul hx hy hxy]
    ring
  · simp only [coordinateJoin, hji, ite_false, Pi.smul_apply, smul_eq_mul]
    calc
      (1 / 2 : ℝ) * (x * v j) + (1 - 1 / 2) * (y * v j) = (x + y) / 2 * v j := by ring
      _ = v j := by rw [hxy]; ring

def productFactorMinus (M : ℝ) (α : DiagonalTriple) (i : Fin 3) : ℝ :=
  1 - Real.sqrt (1 - α i / M)

def productFactorPlus (M : ℝ) (α : DiagonalTriple) (i : Fin 3) : ℝ :=
  1 + Real.sqrt (1 - α i / M)

lemma productFactor_spec {M : ℝ} (hM : 0 < M) (α : DiagonalTriple) (i : Fin 3)
    (hα : 0 < α i ∧ α i < M) :
    0 < productFactorMinus M α i ∧ 0 < productFactorPlus M α i ∧
    productFactorMinus M α i + productFactorPlus M α i = 2 ∧
    productFactorMinus M α i * productFactorPlus M α i = α i / M := by
  have hq : 0 < α i / M := div_pos hα.1 hM
  have hq1 : α i / M < 1 := (div_lt_one hM).2 hα.2
  have hs0 := Real.sqrt_nonneg (1 - α i / M)
  have hs2 := Real.sq_sqrt (show 0 ≤ 1 - α i / M by linarith)
  dsimp [productFactorMinus, productFactorPlus]
  constructor
  · nlinarith
  constructor
  · linarith
  constructor
  · ring
  · nlinarith

lemma IsFiniteLaminate.half_smul {a b : ℝ} (i : Fin 3) (v : DiagonalTriple)
    {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y = 2)
    (hxl : IsFiniteLaminate a b (x • v)) (hyl : IsFiniteLaminate a b (y • v)) :
    IsFiniteLaminate a b (fun j => if j = i then x * y * v j else v j) := by
  rw [← coordinateJoin_half_smul i v hx hy hxy]
  exact IsFiniteLaminate.join i (1/2) (by norm_num) (by norm_num) hxl hyl

theorem product_eight_leaf_laminate {a b M : ℝ} (x y : Fin 3 → ℝ)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) (hsum : ∀ i, x i + y i = 2)
    (hleaf : ∀ t₀ t₁ t₂ : ℝ, (t₀ = x 0 ∨ t₀ = y 0) →
      (t₁ = x 1 ∨ t₁ = y 1) → (t₂ = x 2 ∨ t₂ = y 2) →
      a < M * t₀ * t₁ * t₂ ∧ M * t₀ * t₁ * t₂ < b) :
    IsFiniteLaminate a b (fun i => M * x i * y i) := by
  have h₀ (t₁ t₂ : ℝ) (ht₁ : t₁ = x 1 ∨ t₁ = y 1)
      (ht₂ : t₂ = x 2 ∨ t₂ = y 2) :
      IsFiniteLaminate a b ![M * x 0 * y 0 * t₁ * t₂, M * t₁ * t₂, M * t₁ * t₂] := by
    let v : DiagonalTriple := fun _ => M * t₁ * t₂
    have hp : IsFiniteLaminate a b (x 0 • v) := by
      have hh := hleaf (x 0) t₁ t₂ (Or.inl rfl) ht₁ ht₂
      change IsFiniteLaminate a b (fun _ => x 0 * (M * t₁ * t₂))
      convert IsFiniteLaminate.scalar (M * x 0 * t₁ * t₂) hh.1 hh.2 using 1
      ext j
      ring
    have hm : IsFiniteLaminate a b (y 0 • v) := by
      have hh := hleaf (y 0) t₁ t₂ (Or.inr rfl) ht₁ ht₂
      change IsFiniteLaminate a b (fun _ => y 0 * (M * t₁ * t₂))
      convert IsFiniteLaminate.scalar (M * y 0 * t₁ * t₂) hh.1 hh.2 using 1
      ext j
      ring
    convert IsFiniteLaminate.half_smul 0 v (hx 0) (hy 0) (hsum 0) hp hm using 1
    ext j
    fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
  have h₁ (t₂ : ℝ) (ht₂ : t₂ = x 2 ∨ t₂ = y 2) :
      IsFiniteLaminate a b ![M * x 0 * y 0 * t₂, M * x 1 * y 1 * t₂, M * t₂] := by
    let v : DiagonalTriple := ![M * x 0 * y 0 * t₂, M * t₂, M * t₂]
    have hp : IsFiniteLaminate a b (x 1 • v) := by
      convert h₀ (x 1) t₂ (Or.inl rfl) ht₂ using 1
      ext j
      fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
    have hm : IsFiniteLaminate a b (y 1 • v) := by
      convert h₀ (y 1) t₂ (Or.inr rfl) ht₂ using 1
      ext j
      fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
    convert IsFiniteLaminate.half_smul 1 v (hx 1) (hy 1) (hsum 1) hp hm using 1
    ext j
    fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
  let v : DiagonalTriple := ![M * x 0 * y 0, M * x 1 * y 1, M]
  have hp : IsFiniteLaminate a b (x 2 • v) := by
    convert h₁ (x 2) (Or.inl rfl) using 1
    ext j
    fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
  have hm : IsFiniteLaminate a b (y 2 • v) := by
    convert h₁ (y 2) (Or.inr rfl) using 1
    ext j
    fin_cases j <;> simp [v, mul_assoc, mul_comm, mul_left_comm]
  convert IsFiniteLaminate.half_smul 2 v (hx 2) (hy 2) (hsum 2) hp hm using 1
  ext j
  fin_cases j <;> simp [v, mul_comm, mul_left_comm]

def laminateLower (c C : ℝ) : ℝ :=
  (2 * C) * (1 - Real.sqrt (1 - c / (2 * C))) ^ 3 / 2

def laminateUpper (C : ℝ) : ℝ := 16 * (2 * C)

theorem uniform_laminate_coverage {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C) :
    0 < laminateLower c C ∧ laminateLower c C < laminateUpper C ∧
    ∀ α : DiagonalTriple, (∀ i, c ≤ α i ∧ α i ≤ C) →
      IsFiniteLaminate (laminateLower c C) (laminateUpper C) α := by
  let M := 2 * C
  let ℓ := 1 - Real.sqrt (1 - c / M)
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  have hM : 0 < M := by dsimp [M]; positivity
  have hcM : c < M := by dsimp [M]; linarith
  have hℓ : 0 < ℓ :=
    (productFactor_spec hM (fun _ => c) 0 ⟨hc, hcM⟩).1
  have hℓ1 : ℓ ≤ 1 := by dsimp [ℓ]; linarith [Real.sqrt_nonneg (1 - c / M)]
  have hℓ3 : ℓ ^ 3 ≤ 1 := by
    calc ℓ ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hℓ.le hℓ1 3
         _ = 1 := by norm_num
  have hbase : 0 < M * ℓ ^ 3 := mul_pos hM (pow_pos hℓ 3)
  change 0 < M * ℓ ^ 3 / 2 ∧ M * ℓ ^ 3 / 2 < 16 * M ∧ _
  refine ⟨by positivity, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hℓ3 hM.le]
  intro α hα
  let x := productFactorMinus M α
  let y := productFactorPlus M α
  have hspec (i : Fin 3) : 0 < x i ∧ 0 < y i ∧ x i + y i = 2 ∧ x i * y i = α i / M := by
    apply productFactor_spec hM α i
    constructor
    · exact lt_of_lt_of_le hc (hα i).1
    · dsimp [M]
      linarith [(hα i).2]
  have hx (i : Fin 3) : ℓ ≤ x i ∧ x i ≤ 2 := by
    dsimp [ℓ, x, productFactorMinus]
    constructor
    · have hh : 1 - α i / M ≤ 1 - c / M := by
        linarith [div_le_div_of_nonneg_right (hα i).1 hM.le]
      linarith [Real.sqrt_le_sqrt hh]
    · linarith [Real.sqrt_nonneg (1 - α i / M)]
  have hy (i : Fin 3) : ℓ ≤ y i ∧ y i ≤ 2 := by
    constructor
    · calc ℓ ≤ 1 := hℓ1
           _ ≤ y i := by
             dsimp [y, productFactorPlus]
             linarith [Real.sqrt_nonneg (1 - α i / M)]
    · have hs := hspec i
      linarith [hs.1, hs.2.2.1]
  have heq : (fun i => M * x i * y i) = α := by
    ext i
    rw [mul_assoc, (hspec i).2.2.2]
    exact mul_div_cancel₀ _ hM.ne'
  rw [← heq]
  apply product_eight_leaf_laminate x y (fun i => (hspec i).1.ne')
    (fun i => (hspec i).2.1.ne') (fun i => (hspec i).2.2.1)
  intro t₀ t₁ t₂ ht₀ ht₁ ht₂
  have hb₀ : ℓ ≤ t₀ ∧ t₀ ≤ 2 := ht₀.elim (fun h => h ▸ hx 0) (fun h => h ▸ hy 0)
  have hb₁ : ℓ ≤ t₁ ∧ t₁ ≤ 2 := ht₁.elim (fun h => h ▸ hx 1) (fun h => h ▸ hy 1)
  have hb₂ : ℓ ≤ t₂ ∧ t₂ ≤ 2 := ht₂.elim (fun h => h ▸ hx 2) (fun h => h ▸ hy 2)
  have ht₀0 : 0 ≤ t₀ := hℓ.le.trans hb₀.1
  have ht₁0 : 0 ≤ t₁ := hℓ.le.trans hb₁.1
  have ht₂0 : 0 ≤ t₂ := hℓ.le.trans hb₂.1
  have hlo : M * ℓ ^ 3 ≤ M * t₀ * t₁ * t₂ := by
    calc M * ℓ ^ 3 = M * ℓ * ℓ * ℓ := by ring
         _ ≤ M * t₀ * t₁ * t₂ := by gcongr <;> linarith
  have hhi : M * t₀ * t₁ * t₂ ≤ 8 * M := by
    calc M * t₀ * t₁ * t₂ ≤ M * 2 * 2 * 2 := by gcongr <;> linarith
         _ = 8 * M := by ring
  change M * ℓ ^ 3 / 2 < M * t₀ * t₁ * t₂ ∧ M * t₀ * t₁ * t₂ < 16 * M
  constructor <;> nlinarith

end ScalarConductivity

end

end OAI
