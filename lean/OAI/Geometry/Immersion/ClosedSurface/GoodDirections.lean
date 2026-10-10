import OAI.Geometry.Immersion.ClosedSurface.RealModes

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes
open Set Polynomial



def secondQuadratic {n : ℕ} (B : Fin 3 → RVec n) (v : Base) : RVec n :=
  v.1 ^ 2 • B 0 + (2 * v.1 * v.2) • B 1 + v.2 ^ 2 • B 2


def Good {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base) : Prop :=
  ξ ≠ 0 ∧ secondQuadratic B (-ξ.2, ξ.1) ≠ 0

lemma secondQuadratic_smul {n : ℕ} (B : Fin 3 → RVec n) (v : Base) (w : ℝ) :
    secondQuadratic B (w • v) = w ^ 2 • secondQuadratic B v := by
  ext i
  simp only [secondQuadratic, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring



lemma finite_bad_slopes {n : ℕ} {B : Fin 3 → RVec n} (hB : B ≠ 0) :
    Set.Finite {t : ℝ | secondQuadratic B (-t, 1) = 0} := by
  classical
  have hex : ∃ j i, B j i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hB (funext fun j => funext fun i => hn j i)
  obtain ⟨j, i, hji⟩ := hex
  let p : ℝ[X] := C (B 0 i) * X ^ 2 - C (2 * B 1 i) * X + C (B 2 i)
  have hp : p ≠ 0 := by
    intro hz
    have h0 := congrArg (fun P : ℝ[X] => P.coeff 0) hz
    have h1 := congrArg (fun P : ℝ[X] => P.coeff 1) hz
    have h2 := congrArg (fun P : ℝ[X] => P.coeff 2) hz
    simp [p, coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow] at h0 h1 h2
    fin_cases j <;> simp_all
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  intro t ht
  have hi := congrFun ht i
  simp only [secondQuadratic, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    neg_sq, one_pow, mul_one, one_mul] at hi
  change p.eval t = 0
  simp only [p, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  nlinarith [hi]

lemma exists_interval_avoiding {a b : ℝ} (hab : a < b) {T : Set ℝ} (hT : T.Finite) :
    ∃ t ∈ Ioo a b, t ∉ T := by
  by_contra hn
  push Not at hn
  exact (Set.Ioo_infinite hab) (hT.subset hn)

lemma finite_affine_preimage {T : Set ℝ} (hT : T.Finite) {a b : ℝ} (ha : a ≠ 0) :
    ( (fun t : ℝ => a * t + b) ⁻¹' T).Finite := by
  apply hT.preimage
  intro x hx y hy he
  exact mul_left_cancel₀ ha (by linarith)



lemma choose_three_avoiding {T : Set ℝ} (hT : T.Finite)
    {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ} (h₀ : a₀ < b₀) (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) :
    ∃ t₀ ∈ Ioo a₀ b₀, ∃ t₁ ∈ Ioo a₁ b₁, ∃ t₂ ∈ Ioo a₂ b₂,
      t₀ ∉ T ∧ t₁ ∉ T ∧ t₂ ∉ T ∧ (t₀ + 2*t₁)/3 ∉ T ∧ 2*t₁-t₀ ∉ T ∧
      (t₀ + 4*t₂)/5 ∉ T ∧ (4*t₂-t₀)/3 ∉ T ∧ (t₁ + 2*t₂)/3 ∉ T ∧ 2*t₂-t₁ ∉ T := by
  obtain ⟨t₀, ht₀, hn₀⟩ := exists_interval_avoiding h₀ hT
  let T₁ := T ∪ ((fun t : ℝ => (2/3)*t + t₀/3) ⁻¹' T) ∪
    ((fun t : ℝ => 2*t + (-t₀)) ⁻¹' T)
  have hT₁ : T₁.Finite := (hT.union (finite_affine_preimage hT (by norm_num))).union
    (finite_affine_preimage hT (by norm_num))
  obtain ⟨t₁, ht₁, hn₁⟩ := exists_interval_avoiding h₁ hT₁
  have hn₁a : t₁ ∉ T := fun hh => hn₁ (Or.inl (Or.inl hh))
  have hn₁b : (t₀ + 2*t₁)/3 ∉ T := by
    intro hh
    apply hn₁
    left; right
    change (2/3)*t₁ + t₀/3 ∈ T
    convert hh using 1; ring
  have hn₁c : 2*t₁-t₀ ∉ T := by
    intro hh
    apply hn₁
    right
    change 2*t₁ + (-t₀) ∈ T
    simpa only [sub_eq_add_neg] using hh
  let T₂ := T ∪ ((fun t : ℝ => (4/5)*t + t₀/5) ⁻¹' T) ∪
    ((fun t : ℝ => (4/3)*t + (-t₀/3)) ⁻¹' T) ∪
    ((fun t : ℝ => (2/3)*t + t₁/3) ⁻¹' T) ∪
    ((fun t : ℝ => 2*t + (-t₁)) ⁻¹' T)
  have hT₂ : T₂.Finite := (((hT.union (finite_affine_preimage hT (by norm_num))).union
    (finite_affine_preimage hT (by norm_num))).union
    (finite_affine_preimage hT (by norm_num))).union (finite_affine_preimage hT (by norm_num))
  obtain ⟨t₂, ht₂, hn₂⟩ := exists_interval_avoiding h₂ hT₂
  have hn₂a : t₂ ∉ T := fun hh => hn₂ (Or.inl (Or.inl (Or.inl (Or.inl hh))))
  have hn₂b : (t₀ + 4*t₂)/5 ∉ T := by
    intro hh
    apply hn₂
    left; left; left; right
    change (4/5)*t₂ + t₀/5 ∈ T
    convert hh using 1; ring
  have hn₂c : (4*t₂-t₀)/3 ∉ T := by
    intro hh
    apply hn₂
    left; left; right
    change (4/3)*t₂ + (-t₀/3) ∈ T
    convert hh using 1; ring
  have hn₂d : (t₁ + 2*t₂)/3 ∉ T := by
    intro hh
    apply hn₂
    left; right
    change (2/3)*t₂ + t₁/3 ∈ T
    convert hh using 1; ring
  have hn₂e : 2*t₂-t₁ ∉ T := by
    intro hh
    apply hn₂
    right
    change 2*t₂ + (-t₁) ∈ T
    simpa only [sub_eq_add_neg] using hh
  exact ⟨t₀, ht₀, t₁, ht₁, t₂, ht₂, hn₀, hn₁a, hn₂a, hn₁b, hn₁c,
    hn₂b, hn₂c, hn₂d, hn₂e⟩




theorem choose_three_good_slopes {n : ℕ} {B : Fin 3 → RVec n} (hB : B ≠ 0)
    {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ} (h₀ : a₀ < b₀) (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) :
    ∃ t₀ ∈ Ioo a₀ b₀, ∃ t₁ ∈ Ioo a₁ b₁, ∃ t₂ ∈ Ioo a₂ b₂,
      secondQuadratic B (-t₀, 1) ≠ 0 ∧ secondQuadratic B (-t₁, 1) ≠ 0 ∧
      secondQuadratic B (-t₂, 1) ≠ 0 ∧
      secondQuadratic B (-((t₀ + 2*t₁)/3), 1) ≠ 0 ∧
      secondQuadratic B (-(2*t₁-t₀), 1) ≠ 0 ∧
      secondQuadratic B (-((t₀ + 4*t₂)/5), 1) ≠ 0 ∧
      secondQuadratic B (-((4*t₂-t₀)/3), 1) ≠ 0 ∧
      secondQuadratic B (-((t₁ + 2*t₂)/3), 1) ≠ 0 ∧
      secondQuadratic B (-(2*t₂-t₁), 1) ≠ 0 := by
  exact choose_three_avoiding (finite_bad_slopes hB) h₀ h₁ h₂

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
