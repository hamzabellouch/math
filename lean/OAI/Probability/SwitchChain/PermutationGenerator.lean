import OAI.Probability.SwitchChain.EnergyTransfer

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PermutationGenerator

variable {Ω S : Type*} [Fintype Ω] [Fintype S]

def apply (τ : S → Equiv.Perm Ω) (f : Ω → ℝ) (x : Ω) : ℝ :=
  ∑ s, (f x - f (τ s x))

def operator (τ : S → Equiv.Perm Ω) :
    EuclideanSpace ℝ Ω →ₗ[ℝ] EuclideanSpace ℝ Ω where
  toFun f := WithLp.toLp 2 (apply τ f)
  map_add' f g := by
    ext x
    change (∑ s, ((f x + g x) - (f (τ s x) + g (τ s x)))) =
      (∑ s, (f x - f (τ s x))) + ∑ s, (g x - g (τ s x))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  map_smul' c f := by
    ext x
    change (∑ s, (c * f x - c * f (τ s x))) = c * ∑ s, (f x - f (τ s x))
    simp only [mul_sub, Finset.mul_sum]

omit [Fintype Ω] in
@[simp] theorem operator_apply (τ : S → Equiv.Perm Ω)
    (f : EuclideanSpace ℝ Ω) (x : Ω) : operator τ f x = apply τ f x := rfl

theorem sum_apply (τ : S → Equiv.Perm Ω) (f : Ω → ℝ) :
    ∑ x, apply τ f x = 0 := by
  unfold apply
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro s hs
  rw [Finset.sum_sub_distrib, Equiv.sum_comp (τ s)]
  exact sub_self _

theorem inner_operator (τ : S → Equiv.Perm Ω) (f : EuclideanSpace ℝ Ω) :
    ⟪f, operator τ f⟫ = (1 / 2 : ℝ) * ∑ s, ∑ x, (f x - f (τ s x)) ^ 2 := by
  have hsingle (s : S) :
      (∑ x, f x * (f x - f (τ s x))) =
        (1 / 2 : ℝ) * ∑ x, (f x - f (τ s x)) ^ 2 := by
    have heq : (∑ x, (f (τ s x)) ^ 2) = ∑ x, (f x) ^ 2 :=
      Equiv.sum_comp (τ s) (fun x => (f x) ^ 2)
    have hexpand : (∑ x, (f x - f (τ s x)) ^ 2) =
        (∑ x, (f x) ^ 2) + (∑ x, (f (τ s x)) ^ 2) -
          2 * ∑ x, f x * f (τ s x) := by
      simp only [Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hexpand, heq]
    simp only [mul_sub, ← pow_two, Finset.sum_sub_distrib]
    ring
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, operator_apply, apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simpa only [Finset.mul_sum, mul_comm] using hsingle s

theorem inner_operator_nonneg (τ : S → Equiv.Perm Ω) (f : EuclideanSpace ℝ Ω) :
    0 ≤ ⟪f, operator τ f⟫ := by
  rw [inner_operator]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem inner_operator_eq_zero_iff (τ : S → Equiv.Perm Ω) (f : EuclideanSpace ℝ Ω) :
    ⟪f, operator τ f⟫ = 0 ↔ ∀ s x, f (τ s x) = f x := by
  rw [inner_operator]
  constructor
  · intro hz s x
    have hall : (∑ s, ∑ x, (f x - f (τ s x)) ^ 2) = 0 := by linarith
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ =>
      Finset.sum_nonneg (fun x _ => sq_nonneg (f x - f (τ s x))))).mp hall s (Finset.mem_univ s)
    have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
      sq_nonneg (f x - f (τ s x)))).mp hs x (Finset.mem_univ x)
    nlinarith
  · intro h
    simp [h]

theorem inner_operator_pos_of_centered [Nonempty Ω]
    (τ : S → Equiv.Perm Ω)
    (hconn : ∀ f : Ω → ℝ, (∀ s x, f (τ s x) = f x) → ∀ x y, f x = f y)
    (f : EuclideanSpace ℝ Ω) (hcenter : ∑ x, f x = 0) (hf : f ≠ 0) :
    0 < ⟪f, operator τ f⟫ := by
  have hnonneg := inner_operator_nonneg τ f
  apply lt_of_le_of_ne hnonneg
  intro he
  have hinv := (inner_operator_eq_zero_iff τ f).mp he.symm
  obtain ⟨a⟩ := ‹Nonempty Ω›
  have hc := hconn f hinv
  have hfa : f a = 0 := by
    have heq : (∑ x, f x) = (Fintype.card Ω : ℝ) * f a := by
      simp [fun x => hc x a]
    have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [heq] at hcenter
    exact (mul_eq_zero.mp hcenter).resolve_left hcard
  apply hf
  ext x
  change f x = 0
  rw [hc x a, hfa]

theorem energy_sum_le_of_local_bound
    {ι : Type*} [Fintype ι] (τ : S → Equiv.Perm Ω)
    (f : ι → EuclideanSpace ℝ Ω) (c : ℝ)
    (hlocal : ∀ s x,
      (∑ i, (f i x - f i (τ s x))) ^ 2 ≤
        c * ∑ i, (f i x - f i (τ s x)) ^ 2) :
    ⟪∑ i, f i, operator τ (∑ i, f i)⟫ ≤ c * ∑ i, ⟪f i, operator τ (f i)⟫ := by
  simp_rw [inner_operator]
  have heval (x : Ω) : (∑ i, f i) x = ∑ i, f i x := by simp
  simp_rw [heval, ← Finset.sum_sub_distrib]
  calc
    (1 / 2 : ℝ) * ∑ s, ∑ x, (∑ i, (f i x - f i (τ s x))) ^ 2
        ≤ (1 / 2 : ℝ) * ∑ s, ∑ x, c * ∑ i, (f i x - f i (τ s x)) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun x _ => hlocal s x
    _ = c * ∑ i, (1 / 2 : ℝ) * ∑ s, ∑ x, (f i x - f i (τ s x)) ^ 2 := by
      simp_rw [← Finset.mul_sum]
      have heq : (∑ s, ∑ x, ∑ i, (f i x - f i (τ s x)) ^ 2) =
          ∑ i, ∑ s, ∑ x, (f i x - f i (τ s x)) ^ 2 := by
        calc
          _ = ∑ s, ∑ i, ∑ x, (f i x - f i (τ s x)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [Finset.sum_comm]
          _ = _ := Finset.sum_comm
      rw [heq]
      ring

theorem norm_sum_sq_le_of_invariant_moves [Nonempty Ω]
    {ι : Type*} [Fintype ι] (τ : S → Equiv.Perm Ω)
    (hconn : ∀ f : Ω → ℝ, (∀ s x, f (τ s x) = f x) → ∀ x y, f x = f y)
    (V : ι → Submodule ℝ (EuclideanSpace ℝ Ω))
    (hcenter : ∀ i f, f ∈ V i → ∑ x, f x = 0)
    (hinv : ∀ i f, f ∈ V i → operator τ f ∈ V i)
    (c : ℝ)
    (hlocal : ∀ f : ι → EuclideanSpace ℝ Ω, (∀ i, f i ∈ V i) → ∀ s x,
      (∑ i, (f i x - f i (τ s x))) ^ 2 ≤ c * ∑ i, (f i x - f i (τ s x)) ^ 2)
    (f : ι → EuclideanSpace ℝ Ω) (hf : ∀ i, f i ∈ V i) :
    ‖∑ i, f i‖ ^ 2 ≤ c * ∑ i, ‖f i‖ ^ 2 := by
  apply EnergyTransfer.norm_sum_sq_le_of_invariant_energy_bound V (operator τ) hinv
    (fun i g hg hne => inner_operator_pos_of_centered τ hconn g (hcenter i g hg) hne)
    c _ f hf
  intro g hg
  exact energy_sum_le_of_local_bound τ g c (hlocal g hg)

end Problem315.PermutationGenerator

end

end OAI
