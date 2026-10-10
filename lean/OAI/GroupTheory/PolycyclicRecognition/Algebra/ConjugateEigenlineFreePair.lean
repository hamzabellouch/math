import OAI.GroupTheory.PolycyclicRecognition.Algebra.PowerDominantEigenlines
import Mathlib.Algebra.Group.Conj

namespace OAI

/-! # Free powers of a dominant element and a transverse conjugate

The conjugate has the same spectral gap, with a bounded change-of-coordinates
constant. The power lemma absorbs that constant.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G V : Type} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem linearRepresentation_cancel (ρ : G →* (V →L[ℝ] V)) (g : G) (x : V) :
    ρ g⁻¹ (ρ g x) = x := by
  change (ρ g⁻¹ * ρ g) x = x
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

theorem linearRepresentation_conjugate (ρ : G →* (V →L[ℝ] V)) (g h : G) (x : V) :
    ρ (g * h * g⁻¹) x = ρ g (ρ h (ρ g⁻¹ x)) := by
  rw [map_mul, map_mul]
  rfl

theorem linearRepresentation_conjugate_vector (ρ : G →* (V →L[ℝ] V))
    (g h : G) (x : V) : ρ (g * h * g⁻¹) (ρ g x) = ρ g (ρ h x) := by
  rw [linearRepresentation_conjugate, linearRepresentation_cancel]

theorem linearRepresentation_inverse_mem_line (ρ : G →* (V →L[ℝ] V))
    (g : G) (x v : V) (hx : x ∈ Submodule.span ℝ ({ρ g v} : Set V)) :
    ρ g⁻¹ x ∈ Submodule.span ℝ ({v} : Set V) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  apply Submodule.mem_span_singleton.mpr
  refine ⟨c, ?_⟩
  rw [← hc, map_smul, linearRepresentation_cancel]

variable [FiniteDimensional ℝ V] [MulAction G V]

theorem free_powers_of_transverse_conjugate
    (ρ : G →* (V →L[ℝ] V)) (hact : ∀ g x, ρ g x = g • x)
    (a h : G) (φ : Bool → V →L[ℝ] ℝ) (v : Bool → V) (μ b : Bool → ℝ)
    (hv : ∀ s, ρ (if s then a⁻¹ else a) (v s) = μ s • v s)
    (hφv : ∀ s, φ s (v s) = 1)
    (hφ : ∀ s x, φ s (ρ (if s then a⁻¹ else a) x) = μ s * φ s x)
    (hb : ∀ s, 0 ≤ b s) (hgap : ∀ s, b s < |μ s|)
    (hker : ∀ s x, φ s x = 0 → ‖ρ (if s then a⁻¹ else a) x‖ ≤ b s * ‖x‖)
    (htrans : ∀ s t, φ s (ρ h (v t)) ≠ 0 ∧ φ s (ρ h⁻¹ (v t)) ≠ 0)
    (hlines : ∀ s t,
      ρ h (v t) ∉ Submodule.span ℝ ({v s} : Set V) ∧
      ρ h⁻¹ (v t) ∉ Submodule.span ℝ ({v s} : Set V)) :
    ∃ N : ℕ, 0 < N ∧ Function.Injective
      (FreeGroup.lift (fun i : Bool => if i then h * a ^ N * h⁻¹ else a ^ N)) := by
  let e (i : Bool) : G := if i then h else 1
  let A (i : Bool) : G := e i * a * (e i)⁻¹
  let w (i s : Bool) : V := ρ (e i) (v s)
  let ψ (i s : Bool) : V →L[ℝ] ℝ := (φ s).comp (ρ (e i)⁻¹)
  let C (i : Bool) : ℝ := ‖ρ (e i)‖ * ‖ρ (e i)⁻¹‖
  have hs (i s : Bool) : signedPingPongGenerator A i s =
      e i * (if s then a⁻¹ else a) * (e i)⁻¹ := by
    cases s <;> simp [signedPingPongGenerator, A, mul_inv_rev, mul_assoc]
  have hvA (i s : Bool) : ρ (signedPingPongGenerator A i s) (w i s) = μ s • w i s := by
    rw [hs]
    change ρ (e i * (if s then a⁻¹ else a) * (e i)⁻¹) (ρ (e i) (v s)) = _
    rw [linearRepresentation_conjugate_vector, hv, map_smul]
  have hψw (i s : Bool) : ψ i s (w i s) = 1 := by
    change φ s (ρ (e i)⁻¹ (ρ (e i) (v s))) = 1
    rw [linearRepresentation_cancel, hφv]
  have hψ (i s : Bool) (x : V) : ψ i s (ρ (signedPingPongGenerator A i s) x) =
      μ s * ψ i s x := by
    rw [hs, linearRepresentation_conjugate]
    change φ s (ρ (e i)⁻¹ (ρ (e i) (ρ (if s then a⁻¹ else a) (ρ (e i)⁻¹ x)))) = _
    rw [linearRepresentation_cancel, hφ]
    rfl
  have hk (i s : Bool) (n : ℕ) (x : V) (hx : ψ i s x = 0) :
      ‖(ρ (signedPingPongGenerator A i s) ^ n) x‖ ≤ C i * b s ^ n * ‖x‖ := by
    let y := ρ (e i)⁻¹ x
    have hy : φ s y = 0 := hx
    let T := ρ (if s then a⁻¹ else a)
    have hTy : φ s ((T ^ n) y) = 0 := by
      rw [eigenline_functional_power T _ _ (hφ s), hy, mul_zero]
    have hbound : ‖(T ^ n) y‖ ≤ b s ^ n * ‖y‖ := by
      have hh := eigenlineRemainder_power_bound T (φ s) (v s) (μ s) (b s)
        (hv s) (hφv s) (hφ s) (hb s) (hker s) n y
      simpa only [eigenlineRemainder, hy, hTy, zero_smul, sub_zero] using hh
    have hp : (ρ (signedPingPongGenerator A i s) ^ n) x = ρ (e i) ((T ^ n) y) := by
      rw [← map_pow, hs, conj_pow, linearRepresentation_conjugate, map_pow]
    rw [hp]
    calc
      ‖ρ (e i) ((T ^ n) y)‖ ≤ ‖ρ (e i)‖ * ‖(T ^ n) y‖ := (ρ (e i)).le_opNorm _
      _ ≤ ‖ρ (e i)‖ * (b s ^ n * ‖y‖) := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
      _ ≤ ‖ρ (e i)‖ * (b s ^ n * (‖ρ (e i)⁻¹‖ * ‖x‖)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ((ρ (e i)⁻¹).le_opNorm x) (pow_nonneg (hb s) n))
          (norm_nonneg _)
      _ = C i * b s ^ n * ‖x‖ := by dsimp [C]; ring
  have ht (i s j t : Bool) (hij : i ≠ j) : ψ i s (w j t) ≠ 0 := by
    cases i <;> cases j
    · exact (hij rfl).elim
    · simpa [ψ, w, e] using (htrans s t).1
    · simpa [ψ, w, e] using (htrans s t).2
    · exact (hij rfl).elim
  have hl (i s j t : Bool) (hij : i ≠ j) :
      w j t ∉ Submodule.span ℝ ({w i s} : Set V) := by
    cases i <;> cases j
    · exact (hij rfl).elim
    · simpa [w, e] using (hlines s t).1
    · intro hh
      apply (hlines s t).2
      apply linearRepresentation_inverse_mem_line ρ h
      simpa [w, e] using hh
    · exact (hij rfl).elim
  obtain ⟨N, hN, hf⟩ := free_powers_of_asymptotically_dominant_eigenlines ρ hact A ψ w
    (fun _ s => μ s) (fun _ s => b s) (fun i _ => C i) hvA hψw hψ
    (fun _ s => hb s) (fun _ s => hgap s) (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    hk ht hl
  refine ⟨N, hN, ?_⟩
  have he : (fun i : Bool => if i then h * a ^ N * h⁻¹ else a ^ N) =
      (fun i => A i ^ N) := by
    funext i
    cases i <;> simp [A, e, conj_pow]
  rw [he]
  exact hf

end PolycyclicRecognition

end

end OAI
