import OAI.Analysis.Cotype.WalshSymmetry
import OAI.Analysis.Cotype.DualAction

namespace OAI

noncomputable section

open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

def finiteProbabilityVector (f : Ω → X) : PiLp 2 (fun _ : Ω => X) :=
  Real.sqrt ((Fintype.card Ω : ℝ)⁻¹) • toLp 2 f

def finiteProbabilityDual (f : Ω → (Y →L[ℝ] ℝ)) : (PiLp 2 (fun _ : Ω => Y) →L[ℝ] ℝ) :=
  Real.sqrt ((Fintype.card Ω : ℝ)⁻¹) • finiteL2Dual f

theorem finiteProbabilityVector_norm (f : Ω → X) (hf : ∀ a, ‖f a‖ ≤ 1) :
    ‖finiteProbabilityVector f‖ ≤ 1 := by
  have hc : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos (α := Ω)
  have hb : ‖(toLp 2 f : PiLp 2 (fun _ : Ω => X))‖ ≤ Real.sqrt (Fintype.card Ω) := by
    rw [PiLp.norm_eq_of_L2]
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ ∑ _ : Ω, (1:ℝ) := Finset.sum_le_sum (fun a _ => by
        simpa using (sq_le_sq₀ (norm_nonneg (f a)) zero_le_one).mpr (hf a))
      _ = _ := by simp
  calc
    _ = Real.sqrt ((Fintype.card Ω : ℝ)⁻¹) * ‖(toLp 2 f : PiLp 2 (fun _ : Ω => X))‖ := by
      rw [finiteProbabilityVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ Real.sqrt ((Fintype.card Ω : ℝ)⁻¹) * Real.sqrt (Fintype.card Ω) :=
      mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ = 1 := by rw [← Real.sqrt_mul (by positivity), inv_mul_cancel₀ hc.ne', Real.sqrt_one]

theorem finiteProbabilityDual_norm (f : Ω → (Y →L[ℝ] ℝ)) (hf : ∀ a, ‖f a‖ ≤ 1) :
    ‖finiteProbabilityDual f‖ ≤ 1 := by
  classical
  have he : ‖finiteProbabilityDual f‖ = ‖finiteProbabilityVector f‖ := by
    simp only [finiteProbabilityDual, finiteProbabilityVector, norm_smul, finiteL2Dual_norm]
  rw [he]
  exact finiteProbabilityVector_norm f hf

variable {n : ℕ}
abbrev SymmetryL2 (n : ℕ) (X : Type*) : Type _ := PiLp 2 (fun _ : WalshSymmetry n => X)

def symmetryVector (x : Cube n → X) (u : Cube n) : SymmetryL2 n X :=
  finiteProbabilityVector (fun R : WalshSymmetry n => x (primalSymmetry R u))

def symmetryDual (y : Cube n → (Y →L[ℝ] ℝ)) (v : Cube n) : SymmetryL2 n Y →L[ℝ] ℝ :=
  finiteProbabilityDual (fun R : WalshSymmetry n => y (dualSymmetry R v))

@[simp] theorem symmetryVector_equivariant (x : Cube n → X) (g : WalshSymmetry n) (u : Cube n) :
    rightTranslation g (symmetryVector x u) = symmetryVector x (primalSymmetry g u) := by
  ext R
  rfl

theorem symmetryDual_equivariant (y : Cube n → (Y →L[ℝ] ℝ)) (g : WalshSymmetry n) (v : Cube n) :
    dualAction (rightTranslation (X := Y)) g (symmetryDual y v) = symmetryDual y (dualSymmetry g v) := by
  ext z
  change Real.sqrt ((Fintype.card (WalshSymmetry n) : ℝ)⁻¹) *
    (∑ R : WalshSymmetry n, y (dualSymmetry R v) (z (R*g⁻¹))) =
      Real.sqrt ((Fintype.card (WalshSymmetry n) : ℝ)⁻¹) *
        ∑ R : WalshSymmetry n, y (dualSymmetry R (dualSymmetry g v)) (z R)
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulRight g)]
  apply Finset.sum_congr rfl
  intro R _
  change y (dualSymmetry (R*g) v) (z ((R*g)*g⁻¹)) = _
  simp only [mul_inv_cancel_right]
  rfl

theorem symmetry_exact_pairing (T : X →L[ℝ] Y) (x : Cube n → X)
    (y : Cube n → (Y →L[ℝ] ℝ)) (γ : ℝ)
    (hxy : ∀ u v, y v (T (x u)) = γ * character v u) (u v : Cube n) :
    symmetryDual y v (l2Amplification T (symmetryVector x u)) = γ * character v u := by
  let q := Real.sqrt ((Fintype.card (WalshSymmetry n) : ℝ)⁻¹)
  have hc : (Fintype.card (WalshSymmetry n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hq : q^2 = (Fintype.card (WalshSymmetry n) : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  change q * (∑ R : WalshSymmetry n, y (dualSymmetry R v) (T (q • x (primalSymmetry R u)))) = _
  simp only [map_smul, smul_eq_mul, hxy, symmetry_pairing, Finset.sum_const, nsmul_eq_mul]
  calc
    q * ((Fintype.card (WalshSymmetry n) : ℝ) * (q * (γ * character v u))) =
      (q^2 * (Fintype.card (WalshSymmetry n) : ℝ)) * (γ * character v u) := by ring
    _ = _ := by rw [hq, inv_mul_cancel₀ hc, one_mul]

theorem symmetry_pairing_invariant (T : X →L[ℝ] Y) (g : WalshSymmetry n)
    (x : SymmetryL2 n X) (y : SymmetryL2 n Y →L[ℝ] ℝ) :
    dualAction (rightTranslation (X := Y)) g y
      (l2Amplification T (rightTranslation g x)) = y (l2Amplification T x) := by
  have he : l2Amplification T (rightTranslation g x) = rightTranslation g (l2Amplification T x) := by
    ext R; rfl
  rw [he, dualAction_pairing]

theorem exists_equivariant_exact_pairing (n : ℕ) {T : X →L[ℝ] Y} (hT : T ≠ 0) :
    ∃ (γ : ℝ)
      (x : Cube n → SymmetryL2 n (PiLp 2 (fun _ : Cube (n+n) => X)))
      (y : Cube n → (SymmetryL2 n (PiLp 2 (fun _ : Cube (n+n) => Y)) →L[ℝ] ℝ)),
      walshNorm n T / 2 < γ ∧ 0 < γ ∧
      (∀ u, ‖x u‖ ≤ 1) ∧ (∀ v, ‖y v‖ ≤ 1) ∧
      (∀ u v, y v (l2Amplification (l2Amplification T) (x u)) = γ * character v u) ∧
      (∀ g u, rightTranslation g (x u) = x (primalSymmetry g u)) ∧
      (∀ g v, dualAction (rightTranslation (X := PiLp 2 (fun _ : Cube (n+n) => Y))) g (y v) = y (dualSymmetry g v)) ∧
      (∀ k, walshNorm k (l2Amplification (Ω := WalshSymmetry n)
        (l2Amplification (Ω := Cube (n+n)) T)) = walshNorm k T) := by
  obtain ⟨γ,x,y,hγ,hγp,hx,hy,hxy,hW⟩ := exists_exact_amplified_pairing n hT
  exact ⟨γ, symmetryVector x, symmetryDual y, hγ, hγp,
    fun u => finiteProbabilityVector_norm _ (fun R => hx _),
    fun v => finiteProbabilityDual_norm _ (fun R => hy _),
    symmetry_exact_pairing _ x y γ hxy,
    symmetryVector_equivariant x, symmetryDual_equivariant y,
    fun k => (walshNorm_amplification k _).trans (hW k)⟩

end Cotype

end

end OAI
