import OAI.Analysis.Cotype.TaggedFrames

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem walsh_amplitude_bound {k : ℕ} (T : X →L[ℝ] Y)
    (f : Cube k → X) (g : Cube k → (Y →L[ℝ] ℝ)) (a : ℝ)
    (hf : ∀ u, ‖f u‖ ≤ 1) (hg : ∀ v, ‖g v‖ ≤ 1)
    (ha : ∀ u v, g v (T (f u)) = character v u * a) : |a| ≤ walshNorm k T := by
  have h := walshBilinear_unit_bound T (cubeL2_bound (by positivity) hf)
    (cubeL2_bound (by positivity) hg)
  have he : walshBilinear T f g = a := by
    simp only [walshBilinear, ha, ← mul_assoc, character_sq, one_mul]
    have hc : (Fintype.card (Cube k) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [average]
  rwa [he] at h

theorem norm_half_sub_le_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖(1/2 : ℝ) • (x-y)‖ ≤ 1 := by
  rw [norm_smul]
  norm_num
  linarith [norm_sub_le x y]

theorem character_one_or_neg_one {k : ℕ} (u v : Cube k) :
    character v u = 1 ∨ character v u = -1 := by
  have h := character_sq v u
  exact mul_self_eq_one_iff.mp h

namespace GrowthPairingData
variable {k m : ℕ} {T : X →L[ℝ] Y} {Dg Df : ℝ}
variable (d : GrowthPairingData T (k+m+m) m Dg Df)

theorem tagged_matrix_odd_identity (hn : m+m ≤ k+m+m)
    (S : Fin m × Fin m → Bool) (ε δ : Cube m) (u v : Cube k) :
    (d.tuplePairing (taggedPrimal (fun _ => u)) (taggedDual (fun _ => v) S) ε δ -
      d.tuplePairing (taggedPrimal (fun _ => u)) (taggedDual (fun _ => v) (negateCube S)) ε δ) / 2 =
    character v u * oddPart (fun S => d.patternPairing hn S ε δ) S := by
  have hU := taggedPrimal_frame (fun _ : Fin m => u)
  have hV := taggedDual_frame (fun _ : Fin m => v)
  rcases character_one_or_neg_one u v with hc | hc
  · have hp := d.patternPairing_eq hn S _ _ hU (hV S)
      (fun i j => by rw [taggedFrames_pairing, hc, one_mul]) ε δ
    have hm := d.patternPairing_eq hn (negateCube S) _ _ hU (hV (negateCube S))
      (fun i j => by rw [taggedFrames_pairing, hc, one_mul]) ε δ
    rw [← hp, ← hm, hc, one_mul]
    rfl
  · have hp := d.patternPairing_eq hn (negateCube S) _ _ hU (hV S)
      (fun i j => by rw [taggedFrames_pairing, hc]; simp [negateCube]) ε δ
    have hm := d.patternPairing_eq hn S _ _ hU (hV (negateCube S))
      (fun i j => by rw [taggedFrames_pairing, hc]; simp [negateCube]) ε δ
    rw [← hp, ← hm, hc]
    unfold oddPart
    ring

theorem patternPairing_odd_bound (hn : m+m ≤ k+m+m)
    (S : Fin m × Fin m → Bool) (ε δ : Cube m) :
    |oddPart (fun S => d.patternPairing hn S ε δ) S| ≤ walshNorm k T := by
  let f := fun u : Cube k => d.P (taggedPrimal (fun _ => u)) ε
  let g := fun v : Cube k => (1/2 : ℝ) •
    (d.Z (taggedDual (fun _ => v) S) δ - d.Z (taggedDual (fun _ => v) (negateCube S)) δ)
  have h := walsh_amplitude_bound d.amplifiedOperator f g
    (oddPart (fun S => d.patternPairing hn S ε δ) S)
    (fun u => d.P_norm _ _) (fun v => norm_half_sub_le_one (d.Z_norm _ _) (d.Z_norm _ _))
    (by
      intro u v
      have h := d.tagged_matrix_odd_identity hn S ε δ u v
      simpa [f,g,tuplePairing, div_eq_mul_inv, mul_comm] using h)
  exact h.trans_eq (d.walsh_norms k)

theorem tagged_primal_odd_identity (hm : 0 < m) (hn : m+1 ≤ k+m+m)
    (s : Cube m) (ε : Cube m) (u v : Cube k) :
    (d.primalSlice (taggedPrimal (fun _ => u)) (taggedCovector hm v s) ε -
      d.primalSlice (taggedPrimal (fun _ => u)) (taggedCovector hm v (negateCube s)) ε) / 2 =
    character v u * oddPart (fun s => d.patternPrimal hn s ε) s := by
  have hU := taggedPrimal_frame (fun _ : Fin m => u)
  have hV := taggedCovector_frame hm v
  rcases character_one_or_neg_one u v with hc | hc
  · have hp := d.patternPrimal_eq hn s _ _ hU (hV s)
      (fun i => by rw [taggedCovector_pairing, hc, one_mul]) ε
    have hq := d.patternPrimal_eq hn (negateCube s) _ _ hU (hV (negateCube s))
      (fun i => by rw [taggedCovector_pairing, hc, one_mul]) ε
    rw [← hp, ← hq, hc, one_mul]
    rfl
  · have hp := d.patternPrimal_eq hn (negateCube s) _ _ hU (hV s)
      (fun i => by rw [taggedCovector_pairing, hc]; simp [negateCube]) ε
    have hq := d.patternPrimal_eq hn s _ _ hU (hV (negateCube s))
      (fun i => by rw [taggedCovector_pairing, hc]; simp [negateCube]) ε
    rw [← hp, ← hq, hc]
    unfold oddPart
    ring

theorem patternPrimal_odd_bound (hm : 0 < m) (hn : m+1 ≤ k+m+m)
    (s : Cube m) (ε : Cube m) :
    |oddPart (fun s => d.patternPrimal hn s ε) s| ≤ walshNorm k T := by
  let f := fun u : Cube k => d.P (taggedPrimal (fun _ => u)) ε
  let g := fun v : Cube k => (1/2 : ℝ) •
    (d.y (taggedCovector hm v s) - d.y (taggedCovector hm v (negateCube s)))
  have h := walsh_amplitude_bound d.amplifiedOperator f g
    (oddPart (fun s => d.patternPrimal hn s ε) s)
    (fun u => d.P_norm _ _) (fun v => norm_half_sub_le_one (d.y_norm _) (d.y_norm _))
    (by
      intro u v
      have h := d.tagged_primal_odd_identity hm hn s ε u v
      simpa [f,g,primalSlice, div_eq_mul_inv, mul_comm] using h)
  exact h.trans_eq (d.walsh_norms k)

theorem tagged_dual_odd_identity (hm : 0 < m) (hn : 1+m ≤ k+m+m)
    (s : Cube m) (δ : Cube m) (u v : Cube k) :
    (d.dualSlice (taggedCovector hm u s) (taggedPrimal (fun _ => v)) δ -
      d.dualSlice (taggedCovector hm u (negateCube s)) (taggedPrimal (fun _ => v)) δ) / 2 =
    character v u * oddPart (fun s => d.patternDual hn s δ) s := by
  have hU := taggedCovector_frame hm u
  have hV := taggedPrimal_frame (fun _ : Fin m => v)
  have he (t : Cube m) (j : Fin m) :
      character (taggedPrimal (fun _ => v) j) (taggedCovector hm u t) =
        character v u * sign (t j) := by
    rw [character_symm, taggedCovector_pairing, character_symm u v]
  rcases character_one_or_neg_one u v with hc | hc
  · have hp := d.patternDual_eq hn s _ _ (hU s) hV
      (fun j => by rw [he, hc, one_mul]) δ
    have hq := d.patternDual_eq hn (negateCube s) _ _ (hU (negateCube s)) hV
      (fun j => by rw [he, hc, one_mul]) δ
    rw [← hp, ← hq, hc, one_mul]
    rfl
  · have hp := d.patternDual_eq hn (negateCube s) _ _ (hU s) hV
      (fun j => by rw [he, hc]; simp [negateCube]) δ
    have hq := d.patternDual_eq hn s _ _ (hU (negateCube s)) hV
      (fun j => by rw [he, hc]; simp [negateCube]) δ
    rw [← hp, ← hq, hc]
    unfold oddPart
    ring

theorem patternDual_odd_bound (hm : 0 < m) (hn : 1+m ≤ k+m+m)
    (s : Cube m) (δ : Cube m) :
    |oddPart (fun s => d.patternDual hn s δ) s| ≤ walshNorm k T := by
  let f := fun u : Cube k => (1/2 : ℝ) •
    (d.x (taggedCovector hm u s) - d.x (taggedCovector hm u (negateCube s)))
  let g := fun v : Cube k => d.Z (taggedPrimal (fun _ => v)) δ
  have h := walsh_amplitude_bound d.amplifiedOperator f g
    (oddPart (fun s => d.patternDual hn s δ) s)
    (fun u => norm_half_sub_le_one (d.x_norm _) (d.x_norm _)) (fun v => d.Z_norm _ _)
    (by
      intro u v
      have h := d.tagged_dual_odd_identity hm hn s δ u v
      simpa [f,g,dualSlice, div_eq_mul_inv, mul_comm] using h)
  exact h.trans_eq (d.walsh_norms k)

end GrowthPairingData

end Cotype

end

end OAI
