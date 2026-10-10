import OAI.Combinatorics.Progressions.Geometry.MixedCoordinateTransfer

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_common_weighted_exchange :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ} {N : ℕ} [NeZero N]
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      (i j : Fin W.outputDim) (w : (Fin 2 → ℤ) → ℝ) (G : (Fin 2 → ℤ) → ℂ),
      0 ≤ q →
      NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (fun x => (w x : ℂ)) →
      NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q G →
      (∀ x, 0 ≤ w x ∧ w x ≤ 1) → ∀ {δ ε : ℝ},
      δ ≤ (𝔼 z : Fin 2 → ZMod N, w (fun h => ((z h).val : ℤ)) *
        ‖W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)‖ ^ 2) →
      (𝔼 z : Fin 2 → ZMod N,
        ‖W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ) *
          (w (fun h => ((z h).val : ℤ)) : ℂ) - G (fun h => ((z h).val : ℤ))‖) ≤ ε →
      ∃ v : (Fin 2 → ℤ) → ℝ,
        ∃ U : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
          (∀ x, 0 ≤ v x ∧ v x ≤ 1) ∧
          Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
            (fun x => (v x : ℂ))) ∧
          (∀ k l, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
            ((p + q + C) ^ C) (U k l))) ∧
          δ ≤ (𝔼 z : Fin 2 → ZMod N, v (fun h => ((z h).val : ℤ))) ∧
          (𝔼 z : Fin 2 → ZMod N, Real.sqrt (∑ k, ∑ l,
            ‖W.antisymmetricKernel k l ((z 0).val : ℤ) ((z 1).val : ℤ) *
              (v (fun h => ((z h).val : ℤ)) : ℂ) - U k l (fun h => ((z h).val : ℤ))‖ ^ 2)) ≤ ε := by
  obtain ⟨A, _, htransfer⟩ := NativeMultidegreeNilcharacter.exists_coordinate_transfer_expansions
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + Polynomial.C A) ^ A + X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q N _ W i j w G hq EW EG hw δ ε hmass herr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let r := (p + A) ^ A + q
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htr : (p + A) ^ A ≤ r := le_add_of_nonneg_right hq
  have hqr : q ≤ r := le_add_of_nonneg_left (by positivity)
  have hbig : ((p + q + A) ^ A + (p + q) + B) ^ B ≤ (p + q + C) ^ C := by
    simpa [R, X, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  have hmono : (p + A) ^ A ≤ (p + q + A) ^ A := by gcongr; linarith
  have hcost : (r + B) ^ B ≤ (p + q + C) ^ C :=
    (pow_le_pow_left₀ (by positivity) (by dsimp [r]; linarith) B).trans hbig
  let v := fun x : Fin 2 → ℤ => w x * ‖W.antisymmetricKernel i j (x 0) (x 1)‖ ^ 2
  let U := fun k l (x : Fin 2 → ℤ) => G x * W.coordinateTransfer i j k l x
  obtain ⟨ED⟩ := htransfer W i j i j
  have ED' : NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + A) ^ A)
      (fun x => (‖W.antisymmetricKernel i j (x 0) (x 1)‖ ^ 2 : ℝ)) := by
    have heq : W.coordinateTransfer i j i j =
        (fun x : Fin 2 → ℤ => ((‖W.antisymmetricKernel i j (x 0) (x 1)‖ ^ 2 : ℝ) : ℂ)) :=
      funext (W.coordinateTransfer_diagonal i j)
    exact heq ▸ ED
  obtain ⟨EV⟩ := hmul hr (EW.mono hqr) (ED'.mono htr)
  have hEV : NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
      (fun x => (v x : ℂ)) := by
    simpa only [v, Complex.ofReal_mul] using EV.mono hcost
  have hU (k l : Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C) (U k l)) := by
    obtain ⟨ET⟩ := htransfer W i j k l
    obtain ⟨EU⟩ := hmul hr (EG.mono hqr) (ET.mono htr)
    exact ⟨EU.mono hcost⟩
  refine ⟨v, U, ?_, ⟨hEV⟩, hU, hmass, ?_⟩
  · intro x
    have hsq : ‖W.antisymmetricKernel i j (x 0) (x 1)‖ ^ 2 ≤ 1 := by
      nlinarith [W.antisymmetricKernel_norm i j (x 0) (x 1),
        norm_nonneg (W.antisymmetricKernel i j (x 0) (x 1))]
    exact ⟨mul_nonneg (hw x).1 (sq_nonneg _),
      (mul_le_mul_of_nonneg_left hsq (hw x).1).trans (by simpa using (hw x).2)⟩
  · exact (Finset.expect_le_expect (fun z _ => W.coordinateTransfer_matrix_error i j
      (fun h => ((z h).val : ℤ)) (w (fun h => ((z h).val : ℤ)))
        (G (fun h => ((z h).val : ℤ))))).trans herr

end Erdos3

end

end OAI
