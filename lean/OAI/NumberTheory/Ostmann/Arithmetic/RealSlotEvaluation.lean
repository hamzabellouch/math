import OAI.NumberTheory.Ostmann.Arithmetic.MovingRealSmooth

namespace OAI

/-! # Real bulk coordinates in the original smooth moving tree -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

noncomputable def realSlotProduct {σ : Type*} (value : σ → ℝ) (slots : List σ) : ℝ :=
  (slots.map value).prod

noncomputable def MovingSlotReversal.realValuePivot {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (L R : ℝ) : ℝ :=
  ((s.leftFrequency : ℝ) * realSlotProduct value s.rightSlots * R -
    (s.rightFrequency : ℝ) * realSlotProduct value s.leftSlots * L) /
    ((s.rootFrequency : ℝ) * realSlotProduct value s.compensationSlots)

noncomputable def MovingSlotData.realValueLeafModuli {σ : Type*} (value : σ → ℝ) :
    {n : ℕ} → MovingSlotData σ n → ℝ → ℝ → TreeLeafIndex n → ℝ
  | _, .leaf _ regular, L, R, _ => L * R * realSlotProduct value regular
  | _, .node s CL CR u left right, L, R, j =>
      let p := (MovingSlotData.step s CL CR u left right false).realValuePivot value L R
      match j with
      | .inl j => left.realValueLeafModuli value p L j
      | .inr j => right.realValueLeafModuli value p R j

noncomputable def realValueNodeCutoff {σ : Type*} (value : σ → ℝ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) : {n : ℕ} → MovingSlotData σ n → ℝ → ℝ → ℂ
  | _, .leaf _ _, _, _ => 1
  | n + 1, .node s CL CR u left right, L, R =>
      let p := (MovingSlotData.step s CL CR u left right false).realValuePivot value L R
      (positiveLogCutoff φ (G (n + 1)) p : ℂ) *
        realValueNodeCutoff value φ G left p L * realValueNodeCutoff value φ G right p R

noncomputable def realValueFourierWeight {σ : Type*} (value : σ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (L R : ℝ) : ℂ :=
  ∏ j : TreeLeafIndex n,
    let v := (fourierPolynomialFactor Polynomial.X ψ (T.leafFrequencies j) lo hi hlo hhi).value
      (T.realValueLeafModuli value L R j / X)
    if treeLeafTupleEquiv Bool n (transferConjugations n false) j then conj v else v

noncomputable def realValueSmoothWeight {σ : Type*} (value : σ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) : ℂ :=
  realValueFourierWeight value T ψ X lo hi hlo hhi L R * realValueNodeCutoff value φ G T L R

theorem realSlotProduct_nat {σ : Type*} (value : σ → ℕ) (slots : List σ) :
    realSlotProduct (fun j => (value j : ℝ)) slots =
      (MovingSlotReversal.naturalProduct value slots : ℝ) := by
  induction slots with
  | nil => simp [realSlotProduct, MovingSlotReversal.naturalProduct]
  | cons j slots ih => simpa only [realSlotProduct, MovingSlotReversal.naturalProduct,
      List.map_cons, List.prod_cons, Nat.cast_mul] using congrArg ((value j : ℝ) * ·) ih

theorem MovingSlotReversal.realValuePivot_nat {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (L R : ℝ) :
    s.realValuePivot (fun j => (value j : ℝ)) L R = s.realPivot value L R := by
  simp only [realValuePivot, realPivot, realSlotProduct_nat]

theorem MovingSlotData.realValueLeafModuli_nat {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : ℝ) (j : TreeLeafIndex n) :
    T.realValueLeafModuli (fun i => (value i : ℝ)) L R j = T.realLeafModuli value L R j := by
  induction T generalizing L R with
  | leaf => simp only [realValueLeafModuli, realLeafModuli, realSlotProduct_nat]
  | node s CL CR u left right ihL ihR =>
    cases j with
    | inl j => simp only [realValueLeafModuli, realLeafModuli, MovingSlotReversal.realValuePivot_nat, ihL]
    | inr j => simp only [realValueLeafModuli, realLeafModuli, MovingSlotReversal.realValuePivot_nat, ihR]

theorem realValueNodeCutoff_nat {σ : Type*} (value : σ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : ℝ) :
    realValueNodeCutoff (fun i => (value i : ℝ)) φ G T L R = movingRealNodeCutoff value φ G T L R := by
  induction T generalizing L R with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    simp only [realValueNodeCutoff, movingRealNodeCutoff, MovingSlotReversal.realValuePivot_nat, ihL, ihR]

/-- The extension agrees exactly with the original function at every natural
prime tuple, including points where a cutoff vanishes. -/
theorem realValueSmoothWeight_nat {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueSmoothWeight (fun i => (value i : ℝ)) T ψ X lo hi hlo hhi φ G L R =
      movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G L R := by
  simp only [realValueSmoothWeight, movingRealSmoothWeight, realValueFourierWeight,
    movingRealFourierWeight, realValueNodeCutoff_nat, MovingSlotData.realValueLeafModuli_nat]

end Ostmann

end OAI
