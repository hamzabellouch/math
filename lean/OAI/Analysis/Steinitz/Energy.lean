import OAI.Analysis.Steinitz.Coefficients

namespace OAI

/-! Telescoping matrix energy and trace budgets. -/

namespace EuclideanSteinitz.Energy
open Matrix MatrixEnergy Gain Spectral
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def pTrace (A : Matrix ι ι ℝ) : ℝ := (cfc potential A).trace
noncomputable def hTrace (A : Matrix ι ι ℝ) : ℝ := pTrace A + gainValue A

lemma pTrace_mono {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : A ≤ B) : pTrace A ≤ pTrace B := by
  dsimp only [pTrace]
  rw [← cfc_primitive_eq hA, ← cfc_primitive_eq hB]
  exact trace_primitive_monotone hA.1 hB.1 hAB

lemma gainValue_mono {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hAB : A ≤ B) :
    gainValue A ≤ gainValue B := by
  have h := gainValue_monotone hA (Matrix.le_iff.mp hAB)
    (show (0 : ℝ) ≤ 0 by rfl) (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
  simpa only [zero_smul, one_smul, add_zero, add_sub_cancel] using h

lemma trace_contraction {f : ℝ → ℝ}
    (hf : ∀ {A B : Matrix ι ι ℝ}, A.PosSemidef → B.PosSemidef → A ≤ B →
      (cfc f A).trace ≤ (cfc f B).trace)
    {A C : Matrix ι ι ℝ} (hA : A.PosSemidef) (hC : C * C.transpose ≤ 1) :
    (cfc f (C * A * C.transpose)).trace ≤ (cfc f A).trace := by
  let S := CFC.sqrt A
  have hS : S.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
  have hSS : S * S = A := by simpa only [← sq] using CFC.sq_sqrt A hA.nonneg
  have hCA : (C * A * C.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hA.mul_mul_conjTranspose_same C
  have hSC : (S * (C.transpose * C) * S).PosSemidef := by
    have hp : (C.transpose * C).PosSemidef := by
      simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
        (star_mul_self_nonneg C : (0 : Matrix ι ι ℝ) ≤ star C * C).posSemidef
    simpa only [hS.eq] using hp.conjTranspose_mul_mul_same S
  have hle : S * (C.transpose * C) * S ≤ A := by
    have hp := (Matrix.le_iff.mp (transpose_contraction hC)).conjTranspose_mul_mul_same S
    rw [hS.eq] at hp
    apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hSS] using hp
  have heq : (C * A * C.transpose).charpoly = (S * (C.transpose * C) * S).charpoly := by
    rw [← hSS]
    convert charpoly_mul_comm (C * S) (S * C.transpose) using 1 <;> simp only [Matrix.mul_assoc]
  rw [trace_cfc_eq_of_charpoly hCA.1 hSC.1 heq]
  exact hf hSC hA hle

lemma pTrace_contraction {A C : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hC : C * C.transpose ≤ 1) : pTrace (C * A * C.transpose) ≤ pTrace A :=
  trace_contraction (fun hA hB hAB => pTrace_mono hA hB hAB) hA hC

lemma gainValue_contraction {A C : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hC : C * C.transpose ≤ 1) : gainValue (C * A * C.transpose) ≤ gainValue A :=
  trace_contraction (fun hA _ hAB => gainValue_mono hA hAB) hA hC

noncomputable def stepCost (p : Move ι) (D : Matrix ι ι ℝ) : ℝ :=
  hTrace D - hTrace (p.old D) + hTrace (p.next D) - hTrace (p.old D)

noncomputable def cost (D : Matrix ι ι ℝ) : List (Move ι) → ℝ
  | [] => 0
  | p :: ps => stepCost p D + cost (p.next D) ps

noncomputable def finish (D : Matrix ι ι ℝ) : List (Move ι) → Matrix ι ι ℝ
  | [] => D
  | p :: ps => finish (p.next D) ps

lemma Move.old_le_next {p : Move ι} (hp : p.Admissible) (D : Matrix ι ι ℝ) :
    p.old D ≤ p.next D := by
  exact le_add_of_nonneg_right hp.2.nonneg

lemma step_bounds {D : Matrix ι ι ℝ} (hD : D.PosSemidef) {p : Move ι}
    (hp : p.Admissible) :
    0 ≤ pTrace D - pTrace (p.old D) ∧
    0 ≤ gainValue D - gainValue (p.old D) ∧
    0 ≤ pTrace (p.next D) - pTrace (p.old D) ∧
    0 ≤ gainValue (p.next D) - gainValue (p.old D) := by
  exact ⟨sub_nonneg.mpr (pTrace_contraction hD hp.1),
    sub_nonneg.mpr (gainValue_contraction hD hp.1),
    sub_nonneg.mpr (pTrace_mono (p.old_psd hD) (p.next_psd hp hD) (Move.old_le_next hp D)),
    p.gain_nonneg hp hD⟩

lemma stepCost_nonneg {D : Matrix ι ι ℝ} (hD : D.PosSemidef) {p : Move ι}
    (hp : p.Admissible) : 0 ≤ stepCost p D := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := step_bounds hD hp
  dsimp only [stepCost, hTrace]
  linarith

lemma cost_nonneg {D : Matrix ι ι ℝ} (hD : D.PosSemidef) {ps : List (Move ι)}
    (hp : ∀ p ∈ ps, p.Admissible) : 0 ≤ cost D ps := by
  induction ps generalizing D with
  | nil => rfl
  | cons p ps ih =>
    have hp₀ := hp p (List.mem_cons_self ..)
    exact add_nonneg (stepCost_nonneg hD hp₀)
      (ih (p.next_psd hp₀ hD) (fun q hq => hp q (List.mem_cons_of_mem p hq)))

lemma gainCost_le_cost {D : Matrix ι ι ℝ} (hD : D.PosSemidef) {ps : List (Move ι)}
    (hp : ∀ p ∈ ps, p.Admissible) : gainCost D ps ≤ cost D ps := by
  induction ps generalizing D with
  | nil => rfl
  | cons p ps ih =>
    have hp₀ := hp p (List.mem_cons_self ..)
    have hi := ih (p.next_psd hp₀ hD) (fun q hq => hp q (List.mem_cons_of_mem p hq))
    obtain ⟨h₁,h₂,h₃,h₄⟩ := step_bounds hD hp₀
    dsimp only [gainCost, cost, stepCost, hTrace]
    linarith

lemma trace_change_le_cost {D : Matrix ι ι ℝ} (hD : D.PosSemidef) {ps : List (Move ι)}
    (hp : ∀ p ∈ ps, p.Admissible) : pTrace D - pTrace (finish D ps) ≤ cost D ps := by
  induction ps generalizing D with
  | nil => simp only [finish, cost, sub_self, le_refl]
  | cons p ps ih =>
    have hp₀ := hp p (List.mem_cons_self ..)
    have hi := ih (p.next_psd hp₀ hD) (fun q hq => hp q (List.mem_cons_of_mem p hq))
    obtain ⟨h₁,h₂,h₃,h₄⟩ := step_bounds hD hp₀
    dsimp only [finish, cost, stepCost, hTrace]
    linarith

omit [DecidableEq ι] in
lemma finish_eq_follow (Z V : Matrix ι ι ℝ) (ps : List (Move ι)) :
    finish (Z + V) ps = (follow Z V ps).1 + (follow Z V ps).2 := by
  induction ps generalizing Z V with
  | nil => rfl
  | cons p ps ih =>
    simp only [finish, follow]
    rw [show p.next (Z + V) = p.old Z + p.next V by simp [Move.next, p.old_add, add_assoc]]
    exact ih _ _

omit [DecidableEq ι] in
lemma finish_eq_follow_zero (Y : Matrix ι ι ℝ) (ps : List (Move ι)) :
    finish Y ps = (follow Y 0 ps).1 + (follow Y 0 ps).2 := by
  simpa only [add_zero] using finish_eq_follow Y 0 ps

lemma endpoint_cost {Y : Matrix ι ι ℝ} (hY : Y.PosSemidef) {ps : List (Move ι)}
    (hp : ∀ p ∈ ps, p.Admissible) {E : ℝ} (hcost : cost Y ps ≤ E)
    (hsmall : E ≤ 1 / (16 * gainConstant)) :
    let Z := (follow Y 0 ps).1
    let X := finish Y ps
    (pTrace Y - pTrace Z) + (pTrace X - pTrace Z) ≤
      E + 16 * (gainConstant * E) ^ (1 / exponent) * (cfc sizeWeight X).trace := by
  dsimp only
  have hbound := accumulated_gain_bound hY hp ((gainCost_le_cost hY hp).trans hcost) hsmall
  obtain ⟨hq, hq₁, _, hb⟩ := hbound
  have hpsd := follow_psd hY Matrix.PosSemidef.zero hp
  have hX : (finish Y ps).PosSemidef := by
    rw [finish_eq_follow_zero]
    exact hpsd.1.add hpsd.2
  have hXZ : finish Y ps - (follow Y 0 ps).1 ≤
      (gainConstant * E) ^ (1 / exponent) • (1 + finish Y ps) := by
    rw [finish_eq_follow_zero, add_sub_cancel_left]
    exact hb
  have hg := trace_potential_direct hX hpsd.1 hq hq₁.le hXZ
  have ht := (trace_change_le_cost hY hp).trans hcost
  change pTrace (finish Y ps) - pTrace (follow Y 0 ps).1 ≤ _ at hg
  linarith

lemma gainConstant_one_le : 1 ≤ gainConstant := by
  have hs : 1 ≤ Real.sqrt 8 := by
    exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [gainConstant, two_rpow_exponent]
  norm_num [exponent]
  nlinarith

lemma sizeTrace_nonneg {X : Matrix ι ι ℝ} (hX : X.PosSemidef) :
    0 ≤ (cfc sizeWeight X).trace := by
  apply Matrix.PosSemidef.trace_nonneg
  apply Matrix.nonneg_iff_posSemidef.mp
  apply cfc_nonneg
  intro x hx
  have hx₀ := spectrum_nonneg_of_nonneg hX.nonneg hx
  exact le_min (Real.rpow_nonneg hx₀ _) (inv_nonneg.mpr hx₀)

noncomputable def incrementConstant : ℝ :=
  230400 * (1 + 16 * gainConstant ^ (1 / exponent))

lemma incrementConstant_pos : 0 < incrementConstant := by
  have hc := gainConstant_pos
  unfold incrementConstant
  positivity

lemma cost_power_bound {E k : ℝ} (hE : 0 ≤ E) (hk : 0 ≤ k)
    (hsmall : E ≤ 1 / (16 * gainConstant)) :
    E + 16 * (gainConstant * E) ^ (1 / exponent) * k ≤
      (1 + 16 * gainConstant ^ (1 / exponent)) * (1 + k) * E ^ (1 / exponent) := by
  have hc := gainConstant_one_le
  have hE1 : E ≤ 1 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16) gainConstant_pos)).mp hsmall
    nlinarith
  have he := Real.self_le_rpow_of_le_one hE hE1 (show 1 / exponent ≤ 1 by norm_num [exponent])
  have hr : 0 ≤ E ^ (1 / exponent) := Real.rpow_nonneg hE _
  have hc₀ : 0 ≤ gainConstant ^ (1 / exponent) := Real.rpow_nonneg gainConstant_pos.le _
  rw [Real.mul_rpow gainConstant_pos.le hE]
  nlinarith [mul_nonneg (mul_nonneg hc₀ hr) (by norm_num : (0 : ℝ) ≤ 16), mul_nonneg hk hr]

lemma endpoint_cost_power {Y : Matrix ι ι ℝ} (hY : Y.PosSemidef) {ps : List (Move ι)}
    (hp : ∀ p ∈ ps, p.Admissible) {E : ℝ} (hcost : cost Y ps ≤ E)
    (hsmall : E ≤ 1 / (16 * gainConstant)) :
    let Z := (follow Y 0 ps).1
    let X := finish Y ps
    (pTrace Y - pTrace Z) + (pTrace X - pTrace Z) ≤
      (1 + 16 * gainConstant ^ (1 / exponent)) * (1 + (cfc sizeWeight X).trace) *
        E ^ (1 / exponent) := by
  dsimp only
  have hpsd := follow_psd hY Matrix.PosSemidef.zero hp
  have hX : (finish Y ps).PosSemidef := by
    rw [finish_eq_follow_zero]
    exact hpsd.1.add hpsd.2
  exact (endpoint_cost hY hp hcost hsmall).trans
    (cost_power_bound ((cost_nonneg hY hp).trans hcost) (sizeTrace_nonneg hX) hsmall)

end EuclideanSteinitz.Energy

namespace EuclideanSteinitz.Coefficient
open Matrix MatrixEnergy Gain Energy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma weighted_increment {X Y Z C : Matrix ι ι ℝ}
    (hX : X.PosDef) (hY : Y.PosDef) (hZ : Z.PosDef)
    (hC : IsUnit C) (hContract : C * C.transpose ≤ 1)
    (hZeq : Z = C * Y * C.transpose)
    (T S : Matrix ι κ ℝ) (hT : T * T.transpose = 1) (hS : S * S.transpose = 1)
    (Qold Qnew : Matrix κ κ ℝ) (hOldPSD : Qold.PosSemidef) (hNewPSD : Qnew.PosSemidef)
    (hOldS : S * Qold * S.transpose = Y) (hOldT : T * Qold * T.transpose = Z)
    (hTS : T * S.transpose = C) (hCross : T * Qold * S.transpose = C * Y)
    (hNewT : T * Qnew * T.transpose = X - Z)
    (hZero : lift S (cfc cutoff Y) * Qnew = 0)
    (ps : List (Move ι)) (hp : ∀ p ∈ ps, p.Admissible)
    (hEndX : X = finish Y ps) (hEndZ : Z = (follow Y 0 ps).1)
    {E : ℝ} (hCost : cost Y ps ≤ E) (hSmall : E ≤ 1 / (16 * gainConstant)) :
    weightedSq (lift T (cfc cutoff X) - lift S (cfc cutoff Y)) ((1 + Qold) + Qnew) ≤
      incrementConstant * (1 + (cfc sizeWeight X).trace) * E ^ (1 / exponent) := by
  have h₁ := endpoint_comparison hX hY hZ hC hContract hZeq T S hT hS Qold Qnew
    hOldPSD hNewPSD hOldS hOldT hTS hCross hNewT hZero
  have h₂ := endpoint_cost_power hY.posSemidef hp hCost hSmall
  dsimp only at h₂
  rw [← hEndX, ← hEndZ] at h₂
  have h₃ := mul_le_mul_of_nonneg_left h₂ (by norm_num : (0 : ℝ) ≤ 230400)
  dsimp only [pTrace] at h₃
  unfold incrementConstant
  calc
    _ ≤ _ := h₁.trans h₃
    _ = _ := by ring

end EuclideanSteinitz.Coefficient

end OAI
