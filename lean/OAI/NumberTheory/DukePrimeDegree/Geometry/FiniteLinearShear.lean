import OAI.NumberTheory.DukePrimeDegree.Geometry.FiniteProductShear

namespace OAI

/-! # Elementary shears, including the zero source-factor case -/

noncomputable section
open MeasureTheory ProbabilityTheory Function

namespace DukePrimeDegree

lemma measurable_finiteCoordinateShear {n : ℕ} (i : Fin (n+1))
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) :
    Measurable (finiteCoordinateShear i F) := by
  exact (finiteCoordinateEquiv i).symm.measurable.comp
    ((measurable_fst.prodMk (measurable_snd.add (hF.comp measurable_fst))).comp
      (finiteCoordinateEquiv i).measurable)

def finiteLinearShear {n : ℕ} (i : Fin (n+1)) (j : Fin n) (r : ℝ) :
    (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) :=
  finiteCoordinateShear i (fun x => r * x j)

lemma measurable_finiteLinearShear {n : ℕ} (i : Fin (n+1)) (j : Fin n) (r : ℝ) :
    Measurable (finiteLinearShear i j r) :=
  measurable_finiteCoordinateShear i _ (measurable_const.mul (measurable_pi_apply j))

lemma finiteLinearShear_apply {n : ℕ} (i : Fin (n+1)) (j : Fin n) (r : ℝ)
    (x : Fin (n+1) → ℝ) (k : Fin (n+1)) :
    finiteLinearShear i j r x k = if k = i then x k + r * x (i.succAbove j) else x k := by
  by_cases hk : k = i
  · subst k
    simp only [finiteLinearShear,finiteCoordinateShear_apply_same,ite_true]
  · obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq hk
    simp [finiteLinearShear,finiteCoordinateShear_apply_succAbove,Fin.succAbove_ne]

theorem finiteLinearShear_preserves {n : ℕ} (i : Fin (n+1)) (j : Fin n) (r : ℝ)
    (ν : Fin (n+1) → Measure ℝ) [∀ k, SigmaFinite (ν k)]
    (h : ν (i.succAbove j) = Measure.dirac 0 ∨
      ∀ a : ℝ, (ν i).map (fun t => t+a) = ν i) :
    MeasurePreserving (finiteLinearShear i j r) (Measure.pi ν) (Measure.pi ν) := by
  rcases h with h | h
  · have hz : ∀ᵐ x ∂Measure.pi ν, x (i.succAbove j) = 0 :=
      (Measure.tendsto_eval_ae_ae (μ := ν)).eventually
        (show ∀ᵐ t ∂ν (i.succAbove j), t = 0 by simp [h])
    refine ⟨measurable_finiteLinearShear i j r, ?_⟩
    calc
      _ = (Measure.pi ν).map id := Measure.map_congr (hz.mono fun x hx => by
        funext k
        simp [finiteLinearShear_apply,hx])
      _ = _ := Measure.map_id
  · exact finiteCoordinateShear_preserves i ν _
      (measurable_const.mul (measurable_pi_apply j)) h

end DukePrimeDegree

end

end OAI
