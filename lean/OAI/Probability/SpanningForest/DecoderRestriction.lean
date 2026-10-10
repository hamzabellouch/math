import OAI.Probability.SpanningForest.Picard

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem336.Picard

lemma iterate_restrict {ι κ : Type*} (f : κ → ι)
    (w : ι → ℝ → ℝ) (v : κ → ℝ → ℝ)
    (b : ℝ → (ι → ℝ) → ι → ℝ) (c : ℝ → (κ → ℝ) → κ → ℝ)
    (hw : ∀ k t, w (f k) t = v k t)
    (hb : ∀ t (y : ι → ℝ) k, b t y (f k) = c t (fun j => y (f j)) k) :
    ∀ n k t, iterate w b n (f k) t = iterate v c n k t := by
  intro n
  induction n with
  | zero => exact hw
  | succ n ih =>
    intro k t
    simp only [iterate, hw]
    congr 1
    apply congrArg (fun g : ℝ → ℝ => ∫ s in (0 : ℝ)..t, g s)
    funext s
    rw [hb]
    have hfield : (fun j => iterate w b n (f j) s) =
        (fun j => iterate v c n j s) := by
      funext j
      exact ih j s
    rw [hfield]

lemma decode_restrict {ι κ : Type*} (f : κ → ι)
    (w : ι → ℝ → ℝ) (v : κ → ℝ → ℝ)
    (b : ℝ → (ι → ℝ) → ι → ℝ) (c : ℝ → (κ → ℝ) → κ → ℝ)
    (hw : ∀ k t, w (f k) t = v k t)
    (hb : ∀ t (y : ι → ℝ) k, b t y (f k) = c t (fun j => y (f j)) k)
    (k : κ) (t : ℝ) : decode w b (f k) t = decode v c k t := by
  unfold decode
  congr 1
  funext n
  exact iterate_restrict f w v b c hw hb n k t

lemma iterate_eq_input_of_drift_zero {ι : Type*}
    (w : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ) (i : ι)
    (hb : ∀ t y, b t y i = 0) :
    ∀ n t, iterate w b n i t = w i t := by
  intro n t
  cases n with
  | zero => rfl
  | succ n => simp [iterate, hb]

lemma decode_eq_input_of_drift_zero {ι : Type*}
    (w : ι → ℝ → ℝ) (b : ℝ → (ι → ℝ) → ι → ℝ) (i : ι)
    (hb : ∀ t y, b t y i = 0) (t : ℝ) : decode w b i t = w i t := by
  unfold decode
  have heq : (fun n => iterate w b n i t) = (fun _ : ℕ => w i t) := by
    funext n
    exact iterate_eq_input_of_drift_zero w b i hb n t
  rw [heq]
  exact tendsto_const_nhds.limUnder_eq

end Problem336.Picard

end

end OAI
