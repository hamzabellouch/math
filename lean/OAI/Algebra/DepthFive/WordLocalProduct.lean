import OAI.Algebra.DepthFive.IsolatedWeight

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.WordLocalProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A per-layer factor in the normalized four-path moment bound.
True is the diagonal type; `A = alpha⁻¹`, `B = beta`, `x = n⁻¹`. -/
def localFactor (V : Finset ι) (R : ι → ι → Prop) (A B x : ℝ)
    (w : ι → Bool) (i : ι) : ℝ :=
  if i ∈ V then
    if w i = true then A else 1 + A * x ^ (IsolatedWeight.falseNeighbors R w i).card
  else if w i = true then B else 1

lemma localFactor_eq_parts (V : Finset ι) (R : ι → ι → Prop) (A B x : ℝ)
    (w : ι → Bool) (i : ι) :
    localFactor V R A B x w i =
      (if i ∈ V.filter (fun j => w j = true) then A else 1) *
      (if i ∈ (Finset.univ \ V).filter (fun j => w j = true) then B else 1) *
      (if i ∈ V.filter (fun j => w j = false)
        then 1 + A * x ^ (IsolatedWeight.falseNeighbors R w i).card else 1) := by
  classical
  by_cases hi : i ∈ V <;> cases hw : w i <;> simp [localFactor, hi, hw]

/-- The count-based word summand is exactly the product of the normalized
local factors, including the normal-V coincidences. -/
theorem weight_eq_local_product (edges : Finset (ι × ι)) (V : Finset ι)
    (R : ι → ι → Prop) (A B x : ℝ) (w : ι → Bool) :
    IsolatedWeight.weight edges V R A B x w =
      x ^ SwitchRestoration.switchCount edges w * ∏ i, localFactor V R A B x w i := by
  classical
  simp_rw [localFactor_eq_parts]
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_const]
  simp only [IsolatedWeight.weight, IsolatedWeight.correction]
  ring

/-- An inverse-natural-power form matching the manuscript's original parameters. -/
theorem weight_eq_inverse_local_product (edges : Finset (ι × ι)) (V : Finset ι)
    (R : ι → ι → Prop) (a b d : ℝ) (w : ι → Bool) :
    IsolatedWeight.weight edges V R a⁻¹ b d⁻¹ w =
      (d ^ SwitchRestoration.switchCount edges w)⁻¹ *
        ∏ i, if i ∈ V then
          if w i = true then a⁻¹ else
            1 + a⁻¹ * (d ^ (IsolatedWeight.falseNeighbors R w i).card)⁻¹
        else if w i = true then b else 1 := by
  rw [weight_eq_local_product]
  simp only [localFactor, inv_pow]

lemma localFactor_nonneg (V : Finset ι) (R : ι → ι → Prop)
    {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x)
    (w : ι → Bool) (i : ι) : 0 ≤ localFactor V R A B x w i := by
  unfold localFactor
  split_ifs <;> positivity

/-- Before discarding U-coincidence factors, a normal U layer may have
weight `1+B`. The Boolean `coincides` records the relevant equality event. -/
def momentLocalFactor (V : Finset ι) (R : ι → ι → Prop) (A B x : ℝ)
    (w coincides : ι → Bool) (i : ι) : ℝ :=
  if i ∈ V then localFactor V R A B x w i
  else if w i = true then B else if coincides i = true then 1 + B else 1

lemma momentLocalFactor_nonneg (V : Finset ι) (R : ι → ι → Prop)
    {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x)
    (w coincides : ι → Bool) (i : ι) :
    0 ≤ momentLocalFactor V R A B x w coincides i := by
  unfold momentLocalFactor
  split_ifs
  · exact localFactor_nonneg V R hA hB hx w i
  all_goals positivity

lemma momentLocalFactor_le (V : Finset ι) (R : ι → ι → Prop)
    {A B x : ℝ} (hB : 0 ≤ B) (w coincides : ι → Bool) (i : ι) :
    momentLocalFactor V R A B x w coincides i ≤
      localFactor V R A B x w i * (if i ∈ Finset.univ \ V then 1 + B else 1) := by
  classical
  by_cases hi : i ∈ V
  · simp [momentLocalFactor, hi]
  · cases hw : w i <;> cases hc : coincides i <;>
      simp [momentLocalFactor, localFactor, hi, hw, hc] <;> nlinarith

/-- The global U-coincidence cost is at most `(1+B)^|U|`, without any
independence assumption on U layers. -/
theorem prod_momentLocalFactor_le (V : Finset ι) (R : ι → ι → Prop)
    {A B x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x)
    (w coincides : ι → Bool) :
    (∏ i, momentLocalFactor V R A B x w coincides i) ≤
      (∏ i, localFactor V R A B x w i) * (1 + B) ^ (Finset.univ \ V).card := by
  classical
  have h := Finset.prod_le_prod₀
    (fun i (_ : i ∈ Finset.univ) => momentLocalFactor_nonneg V R hA hB hx w coincides i)
    (fun i (_ : i ∈ Finset.univ) => momentLocalFactor_le V R hB w coincides i)
  simpa only [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_const] using h


/-- A switch-weighted local moment product is controlled by the canonical
word weight and the single global U-coincidence factor. -/
theorem switchWeighted_momentLocalFactor_le (edges : Finset (ι × ι))
    (V : Finset ι) (R : ι → ι → Prop) {A B x : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x) (w coincides : ι → Bool) :
    x ^ SwitchRestoration.switchCount edges w *
        (∏ i, momentLocalFactor V R A B x w coincides i) ≤
      (1 + B) ^ (Finset.univ \ V).card * IsolatedWeight.weight edges V R A B x w := by
  have h := mul_le_mul_of_nonneg_left
    (prod_momentLocalFactor_le V R hA hB hx w coincides)
    (pow_nonneg hx (SwitchRestoration.switchCount edges w))
  rw [weight_eq_local_product]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

/-- The global moment reduction may discard all U-coincidence events,
even when they depend jointly on the entire word. -/
theorem sum_switchWeighted_momentLocalFactor_le (edges : Finset (ι × ι))
    (V : Finset ι) (R : ι → ι → Prop) {A B x : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 0 ≤ x)
    (coincides : (ι → Bool) → ι → Bool) :
    (∑ w : ι → Bool, x ^ SwitchRestoration.switchCount edges w *
      (∏ i, momentLocalFactor V R A B x w (coincides w) i)) ≤
      (1 + B) ^ (Finset.univ \ V).card *
        ∑ w : ι → Bool, IsolatedWeight.weight edges V R A B x w := by
  classical
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun w _ =>
    switchWeighted_momentLocalFactor_le edges V R hA hB hx w (coincides w))

end Problem335.WordLocalProduct

end

end OAI
