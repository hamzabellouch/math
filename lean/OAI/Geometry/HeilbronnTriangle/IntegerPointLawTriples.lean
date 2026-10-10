import OAI.Geometry.HeilbronnTriangle.IntegerPointLaw
import OAI.Geometry.HeilbronnTriangle.OrbitSampling
import OAI.Geometry.HeilbronnTriangle.ProjectiveBadEvent

namespace OAI


noncomputable section

namespace Problem355.IntegerPointLaw

open IntegerSampling ConditionalSamples ParameterSampling
open Finset
attribute [local instance] Classical.propDecidable

theorem shared_mixture_expectation {Θ D X : Type*}
    [Fintype Θ] [Fintype D] [Fintype X]
    (rho : Θ → ℝ) (p : D → ℝ) (nu : Θ → D → X → ℝ)
    (F : (Fin 3 → X) → ℝ) :
    (∑ θ, rho θ * ∑ x : Fin 3 → X,
      productWeight (mixtureWeight p (nu θ)) x * F x) =
    ∑ d : Fin 3 → D, productWeight p d *
      ∑ x : Fin 3 → X, (∑ θ, rho θ * ∏ i, nu θ (d i) (x i)) * F x := by
  simp_rw [expectation_productWeight_mixture, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ _
  ring

theorem ofSpecialLinear_expectation {Ω D : Type} [Fintype Ω] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ ω, (V ω).card = s)
    (F : (Fin 3 → Box (L * (h * q)) 3 (samplingShift (L * (h * q)))) → ℝ) :
    let law := ofSpecialLinear h q L s hc hL hs w p c V hw hwsum hp hpsum hV
    (∑ z : law.Environment × (Fin 3 → law.Column),
      sharedWeight law.rho law.mu z * F z.2) =
    ∑ d : Fin 3 → D, productWeight p d *
      ∑ x, LiftingProbability.liftedMass
        (fun x i => residue h (x i)) (fun x i => residue q (x i))
        (OrbitSampling.orbitFinset (OrbitSampling.MainGroup h) (fun i => c (d i)))
        w V s (L ^ 9) x * F x := by
  classical
  dsimp only
  change (∑ z : (OrbitSampling.MainGroup h × Ω) ×
      (Fin 3 → Box (L * (h * q)) 3 (samplingShift (L * (h * q)))),
    ((1 / (Nat.card (OrbitSampling.MainGroup h) : ℝ)) * w z.1.2) *
      productWeight (mixtureWeight p (fun d => columnLaw h q L
        (samplingShift (L * (h * q))) (z.1.1 • c d) (V z.1.2) s)) z.2 * F z.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [mul_assoc]
  conv_lhs =>
    arg 2
    ext θ
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_assoc]
  rw [shared_mixture_expectation]
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [Fintype.sum_prod_type]
  simpa only [Finset.mul_sum, mul_assoc, Pi.smul_apply] using
    (OrbitSampling.sl_averaged_columns_eq_liftedMass h q L
      (samplingShift (L * (h * q))) (fun i => c (d i)) w V s x)

def triangleEvent {N : ℕ} (a : ℝ)
    (x : Fin 3 → Box N 3 (samplingShift N)) : Prop :=
  Alteration.smallTriangle a (project (x 0)) (project (x 1)) (project (x 2))

def badDeterminantEvent {N : ℕ} (τ : ℤ)
    (x : Fin 3 → Box N 3 (samplingShift N)) : Prop :=
  project (x 0) ≠ project (x 1) ∧ project (x 0) ≠ project (x 2) ∧
    project (x 1) ≠ project (x 2) ∧ |(OrbitSampling.integralMatrix x).det| ≤ τ

theorem column_inBox {N : ℕ} (x : Box N 3 (samplingShift N)) :
    Homogeneous.InBox (N : ℝ) (fun i => ((x i).val : ℝ)) := by
  have hx : 0 ≤ (x 0).val ∧ (x 0).val < (N : ℤ) := by
    simpa [samplingShift] using (x 0).property
  have hy : 0 ≤ (x 1).val ∧ (x 1).val < (N : ℤ) := by
    simpa [samplingShift] using (x 1).property
  have hz : (N : ℤ) ≤ (x 2).val ∧ (x 2).val < (N : ℤ) + N :=
    (x 2).property
  unfold Homogeneous.InBox
  dsimp only
  refine ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2,
    by exact_mod_cast hy.1, by exact_mod_cast hy.2,
    by exact_mod_cast hz.1, ?_⟩
  have hh : ((x 2).val : ℝ) < (N : ℝ) + N := by exact_mod_cast hz.2
  linarith

theorem triangleEvent_implies_badDeterminantEvent {N : ℕ} (hN : 0 < N)
    {τ : ℤ} (hτ : 0 ≤ τ) (x : Fin 3 → Box N 3 (samplingShift N))
    (hx : triangleEvent ((τ : ℝ) / (16 * (N : ℝ) ^ 3)) x) :
    badDeterminantEvent τ x := by
  have hcol (j : Fin 3) : Homogeneous.InBox (N : ℝ)
      (Homogeneous.integerColumn (OrbitSampling.integralMatrix x) j) :=
    column_inBox (x j)
  have he := Homogeneous.smallTriangle_integer_determinant
    (by exact_mod_cast hN) hτ (hcol 0) (hcol 1) (hcol 2)
    (OrbitSampling.integralMatrix x).det
    (Homogeneous.integer_columns_det (OrbitSampling.integralMatrix x)) hx
  exact ⟨he.1.1, he.1.2.1, he.1.2.2, he.2⟩

theorem ofSpecialLinear_tripleProbability_eq {Ω D : Type} [Fintype Ω] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ ω, (V ω).card = s) (a : ℝ) :
    (ofSpecialLinear h q L s hc hL hs w p c V hw hwsum hp hpsum hV).tripleProbability a =
    ∑ d : Fin 3 → D, productWeight p d *
      ∑ x ∈ (Finset.univ : Finset (Fin 3 → Box (L * (h * q)) 3
        (samplingShift (L * (h * q))))).filter (triangleEvent a), LiftingProbability.liftedMass
        (fun x i => residue h (x i)) (fun x i => residue q (x i))
        (OrbitSampling.orbitFinset (OrbitSampling.MainGroup h) (fun i => c (d i)))
        w V s (L ^ 9) x := by
  classical
  have he := ofSpecialLinear_expectation h q L s hc hL hs w p c V
    hw hwsum hp hpsum hV (fun x => if triangleEvent a x then 1 else 0)
  unfold PointLaw.tripleProbability SharedGeometricAlteration.tripleMass
  change (∑ z : (OrbitSampling.MainGroup h × Ω) ×
      (Fin 3 → Box (L * (h * q)) 3 (samplingShift (L * (h * q)))),
    if triangleEvent a z.2 then
      sharedWeight (ofSpecialLinear h q L s hc hL hs w p c V hw hwsum hp hpsum hV).rho
        (ofSpecialLinear h q L s hc hL hs w p c V hw hwsum hp hpsum hV).mu z
    else 0) = _
  simp only [ofSpecialLinear, ofIndependentEnvironments, ofMixture,
    Finset.sum_filter, mul_ite, mul_one, mul_zero] at he ⊢
  convert he using 1
  all_goals congr 1

theorem ofSpecialLinear_tripleProbability_le_badDeterminant {Ω D : Type}
    [Fintype Ω] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ ω, (V ω).card = s) {τ : ℤ} (hτ : 0 ≤ τ) :
    (ofSpecialLinear h q L s hc hL hs w p c V hw hwsum hp hpsum hV).tripleProbability
      ((τ : ℝ) / (16 * ((L * (h * q) : ℕ) : ℝ) ^ 3)) ≤
    ∑ d : Fin 3 → D, productWeight p d *
      ∑ x ∈ (Finset.univ : Finset (Fin 3 → Box (L * (h * q)) 3
        (samplingShift (L * (h * q))))).filter (badDeterminantEvent τ),
        LiftingProbability.liftedMass
          (fun x i => residue h (x i)) (fun x i => residue q (x i))
          (OrbitSampling.orbitFinset (OrbitSampling.MainGroup h) (fun i => c (d i)))
          w V s (L ^ 9) x := by
  classical
  rw [ofSpecialLinear_tripleProbability_eq]
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ (productWeight_nonneg p hp d)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩
    exact triangleEvent_implies_badDeterminantEvent
      (mul_pos hL (mul_pos (NeZero.pos h) (NeZero.pos q))) hτ x
      (Finset.mem_filter.mp hx).2
  · intro x _ _
    exact LiftingProbability.liftedMass_nonneg _ _ _ w V s (L ^ 9) hw x

end Problem355.IntegerPointLaw

end

end OAI
