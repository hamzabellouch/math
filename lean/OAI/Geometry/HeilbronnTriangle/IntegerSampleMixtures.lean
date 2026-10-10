import OAI.Geometry.HeilbronnTriangle.IntegerSampling
import OAI.Geometry.HeilbronnTriangle.MixtureLifting

namespace OAI


namespace Problem355.IntegerSampleMixtures

noncomputable section
open IntegerSampling ConditionalSamples LiftingProbability

abbrev Column (h q L : ℕ) :=
  Box (L * (h * q)) 3 (samplingShift (L * (h * q)))

variable {β Θ Ω : Type*}

def mixedColumnLaw [Fintype β] (h q L : ℕ)
    (F : Θ → β → Fin 3 → ZMod h) (p : β → ℝ)
    (V : Ω → Finset (Fin 3 → ZMod q)) (s : ℕ) (z : Θ × Ω)
    (x : Column h q L) : ℝ :=
  MixtureLifting.mixtureColumnMass (residue h) (residue q) F p V s L z x

lemma mixedColumnLaw_nonneg [Fintype β] (h q L : ℕ)
    (F : Θ → β → Fin 3 → ZMod h) (p : β → ℝ)
    (V : Ω → Finset (Fin 3 → ZMod q)) (s : ℕ)
    (hp : ∀ b, 0 ≤ p b) (z : Θ × Ω) (x : Column h q L) :
    0 ≤ mixedColumnLaw h q L F p V s z x :=
  MixtureLifting.mixtureColumnMass_nonneg (residue h) (residue q) F p V s L hp z x

lemma sum_mixedColumnLaw [Fintype β] (h q L : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L)
    (F : Θ → β → Fin 3 → ZMod h) (p : β → ℝ)
    (V : Ω → Finset (Fin 3 → ZMod q)) (s : ℕ)
    (hp : ∑ b, p b = 1) (hs : 0 < s) (hV : ∀ ω, (V ω).card = s)
    (z : Θ × Ω) : ∑ x, mixedColumnLaw h q L F p V s z x = 1 := by
  apply MixtureLifting.sum_mixtureColumnMass (residue h) (residue q) F p V s L
    hp hs hL hV
  exact card_joint_residue_fibre h q L 3 hc (samplingShift (L * (h * q)))

def sampleLaw [Fintype β] (h q L m : ℕ)
    (F : Θ → β → Fin 3 → ZMod h) (ρ : Θ → ℝ) (w : Ω → ℝ) (p : β → ℝ)
    (V : Ω → Finset (Fin 3 → ZMod q)) (s : ℕ)
    (z : (Θ × Ω) × (Fin m → Column h q L)) : ℝ :=
  sharedWeight (fun a => ρ a.1 * w a.2) (mixedColumnLaw h q L F p V s) z

lemma sampleLaw_nonneg [Fintype β] (h q L m : ℕ)
    (F : Θ → β → Fin 3 → ZMod h) (ρ : Θ → ℝ) (w : Ω → ℝ) (p : β → ℝ)
    (V : Ω → Finset (Fin 3 → ZMod q)) (s : ℕ)
    (hρ : ∀ θ, 0 ≤ ρ θ) (hw : ∀ ω, 0 ≤ w ω) (hp : ∀ b, 0 ≤ p b)
    (z : (Θ × Ω) × (Fin m → Column h q L)) :
    0 ≤ sampleLaw h q L m F ρ w p V s z := by
  apply sharedWeight_nonneg
  · intro a
    exact mul_nonneg (hρ a.1) (hw a.2)
  · intro a x
    exact mixedColumnLaw_nonneg h q L F p V s hp a x

lemma sum_sampleLaw [Fintype β] [Fintype Θ] [Fintype Ω]
    (h q L m : ℕ) [NeZero h] [NeZero q] (hc : h.Coprime q) (hL : 0 < L)
    (F : Θ → β → Fin 3 → ZMod h) (ρ : Θ → ℝ) (w : Ω → ℝ) (p : β → ℝ)
    (V : Ω → Finset (Fin 3 → ZMod q)) (s : ℕ)
    (hρ : ∑ θ, ρ θ = 1) (hw : ∑ ω, w ω = 1) (hp : ∑ b, p b = 1)
    (hs : 0 < s) (hV : ∀ ω, (V ω).card = s) :
    ∑ z, sampleLaw h q L m F ρ w p V s z = 1 := by
  apply sum_sharedWeight
  · rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hw, mul_one]
    exact hρ
  · intro a
    exact sum_mixedColumnLaw h q L hc hL F p V s hp hs hV a

lemma projected_mem_unitSquare (h q L : ℕ) [NeZero h] [NeZero q]
    (hL : 0 < L) (x : Column h q L) : pointInUnitSquare (project x) := by
  apply project_in_unitSquare
  exact Nat.mul_pos hL (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne h))
    (Nat.pos_of_ne_zero (NeZero.ne q)))

lemma triple_pointwise_law [Fintype β] [Fintype Θ] [Fintype Ω]
    (h q L : ℕ) (F : Θ → β → Fin 3 → ZMod h)
    (ρ : Θ → ℝ) (w : Ω → ℝ) (p : β → ℝ)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (O : (Fin 3 → β) → Finset (Fin 3 → Fin 3 → ZMod h)) (s : ℕ)
    (hpush : ∀ labels a,
      pushforwardMass ρ (fun θ i => F θ (labels i)) a = mainMass (O labels) a)
    (x : Fin 3 → Column h q L) :
    (∑ a : Θ × Ω, sampleLaw h q L 3 F ρ w p V s (a, x)) =
      ∑ labels : Fin 3 → β, productWeight p labels *
        liftedMass (fun x i => residue h (x i)) (fun x i => residue q (x i))
          (O labels) w V s (L ^ 9) x := by
  unfold sampleLaw sharedWeight mixedColumnLaw
  have H := MixtureLifting.averaged_mixture_columns_eq_liftedMixture
    (residue h) (residue q) F ρ w p V O s L hpush x
  simpa only [sampleLaw, sharedWeight, mixedColumnLaw, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc] using H

lemma triple_event_law [Fintype β] [Fintype Θ] [Fintype Ω]
    (h q L : ℕ) (F : Θ → β → Fin 3 → ZMod h)
    (ρ : Θ → ℝ) (w : Ω → ℝ) (p : β → ℝ)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (O : (Fin 3 → β) → Finset (Fin 3 → Fin 3 → ZMod h)) (s : ℕ)
    (hpush : ∀ labels a,
      pushforwardMass ρ (fun θ i => F θ (labels i)) a = mainMass (O labels) a)
    (E : Finset (Fin 3 → Column h q L)) :
    (∑ x ∈ E, ∑ a : Θ × Ω, sampleLaw h q L 3 F ρ w p V s (a, x)) =
      ∑ labels : Fin 3 → β, productWeight p labels *
        ∑ x ∈ E, liftedMass (fun x i => residue h (x i))
          (fun x i => residue q (x i)) (O labels) w V s (L ^ 9) x := by
  simp_rw [triple_pointwise_law h q L F ρ w p V O s hpush]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro labels _
  rw [Finset.mul_sum]

abbrev MainChange (h : ℕ) := Matrix.SpecialLinearGroup (Fin 3) (ZMod h)

def slColumn {h : ℕ} (G : MainChange h) (c : Fin 3 → ZMod h) : Fin 3 → ZMod h :=
  (G : Matrix (Fin 3) (Fin 3) (ZMod h)).mulVec c

def mainLaw (h : ℕ) [NeZero h] (_G : MainChange h) : ℝ :=
  1 / (Fintype.card (MainChange h) : ℝ)

lemma mainLaw_nonneg (h : ℕ) [NeZero h] (G : MainChange h) : 0 ≤ mainLaw h G := by
  unfold mainLaw
  positivity

lemma sum_mainLaw (h : ℕ) [NeZero h] : ∑ G, mainLaw h G = 1 := by
  have hc : (Fintype.card (MainChange h) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [mainLaw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_one_div_cancel hc

lemma sum_SL_sampleLaw [Fintype β] [Fintype Ω]
    (h q L m : ℕ) [NeZero h] [NeZero q] (hc : h.Coprime q) (hL : 0 < L)
    (c : β → Fin 3 → ZMod h) (w : Ω → ℝ) (p : β → ℝ)
    (V : Ω → Finset (Fin 3 → ZMod q)) (s : ℕ)
    (hw : ∑ ω, w ω = 1) (hp : ∑ b, p b = 1)
    (hs : 0 < s) (hV : ∀ ω, (V ω).card = s) :
    (∑ z, sampleLaw h q L m (fun G b => slColumn G (c b)) (mainLaw h) w p V s z) = 1 :=
  sum_sampleLaw h q L m hc hL (fun G b => slColumn G (c b))
    (mainLaw h) w p V s (sum_mainLaw h) hw hp hs hV

end
end Problem355.IntegerSampleMixtures

end OAI
