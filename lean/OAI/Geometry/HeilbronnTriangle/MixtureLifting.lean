import OAI.Geometry.HeilbronnTriangle.FiniteMixtures
import OAI.Geometry.HeilbronnTriangle.LiftingProbability

namespace OAI


namespace Problem355.MixtureLifting

noncomputable section
open ConditionalSamples LiftingProbability

variable {X A B β Θ Ω : Type*}

def mixtureColumnMass [Fintype β] (f : X → A) (g : X → B)
    (F : Θ → β → A) (p : β → ℝ) (V : Ω → Finset B) (s L : ℕ)
    (z : Θ × Ω) (x : X) : ℝ :=
  mixtureWeight p (fun b => conditionalColumnMass f g (F z.1 b) (V z.2) s L) x

lemma mixtureColumnMass_nonneg [Fintype β] (f : X → A) (g : X → B)
    (F : Θ → β → A) (p : β → ℝ) (V : Ω → Finset B) (s L : ℕ)
    (hp : ∀ b, 0 ≤ p b) (z : Θ × Ω) (x : X) :
    0 ≤ mixtureColumnMass f g F p V s L z x := by
  apply mixtureWeight_nonneg p _ hp
  intro b a
  exact conditionalColumnMass_nonneg f g (F z.1 b) (V z.2) s L a

lemma sum_mixtureColumnMass [Fintype X] [Fintype A] [Fintype B] [Fintype β]
    [DecidableEq A] [DecidableEq B]
    (f : X → A) (g : X → B) (F : Θ → β → A) (p : β → ℝ)
    (V : Ω → Finset B) (s L : ℕ) (hp : ∑ b, p b = 1)
    (hs : 0 < s) (hL : 0 < L) (hV : ∀ ω, (V ω).card = s)
    (hf : ∀ r : A × B, (Finset.univ.filter (fun x => (f x, g x) = r)).card = L ^ 3)
    (z : Θ × Ω) :
    ∑ x, mixtureColumnMass f g F p V s L z x = 1 := by
  apply sum_mixtureWeight p _ hp
  intro b
  exact sum_conditionalColumnMass f g (F z.1 b) (V z.2) s L hs hL (hV z.2) hf

lemma exchange_shared_latent [Fintype Θ] [Fintype Ω] [Fintype β]
    (ρ : Θ → ℝ) (w : Ω → ℝ) (p : β → ℝ) (H : Θ → Ω → β → ℝ) :
    (∑ θ, ρ θ * ∑ ω, w ω * ∑ b, p b * H θ ω b) =
      ∑ b, p b * (∑ θ, ρ θ * ∑ ω, w ω * H θ ω b) := by
  simp_rw [Finset.mul_sum]
  calc
    (∑ θ, ∑ ω, ∑ b, ρ θ * (w ω * (p b * H θ ω b))) =
        ∑ θ, ∑ b, ∑ ω, ρ θ * (w ω * (p b * H θ ω b)) := by
      apply Finset.sum_congr rfl
      intro θ _
      exact Finset.sum_comm
    _ = ∑ b, ∑ θ, ∑ ω, ρ θ * (w ω * (p b * H θ ω b)) := Finset.sum_comm
    _ = ∑ b, ∑ θ, ∑ ω, p b * (ρ θ * (w ω * H θ ω b)) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro θ _
      apply Finset.sum_congr rfl
      intro ω _
      ring

lemma averaged_mixture_columns_eq_liftedMixture
    [Fintype Θ] [Fintype Ω] [Fintype β]
    (f : X → A) (g : X → B) (F : Θ → β → A)
    (ρ : Θ → ℝ) (w : Ω → ℝ) (p : β → ℝ) (V : Ω → Finset B)
    (O : (Fin 3 → β) → Finset (Fin 3 → A)) (s L : ℕ)
    (hpush : ∀ labels a,
      pushforwardMass ρ (fun θ i => F θ (labels i)) a = mainMass (O labels) a)
    (x : Fin 3 → X) :
    (∑ θ, ρ θ * ∑ ω, w ω *
      productWeight (mixtureColumnMass f g F p V s L (θ, ω)) x) =
      ∑ labels : Fin 3 → β, productWeight p labels *
        liftedMass (fun x i => f (x i)) (fun x i => g (x i))
          (O labels) w V s (L ^ 9) x := by
  classical
  unfold mixtureColumnMass
  simp_rw [productWeight_mixture]
  rw [exchange_shared_latent]
  apply Finset.sum_congr rfl
  intro labels _
  rw [averaged_columns_eq_liftedMass f g (fun θ i => F θ (labels i))
    ρ w V (O labels) s L (hpush labels) x]

lemma mixture_event_eq_liftedMixture
    [Fintype Θ] [Fintype Ω] [Fintype β]
    (f : X → A) (g : X → B) (F : Θ → β → A)
    (ρ : Θ → ℝ) (w : Ω → ℝ) (p : β → ℝ) (V : Ω → Finset B)
    (O : (Fin 3 → β) → Finset (Fin 3 → A)) (s L : ℕ)
    (hpush : ∀ labels a,
      pushforwardMass ρ (fun θ i => F θ (labels i)) a = mainMass (O labels) a)
    (E : Finset (Fin 3 → X)) :
    (∑ x ∈ E, ∑ θ, ρ θ * ∑ ω, w ω *
      productWeight (mixtureColumnMass f g F p V s L (θ, ω)) x) =
      ∑ labels : Fin 3 → β, productWeight p labels *
        ∑ x ∈ E, liftedMass (fun x i => f (x i)) (fun x i => g (x i))
          (O labels) w V s (L ^ 9) x := by
  simp_rw [averaged_mixture_columns_eq_liftedMixture f g F ρ w p V O s L hpush]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro labels _
  rw [Finset.mul_sum]

lemma sum_shared_mixtureWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype X] [Fintype A] [Fintype B] [Fintype β] [Fintype Θ] [Fintype Ω]
    [DecidableEq A] [DecidableEq B]
    (f : X → A) (g : X → B) (F : Θ → β → A)
    (ρ : Θ → ℝ) (w : Ω → ℝ) (p : β → ℝ) (V : Ω → Finset B)
    (s L : ℕ) (hρ : ∑ θ, ρ θ = 1) (hw : ∑ ω, w ω = 1)
    (hp : ∑ b, p b = 1) (hs : 0 < s) (hL : 0 < L)
    (hV : ∀ ω, (V ω).card = s)
    (hf : ∀ r : A × B, (Finset.univ.filter (fun x => (f x, g x) = r)).card = L ^ 3) :
    ∑ z : (Θ × Ω) × (ι → X),
      sharedWeight (fun a => ρ a.1 * w a.2) (mixtureColumnMass f g F p V s L) z = 1 := by
  apply sum_sharedWeight
  · rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hw, mul_one]
    exact hρ
  · intro z
    exact sum_mixtureColumnMass f g F p V s L hp hs hL hV hf z

end
end Problem355.MixtureLifting

end OAI
