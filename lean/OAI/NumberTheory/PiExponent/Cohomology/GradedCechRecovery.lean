import Mathlib

namespace OAI

namespace PiExponent.GradedCechRecovery

theorem augmentation_surjective_on_closed
    {P M A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ : Type*}
    [AddCommGroup P] [AddCommGroup M]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [AddCommGroup C₀] [AddCommGroup C₁]
    (a₀ : A₀ →+ A₁) (a₁ : A₁ →+ A₂)
    (b₀ : B₀ →+ B₁) (b₁ : B₁ →+ B₂) (c₀ : C₀ →+ C₁)
    (f₀ : A₀ →+ B₀) (f₁ : A₁ →+ B₁) (f₂ : A₂ →+ B₂)
    (g₀ : B₀ →+ C₀) (g₁ : B₁ →+ C₁)
    (εB : P →+ B₀) (εC : M →+ C₀) (g : P →+ M)
    (hg₀ : Function.Surjective g₀)
    (hker : ∀ z : B₁, g₁ z = 0 → ∃ y : A₁, f₁ y = z)
    (hf₂ : Function.Injective f₂)
    (hff₀ : ∀ x, b₀ (f₀ x) = f₁ (a₀ x))
    (hff₁ : ∀ x, b₁ (f₁ x) = f₂ (a₁ x))
    (hgg : ∀ x, g₁ (b₀ x) = c₀ (g₀ x))
    (hzero : ∀ x, g₀ (f₀ x) = 0)
    (hdiff : ∀ x, b₁ (b₀ x) = 0)
    (hε : ∀ x, εC (g x) = g₀ (εB x))
    (hfree : ∀ x : B₀, b₀ x = 0 → ∃ p : P, εB p = x)
    (hkernel : ∀ x : A₁, a₁ x = 0 → ∃ y : A₀, a₀ y = x) :
    ∀ x : C₀, c₀ x = 0 → ∃ m : M, εC m = x := by
  intro x hx
  obtain ⟨b, hb⟩ := hg₀ x
  have hdb : g₁ (b₀ b) = 0 := by rw [hgg, hb, hx]
  obtain ⟨a, ha⟩ := hker (b₀ b) hdb
  have hclosed : a₁ a = 0 := by
    apply hf₂
    rw [map_zero, ← hff₁, ha, hdiff]
  obtain ⟨v, hv⟩ := hkernel a hclosed
  have hcorrected : b₀ (b - f₀ v) = 0 := by
    rw [map_sub, hff₀, hv, ha, sub_self]
  obtain ⟨p, hp⟩ := hfree (b - f₀ v) hcorrected
  refine ⟨g p, ?_⟩
  rw [hε, hp, map_sub, hzero, sub_zero, hb]

theorem unique_recovery_of_injective
    {M C₀ C₁ : Type*} [AddCommGroup M] [AddCommGroup C₀] [AddCommGroup C₁]
    (ε : M →+ C₀) (d : C₀ →+ C₁) (hinj : Function.Injective ε)
    (hrec : ∀ c, d c = 0 → ∃ m, ε m = c) :
    ∀ c, d c = 0 → ∃! m, ε m = c := by
  intro c hc
  obtain ⟨m, hm⟩ := hrec c hc
  exact ⟨m, hm, fun n hn => hinj (hn.trans hm.symm)⟩

theorem eventual_unique_recovery
    {M C₀ C₁ : ℕ → Type*}
    [∀ n, AddCommGroup (M n)] [∀ n, AddCommGroup (C₀ n)] [∀ n, AddCommGroup (C₁ n)]
    (ε : ∀ n, M n →+ C₀ n) (d : ∀ n, C₀ n →+ C₁ n)
    (hinj : ∃ N, ∀ n, N ≤ n → Function.Injective (ε n))
    (hrec : ∃ N, ∀ n, N ≤ n → ∀ c, d n c = 0 → ∃ m, ε n m = c) :
    ∃ N, ∀ n, N ≤ n → ∀ c, d n c = 0 → ∃! m, ε n m = c := by
  obtain ⟨N₁, h₁⟩ := hinj
  obtain ⟨N₂, h₂⟩ := hrec
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  exact unique_recovery_of_injective (ε n) (d n)
    (h₁ n ((le_max_left _ _).trans hn)) (h₂ n ((le_max_right _ _).trans hn))

end PiExponent.GradedCechRecovery

end OAI
