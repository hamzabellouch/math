import OAI.NumberTheory.DirichletL.Descent.Fibers
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators
noncomputable section

theorem bounded_finset_coefficient_sum_sq {C : Type*} (s : Finset C)
    (b f : C → ℂ) (hb : ∀ c ∈ s, ‖b c‖ ≤ 1) :
    ‖∑ c ∈ s, b c * f c‖ ^ 2 ≤ (s.card : ℝ) * ∑ c ∈ s, ‖f c‖ ^ 2 := by
  classical
  have h := finite_expansion_energy ({()} : Finset Unit) s
    (fun _ => s) (fun _ => b) (fun _ => f) (s.card : ℝ)
    (by simp) (by simpa using hb) (by simp)
  simpa using h

theorem bounded_coefficient_sum_sq {C : Type*} [Fintype C]
    (b f : C → ℂ) (hb : ∀ c, ‖b c‖ ≤ 1) :
    ‖∑ c, b c * f c‖ ^ 2 ≤ (Fintype.card C : ℝ) * ∑ c, ‖f c‖ ^ 2 := by
  classical
  simpa using bounded_finset_coefficient_sum_sq Finset.univ b f (by simpa using hb)

theorem positive_triple_enlarge {M H C : Type*}
    [DecidableEq M] [DecidableEq H] [DecidableEq C]
    (pairs : Finset (M × H)) (cset : M → Finset C)
    (hs : Finset H) (mc : Finset (M × C)) (E : H → M → C → ℝ)
    (hh : ∀ p ∈ pairs, p.2 ∈ hs)
    (hm : ∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ mc)
    (hE : ∀ h m c, 0 ≤ E h m c) :
    (∑ p ∈ pairs, ∑ c ∈ cset p.1, E p.2 p.1 c) ≤
      ∑ h ∈ hs, ∑ u ∈ mc, E h u.1 u.2 := by
  let f : (Σ _p : M × H, C) → H × (M × C) := fun p => (p.1.2, (p.1.1, p.2))
  have hf : Function.Injective f := by
    have hi : Function.LeftInverse
        (fun u : H × (M × C) => (⟨(u.2.1, u.1), u.2.2⟩ : Σ _p : M × H, C)) f := by
      rintro ⟨⟨m, h⟩, c⟩
      rfl
    exact hi.injective
  have hmapped : ((pairs.sigma (fun p => cset p.1)).image f) ⊆ hs ×ˢ mc := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    have hp' := Finset.mem_sigma.mp hp
    exact Finset.mem_product.mpr ⟨hh p.1 hp'.1, hm p.1 hp'.1 p.2 hp'.2⟩
  have hb := Finset.sum_le_sum_of_injOn f hf.injOn hmapped
    (f := fun p : Σ _p : M × H, C => E p.1.2 p.1.1 p.2)
    (g := fun u : H × (M × C) => E u.1 u.2.1 u.2.2)
    (by intros; exact le_rfl) (by intro u _ _; exact hE _ _ _)
  simpa only [Finset.sum_sigma, Finset.sum_product] using hb

theorem column_fiber_sieve {K X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (rows : Finset K) (source : Finset X) (target : Finset Y)
    (φ : X → Y) (q : K → Y → ℂ) (a : X → ℂ) (Q D : ℝ) (hQ : 0 ≤ Q)
    (hφ : ∀ x ∈ source, φ x ∈ target)
    (hfiber : ∀ y ∈ target, ((source.filter (fun x => φ x = y)).card : ℝ) ≤ D)
    (hsieve : ∀ f : Y → ℂ,
      (∑ k ∈ rows, ‖∑ y ∈ target, q k y * f y‖ ^ 2) ≤
        Q * ∑ y ∈ target, ‖f y‖ ^ 2) :
    (∑ k ∈ rows, ‖∑ x ∈ source, q k (φ x) * a x‖ ^ 2) ≤
      Q * D * ∑ x ∈ source, ‖a x‖ ^ 2 := by
  let f : Y → ℂ := fun y => ∑ x ∈ source with φ x = y, a x
  have he (k : K) : (∑ x ∈ source, q k (φ x) * a x) =
      ∑ y ∈ target, q k y * f y := by
    rw [← Finset.sum_fiberwise_of_maps_to hφ]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp only [f]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  have hf := finite_expansion_energy target source
    (fun y => source.filter (fun x => φ x = y)) (fun _ _ => 1) (fun _ => a) D
    (fun _ _ => Finset.filter_subset _ _) (by simp) hfiber
  have hf' : (∑ y ∈ target, ‖f y‖ ^ 2) ≤ D * ∑ x ∈ source, ‖a x‖ ^ 2 := by
    have hrhs : (∑ x ∈ source, ∑ y ∈ target,
        if x ∈ source.filter (fun x => φ x = y) then ‖a x‖ ^ 2 else 0) =
        ∑ x ∈ source, ‖a x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [hx, hφ x hx]
    rw [hrhs] at hf
    simpa only [one_mul, f] using hf
  simp_rw [he]
  exact (hsieve f).trans (by
    calc
      _ ≤ Q * (D * ∑ x ∈ source, ‖a x‖ ^ 2) := mul_le_mul_of_nonneg_left hf' hQ
      _ = _ := by ring)

theorem quadratic_cubic_composition
    {K M H C P : Type*} [Fintype K] [Fintype M] [Fintype H] [Fintype C] [Fintype P]
    (q : K → M → H → ℂ) (χ : M → C → P → ℂ)
    (a : H → P → ℂ) (beta : C → M → H → ℂ) (Q S : ℝ) (hQ : 0 ≤ Q)
    (hbeta : ∀ c m h, ‖beta c m h‖ ≤ 1)
    (hquadratic : ∀ f : M → H → ℂ,
      (∑ k, ‖∑ m, ∑ h, q k m h * f m h‖ ^ 2) ≤ Q * ∑ m, ∑ h, ‖f m h‖ ^ 2)
    (hcubic : ∀ u : P → ℂ,
      (∑ m, ∑ c, ‖∑ p, u p * χ m c p‖ ^ 2) ≤ S * ∑ p, ‖u p‖ ^ 2) :
    (∑ k, ‖∑ m, ∑ h, q k m h *
      (∑ c, beta c m h * (∑ p, a h p * χ m c p))‖ ^ 2) ≤
      Q * (Fintype.card C : ℝ) * S * ∑ h, ∑ p, ‖a h p‖ ^ 2 := by
  classical
  apply (hquadratic (fun m h => ∑ c, beta c m h * (∑ p, a h p * χ m c p))).trans
  have hcauchy :
      (∑ m, ∑ h, ‖∑ c, beta c m h * (∑ p, a h p * χ m c p)‖ ^ 2) ≤
      (Fintype.card C : ℝ) * ∑ h, ∑ m, ∑ c, ‖∑ p, a h p * χ m c p‖ ^ 2 := by
    calc
      _ ≤ ∑ m, ∑ h, (Fintype.card C : ℝ) *
          ∑ c, ‖∑ p, a h p * χ m c p‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro m _
        apply Finset.sum_le_sum
        intro h _
        exact bounded_coefficient_sum_sq _ _ (fun c => hbeta c m h)
      _ = _ := by
        simp only [← Finset.mul_sum]
        congr 1
        exact Finset.sum_comm
  have hcs : (∑ h, ∑ m, ∑ c, ‖∑ p, a h p * χ m c p‖ ^ 2) ≤
      S * ∑ h, ∑ p, ‖a h p‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun h _ => hcubic (a h)
  calc
    _ ≤ Q * ((Fintype.card C : ℝ) *
        ∑ h, ∑ m, ∑ c, ‖∑ p, a h p * χ m c p‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcauchy hQ
    _ ≤ Q * ((Fintype.card C : ℝ) * (S * ∑ h, ∑ p, ‖a h p‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcs (Nat.cast_nonneg _)) hQ
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI
