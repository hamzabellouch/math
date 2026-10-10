import Mathlib
import OAI.Analysis.Commutator.FinitePairings3
import OAI.Analysis.Commutator.HilbertTensors3
import OAI.Analysis.Commutator.HilbertTensors5

namespace OAI

noncomputable section

noncomputable section

open scoped TensorProduct

namespace Kadison

attribute [instance] PreHilbert.normed PreHilbert.ipSpace

namespace PreHilbert

end PreHilbert

end Kadison

namespace Kadison.PreHilbert

end Kadison.PreHilbert

namespace Kadison

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

end Kadison

namespace Kadison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end Kadison

namespace Kadison

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

end Kadison

noncomputable section

namespace Kadison

namespace Pairing

variable {J : Type*}

variable [LinearOrder J]

variable [Fintype J]

end Pairing

end Kadison

namespace Kadison

open PreHilbert

theorem pairing_coefficient_zero_source (E : PreHilbert) (k l : ℕ)
    (T : hilbertPower E k →L[ℂ] hilbertPower E l)
    (Jmap : E → E) (B : E → E → ℂ) (c : Pairing (TailSlots k l) → ℂ)
    (h : TailSlots k l × ℕ → E) (horth : Orthonormal ℂ h)
    (hself : ∀ a, Jmap (h a) = h a)
    (hB : ∀ a b, B (h a) (h b) = if a = b then 1 else 0)
    (hexp : ∀ v : TailSlots k l → E,
      inner ℂ (hilbertPure E l (fun j => Jmap (v (.inr j))))
        (T (hilbertPure E k (fun i => v (.inl i)))) =
        ∑ σ, c σ * Pairing.contraction σ B v)
    (τ : Pairing (TailSlots k l)) (a b : Fin k) (hab : τ (.inl a) = .inl b) :
    c τ = 0 := by
  classical
  let labels := fun n => Pairing.labels τ (.inl a) n
  let source := fun n (i : Fin k) => labels n (.inl i)
  let test := fun (j : Fin l) => labels 0 (.inr j)
  have htest (n : ℕ) (j : Fin l) : labels n (.inr j) = test j := by
    have hne : Pairing.repr τ (.inr j) ≠ Pairing.repr τ (.inl a) := by
      intro hh
      rcases (Pairing.repr_eq_iff τ (.inl a) (.inr j)).mp hh.symm with hh | hh
      · cases hh
      · rw [hab] at hh
        cases hh
    simp only [labels, test, Pairing.labels, ite_eq_right hne]
  have hinj : Function.Injective source := by
    intro n m he
    have hh := congrArg Prod.snd (congrFun he a)
    simpa only [source, labels, Pairing.labels, ite_true] using hh
  have hsource : Orthonormal ℂ
      (fun n => hilbertPure E k (fun i => h (source n i))) :=
    (hilbertPure_orthonormal E h horth k).comp source hinj
  apply constant_operator_right_coefficient_zero T _ hsource
    (hilbertPure E l (fun j => h (test j))) (c τ)
  intro n
  have hh := hexp (fun j => h (labels n j))
  have hsum : (∑ σ, c σ * Pairing.contraction σ B (fun j => h (labels n j))) = c τ := by
    simp only [labels, Pairing.contraction_isolation τ _ (.inl a) n h B hB,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hsum] at hh
  simpa only [source, hself, htest] using hh

end Kadison

namespace Kadison

open PreHilbert

theorem pairing_coefficient_zero_test (E : PreHilbert) (k l : ℕ)
    (T : hilbertPower E k →L[ℂ] hilbertPower E l)
    (Jmap : E → E) (B : E → E → ℂ) (c : Pairing (TailSlots k l) → ℂ)
    (h : TailSlots k l × ℕ → E) (horth : Orthonormal ℂ h)
    (hself : ∀ a, Jmap (h a) = h a)
    (hB : ∀ a b, B (h a) (h b) = if a = b then 1 else 0)
    (hexp : ∀ v : TailSlots k l → E,
      inner ℂ (hilbertPure E l (fun j => Jmap (v (.inr j))))
        (T (hilbertPure E k (fun i => v (.inl i)))) =
        ∑ σ, c σ * Pairing.contraction σ B v)
    (τ : Pairing (TailSlots k l)) (a b : Fin l) (hab : τ (.inr a) = .inr b) :
    c τ = 0 := by
  classical
  let labels := fun n => Pairing.labels τ (.inr a) n
  let source := fun (i : Fin k) => labels 0 (.inl i)
  let test := fun n (j : Fin l) => labels n (.inr j)
  have hsource (n : ℕ) (i : Fin k) : labels n (.inl i) = source i := by
    have hne : Pairing.repr τ (.inl i) ≠ Pairing.repr τ (.inr a) := by
      intro hh
      rcases (Pairing.repr_eq_iff τ (.inr a) (.inl i)).mp hh.symm with hh | hh
      · cases hh
      · rw [hab] at hh
        cases hh
    simp only [labels, source, Pairing.labels, ite_eq_right hne]
  have hinj : Function.Injective test := by
    intro n m he
    have hh := congrArg Prod.snd (congrFun he a)
    simpa only [test, labels, Pairing.labels, ite_true] using hh
  have htest : Orthonormal ℂ
      (fun n => hilbertPure E l (fun j => h (test n j))) :=
    (hilbertPure_orthonormal E h horth l).comp test hinj
  apply constant_orthonormal_coefficient_zero _ htest
    (T (hilbertPure E k (fun i => h (source i)))) (c τ)
  intro n
  have hh := hexp (fun j => h (labels n j))
  have hsum : (∑ σ, c σ * Pairing.contraction σ B (fun j => h (labels n j))) = c τ := by
    simp only [labels, Pairing.contraction_isolation τ _ (.inr a) n h B hB,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hsum] at hh
  simpa only [test, hself, hsource] using hh

theorem pairing_crossing_card_eq (k l : ℕ) (τ : Pairing (TailSlots k l))
    (hs : ∀ a : Fin k, ∃ b : Fin l, τ (.inl a) = .inr b)
    (ht : ∀ b : Fin l, ∃ a : Fin k, τ (.inr b) = .inl a) : k = l := by
  classical
  let f : Fin k → Fin l := fun a => (hs a).choose
  have hf (a : Fin k) : τ (.inl a) = .inr (f a) := (hs a).choose_spec
  have hinj : Function.Injective f := by
    intro a b hab
    apply Sum.inl_injective
    apply τ.injective
    rw [hf, hf, hab]
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a, ha⟩ := ht b
    refine ⟨a, ?_⟩
    have hh := τ.apply_apply (.inr b)
    rw [ha, hf] at hh
    exact Sum.inr_injective hh
  have hh := Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  simpa only [Fintype.card_fin] using hh

theorem pairing_coefficients_zero_of_ne (E : PreHilbert) (k l : ℕ)
    (T : hilbertPower E k →L[ℂ] hilbertPower E l)
    (Jmap : E → E) (B : E → E → ℂ) (c : Pairing (TailSlots k l) → ℂ)
    (h : TailSlots k l × ℕ → E) (horth : Orthonormal ℂ h)
    (hself : ∀ a, Jmap (h a) = h a)
    (hB : ∀ a b, B (h a) (h b) = if a = b then 1 else 0)
    (hexp : ∀ v : TailSlots k l → E,
      inner ℂ (hilbertPure E l (fun j => Jmap (v (.inr j))))
        (T (hilbertPure E k (fun i => v (.inl i)))) =
        ∑ σ, c σ * Pairing.contraction σ B v)
    (hkl : k ≠ l) : ∀ τ, c τ = 0 := by
  intro τ
  by_contra hc
  apply hkl
  apply pairing_crossing_card_eq k l τ
  · intro a
    cases he : τ (.inl a) with
    | inl b => exact (hc (pairing_coefficient_zero_source E k l T Jmap B c h horth hself hB hexp τ a b he)).elim
    | inr b => exact ⟨b, rfl⟩
  · intro a
    cases he : τ (.inr a) with
    | inl b => exact ⟨b, rfl⟩
    | inr b => exact (hc (pairing_coefficient_zero_test E k l T Jmap B c h horth hself hB hexp τ a b he)).elim

end Kadison
end
end
end

end OAI
