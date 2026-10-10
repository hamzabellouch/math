import OAI.Combinatorics.ProgressionColoring.Model

namespace OAI

universe uAlpha uBeta

namespace QuantitativeVanDerWaerden

theorem apTerm_lt {a d k N j : ℕ}
    (hbound : a + (k - 1) * d < N) (hj : j < k) : a + j * d < N := by
  have hle : j ≤ k - 1 := by omega
  have := Nat.mul_le_mul_right d hle
  omega

theorem apStart_lt {a d k N : ℕ} (hbound : a + (k - 1) * d < N) : a < N := by
  omega

theorem MonoAP.recolor {α : Type uAlpha} {β : Type uBeta} {c : ℕ → α} {k a d : ℕ}
    (h : MonoAP c k a d) (f : α → β) : MonoAP (f ∘ c) k a d := by
  intro j hj
  exact congrArg f (h j hj)

theorem MonoAP.of_injective_recolor {α : Type uAlpha} {β : Type uBeta} {c : ℕ → α}
    {k a d : ℕ} {f : α → β} (hf : Function.Injective f)
    (h : MonoAP (f ∘ c) k a d) : MonoAP c k a d := by
  intro j hj
  exact hf (h j hj)

theorem HasMonoAP.recolor {α : Type uAlpha} {β : Type uBeta} {c : ℕ → α} {k N : ℕ}
    (h : HasMonoAP c k N) (f : α → β) : HasMonoAP (f ∘ c) k N := by
  obtain ⟨a, d, hd, hb, hm⟩ := h
  exact ⟨a, d, hd, hb, hm.recolor f⟩

theorem HasMonoAP.of_injective_recolor {α : Type uAlpha} {β : Type uBeta} {c : ℕ → α}
    {k N : ℕ} {f : α → β} (hf : Function.Injective f)
    (h : HasMonoAP (f ∘ c) k N) : HasMonoAP c k N := by
  obtain ⟨a, d, hd, hb, hm⟩ := h
  exact ⟨a, d, hd, hb, hm.of_injective_recolor hf⟩

theorem not_hasMonoAP_of_recolor_injective {α : Type uAlpha} {β : Type uBeta} {c : ℕ → α}
    {k N : ℕ} {f : α → β} (hf : Function.Injective f)
    (hc : ¬ HasMonoAP c k N) : ¬ HasMonoAP (f ∘ c) k N :=
  fun h => hc (h.of_injective_recolor hf)

theorem HasMonoAP.mono {α : Type uAlpha} {c : ℕ → α} {k N M : ℕ}
    (h : HasMonoAP c k N) (hNM : N ≤ M) : HasMonoAP c k M := by
  obtain ⟨a, d, hd, hb, hm⟩ := h
  exact ⟨a, d, hd, hb.trans_le hNM, hm⟩

theorem HasMonoAP.mono_length {α : Type uAlpha} {c : ℕ → α} {k l N : ℕ}
    (h : HasMonoAP c k N) (hlk : l ≤ k) : HasMonoAP c l N := by
  obtain ⟨a, d, hd, hb, hm⟩ := h
  have hpred : l - 1 ≤ k - 1 := by omega
  have hmul := Nat.mul_le_mul_right d hpred
  refine ⟨a, d, hd, by omega, ?_⟩
  intro j hj
  exact hm j (hj.trans_le hlk)

theorem HasMonoAP.length_le {α : Type uAlpha} {c : ℕ → α} {k N : ℕ}
    (h : HasMonoAP c k N) (hk : 0 < k) : k ≤ N := by
  obtain ⟨a, d, hd, hb, _⟩ := h
  have hmul : k - 1 ≤ (k - 1) * d := by
    simpa using Nat.mul_le_mul_left (k - 1) (show 1 ≤ d by omega)
  omega

theorem HasMonoAP.congr {α : Type uAlpha} {c c' : ℕ → α} {k N : ℕ}
    (h : HasMonoAP c k N) (heq : ∀ n < N, c n = c' n) :
    HasMonoAP c' k N := by
  obtain ⟨a, d, hd, hb, hm⟩ := h
  refine ⟨a, d, hd, hb, ?_⟩
  intro j hj
  rw [← heq _ (apTerm_lt hb hj), ← heq _ (apStart_lt hb)]
  exact hm j hj

theorem HasMonoAP.translate {α : Type uAlpha} {c : ℕ → α} {k N offset : ℕ}
    (h : HasMonoAP (fun n => c (offset + n)) k N) :
    HasMonoAP c k (offset + N) := by
  obtain ⟨a, d, hd, hb, hm⟩ := h
  refine ⟨offset + a, d, hd, by omega, ?_⟩
  intro j hj
  simpa only [Nat.add_assoc] using hm j hj

theorem IsRamsey.mono {α : Type uAlpha} {k N M : ℕ}
    (h : IsRamsey α k N) (hNM : N ≤ M) : IsRamsey α k M :=
  fun c => (h c).mono hNM

theorem IsRamsey.of_injective {α : Type uAlpha} {β : Type uBeta} {k N : ℕ}
    (h : IsRamsey β k N) {f : α → β} (hf : Function.Injective f) :
    IsRamsey α k N := by
  intro c
  exact (h (f ∘ c)).of_injective_recolor hf

theorem isRamsey_one (α : Type uAlpha) : IsRamsey α 1 1 := by
  intro c
  refine ⟨0, 1, by omega, by norm_num, ?_⟩
  intro j hj
  have : j = 0 := by omega
  simp [this]

theorem isRamsey_subsingleton (α : Type uAlpha) [Subsingleton α] {k : ℕ}
    (hk : 0 < k) : IsRamsey α k k := by
  intro c
  refine ⟨0, 1, by omega, by omega, ?_⟩
  exact fun _ _ => Subsingleton.elim _ _

/-- A literal finite-coloring formulation of the same progression. -/
def FiniteHasMonoAP {α : Type uAlpha} {N : ℕ} (c : Fin N → α) (k : ℕ) : Prop :=
  ∃ a d, 0 < d ∧ ∃ hbound : a + (k - 1) * d < N,
    ∀ j : Fin k,
      c ⟨a + j.val * d, apTerm_lt hbound j.isLt⟩ =
        c ⟨a, apStart_lt hbound⟩

def restrictColor {α : Type uAlpha} (c : ℕ → α) (N : ℕ) : Fin N → α :=
  fun n => c n.val

theorem hasMonoAP_iff_finite_restriction {α : Type uAlpha} (c : ℕ → α) (k N : ℕ) :
    HasMonoAP c k N ↔ FiniteHasMonoAP (restrictColor c N) k := by
  constructor
  · rintro ⟨a, d, hd, hb, hm⟩
    exact ⟨a, d, hd, hb, fun j => hm j.val j.isLt⟩
  · rintro ⟨a, d, hd, hb, hm⟩
    exact ⟨a, d, hd, hb, fun j hj => hm ⟨j, hj⟩⟩

/-- Only the finitely many colors on `[0,N)` matter. The nonempty color type
allows every finite coloring to be extended beyond that interval. -/
theorem isRamsey_iff_finite (α : Type uAlpha) [Nonempty α] (k N : ℕ) :
    IsRamsey α k N ↔ ∀ c : Fin N → α, FiniteHasMonoAP c k := by
  classical
  constructor
  · intro h c
    let extended : ℕ → α := fun n =>
      if hn : n < N then c ⟨n, hn⟩ else Classical.choice ‹Nonempty α›
    have hc := (hasMonoAP_iff_finite_restriction extended k N).mp (h extended)
    have heq : restrictColor extended N = c := by
      funext n
      simp [restrictColor, extended, n.isLt]
    rwa [heq] at hc
  · intro h c
    exact (hasMonoAP_iff_finite_restriction c k N).mpr (h (restrictColor c N))

theorem W_le_of_isRamsey {r k N : ℕ} (hN : 0 < N)
    (h : IsRamsey (Fin r) k N) : W r k ≤ N :=
  Nat.sInf_le ⟨hN, h⟩

theorem W_spec_of_finite {r k : ℕ}
    (hfinite : ∃ N, 0 < N ∧ IsRamsey (Fin r) k N) :
    0 < W r k ∧ IsRamsey (Fin r) k (W r k) :=
  Nat.sInf_mem hfinite

/-- An avoiding coloring gives a strict lower bound once finiteness has been
proved. Monotonicity is used: failure at one size alone is not minimality. -/
theorem lt_W_of_avoiding {r k N : ℕ}
    (hfinite : ∃ M, 0 < M ∧ IsRamsey (Fin r) k M)
    (c : ℕ → Fin r) (hc : ¬ HasMonoAP c k N) : N < W r k := by
  have hw := W_spec_of_finite hfinite
  by_contra hn
  exact hc ((hw.2.mono (by omega)) c)

theorem lt_W_of_not_isRamsey {r k N : ℕ}
    (hfinite : ∃ M, 0 < M ∧ IsRamsey (Fin r) k M)
    (hN : ¬ IsRamsey (Fin r) k N) : N < W r k := by
  have hw := W_spec_of_finite hfinite
  by_contra hn
  exact hN (hw.2.mono (by omega))

theorem W_one (r : ℕ) : W r 1 = 1 := by
  have hw := W_spec_of_finite (r := r) ⟨1, by omega, isRamsey_one (Fin r)⟩
  have hu := W_le_of_isRamsey (r := r) (by omega : 0 < 1) (isRamsey_one (Fin r))
  omega

theorem W_one_color {k : ℕ} (hk : 0 < k) : W 1 k = k := by
  have hramsey := isRamsey_subsingleton (Fin 1) hk
  have hw := W_spec_of_finite (r := 1) ⟨k, hk, hramsey⟩
  have hu := W_le_of_isRamsey hk hramsey
  have hl := (hw.2 (fun _ => (0 : Fin 1))).length_le hk
  omega

end QuantitativeVanDerWaerden

end OAI
