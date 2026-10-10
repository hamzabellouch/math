import OAI.Analysis.MarkovType.OrderedSequences
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace MarkovSuperreflexivity.SeminormLimit

def value (p : ℕ → Seminorm ℝ C00) (x : C00) : ℝ := ⨅ n, p n x

theorem boundedBelow (p : ℕ → Seminorm ℝ C00) (x : C00) :
    BddBelow (Set.range fun n => p n x) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact apply_nonneg (p n) x

theorem tendsto_value (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) (x : C00) :
    Tendsto (fun n => p n x) atTop (𝓝 (value p x)) :=
  tendsto_atTop_ciInf (ha x) (boundedBelow p x)

def seminorm (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) : Seminorm ℝ C00 :=
  Seminorm.of (value p)
    (fun x y => le_of_tendsto_of_tendsto'
      (tendsto_value p ha (x + y))
      ((tendsto_value p ha x).add (tendsto_value p ha y))
      (fun n => (p n).add_le' x y))
    (fun r x => tendsto_nhds_unique
      (tendsto_value p ha (r • x))
      (by
        simpa only [map_smul_eq_mul] using
          (tendsto_const_nhds.mul (tendsto_value p ha x) :
            Tendsto (fun n => ‖r‖ * p n x) atTop (𝓝 (‖r‖ * value p x)))))

@[simp] theorem seminorm_apply (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) (x : C00) :
    seminorm p ha x = value p x := rfl

theorem seminorm_le (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) (x : C00) (n : ℕ) :
    seminorm p ha x ≤ p n x :=
  ciInf_le (boundedBelow p x) n

theorem lower_bound (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) (x : C00) {b : ℝ}
    (h : ∀ n, b ≤ p n x) : b ≤ seminorm p ha x :=
  ge_of_tendsto' (tendsto_value p ha x) h

theorem upper_bound (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) (x : C00) {b : ℝ}
    (h : ∀ n, p n x ≤ b) : seminorm p ha x ≤ b :=
  le_of_tendsto' (tendsto_value p ha x) h

theorem spreading (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x)
    (hs : ∀ n, ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
      ∀ a, p n (C00.place ι a) = p n (C00.ofArray a))
    {m : ℕ} (ι : Fin m → ℕ) (hι : StrictMono ι) (a : Fin m → ℝ) :
    seminorm p ha (C00.place ι a) = seminorm p ha (C00.ofArray a) := by
  change (⨅ n, p n (C00.place ι a)) = ⨅ n, p n (C00.ofArray a)
  congr 1
  funext n
  exact hs n ι hι a

theorem prefix_lower (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) (d : ℝ)
    (hl : ∀ n x k, d * |prefixCut x k| ≤ p n x) (x : C00) (k : ℕ) :
    d * |prefixCut x k| ≤ seminorm p ha x :=
  lower_bound p ha x (fun n => hl n x k)

theorem definite (p : ℕ → Seminorm ℝ C00)
    (ha : ∀ x, Antitone fun n => p n x) {d : ℝ} (hd : 0 < d)
    (hl : ∀ n x k, d * |prefixCut x k| ≤ p n x)
    (x : C00) (hx : seminorm p ha x = 0) : x = 0 := by
  have hp (k : ℕ) : prefixCut x k = 0 := by
    have h := prefix_lower p ha d hl x k
    rw [hx] at h
    have hz : |prefixCut x k| ≤ 0 := by nlinarith
    exact abs_nonpos_iff.mp hz
  ext i
  have h := prefixCut_succ x i
  rw [hp (i + 1), hp i] at h
  simpa only [zero_add, Finsupp.zero_apply] using h.symm

end MarkovSuperreflexivity.SeminormLimit

end

end OAI
