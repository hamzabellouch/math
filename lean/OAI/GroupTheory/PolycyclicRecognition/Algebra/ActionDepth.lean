import OAI.GroupTheory.PolycyclicRecognition.Algebra.LinearActionFiltration
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! # Commutators advance an operator filtration

If every action difference raises a descending filtration by one step, its
commutators raise it further. This controls the lower central series using
the length at which the action filtration vanishes.
-/

namespace PolycyclicRecognition

open scoped commutatorElement

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

def ActionDepth (D : I → Module.End K V) (k : ℕ) (f : Module.End K V) : Prop :=
  ∀ n v, v ∈ linearActionFiltration D n → f v ∈ linearActionFiltration D (n + k)

namespace ActionDepth

variable {D : I → Module.End K V} {k l : ℕ} {f g : Module.End K V}

theorem zero (k : ℕ) : ActionDepth D k 0 := fun _ _ _ => Submodule.zero_mem _

theorem mono (hf : ActionDepth D k f) (hl : l ≤ k) : ActionDepth D l f := by
  intro n v hv
  exact linearActionFiltration_antitone D (Nat.add_le_add_left hl n) (hf n v hv)

theorem add (hf : ActionDepth D k f) (hg : ActionDepth D k g) :
    ActionDepth D k (f + g) := fun n v hv =>
  Submodule.add_mem _ (hf n v hv) (hg n v hv)

theorem neg (hf : ActionDepth D k f) : ActionDepth D k (-f) := fun n v hv =>
  Submodule.neg_mem _ (hf n v hv)

theorem sub (hf : ActionDepth D k f) (hg : ActionDepth D k g) :
    ActionDepth D k (f - g) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : ActionDepth D k f) (hg : ActionDepth D l g) :
    ActionDepth D (k + l) (f * g) := by
  intro n v hv
  simpa only [Module.End.mul_apply, Nat.add_assoc, Nat.add_comm l k] using hf (n + l) (g v) (hg n v hv)

theorem one : ActionDepth D 0 1 := by
  intro n v hv
  simpa using hv

theorem generator (i : I) : ActionDepth D 1 (D i) := by
  intro n v hv
  exact (le_iSup (fun j => (linearActionFiltration D n).map (D j)) i) ⟨v, hv, rfl⟩

theorem eq_zero {c : ℕ} (hf : ActionDepth D c f)
    (hc : linearActionFiltration D c = ⊥) : f = 0 := by
  apply LinearMap.ext
  intro v
  have hv := hf 0 v (Submodule.mem_top)
  simpa only [Nat.zero_add, hc, Submodule.mem_bot, LinearMap.zero_apply] using hv

end ActionDepth

variable {G : Type*} [Group G]

theorem lowerCentralSeries_le_ker_of_actionFiltration
    (ρ : G →* Module.End K V) (c : ℕ)
    (hc : linearActionFiltration (fun g => ρ g - 1) c = ⊥) :
    (⊤ : Subgroup G).lowerCentralSeries c ≤ ρ.ker := by
  let D := fun g => ρ g - 1
  have h1 (g : G) : ActionDepth D 1 (ρ g - 1) := ActionDepth.generator g
  have h0 (g : G) : ActionDepth D 0 (ρ g) := by
    have hh := ((h1 g).mono (Nat.zero_le 1)).add ActionDepth.one
    simpa only [sub_add_cancel] using hh
  have hmul (g h : G) :
      ρ (g * h) - 1 = (ρ g - 1) + (ρ h - 1) + (ρ g - 1) * (ρ h - 1) := by
    rw [ρ.map_mul]
    noncomm_ring
  have hinv (g : G) : ρ g⁻¹ - 1 = -(ρ g⁻¹ * (ρ g - 1)) := by
    have he : ρ g⁻¹ * ρ g = 1 := by rw [← ρ.map_mul, inv_mul_cancel, ρ.map_one]
    rw [mul_sub, he]
    noncomm_ring
  let S (k : ℕ) : Subgroup G :=
    { carrier := {g | ActionDepth D k (ρ g - 1)}
      one_mem' := by
        change ActionDepth D k (ρ 1 - 1)
        rw [ρ.map_one, sub_self]
        exact ActionDepth.zero k
      mul_mem' := by
        intro g h hg hh
        change ActionDepth D k (ρ (g * h) - 1)
        rw [hmul]
        exact (hg.add hh).add ((hg.mul hh).mono (by omega))
      inv_mem' := by
        intro g hg
        change ActionDepth D k (ρ g⁻¹ - 1)
        rw [hinv]
        simpa only [Nat.zero_add] using ((h0 g⁻¹).mul hg).neg }
  have hcomm (k : ℕ) (x y : G) (hx : x ∈ S k) : ⁅x, y⁆ ∈ S (k + 1) := by
    have hxy : ActionDepth D (k + 1)
        ((ρ x - 1) * (ρ y - 1) - (ρ y - 1) * (ρ x - 1)) :=
      (hx.mul (h1 y)).sub (by simpa only [Nat.add_comm] using (h1 y).mul hx)
    have hxi : ρ x * ρ x⁻¹ = 1 := by rw [← ρ.map_mul, mul_inv_cancel, ρ.map_one]
    have hyi : ρ y * ρ y⁻¹ = 1 := by rw [← ρ.map_mul, mul_inv_cancel, ρ.map_one]
    have he : ρ ⁅x, y⁆ - 1 =
        ((ρ x - 1) * (ρ y - 1) - (ρ y - 1) * (ρ x - 1)) * ρ x⁻¹ * ρ y⁻¹ := by
      simp only [commutatorElement_def, ρ.map_mul]
      calc
        _ = ρ x * ρ y * ρ x⁻¹ * ρ y⁻¹ - (ρ y * (ρ x * ρ x⁻¹)) * ρ y⁻¹ := by
          rw [hxi, mul_one, hyi]
        _ = _ := by noncomm_ring
    change ActionDepth D (k + 1) (ρ ⁅x, y⁆ - 1)
    rw [he]
    simpa only [Nat.add_zero] using (hxy.mul (h0 x⁻¹)).mul (h0 y⁻¹)
  have hs (k : ℕ) : (⊤ : Subgroup G).lowerCentralSeries k ≤ S (k + 1) := by
    induction k with
    | zero => exact fun g _ => h1 g
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_le.mpr (fun x hx y _ => hcomm (k + 1) x y (ih hx))
  intro g hg
  change ρ g = 1
  exact sub_eq_zero.mp (((hs c hg).mono (Nat.le_succ c)).eq_zero hc)

end PolycyclicRecognition

end OAI
