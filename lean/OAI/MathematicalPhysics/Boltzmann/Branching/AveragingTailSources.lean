import OAI.MathematicalPhysics.Boltzmann.Branching.PublishedInputs
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability

namespace OAI

section

/-! # A single GLPS subsequence for a countable family of velocity tests

The resolvent compactness hypothesis yields a common diagonal subsequence
for the countable family.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

theorem LocalL1Converges.comp {f : ℕ → SpaceTime → ℝ} {g : SpaceTime → ℝ}
    (h : LocalL1Converges f g) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    LocalL1Converges (fun n => f (φ n)) g := by
  refine ⟨h.1,fun K hK => ?_⟩
  exact (h.2 K hK).comp hφ

theorem GLPS1988Proposition3.countable_tests (hGLPS : GLPS1988Proposition3)
    (r : ℕ → KineticPhase → ℝ) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ n, ∀ᵐ z ∂(volume : Measure KineticPhase), R < ‖z.2‖ → r n z = 0)
    (hUI : UniformIntegrable r 1 volume)
    (ψ : ℕ → Velocity → ℝ)
    (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j)) (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, LocalL1Converges (fun n => resolventAverage (r (φ n)) (ψ j)) (g j) := by
  have hsub (a : ℕ → ℕ) : UniformIntegrable (fun n => r (a n)) 1 volume := by
    obtain ⟨hu,C,hC⟩ := hUI
    exact ⟨hu.comp a,C,fun n => hC (a n)⟩
  have hex (j : ℕ) (a : ℕ → ℕ) := hGLPS (fun n => r (a n)) R hR
    (fun n => hsupp (a n)) (hsub a) (ψ j) (hψ j) (hψc j)
  choose σ g hσ hg using hex
  let a : ℕ → ℕ → ℕ := fun n => Nat.rec id (fun j aj => aj ∘ σ j aj) n
  have has (j : ℕ) : a (j+1) = a j ∘ σ j (a j) := rfl
  have ha (j : ℕ) : StrictMono (a j) := by
    induction j with
    | zero => exact strictMono_id
    | succ j hj => rw [has]; exact hj.comp (hσ j (a j))
  have hnest (i j : ℕ) (hij : i ≤ j) :
      ∀ k, ∃ m, k ≤ m ∧ a i m = a j k := by
    induction j with
    | zero =>
      have hi : i = 0 := by omega
      subst i
      exact fun k => ⟨k,le_rfl,rfl⟩
    | succ j ih =>
      by_cases hi : i ≤ j
      · intro k
        obtain ⟨m,hm,he⟩ := ih hi (σ j (a j) k)
        exact ⟨m,((hσ j (a j)).id_le k).trans hm,he⟩
      · have he : i = j+1 := by omega
        subst i
        exact fun k => ⟨k,le_rfl,rfl⟩
  let φ : ℕ → ℕ := fun n => a (n+1) n
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    change a (n+1) n < a (n+2) (n+1)
    rw [has (n+1)]
    exact (ha (n+1)) ((Nat.lt_succ_self n).trans_le ((hσ (n+1) (a (n+1))).id_le (n+1)))
  refine ⟨φ,fun j => g j (a j),hφ,?_⟩
  intro j
  have hj : LocalL1Converges (fun n => resolventAverage (r (a (j+1) n)) (ψ j)) (g j (a j)) :=
    hg j (a j)
  let ρ : ℕ → ℕ := fun n => if hn : j+1 ≤ n+1 then (hnest (j+1) (n+1) hn n).choose else n
  have hρ (n : ℕ) : n ≤ ρ n := by
    dsimp only [ρ]
    split_ifs with hn
    · exact (hnest (j+1) (n+1) hn n).choose_spec.1
    · exact le_rfl
  have hρtop : Tendsto ρ atTop atTop := tendsto_atTop_mono hρ tendsto_id
  have he : ∀ᶠ n in atTop, a (j+1) (ρ n) = φ n := by
    filter_upwards [eventually_ge_atTop j] with n hn
    have hn' : j+1 ≤ n+1 := by omega
    exact (by
      dsimp only [ρ]
      rw [dite_eq_left hn']
      exact (hnest (j+1) (n+1) hn' n).choose_spec.2)
  refine ⟨hj.1,fun K hK => ?_⟩
  apply ((hj.2 K hK).comp hρtop).congr'
  filter_upwards [he] with n hn
  simp only [Function.comp_apply]
  rw [hn]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A GLPS diagonal for countably many localized sources and velocity tests

The resolvent compactness hypothesis yields a common diagonal subsequence
for the countable family.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

theorem GLPS1988Proposition3.countable_sources_tests (hGLPS : GLPS1988Proposition3)
    (r : ℕ → ℕ → KineticPhase → ℝ) (R : ℕ → ℝ) (hR : ∀ j, 0 < R j)
    (hsupp : ∀ j n, ∀ᵐ z ∂(volume : Measure KineticPhase), R j < ‖z.2‖ → r j n z = 0)
    (hUI : ∀ j, UniformIntegrable (r j) 1 volume)
    (ψ : ℕ → Velocity → ℝ)
    (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j)) (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, LocalL1Converges (fun n => resolventAverage (r j (φ n)) (ψ j)) (g j) := by
  have hsub (j : ℕ) (a : ℕ → ℕ) : UniformIntegrable (fun n => r j (a n)) 1 volume := by
    obtain ⟨hu,C,hC⟩ := hUI j
    exact ⟨hu.comp a,C,fun n => hC (a n)⟩
  have hex (j : ℕ) (a : ℕ → ℕ) := hGLPS (fun n => r j (a n)) (R j) (hR j)
    (fun n => hsupp j (a n)) (hsub j a) (ψ j) (hψ j) (hψc j)
  choose σ g hσ hg using hex
  let a : ℕ → ℕ → ℕ := fun n => Nat.rec id (fun j aj => aj ∘ σ j aj) n
  have has (j : ℕ) : a (j+1) = a j ∘ σ j (a j) := rfl
  have ha (j : ℕ) : StrictMono (a j) := by
    induction j with
    | zero => exact strictMono_id
    | succ j hj => rw [has]; exact hj.comp (hσ j (a j))
  have hnest (i j : ℕ) (hij : i ≤ j) :
      ∀ k, ∃ m, k ≤ m ∧ a i m = a j k := by
    induction j with
    | zero =>
      have hi : i = 0 := by omega
      subst i
      exact fun k => ⟨k,le_rfl,rfl⟩
    | succ j ih =>
      by_cases hi : i ≤ j
      · intro k
        obtain ⟨m,hm,he⟩ := ih hi (σ j (a j) k)
        exact ⟨m,((hσ j (a j)).id_le k).trans hm,he⟩
      · have he : i = j+1 := by omega
        subst i
        exact fun k => ⟨k,le_rfl,rfl⟩
  let φ : ℕ → ℕ := fun n => a (n+1) n
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    change a (n+1) n < a (n+2) (n+1)
    rw [has (n+1)]
    exact (ha (n+1)) ((Nat.lt_succ_self n).trans_le ((hσ (n+1) (a (n+1))).id_le (n+1)))
  refine ⟨φ,fun j => g j (a j),hφ,?_⟩
  intro j
  have hj : LocalL1Converges (fun n => resolventAverage (r j (a (j+1) n)) (ψ j)) (g j (a j)) :=
    hg j (a j)
  let ρ : ℕ → ℕ := fun n => if hn : j+1 ≤ n+1 then (hnest (j+1) (n+1) hn n).choose else n
  have hρ (n : ℕ) : n ≤ ρ n := by
    dsimp only [ρ]
    split_ifs with hn
    · exact (hnest (j+1) (n+1) hn n).choose_spec.1
    · exact le_rfl
  have hρtop : Tendsto ρ atTop atTop := tendsto_atTop_mono hρ tendsto_id
  have he : ∀ᶠ n in atTop, a (j+1) (ρ n) = φ n := by
    filter_upwards [eventually_ge_atTop j] with n hn
    have hn' : j+1 ≤ n+1 := by omega
    exact (by
      dsimp only [ρ]
      rw [dite_eq_left hn']
      exact (hnest (j+1) (n+1) hn' n).choose_spec.2)
  refine ⟨hj.1,fun K hK => ?_⟩
  apply ((hj.2 K hK).comp hρtop).congr'
  filter_upwards [he] with n hn
  simp only [Function.comp_apply]
  rw [hn]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # A common GLPS subsequence when each source has its own finite prefix -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

theorem GLPS1988Proposition3.countable_tail_sources_tests (hGLPS : GLPS1988Proposition3)
    (r : ℕ → ℕ → KineticPhase → ℝ) (R : ℕ → ℝ) (hR : ∀ j, 0 < R j)
    (hsupp : ∀ j n, ∀ᵐ z ∂(volume : Measure KineticPhase), R j < ‖z.2‖ → r j n z = 0)
    (hUI : ∀ j, ∃ N : ℕ, UniformIntegrable (fun n => r j (n+N)) 1 volume)
    (ψ : ℕ → Velocity → ℝ)
    (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j)) (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, LocalL1Converges (fun n => resolventAverage (r j (φ n)) (ψ j)) (g j) := by
  choose N hN using hUI
  let r' := fun j => Compactness.zeroPrefix (N j) (r j)
  have hui j : UniformIntegrable (r' j) 1 volume :=
    Compactness.uniformIntegrable_zeroPrefix (hN j)
  have hs j n : ∀ᵐ z ∂(volume : Measure KineticPhase), R j < ‖z.2‖ → r' j n z = 0 := by
    by_cases hn : N j ≤ n
    · simpa only [r',Compactness.zeroPrefix,ite_eq_left hn] using hsupp j n
    · exact ae_of_all _ (by simp [r',Compactness.zeroPrefix,hn])
  obtain ⟨φ,g,hφ,hg⟩ := hGLPS.countable_sources_tests r' R hR hs hui ψ hψ hψc
  refine ⟨φ,g,hφ,fun j => ⟨(hg j).1,fun K hK => ?_⟩⟩
  apply ((hg j).2 K hK).congr'
  filter_upwards [hφ.tendsto_atTop.eventually (Compactness.zeroPrefix_eventually (N j) (r j))]
    with n hn
  dsimp only [r']
  rw [hn]

end BoltzmannNonuniqueness.Published

end

end

end OAI
