import OAI.Combinatorics.TreewidthL1.Annulus

namespace OAI

namespace BoundedTreewidthL1
namespace PaddedPartitions

/-- A partition is represented by its block-label map. The fibers are the
blocks; using vertices as labels represents every partition of a finite
nonempty vertex set. Unused labels impose no extra block condition. -/
abbrev Partition (V : Type*) := V → V

/-- Weak diameter, measured in the original weighted graph metric. -/
def BoundedDiameter {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)
    (r : ℝ) (P : Partition V) : Prop :=
  ∀ u v, P u = P v → shortestPathDistance G ℓ u v ≤ r

/-- The closed metric ball is contained in the block containing x. -/
def PaddedAt {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)
    (s : ℝ) (P : Partition V) (x : V) : Prop :=
  ∀ y, shortestPathDistance G ℓ x y ≤ s → P y = P x

noncomputable def paddingProbability {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ) (s : ℝ)
    (μ : Partition V → ℝ) (x : V) : ℝ := by
  classical
  exact ∑ P, if PaddedAt G ℓ s P x then μ P else 0

def UniformPaddedPartitions : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ α π : ℝ,
    0 < α ∧ α ≤ 1 / 8 ∧ 0 < π ∧ π ≤ 1 ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V), G.Connected → HasTreeDecomposition G k →
      ∀ ℓ : G.edgeSet → ℝ, (∀ e, 0 < ℓ e) →
      ∀ r : ℝ, 0 < r → ∃ μ : Partition V → ℝ,
        (∀ P, 0 ≤ μ P) ∧ (∑ P, μ P) = 1 ∧
        (∀ P, 0 < μ P → BoundedDiameter G ℓ r P) ∧
        ∀ x, π ≤ paddingProbability G ℓ (α * r) μ x

end PaddedPartitions
end BoundedTreewidthL1

namespace BoundedTreewidthL1.PaddedPartitions
open Annulus

theorem uniform_padded_partitions : UniformPaddedPartitions := by
  classical
  intro k hk
  have hk0 : 0 < k := by omega
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkR0 : (0 : ℝ) < k := by positivity
  let α : ℝ := 1 / (64 * (k : ℝ)^2)
  have hα : 0 < α := by dsimp [α]; positivity
  have hα8 : α ≤ 1 / 8 := by
    dsimp [α]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  refine ⟨α, 1/2, hα, hα8, by norm_num, by norm_num, ?_⟩
  intro V _ _ _ G hG hdec ℓ hℓ r hr
  let w : Sym2 V → ℝ := fun e => if h : e ∈ G.edgeSet then ℓ ⟨e, h⟩ else 0
  have hw : ∀ e, 0 ≤ w e := by
    intro e
    dsimp [w]
    split_ifs with h
    · exact (hℓ ⟨e, h⟩).le
    · exact le_rfl
  have hweights : weights G w = ℓ := by
    funext e
    simp [weights, w, e.property]
  let : MetricSpace V := weightedMetricSpace G ℓ hG hℓ
  have hdist : ∀ u v, dist u v = distance G w u v := by
    intro u v
    change shortestPathDistance G ℓ u v = shortestPathDistance G (weights G w) u v
    rw [hweights]
  let M := 4 * k
  have hM : 0 < M := by dsimp [M]; omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMR4 : (M : ℝ) = 4 * (k : ℝ) := by simp [M]
  let R := r / (4 * (k : ℝ))
  have hR : 0 < R := by dsimp [R]; positivity
  let ε := R / (4 * (M : ℝ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεα : ε = α * r := by
    dsimp [ε, R, α]
    rw [hMR4]
    field_simp
    ; ring
  have hsep : 2 * (M : ℝ) * (ε / R) < 1 := by
    have heq : 2 * (M : ℝ) * (ε / R) = 1/2 := by
      dsimp [ε]
      field_simp
      ; ring
    rw [heq]
    norm_num
  have hdiam : (k : ℝ) * (2 * R + 4 * ε) ≤ r := by
    have hMlarge : (1 : ℝ) ≤ M := by rw [hMR4]; nlinarith
    have hεR : 4 * ε ≤ R := by
      have heq : 4 * ε = R / (M : ℝ) := by
        dsimp [ε]
        field_simp
      rw [heq]
      apply (div_le_iff₀ hMR).mpr
      nlinarith
    have hkr : (k : ℝ) * R = r/4 := by dsimp [R]; field_simp [hkR0.ne']
    nlinarith
  obtain ⟨d, T, bag, hT, hcover, hedge, hocc, hwidth⟩ := hdec
  let H := smallEdges G w ε
  let F : (Fin k → Fin M) → SimpleGraph V := run w R (gridOffset M R) k H
  let P : (Fin k → Fin M) → Partition V := fun σ => root (F σ)
  have hPdiam : ∀ σ, BoundedDiameter G ℓ r (P σ) := by
    intro σ u v huv
    have hreach : (F σ).Reachable u v := by
      have hu := root_reachable (F σ) u
      have hv := root_reachable (F σ) v
      change root (F σ) u = root (F σ) v at huv
      rw [huv] at hu
      exact hu.symm.trans hv
    have hballs : ∀ c, (G.induce {z | dist c z ≤ R + ε}).Connected := by
      intro c
      exact shortest_closedBall_connected G ℓ hG (fun e => (hℓ e).le) c (by positivity)
    have hd := run_diameter G H (smallEdges_le G w ε) w hw hdist T bag k
      (by omega) hT hedge hocc hwidth hR hε (smallEdges_mesh G w ε) hballs
      (gridOffset M R) (gridOffset_nonneg hR.le) (gridOffset_lt hR) σ u v hreach
    exact hd.trans hdiam
  let μ := FiniteLawPush.law P
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  refine ⟨μ, FiniteLawPush.nonneg P, FiniteLawPush.total P, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨σ, rfl⟩ := FiniteLawPush.supported P Q hQ
    exact hPdiam σ
  · intro x
    have hcount := preserves_fraction G w hw hG M hM hR hε.le hsep k x
    have hgood : ∀ σ, PreservesBall G (F σ) w ε x → PaddedAt G ℓ (α*r) (P σ) x := by
      intro σ hp y hy
      have hdy : distance G w x y ≤ ε := by
        dsimp [distance]
        rw [hweights, hεα]
        exact hy
      obtain ⟨p, _⟩ := hp y hdy
      exact root_eq p.reachable.symm
    have hsum : (∑ σ : Fin k → Fin M,
        if PreservesBall G (F σ) w ε x then (1 : ℝ) else 0) ≤
        ∑ σ : Fin k → Fin M, if PaddedAt G ℓ (α*r) (P σ) x then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro σ _
      by_cases hp : PreservesBall G (F σ) w ε x
      · simp [hp, hgood σ hp]
      · simp only [hp, ↓reduceIte]
        split <;> norm_num
    have hhalf : (1 : ℝ)/2 ≤ 1 - (k : ℝ)/M := by
      rw [hMR4]
      have hq : (k : ℝ) / (4 * (k : ℝ)) = 1/4 := by field_simp [hkR0.ne']
      rw [hq]
      norm_num
    calc
      (1 : ℝ)/2 ≤ 1 - (k : ℝ)/M := hhalf
      _ ≤ (∑ σ : Fin k → Fin M,
          if PreservesBall G (F σ) w ε x then (1 : ℝ) else 0) / (M : ℝ)^k := hcount
      _ ≤ (∑ σ : Fin k → Fin M,
          if PaddedAt G ℓ (α*r) (P σ) x then (1 : ℝ) else 0) / (M : ℝ)^k :=
        div_le_div_of_nonneg_right hsum (pow_nonneg hMR.le k)
      _ = paddingProbability G ℓ (α*r) μ x := by
        let : DecidableEq V := Classical.decEq V
        unfold paddingProbability
        have hh := (FiniteLawPush.event P (fun Q => PaddedAt G ℓ (α*r) Q x)).symm
        simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hh

end BoundedTreewidthL1.PaddedPartitions

end OAI
