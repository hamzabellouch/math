import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.RootedTemplates
import OAI.Combinatorics.TriangleRemoval.Process.CommonNeighbors

namespace OAI

section
section
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def prefixEpsilon : ℝ := 1 / 2000
def prefixCycleCap : ℕ := 8000
def prefixSuffixLength : ℕ := 100
def prefixSuppression : ℕ := 50
def prefixTemplateCap : ℕ := 8001

noncomputable def prefixTargetDensity (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 / 2 : ℝ) + prefixEpsilon)

noncomputable def prefixTargetTime (n : ℕ) : ℝ :=
  (n : ℝ)^2 / 6 * (1 - 1 / (n : ℝ) - prefixTargetDensity n)

noncomputable def prefixTime (n : ℕ) : ℕ := ⌊prefixTargetTime n⌋₊

noncomputable def prefixDensity (n : ℕ) : ℝ :=
  1 - 1 / (n : ℝ) - 6 * prefixTime n / (n : ℝ)^2

noncomputable def prefixD (n : ℕ) : ℝ := n * prefixDensity n ^ 2
noncomputable def prefixM (n : ℕ) : ℝ := (n : ℝ)^2 * prefixDensity n / 2

noncomputable def prefixLaw (n : ℕ) : PMF (Graph n) :=
  evolve (completeGraph n) (prefixTime n)

def neighbors {n : ℕ} (G : Graph n) (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => {u,v} ∈ G)

def currentDegree {n : ℕ} (G : Graph n) (u : Fin n) : ℕ :=
  (neighbors G u).card

def cycleNext {j : ℕ} (i : Fin j) : Fin j :=
  ⟨(i.val + 1) % j, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

noncomputable def linkCycleCount {n : ℕ} (j : ℕ) (G : Graph n) (u : Fin n) : ℝ := by
  classical
  exact ∑ φ : Fin j ↪ Fin n,
    if ∀ i, {u, φ i} ∈ G ∧ {φ i, φ (cycleNext i)} ∈ G then 1 else 0

def largeTemplateEligible {k : ℕ} (T : RootedTemplate k) (n : ℕ) (p : ℝ) : Prop :=
  ∀ W : Finset (Fin k), T.roots ⊆ W →
    ∀ F : Graph k, F ⊆ T.edges → (∀ e ∈ F, e ⊆ W) →
      1 ≤ (n : ℝ) ^ (W.card - T.roots.card) * p ^ F.card

def smallTemplateEligible {k : ℕ} (T : RootedTemplate k) (n : ℕ) (p : ℝ) : Prop :=
  ∀ J : Finset (Fin k), T.roots ⊆ J →
    (n : ℝ) ^ (k - J.card) * p ^ (T.edges.card - (T.edges.filter (· ⊆ J)).card) ≤ 1

noncomputable def prefixTemplateFactor (n : ℕ) (C : ℝ) : ℝ :=
  (1 + Real.log n) ^ C

def GoodPrefixGraph (n : ℕ) (c C : ℝ) (G : Graph n) : Prop :=
  G ⊆ completeGraph n ∧
  (G.card : ℝ) = prefixM n ∧
  (∀ u, |(currentDegree G u : ℝ) - n * prefixDensity n| ≤
    (n : ℝ)^(-c) * (n * prefixDensity n)) ∧
  (∀ u v, u ≠ v → |(currentCodegree G u v : ℝ) - prefixD n| ≤
    (n : ℝ)^(-c) * prefixD n) ∧
  (∀ j, 3 ≤ j → j ≤ prefixCycleCap → ∀ u,
    |linkCycleCount j G u - prefixD n ^ j| ≤ (n : ℝ)^(-c) * prefixD n ^ j) ∧
  (∀ k, k ≤ prefixTemplateCap → ∀ T : RootedTemplate k,
    ∀ ψ : {v // v ∈ T.roots} ↪ Fin n,
      (largeTemplateEligible T n (prefixDensity n) →
        rootedCount T ψ G ≤ prefixTemplateFactor n C * rootedScaling T n (prefixDensity n)) ∧
      (smallTemplateEligible T n (prefixDensity n) →
        rootedCount T ψ G ≤ prefixTemplateFactor n C))

noncomputable def prefixFailure (n : ℕ) (c C : ℝ) : ℝ := by
  classical
  exact pmfMean (prefixLaw n) (fun G => if GoodPrefixGraph n c C G then 0 else 1)

def UniformPrefixObligation : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
    prefixFailure n c C ≤ Real.exp (- (Real.log n) ^ (4 / 3 : ℝ))

theorem prefixDensity_bounds (n : ℕ) (hn : 0 < n)
    (ht : 0 ≤ prefixTargetTime n) :
    prefixTargetDensity n ≤ prefixDensity n ∧
      prefixDensity n < prefixTargetDensity n + 6 / (n : ℝ)^2 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn2 : 0 < (n : ℝ)^2 := sq_pos_of_pos hnR
  have hf : (prefixTime n : ℝ) ≤ prefixTargetTime n := Nat.floor_le ht
  have hg : prefixTargetTime n < (prefixTime n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hx : prefixTargetTime n * 6 =
      (n : ℝ)^2 * (1 - 1 / (n : ℝ) - prefixTargetDensity n) := by
    unfold prefixTargetTime
    ring
  have hp : prefixDensity n * (n : ℝ)^2 =
      (1 - 1 / (n : ℝ)) * (n : ℝ)^2 - 6 * prefixTime n := by
    unfold prefixDensity
    field_simp
  constructor
  · apply (le_of_mul_le_mul_right (a := (n : ℝ)^2) _ hn2)
    nlinarith
  · apply (lt_of_mul_lt_mul_right (a := (n : ℝ)^2) _ (le_of_lt hn2))
    have he : (6 / (n : ℝ)^2) * (n : ℝ)^2 = 6 := div_mul_cancel₀ _ (ne_of_gt hn2)
    nlinarith

theorem step_card_mass_lower {n : ℕ} {G H : Graph n}
    (h : H ∈ (step G).support) : G.card ≤ H.card + 3 := by
  by_cases ha : (triangles G).Nonempty
  · exact le_of_eq (step_card_of_active ha h).symm
  · simp only [step,dite_eq_right ha,PMF.mem_support_pure_iff] at h
    subst H
    omega

theorem evolve_card_mass_lower {n : ℕ} (G : Graph n) (k : ℕ) {H : Graph n}
    (h : H ∈ (evolve G k).support) : G.card ≤ H.card + 3*k := by
  induction k generalizing H with
  | zero =>
    simp only [evolve,PMF.mem_support_pure_iff] at h
    simp [h]
  | succ k ih =>
    obtain ⟨J,hJ,hH⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
    have h₁ := ih hJ
    have h₂ := step_card_mass_lower hH
    omega

theorem mass_equality_prevents_early_stop {n : ℕ} {G H K : Graph n}
    {j k : ℕ} (hjk : j < k) (hK : K ∈ (evolve G j).support)
    (hH : H ∈ (evolve K (k-j)).support)
    (hm : H.card + 3*k = G.card) : (triangles K).Nonempty := by
  by_contra hn
  have hKe : triangles K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  rw [evolve_absorbing K hKe] at hH
  have he : H = K := by simpa only [PMF.mem_support_pure_iff] using hH
  subst H
  have hb := evolve_card_mass_lower G j hK
  omega

theorem prefixM_mass (n : ℕ) (hn : 0 < n) :
    prefixM n + 3 * prefixTime n = (n.choose 2 : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  rw [Nat.cast_choose_two]
  unfold prefixM prefixDensity
  field_simp
  ring

theorem goodPrefix_mass {n : ℕ} {c C : ℝ} {G : Graph n}
    (hn : 0 < n) (hG : GoodPrefixGraph n c C G) :
    G.card + 3 * prefixTime n = (completeGraph n).card := by
  have hm := prefixM_mass n hn
  rw [← hG.2.1] at hm
  rw [card_completeGraph]
  exact_mod_cast hm

end SharpTerminalLeave

open InnerProductSpace
open scoped InnerProductSpace

end
end

end OAI
