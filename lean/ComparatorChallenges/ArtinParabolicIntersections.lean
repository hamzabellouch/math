import Mathlib

namespace OAI

/-! Parabolic intersections, parabolic closure, and non-clique Artin-group dynamics. -/

namespace HarmonicArtin

universe u

variable {S : Type u}

def alternating (s t : S) : ℕ → FreeGroup S
  | 0 => 1
  | n + 1 => FreeGroup.of s * alternating t s n

def braidRelators (M : CoxeterMatrix S) : Set (FreeGroup S) :=
  Set.range fun st : S × S =>
    alternating st.1 st.2 (M st.1 st.2) *
      (alternating st.2 st.1 (M st.1 st.2))⁻¹

abbrev Artin (M : CoxeterMatrix S) := PresentedGroup (braidRelators M)

def generator (M : CoxeterMatrix S) (s : S) : Artin M := PresentedGroup.of s

def artinParabolic (M : CoxeterMatrix S) (T : Set S) : Subgroup (Artin M) :=
  Subgroup.closure (generator M '' T)

end HarmonicArtin

namespace HarmonicArtin.ParabolicIntersections

variable {G : Type*} [Group G]

/-- `g P g⁻¹`, with membership expressed without existential witnesses. -/
def conjugate (g : G) (P : Subgroup G) : Subgroup G :=
  P.comap (MulAut.conj g⁻¹).toMonoidHom

variable {S : Type*} (M : CoxeterMatrix S)

/-- Conjugates of standard subgroups, with no spherical-type restriction. -/
def IsParabolic (P : Subgroup (Artin M)) : Prop :=
  ∃ (X : Set S) (g : Artin M), P = conjugate g (artinParabolic M X)

end HarmonicArtin.ParabolicIntersections

namespace HarmonicArtin.ParabolicIntersections

noncomputable def gromovProduct {X : Type} [MetricSpace X] (o x y : X) : ℝ :=
  (dist o x + dist o y - dist x y)/2

def IsGromovHyperbolic (X : Type) [MetricSpace X] : Prop :=
  ∃ δ : ℝ, 0 ≤ δ ∧ ∀ o x y z : X,
    min (gromovProduct o x y) (gromovProduct o y z) ≤ gromovProduct o x z + δ

def IsGeodesicMetric (X : Type) [MetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ : Set.Icc (0 : ℝ) (dist x y) → X,
    Isometry γ ∧ γ ⟨0,le_rfl,dist_nonneg⟩=x ∧ γ ⟨dist x y,dist_nonneg,le_rfl⟩=y

def IsGromovSequence {X : Type} [MetricSpace X] (o : X) (u : ℕ → X) : Prop :=
  ∀ R : ℝ, ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n → R ≤ gromovProduct o (u m) (u n)

def IsAcylindrical (G X : Type) [Group G] [MetricSpace X] [MulAction G X] : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∃ N : ℕ, ∀ x y : X, R ≤ dist x y →
    {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε}.Finite ∧
      {g : G | dist x (g • x) ≤ ε ∧ dist y (g • y) ≤ ε}.ncard ≤ N

def HasThreeOrbitLimitPoints (G X : Type) [Group G] [MetricSpace X] [MulAction G X] : Prop :=
  ∃ o : X, ∃ u : Fin 3 → ℕ → G,
    (∀ i, IsGromovSequence o (fun n => u i n • o)) ∧
    ∀ i j, i ≠ j → ∃ B : ℝ, ∀ m n, gromovProduct o (u i m • o) (u j n • o) ≤ B

/-- An isometric non-elementary acylindrical action on a geodesic
Gromov-hyperbolic metric space. -/
def AcylindricallyHyperbolic (G : Type) [Group G] : Prop :=
  ∃ (X : Type) (metric : MetricSpace X) (action : MulAction G X),
    @IsGeodesicMetric X metric ∧ @IsGromovHyperbolic X metric ∧
    (∀ g : G, @Isometry X X metric.toPseudoMetricSpace.toPseudoEMetricSpace metric.toPseudoMetricSpace.toPseudoEMetricSpace
      (fun x => @SMul.smul G X action.toSMul g x)) ∧
    @IsAcylindrical G X _ metric action ∧ @HasThreeOrbitLimitPoints G X _ metric action

def WeaklyMalnormal {G : Type} [Group G] (P : Subgroup G) : Prop :=
  ∃ g : G, (↑(P ⊓ conjugate g P) : Set G).Finite

variable {S : Type} (M : CoxeterMatrix S)

/-- No nontrivial partition has every cross label equal to two. -/
def IsIrreducible : Prop :=
  ∀ Y : Set S, Y.Nonempty → Yᶜ.Nonempty → ∃ s ∈ Y, ∃ t ∉ Y, M s t ≠ 2

end HarmonicArtin.ParabolicIntersections

namespace HarmonicArtin.ParabolicIntersections

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

/-- The intersection of two conjugates of standard parabolics is parabolic. -/
theorem unconditional_parabolic_intersections
    (X Y : Set S) (g h : Artin M) :
    ∃ (Z : Set S) (k : Artin M),
      conjugate g (artinParabolic M X) ⊓ conjugate h (artinParabolic M Y) =
        conjugate k (artinParabolic M Z) := by
  sorry

/-- An arbitrary parabolic intersection is obtained from at most the rank many members. -/
theorem unconditional_arbitrary_intersections
    (F : Set (Subgroup (Artin M))) (hF : ∀ P ∈ F, IsParabolic M P) :
    (∃ F₀ : Finset (Subgroup (Artin M)),
      (↑F₀ : Set (Subgroup (Artin M))) ⊆ F ∧ F₀.card ≤ Nat.card S ∧
        sInf F = sInf (↑F₀ : Set (Subgroup (Artin M)))) ∧ IsParabolic M (sInf F) := by
  sorry

/-- Every subset is contained in a unique smallest parabolic subgroup. -/
theorem unconditional_parabolic_closure (E : Set (Artin M)) :
    ∃! P : Subgroup (Artin M), IsParabolic M P ∧ E ⊆ P ∧
      ∀ Q : Subgroup (Artin M), IsParabolic M Q → E ⊆ Q → P ≤ Q := by
  sorry

/-- An irreducible non-clique Artin group has an acylindrical non-elementary
hyperbolic action and all its proper parabolics are weakly malnormal. -/
theorem unconditional_nonclique_dynamics
    (hIrred : IsIrreducible M) (hInf : ∃ s t : S, s ≠ t ∧ M s t = 0) :
    AcylindricallyHyperbolic (Artin M) ∧
      ∀ P : Subgroup (Artin M), IsParabolic M P → P ≠ ⊤ → WeaklyMalnormal P := by
  sorry

end HarmonicArtin.ParabolicIntersections

end OAI
