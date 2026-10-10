import OAI.LinearAlgebra.MatrixMultiplication.Duality.Information

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualInformationTransport

open MatrixMultiplication.Foundation DualEntropyHelpers DualInformation
open scoped BigOperators

variable {A B R L X R' L' X' : Type*}
  [Fintype A] [Fintype B] [Fintype R] [Fintype L] [Fintype X]
  [Fintype R'] [Fintype L'] [Fintype X']

theorem mass_factorization_congr_mass_iff (p q : FiniteLaw A)
    (hmass : p.mass = q.mass) (prior : A → R) (label : A → L) (x : A → X) :
    ConditionalMassFactorization p prior label x ↔
      ConditionalMassFactorization q prior label x := by
  classical
  simp only [ConditionalMassFactorization, FiniteLaw.map_mass, hmass]

theorem mass_factorization_map_iff (p : FiniteLaw A) (e : A → B)
    (prior : B → R) (label : B → L) (x : B → X) :
    ConditionalMassFactorization (p.map e) prior label x ↔
      ConditionalMassFactorization p (fun a => prior (e a))
        (fun a => label (e a)) (fun a => x (e a)) := by
  simp only [ConditionalMassFactorization, map_comp_mass]

theorem conditionalIndependent_map_of_mass_factorization
    (p : FiniteLaw A) (e : A → B)
    (prior : B → R) (label : B → L) (x : B → X)
    (h : ConditionalMassFactorization p (fun a => prior (e a))
      (fun a => label (e a)) (fun a => x (e a))) :
    ConditionalIndependent (p.map e) prior label x := by
  apply conditionalIndependent_of_mass_factorization
  exact (mass_factorization_map_iff p e prior label x).mpr h

theorem map_mass_eq_of_fiber (p : FiniteLaw A) (f : A → B) (g : A → R)
    (b : B) (r : R) (fiber : ∀ a, f a = b ↔ g a = r) :
    (p.map f).mass b = (p.map g).mass r := by
  classical
  simp only [FiniteLaw.map_mass]
  apply Finset.sum_congr rfl
  intro a _
  rw [fiber a]

theorem mass_factorization_of_same_partitions (p : FiniteLaw A)
    (priorA : A → R) (labelA : A → L) (xA : A → X)
    (priorB : A → R') (labelB : A → L') (xB : A → X')
    (hprior : ∀ a b, priorA a = priorA b ↔ priorB a = priorB b)
    (hlabel : ∀ a b, labelA a = labelA b ↔ labelB a = labelB b)
    (hx : ∀ a b, xA a = xA b ↔ xB a = xB b)
    (factor : ConditionalMassFactorization p priorA labelA xA) :
    ConditionalMassFactorization p priorB labelB xB := by
  classical
  intro r l xx
  by_cases hr : ∃ a, priorB a = r
  · obtain ⟨a, rfl⟩ := hr
    by_cases hl : ∃ b, labelB b = l
    · obtain ⟨b, rfl⟩ := hl
      by_cases hxx : ∃ c, xB c = xx
      · obtain ⟨c, rfl⟩ := hxx
        have hp : (p.map priorB).mass (priorB a) =
            (p.map priorA).mass (priorA a) :=
          map_mass_eq_of_fiber p priorB priorA _ _ (fun d => (hprior d a).symm)
        have hpl : (p.map (fun d => (priorB d, labelB d))).mass
              (priorB a, labelB b) =
            (p.map (fun d => (priorA d, labelA d))).mass (priorA a, labelA b) := by
          apply map_mass_eq_of_fiber
          intro d
          simp only [Prod.mk.injEq, ← hprior, ← hlabel]
        have hpx : (p.map (fun d => (priorB d, xB d))).mass
              (priorB a, xB c) =
            (p.map (fun d => (priorA d, xA d))).mass (priorA a, xA c) := by
          apply map_mass_eq_of_fiber
          intro d
          simp only [Prod.mk.injEq, ← hprior, ← hx]
        have hplx : (p.map (fun d => (priorB d, (labelB d, xB d)))).mass
              (priorB a, (labelB b, xB c)) =
            (p.map (fun d => (priorA d, (labelA d, xA d)))).mass
              (priorA a, (labelA b, xA c)) := by
          apply map_mass_eq_of_fiber
          intro d
          simp only [Prod.mk.injEq, ← hprior, ← hlabel, ← hx]
        rw [hplx, hp, hpl, hpx]
        exact factor (priorA a) (labelA b) (xA c)
      · have hn : ∀ c, xB c ≠ xx := not_exists.mp hxx
        simp [FiniteLaw.map_mass, Prod.mk.injEq, hn]
    · have hn : ∀ b, labelB b ≠ l := not_exists.mp hl
      simp [FiniteLaw.map_mass, Prod.mk.injEq, hn]
  · have hn : ∀ a, priorB a ≠ r := not_exists.mp hr
    simp [FiniteLaw.map_mass, Prod.mk.injEq, hn]

theorem mass_factorization_partition_iff (p : FiniteLaw A)
    (priorA : A → R) (labelA : A → L) (xA : A → X)
    (priorB : A → R') (labelB : A → L') (xB : A → X')
    (hprior : ∀ a b, priorA a = priorA b ↔ priorB a = priorB b)
    (hlabel : ∀ a b, labelA a = labelA b ↔ labelB a = labelB b)
    (hx : ∀ a b, xA a = xA b ↔ xB a = xB b) :
    ConditionalMassFactorization p priorA labelA xA ↔
      ConditionalMassFactorization p priorB labelB xB := by
  constructor
  · exact mass_factorization_of_same_partitions p priorA labelA xA priorB labelB xB
      hprior hlabel hx
  · exact mass_factorization_of_same_partitions p priorB labelB xB priorA labelA xA
      (fun a b => (hprior a b).symm) (fun a b => (hlabel a b).symm)
      (fun a b => (hx a b).symm)

end MatrixMultiplication.DualInformationTransport

end

end OAI
