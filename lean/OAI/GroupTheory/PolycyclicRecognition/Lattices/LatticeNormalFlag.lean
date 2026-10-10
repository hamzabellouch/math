import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FreeAbelianDuality

namespace OAI

/-! # The normal cyclic flag of a lattice quotient -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] {r : ℕ} (q : G →* IntegralLatticeGroup r)

def latticeNormalFlag (i : ℕ) : Subgroup G where
  carrier := {g | ∀ j : Fin r, i ≤ j.val → (q g).toAdd j = 0}
  one_mem' := by intro j _; rw [q.map_one]; rfl
  mul_mem' := by
    intro a b ha hb j hj
    rw [map_mul]
    change (q a).toAdd j + (q b).toAdd j = 0
    rw [ha j hj, hb j hj, add_zero]
  inv_mem' := by
    intro a ha j hj
    rw [map_inv]
    change -(q a).toAdd j = 0
    rw [ha j hj, neg_zero]

instance latticeNormalFlag_normal (i : ℕ) : (latticeNormalFlag q i).Normal where
  conj_mem x hx g := by
    intro j hj
    rw [q.map_mul, q.map_mul, q.map_inv]
    change (q g).toAdd j + (q x).toAdd j + -(q g).toAdd j = 0
    rw [hx j hj]
    abel

theorem latticeNormalFlag_mono {i j : ℕ} (hij : i ≤ j) :
    latticeNormalFlag q i ≤ latticeNormalFlag q j :=
  fun _ hx k hk => hx k (hij.trans hk)

theorem latticeNormalFlag_zero : latticeNormalFlag q 0 = q.ker := by
  ext g
  constructor
  · intro hg
    change q g = 1
    apply Multiplicative.toAdd.injective
    funext j
    exact hg j (Nat.zero_le _)
  · intro hg j _
    change q g = 1 at hg
    rw [hg]
    rfl

theorem latticeNormalFlag_top : latticeNormalFlag q r = ⊤ := by
  apply top_unique
  intro g _ j hj
  exact False.elim (Nat.not_le_of_gt j.isLt hj)

def latticeNormalFlagStep (i : Fin r) :
    latticeNormalFlag q (i.val + 1) →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd ((q (g : G)).toAdd i)
  map_one' := by change Multiplicative.ofAdd ((q 1).toAdd i) = 1; rw [q.map_one]; rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    change (q ((a : G) * (b : G))).toAdd i = (q (a : G)).toAdd i + (q (b : G)).toAdd i
    rw [map_mul]
    rfl

theorem latticeNormalFlagStep_ker (i : Fin r) :
    (latticeNormalFlagStep q i).ker =
      (latticeNormalFlag q i.val).subgroupOf (latticeNormalFlag q (i.val + 1)) := by
  ext g
  constructor
  · intro hg j hj
    have hh := congrArg Multiplicative.toAdd hg
    change (q (g : G)).toAdd i = 0 at hh
    by_cases hji : j = i
    · subst j; exact hh
    · exact g.property j (by have hne : j.val ≠ i.val := fun h => hji (Fin.ext h); omega)
  · intro hg
    exact congrArg Multiplicative.ofAdd (hg i (le_refl _))

theorem latticeNormalFlagStep_generator (hq : Function.Surjective q) (i : Fin r) :
    ∃ t : latticeNormalFlag q (i.val + 1), latticeNormalFlagStep q i t = Multiplicative.ofAdd 1 := by
  classical
  obtain ⟨g, hg⟩ := hq (Multiplicative.ofAdd (Pi.single i 1))
  have hmem : g ∈ latticeNormalFlag q (i.val + 1) := by
    intro j hj
    rw [hg]
    change (Pi.single i 1 : Fin r → ℤ) j = 0
    have hji : j ≠ i := by intro h; subst j; omega
    simp [hji]
  refine ⟨⟨g, hmem⟩, ?_⟩
  change Multiplicative.ofAdd ((q g).toAdd i) = _
  rw [hg]
  simp

end PolycyclicRecognition

end

end OAI
