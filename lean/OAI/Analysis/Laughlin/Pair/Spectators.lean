import OAI.Analysis.Laughlin.Operators.PhysicalPairKernel
import OAI.Analysis.Laughlin.Spin.Polynomial2

namespace OAI

namespace Laughlin
open scoped BigOperators

abbrev PairSpectators {N Q : ℕ} (i j : Fin N) :=
  {a : Configuration N Q // a i = 0 ∧ a j = 0}

noncomputable def pairConfigurationEquiv {N Q : ℕ} (i j : Fin N) (hij : i ≠ j) :
    PairSpectators (Q := Q) i j × (Fin (Q+1) × Fin (Q+1)) ≃ Configuration N Q where
  toFun b := Function.update (Function.update b.1.val i b.2.1) j b.2.2
  invFun a := (⟨Function.update (Function.update a i 0) j 0, by simp [hij]⟩, a i, a j)
  left_inv := by
    rintro ⟨⟨a,hai,haj⟩,x,y⟩
    apply Prod.ext
    · apply Subtype.ext
      funext k
      by_cases hki : k=i
      · subst k; simp [hij,hai]
      · by_cases hkj : k=j
        · subst k; simp [haj]
        · simp [hki,hkj]
    · simp [hij]
  right_inv := by
    intro a
    funext k
    by_cases hki : k=i
    · subst k; simp [hij]
    · by_cases hkj : k=j
      · subst k; simp
      · simp [hki,hkj]

theorem sum_pair_configurations {N Q : ℕ} {R : Type*} [AddCommMonoid R]
    (i j : Fin N) (hij : i ≠ j) (F : Configuration N Q → R) :
    (∑ a, F a) = ∑ a : PairSpectators (Q := Q) i j, ∑ x, ∑ y,
      F (Function.update (Function.update a.val i x) j y) := by
  classical
  rw [← Equiv.sum_comp (pairConfigurationEquiv (Q := Q) i j hij)]
  simp only [Fintype.sum_prod_type, pairConfigurationEquiv, Equiv.coe_fn_mk]

end Laughlin

end OAI
