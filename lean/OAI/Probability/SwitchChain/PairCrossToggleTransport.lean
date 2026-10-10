import OAI.Probability.SwitchChain.PairFiberSliceComparison
import OAI.Probability.SwitchChain.PairFiberTransport

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber

variable {n : ℕ} {d : Fin n → ℕ}
attribute [local instance] Classical.propDecidable

def fiberSwapEquiv (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) : Equiv.Perm (StateFiber G i j) :=
  ((stateFiberEquiv G i j hij).trans
    (assignmentRelabelEquiv G.val i j (Equiv.swap x y))).trans
      (stateFiberEquiv G i j hij).symm

theorem fiberSwapEquiv_apply (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (H : StateFiber G i j) :
    fiberSwapEquiv G i j hij x y H =
      (stateFiberEquiv G i j hij).symm
        (assignmentRelabel G.val i j (Equiv.swap x y)
          (stateFiberEquiv G i j hij H)) := rfl

theorem fiberSwapEquiv_leftSet (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (H : StateFiber G i j) :
    leftSet (fiberSwapEquiv G i j hij x y H).val.val i j =
      (leftSet H.val.val i j).map (Equiv.swap x.val y.val).toEmbedding := by
  rw [fiberSwapEquiv_apply]
  rw [stateFiberEquiv_symm_apply, leftSet_trade, assignmentRelabel_swap_val]
  rfl

theorem fiberSwapEquiv_eq_of_key_leftSet
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (H : StateFiber G i j)
    (K : GraphState n d)
    (hkey : key i j K.val = key i j H.val.val)
    (hleft : leftSet K.val i j =
      (leftSet H.val.val i j).map (Equiv.swap x.val y.val).toEmbedding) :
    (fiberSwapEquiv G i j hij x y H).val = K := by
  apply Subtype.ext
  apply graph_eq_of_key_leftSet_eq
  · exact (fiberSwapEquiv G i j hij x y H).property.trans
      (hkey.trans H.property).symm
  · exact (fiberSwapEquiv_leftSet G i j hij x y H).trans hleft.symm

theorem fiberSwapEquiv_involutive
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) :
    Function.Involutive (fiberSwapEquiv G i j hij x y) := by
  intro H
  apply Subtype.ext
  apply Subtype.ext
  apply graph_eq_of_key_leftSet_eq
  · exact (fiberSwapEquiv G i j hij x y
      (fiberSwapEquiv G i j hij x y H)).property.trans H.property.symm
  · rw [fiberSwapEquiv_leftSet, fiberSwapEquiv_leftSet, Finset.map_map]
    have he : (Equiv.swap x.val y.val).toEmbedding.trans
        (Equiv.swap x.val y.val).toEmbedding = Function.Embedding.refl (Fin n) := by
      apply Function.Embedding.ext
      intro z
      exact Equiv.swap_apply_self x.val y.val z
    rw [he, Finset.map_refl]

theorem fiberSwap_squared_displacement
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (f : GraphState n d → ℝ) :
    (∑ H : StateFiber G i j,
      (f H.val - f (fiberSwapEquiv G i j hij x y H).val) ^ 2) =
    ∑ T : Assignment G.val i j,
      (f ((stateFiberEquiv G i j hij).symm T).val -
       f ((stateFiberEquiv G i j hij).symm
         (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) ^ 2 := by
  let e := stateFiberEquiv G i j hij
  apply Fintype.sum_equiv e
  intro H
  simp only [e, Equiv.symm_apply_apply, fiberSwapEquiv_apply]

theorem toggle_squared_displacement_eq_assignment_swap
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (toggle : GraphState n d → GraphState n d)
    (hkey : ∀ H : StateFiber G i j,
      key i j (toggle H.val).val = key i j H.val.val)
    (hleft : ∀ H : StateFiber G i j,
      leftSet (toggle H.val).val i j =
        (leftSet H.val.val i j).map (Equiv.swap x.val y.val).toEmbedding)
    (f : GraphState n d → ℝ) :
    (∑ H : StateFiber G i j, (f H.val - f (toggle H.val)) ^ 2) =
    ∑ T : Assignment G.val i j,
      (f ((stateFiberEquiv G i j hij).symm T).val -
       f ((stateFiberEquiv G i j hij).symm
         (assignmentRelabel G.val i j (Equiv.swap x y) T)).val) ^ 2 := by
  rw [← fiberSwap_squared_displacement G i j hij x y f]
  apply Finset.sum_congr rfl
  intro H _
  rw [fiberSwapEquiv_eq_of_key_leftSet G i j hij x y H
    (toggle H.val) (hkey H) (hleft H)]

end Problem315.PairFiber

end

end OAI
