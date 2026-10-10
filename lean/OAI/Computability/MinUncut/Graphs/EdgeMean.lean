import Mathlib
import OAI.Computability.MinUncut.Games.JointHintSampling

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I S : Type*} [Fintype I] [Fintype S]

abbrev EdgeStatistic (Name I : Type*) [Fintype I] :=
  (U : I → Equation Name) → (hidden : I → Bool) → (pos : I → Fin 3) → ℝ

def edgeMean (equations : S → Equation Name) (k : ℕ) (F : EdgeStatistic Name I) : ℝ :=
  𝔼 H : FixedSets I k, 𝔼 a : I → S, 𝔼 pos : I → Fin 3,
    F (fun i => equations (a i)) (hiddenSet H.val) pos

lemma edgeMean_mono (equations : S → Equation Name) (k : ℕ) {F G : EdgeStatistic Name I}
    (h : ∀ U hidden pos, F U hidden pos ≤ G U hidden pos) :
    edgeMean equations k F ≤ edgeMean equations k G := by
  exact Finset.expect_le_expect (fun H _ => Finset.expect_le_expect (fun a _ =>
    Finset.expect_le_expect (fun pos _ => h _ _ _)))

lemma edgeMean_add (equations : S → Equation Name) (k : ℕ) (F G : EdgeStatistic Name I) :
    edgeMean equations k (fun U h pos => F U h pos+G U h pos) =
      edgeMean equations k F+edgeMean equations k G := by
  simp only [edgeMean,Finset.expect_add_distrib]

lemma edgeMean_mul (equations : S → Equation Name) (k : ℕ) (F : EdgeStatistic Name I) (t : ℝ) :
    edgeMean equations k (fun U h pos => t*F U h pos) = t*edgeMean equations k F := by
  simp only [edgeMean,← Finset.mul_expect]

lemma edgeMean_expect {X : Type*} [Fintype X] (equations : S → Equation Name) (k : ℕ)
    (F : X → EdgeStatistic Name I) :
    (𝔼 x, edgeMean equations k (F x)) = edgeMean equations k (fun U h pos => 𝔼 x,F x U h pos) := by
  unfold edgeMean
  rw [Finset.expect_comm]
  congr 1
  funext H
  rw [Finset.expect_comm]
  congr 1
  funext a
  rw [Finset.expect_comm]

lemma edgeMean_const [Nonempty S] (equations : S → Equation Name) {k : ℕ}
    (hk : k≤Fintype.card I) (t : ℝ) : edgeMean (I := I) equations k (fun _ _ _ => t)=t := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  simp only [edgeMean,Fintype.expect_const]

end MinUncut.Outer

end
end

end OAI
