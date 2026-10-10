import Mathlib
import OAI.Computability.QuantumFactoring.CyclicTestCircuit

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork

abbrev cyclicAddBound (s w ac bc mc : ℕ) :=
  s*w*(ac+bc+mc+216*(w+1)^2+142*(w+1)+15)

lemma cyclicAddBound_mono {s w a b c a' b' c' : ℕ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    cyclicAddBound s w a b c ≤ cyclicAddBound s w a' b' c' := by
  dsimp [cyclicAddBound]
  gcongr

abbrev cyclicTestBound (s w : ℕ) :=
  cyclicAddBound s w (s*w*w) (s*w*w) 0+s*w*w+w*cyclicStepBound s w+
    cyclicAddBound s w (2*(s*w*w)+w*cyclicStepBound s w) (s*w*w) 0+96*(s*w)+21

lemma cyclicTest_count (s w a : ℕ) [NeZero s] :
    (cyclicTest s w a).net.count ≤ cyclicTestBound s w := by
  let m : BooleanNetwork w w := select id
  let e : BooleanNetwork w w := select Fin.rev
  let X : BooleanNetwork w (s*w) := cyclicXNet s w
  let C : BooleanNetwork w (s*w) := cyclicCNet s w a
  let lhs := cyclicPowerOn (cyclicAddNet X C m) m e
  let rhs := cyclicAddNet (cyclicPowerOn X m e) C m
  have hx : X.net.count ≤ s*w*w := arrayConstant_count _
  have hc : C.net.count ≤ s*w*w := arrayConstant_count _
  have hm : m.net.count=0 := rfl
  have he : e.net.count=0 := rfl
  have ha : (cyclicAddNet X C m).net.count ≤ cyclicAddBound s w (s*w*w) (s*w*w) 0 :=
    (cyclicAddNet_count X C m).trans (cyclicAddBound_mono hx hc (by rfl))
  have hl := cyclicPowerOn_count (cyclicAddNet X C m) m e
  rw [hm,he] at hl
  have hp : (cyclicPowerOn X m e).net.count ≤ 2*(s*w*w)+w*cyclicStepBound s w := by
    have h := cyclicPowerOn_count X m e
    rw [hm,he] at h
    omega
  have hr : rhs.net.count ≤ cyclicAddBound s w (2*(s*w*w)+w*cyclicStepBound s w) (s*w*w) 0 :=
    (cyclicAddNet_count (cyclicPowerOn X m e) C m).trans
      (cyclicAddBound_mono hp hc (by rfl))
  have hq := wordEq_count (s*w)
  change ((lhs.pair rhs).comp (wordEq (s*w))).net.count ≤ _
  rw [count_comp,count_pair]
  change (cyclicPowerOn (cyclicAddNet X C m) m e).net.count+rhs.net.count+_ ≤ _
  dsimp [cyclicTestBound]
  omega

lemma cyclicStepBound_mono {s w s' w' : ℕ} (hs : s ≤ s') (hw : w ≤ w') :
    cyclicStepBound s w ≤ cyclicStepBound s' w' := by
  unfold cyclicStepBound cyclicMulBound
  gcongr

lemma cyclicTestBound_mono {s w s' w' : ℕ} (hs : s ≤ s') (hw : w ≤ w') :
    cyclicTestBound s w ≤ cyclicTestBound s' w' := by
  unfold cyclicTestBound cyclicAddBound
  gcongr <;> exact cyclicStepBound_mono hs hw

end ExactQuantumFactoring.BitArithmetic


end

end OAI
