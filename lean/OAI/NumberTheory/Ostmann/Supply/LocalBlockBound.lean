import OAI.NumberTheory.Ostmann.Supply.BlockNorm
import OAI.NumberTheory.Ostmann.Supply.LocalBlock

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "H" => EuclideanSpace ℂ ι

theorem localBlock_norm_le (S T : Finset ι) (K : H →L[ℂ] H)
    {s e d : ℝ} (hs : 98/100 ≤ s) (hs' : s ≤ 102/100)
    (he : 0 ≤ e) (he' : e ≤ 1/100) (hd : 0 ≤ d) (hd' : d ≤ 95/100)
    (hscalar : ‖inner ℂ (uniformVector S) (K (uniformVector T))‖ ≤ s)
    (hrow : ∀ v : centeredSpace T,
      ‖inner ℂ (uniformVector S) (K (v:H))‖ ≤ e*‖v‖)
    (hcolumn : ‖centeredProjection S (K (uniformVector T))‖ ≤ e)
    (hlower : ∀ v : centeredSpace T, ‖centeredProjection S (K (v:H))‖ ≤ d*‖v‖) :
    ‖localBlock S T K‖ ≤ s+100*e^2 := by
  apply block_operator_norm_le _ hs hs' he he' hd hd'
  · intro x
    rw [localBlock_fst]
    calc
      _ ≤ ‖x.fst * inner ℂ (uniformVector S) (K (uniformVector T))‖ +
          ‖inner ℂ (uniformVector S) (K (x.snd:H))‖ := norm_add_le _ _
      _ ≤ ‖x.fst‖*s + e*‖x.snd‖ := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hscalar (norm_nonneg _)) (hrow x.snd)
      _ = _ := by ring
  · intro x
    change ‖((localBlock S T K x).snd : H)‖ ≤ _
    rw [localBlock_snd]
    calc
      _ ≤ ‖x.fst • centeredProjection S (K (uniformVector T))‖ +
          ‖centeredProjection S (K (x.snd:H))‖ := norm_add_le _ _
      _ ≤ ‖x.fst‖*e + d*‖x.snd‖ := by
        rw [norm_smul]
        exact add_le_add (mul_le_mul_of_nonneg_left hcolumn (norm_nonneg _)) (hlower x.snd)
      _ = _ := by ring

end Ostmann.Supply

end

end OAI
