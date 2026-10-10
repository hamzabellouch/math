import OAI.Analysis.MutuallyUnbiased.Tao.TaoTarget

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

def knownParams8 : List (Charge × Coeff) := [(![-1, -1, 0, 0, 1, 1], (-144, 0)), (![-1, -1, 0, 1, 0, 1], (-144, 0)), (![-1, -1, 0, 1, 1, 0], (0, -144)), (![-1, -1, 1, 0, 0, 1], (144, 144)), (![-1, -1, 1, 0, 1, 0], (-144, 0)), (![-1, -1, 1, 1, 0, 0], (-144, 0)), (![-1, 0, -1, 0, 1, 1], (0, -144)), (![-1, 0, -1, 1, 0, 1], (-144, 0)), (![-1, 0, -1, 1, 1, 0], (-144, 0)), (![-1, 0, 0, -1, 1, 1], (-144, 0)), (![-1, 0, 0, 1, -1, 1], (144, 144)), (![-1, 0, 0, 1, 1, -1], (-144, 0)), (![-1, 0, 1, -1, 0, 1], (-144, 0)), (![-1, 0, 1, -1, 1, 0], (144, 144)), (![-1, 0, 1, 0, -1, 1], (-144, 0))]

def knownTarget8 : Sparse := [([0, -1, -1, 0, 0, 1, 1], -144), ([0, -1, -1, 0, 1, 0, 1], -144), ([0, -1, -1, 1, 0, 0, 1], 144), ([0, -1, -1, 1, 0, 1, 0], -144), ([0, -1, -1, 1, 1, 0, 0], -144), ([0, -1, 0, -1, 1, 0, 1], -144), ([0, -1, 0, -1, 1, 1, 0], -144), ([0, -1, 0, 0, -1, 1, 1], -144), ([0, -1, 0, 0, 1, -1, 1], 144), ([0, -1, 0, 0, 1, 1, -1], -144), ([0, -1, 0, 1, -1, 0, 1], -144), ([0, -1, 0, 1, -1, 1, 0], 144), ([0, -1, 0, 1, 0, -1, 1], -144), ([1, -1, -1, 0, 1, 1, 0], -144), ([1, -1, -1, 1, 0, 0, 1], 144), ([1, -1, 0, -1, 0, 1, 1], -144), ([1, -1, 0, 0, 1, -1, 1], 144), ([1, -1, 0, 1, -1, 1, 0], 144)]

theorem knownTarget8_checked : normalize (knownTerms knownParams8) = knownTarget8 := by
  decide +kernel

theorem knownParams8_valid : knownParams8.Forall (fun p =>
    Balanced p.1 ∧ order p.1 = 2 ∧ mul p.2 (counts p.1) = (-432, 0)) := by
  unfold Balanced
  decide +kernel

theorem knownTarget8_value (f : Charge → ℂ) (hf : OrderTwoValues f) :
    Certificate.Integer.Sparse.eval knownTarget8 (momentValues f) = 216 := by
  rw [← knownTarget8_checked, eval_normalize,
    eval_knownTerms f hf knownParams8 (-432) knownParams8_valid]
  norm_num [knownParams8]

end MUB6.TaoCertificate

end OAI
