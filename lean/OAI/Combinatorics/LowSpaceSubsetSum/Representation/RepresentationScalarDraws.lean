import OAI.Combinatorics.LowSpaceSubsetSum.Counting.ScalarSamplerArrays

namespace OAI

/-! # The nested prime draw at the actually stored widths

Equality witnesses transport only the seed types. The called sampler reads
the three widths from the supplied integer array.
-/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationScalarDraws

variable {n : ℕ}

abbrev Seed (n : ℕ) (widths : Vector ℕ 4) :=
  (triplePrimeCoupling n widths[0] widths[1] widths[2]).Seed

def nested (n : ℕ) (widths : Vector ℕ 4) (s : Seed n widths) : Option (Vector ℕ 3) × ℕ :=
  ScalarSamplerArrays.nested n widths[0] widths[1] widths[2] s

def transport {w w' : Vector ℕ 4} (h : w = w') (s : Seed n w') : Seed n w := h.symm ▸ s

theorem nested_transport {w w' : Vector ℕ 4} (h : w = w') (s : Seed n w') :
    nested n w (transport h s) = nested n w' s := by
  subst w'
  rfl

def sourceWidths (R : RepresentationSetup n) (z : RepresentationSetup.Layout n) : Vector ℕ 4 :=
  Vector.ofFn (R.samplerPrimeWidths z)

theorem widths_eq (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (widths : Vector ℕ 4) (h : ∀ j : Fin 4, widths[j.val] = R.samplerPrimeWidths z j) :
    widths = sourceWidths R z := by
  apply Vector.ext
  intro i hi
  simpa only [sourceWidths, Vector.getElem_ofFn] using h ⟨i, hi⟩

def draw (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (widths : Vector ℕ 4) (h : ∀ j : Fin 4, widths[j.val] = R.samplerPrimeWidths z j)
    (s : (R.nestedCoupling z).Seed) : Option (Vector ℕ 3) × ℕ :=
  nested n widths (transport (widths_eq R z widths h) s)

theorem draw_value (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (widths : Vector ℕ 4) (h : ∀ j : Fin 4, widths[j.val] = R.samplerPrimeWidths z j)
    (s : (R.nestedCoupling z).Seed) :
    (draw R z widths h s).1 =
      ((R.nestedCoupling z).bounded s).map (fun p => ScalarSamplerArrays.factors p.val) := by
  exact (congrArg Prod.fst (nested_transport (n := n) (widths_eq R z widths h)
    (show Seed n (sourceWidths R z) from s))).trans
    (ScalarSamplerArrays.nested_value n (R.factorExponents z 0)
      (R.factorExponents z 1) (R.factorExponents z 2) s)

theorem draw_work (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (widths : Vector ℕ 4) (h : ∀ j : Fin 4, widths[j.val] = R.samplerPrimeWidths z j)
    (s : (R.nestedCoupling z).Seed) :
    (draw R z widths h s).2 ≤ 3 * n ^ 3 + 3 * SamplerExecution.primeTestBudget n + 7 := by
  calc
    _ = (nested n (sourceWidths R z) (show Seed n (sourceWidths R z) from s)).2 :=
      congrArg Prod.snd (nested_transport (n := n) (widths_eq R z widths h)
        (show Seed n (sourceWidths R z) from s))
    _ ≤ _ := ScalarSamplerArrays.nested_work (R.factorExponents_le_n z 0)
      (R.factorExponents_le_n z 1) (R.factorExponents_le_n z 2) s

end LowSpaceSubsetSum.RepresentationScalarDraws

end

end OAI
