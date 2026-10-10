import OAI.Geometry.HeilbronnTriangle.MainResidueSystem
import OAI.Geometry.HeilbronnTriangle.DigitColumnLaw
import OAI.Geometry.HeilbronnTriangle.SmithDigitMoment
import OAI.Geometry.HeilbronnTriangle.ParameterSequence

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT Problem355.heilbronnM

namespace Problem355.MainDigitLaw

open Parameters FiniteFieldLabels
open scoped BigOperators

variable {r : ℕ} [Fact r.Prime]

abbrev Sample (r : ℕ) := Fin (r ^ 9)
abbrev Latent (r : ℕ) [Fact r.Prime] :=
  DigitColumnLaw.Latent (Label r) (Sample r) heilbronnK
abbrev Array (r : ℕ) := DigitColumnLaw.Array (Sample r) heilbronnK

variable (D : PrimeParameterData heilbronnK r)

omit [Fact r.Prime] in
lemma alphabet_bound : r * r ^ 9 < D.B := by
  convert D.alphabet_lt_base using 1
  ring

def digit (label : Label r) (a : Fin 3) (v : Fin heilbronnK)
    (x : Sample r) : Fin D.B :=
  ConditionalMatrix.prescribedDigit (alphabet_bound D)
    (fun i _ w => MainResidueSystem.finiteResidue r i w label) a 0 v x

lemma digit_injective (label : Label r) (a : Fin 3) (v : Fin heilbronnK) :
    Function.Injective (digit D label a v) :=
  ConditionalMatrix.prescribedDigit_injective (alphabet_bound D)
    (fun i _ w => MainResidueSystem.finiteResidue r i w label) a 0 v

lemma digit_positive (label : Label r) (a : Fin 3) (v : Fin heilbronnK)
    (x : Sample r) : 0 < (digit D label a v x).val :=
  ConditionalMatrix.prescribedDigit_positive (alphabet_bound D)
    (fun i _ w => MainResidueSystem.finiteResidue r i w label) a 0 v x

lemma digit_le (label : Label r) (a : Fin 3) (v : Fin heilbronnK)
    (x : Sample r) : (digit D label a v x).val ≤ r ^ 10 := by
  have hb := (DigitUnits.digitFiberEquiv_bounds
    (MainResidueSystem.finiteResidue r a v label) (r ^ 9) x).2.1
  change (digit D label a v x).val ≤ r * r ^ 9 at hb
  convert hb using 1
  ring

lemma digit_residue (label : Label r) (a : Fin 3) (v : Fin heilbronnK)
    (x : Sample r) :
    ((digit D label a v x).val : ZMod r) =
      MainResidueSystem.finiteResidue r a v label :=
  ConditionalMatrix.prescribedDigit_residue (alphabet_bound D)
    (fun i _ w => MainResidueSystem.finiteResidue r i w label) a 0 v x

def column (x : Latent r) : Fin 3 → ZMod (D.B ^ heilbronnK) :=
  @DigitColumnLaw.residueColumn (Label r) (Sample r) D.B heilbronnK (digit D) x

def arrayDigit (labels : Fin 3 → Label r) :
    Fin 3 → Fin 3 → Fin heilbronnK → Sample r → Fin D.B :=
  fun a c v x => digit D (labels c) a v x

def matrix (labels : Fin 3 → Label r) (f : Array r) :
    Matrix (Fin 3) (Fin 3) (ZMod (D.B ^ heilbronnK)) :=
  @ConditionalMatrix.arrayMatrix (Sample r) D.B heilbronnK
    (arrayDigit D labels) f heilbronnK

lemma column_matrix (s : Fin 3 → Latent r) :
    (fun a c => column D (s c) a) =
      matrix D (DigitColumnLaw.tripleEquiv s).1 (DigitColumnLaw.tripleEquiv s).2 := rfl

def smith (labels : Fin 3 → Label r) (f : Array r) :
    PrimePowerData D.B heilbronnK (matrix D labels f) :=
  PrimePowerData.ofArray (X := Sample r) (B := D.B) (k := heilbronnK)
    D.base_prime heilbronnK_pos (arrayDigit D labels)
    (fun a c v x => digit_positive D (labels c) a v x) f

omit [Fact r.Prime] in
lemma moment_parameter :
    (D.B : ℝ) * (1 / (Fintype.card (Sample r) : ℝ)) ^ 4 ≤ 1 / 2 := by
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast D.r_pos.ne'
  have hid : (r : ℝ) / (r : ℝ) ^ 10 = 1 / (r : ℝ) ^ 9 := by
    field_simp
  simpa only [Sample, Fintype.card_fin, Nat.cast_pow, hid] using D.digit_moment_bound

theorem conditional_moment (labels : Fin 3 → Label r) :
    (∑ f : Array r, DigitColumnLaw.uniformWeight (Array r) f *
      (D.B : ℝ) ^ (smith D labels f).b) ≤ 2 := by
  let : NeZero (r ^ 9) := ⟨pow_ne_zero _ D.r_pos.ne'⟩
  exact PrimePowerData.array_moment_le_two (X := Sample r) (B := D.B) (k := heilbronnK)
    D.base_prime heilbronnK_pos
    (arrayDigit D labels) (fun a c v => digit_injective D (labels c) a v)
    (fun a c v x => digit_positive D (labels c) a v x)
    (smith D labels) (moment_parameter D)

theorem triple_moment [Fintype (Label r)] :
    (∑ s : Fin 3 → Latent r,
      ConditionalSamples.productWeight (DigitColumnLaw.uniformWeight (Latent r)) s *
        (D.B : ℝ) ^ (smith D (DigitColumnLaw.tripleEquiv s).1
          (DigitColumnLaw.tripleEquiv s).2).b) ≤ 2 :=
  DigitColumnLaw.expectation_triple_le _ 2 (conditional_moment D)

end Problem355.MainDigitLaw

end

end OAI
