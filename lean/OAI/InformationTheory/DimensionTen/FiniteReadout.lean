import OAI.InformationTheory.SecretKey.Main

namespace OAI

/-! Key rates for protocols with finite total terminal readouts. -/

noncomputable section
open Matrix MeasureTheory Filter
open scoped ComplexOrder Kronecker ENNReal

namespace DimensionTen
universe u

structure AdmittedKeyTrial {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : ZeroKey.Density R)
    (ell : ℕ) where
  messages : ZeroKey.ClassicalRecordSpace.{u}
  implementation : ZeroKey.KeyImplementation a b ell messages
  eveDim : ℕ
  purification : Matrix (Fin a × Fin b) (Fin eveDim) ℂ
  prepares : purification * purificationᴴ = R
  referenceMeasure : Measure (ℕ → messages)
  sigmaFinite : SigmaFinite referenceMeasure
  dominates : implementation.discussion.transcriptLaw ≪ referenceMeasure
  ideal : ZeroKey.EveDensity referenceMeasure (Fin eveDim)
attribute [instance] AdmittedKeyTrial.sigmaFinite

namespace AdmittedKeyTrial
variable {a b ell : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    {R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ} {hR : ZeroKey.Density R}
    (p : AdmittedKeyTrial.{u} R hR ell)

def actual : ZeroKey.KeyDensity p.referenceMeasure (ZeroKey.KeyWord ell) (Fin p.eveDim) :=
  p.implementation.output R hR p.purification p.prepares p.referenceMeasure p.dominates

def error : ℝ := p.actual.idealError p.ideal

def toCompleted : ZeroKey.CompletedKeyTrial.{u} R hR ell where
  messages := p.messages
  eveDim := p.eveDim
  purification := p.purification
  prepares := p.prepares
  referenceMeasure := p.referenceMeasure
  sigmaFinite := p.sigmaFinite
  actual := p.actual
  completed := ZeroKey.IsCompletedKeyOutput.of_implementation p.implementation p.dominates
  ideal := p.ideal

lemma toCompleted_error : p.toCompleted.error = p.error := rfl
end AdmittedKeyTrial

structure AdmittedKeyScheme {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : ZeroKey.Density R) where
  length : ℕ → ℕ
  trial : (k : ℕ) → AdmittedKeyTrial.{u} (ZeroKey.positiveCopies R k)
    (hR.positiveCopies k) (length k)

namespace AdmittedKeyScheme
variable {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    {R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ} {hR : ZeroKey.Density R}
    (s : AdmittedKeyScheme.{u} R hR)

def Secure : Prop := Tendsto (fun k => (s.trial k).error) atTop (nhds 0)

def lowerRate : ℝ≥0∞ :=
  liminf (fun k : ℕ => (s.length k : ℝ≥0∞) / (k+1 : ℕ)) atTop

def toCompleted : ZeroKey.CompletedKeyScheme.{u} R hR where
  length := s.length
  trial k := (s.trial k).toCompleted

lemma toCompleted_secure (hs : s.Secure) : s.toCompleted.Secure := hs

lemma toCompleted_lowerRate : s.toCompleted.lowerRate = s.lowerRate := rfl
end AdmittedKeyScheme

def distillableSecretKey {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : ZeroKey.Density R) : ℝ≥0∞ :=
  sSup {r | r = 0 ∨ ∃ s : AdmittedKeyScheme.{u} R hR, s.Secure ∧ r = s.lowerRate}

lemma distillableSecretKey_le_completed {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : ZeroKey.Density R) :
    distillableSecretKey.{u} R hR ≤ ZeroKey.distillableSecretKey.{u} R hR := by
  apply sSup_le
  intro r hr
  apply le_sSup
  rcases hr with hz | ⟨s,hs,hr⟩
  · exact Or.inl hz
  · exact Or.inr ⟨s.toCompleted,s.toCompleted_secure hs,hr⟩

lemma distillableSecretKey_zero_of_inClass {a b : ℕ}
    [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : ZeroKey.Density R)
    (hc : ZeroKey.InClass R) : distillableSecretKey.{u} R hR = 0 := by
  apply le_antisymm _ bot_le
  exact (distillableSecretKey_le_completed R hR).trans
    (le_of_eq (ZeroKey.class_distillableSecretKey_zero R hR hc))

end DimensionTen

end

end OAI
