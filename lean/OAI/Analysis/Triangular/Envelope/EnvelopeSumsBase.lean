import OAI.Analysis.Triangular.Envelope.EnvelopeBoxes

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction

def finiteEnvelopeSum (q v : Fin 2) (j : Fin 31) : ℝ :=
  ∑ n : Fin 10, normJetEnvelope (damping q) (damping v) (finiteNode n) (frequency j)
def tailEnvelopeSum (q v : Fin 2) (j : Fin 31) : ℝ :=
  (∑ a : Fin 15, normJetEnvelope (damping q) (damping v) (tailBase a) (frequency j)) *
    (1-Real.exp (-frequencyDecay (damping q) (damping v) (frequency j)*36))⁻¹

def finiteTailEnvelope (d : Fin 2) : ℝ :=
  ∑ i : Fin 15, finiteEnvelopeSum 0 1 ⟨i.val+16,by omega⟩ * fullTailW i d
def tailTailEnvelope (d : Fin 2) : ℝ :=
  ∑ i : Fin 15, tailEnvelopeSum 0 0 ⟨i.val+16,by omega⟩ * fullTailW i d
def tailFiniteEnvelope (c : Fin 22) : ℝ :=
  ∑ j : Fin 31, tailEnvelopeSum 1 0 j * ‖finiteColumn ⟨c.val,by omega⟩ j‖
def tailConstantEnvelope : ℝ :=
  ∑ j : Fin 31, tailEnvelopeSum 0 0 j * ‖fourierCoeff j‖
end AtomicTriangular.Construction
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma ri_mem_lt {a : RI} {x : ℝ} (hx : a.Mem x) (p : ℤ) (q : ℕ) (hq : 0<q)
    (h : a.hi*q < p*scale) : x < p/q := by
  have hh : (a.hi:ℝ)*(q:ℝ) < p*(scale:ℝ) := by exact_mod_cast h
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  apply (lt_div_iff₀ hqR).mpr
  have hx' := mul_le_mul_of_nonneg_right hx.2 hqR.le
  exact (mul_lt_mul_iff_right₀ scale_pos).mp (by nlinarith)
end AtomicTriangular.FiniteCertificate
end

end OAI
