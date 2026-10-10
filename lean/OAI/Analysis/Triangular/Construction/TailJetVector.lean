import OAI.Analysis.Triangular.Schwartz.SpectralEnvelope
import OAI.Analysis.Triangular.Envelope.JetEnvelopeAnalytic

namespace OAI

noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction
abbrev JetVector := PiLp 1 (fun _ : Fin 2 => ℂ)
def jetVector (k v : ℝ) (n : ℤ) (t : ℝ) : JetVector :=
  WithLp.toLp 1 (fun d => jetMultiplier k v n d t)
lemma continuous_jetMultiplier {k : ℝ} (hk : 0<k) (v : ℝ) (n : ℤ) (d : Fin 2) :
    Continuous (jetMultiplier k v n d) := by
  have hl : Continuous (lambda k) := by
    unfold lambda
    apply Continuous.div
    · fun_prop
    · unfold waveDen; fun_prop
    · intro t; exact_mod_cast (mul_pos b_pos (waveDen_pos hk t)).ne'
  have hX : Continuous (Xwave k) := by
    unfold Xwave
    exact continuous_const.div (by unfold waveDen; fun_prop) (fun t => (waveDen_pos hk t).ne')
  have hz : Continuous (zeta k v) := by unfold zeta; fun_prop
  unfold jetMultiplier transformedWave
  split_ifs <;> fun_prop
lemma continuous_jetVector {k : ℝ} (hk : 0<k) (v : ℝ) (n : ℤ) :
    Continuous (jetVector k v n) := by
  exact (PiLp.continuousLinearEquiv 1 ℂ (fun _ : Fin 2 => ℂ)).symm.continuous.comp
    (continuous_pi (fun d => continuous_jetMultiplier hk v n d))
lemma jetVector_norm_bound (k v t : ℝ) (n : ℤ) (hQ : 0<Q n) :
    ‖jetVector k v n t‖  ≤  normJetEnvelope k v n t := by
  rw [PiLp.norm_eq_of_L1]
  exact jetMultiplier_pair_bound k v t n hQ

def tailJetVector (k v : ℝ) (m n : ℤ) (c : Fin 2) : JetVector :=
  if c.val=0 then spectralCVector n (jetVector k v m) else spectralDVector n (jetVector k v m)
def tailJet (k v : ℝ) (m n : ℤ) (c d : Fin 2) : ℝ :=
  (tailJetVector k v m n c d).re
lemma finiteEndpoint (i : Fin 15) :
    frequency ⟨i.val+16,by omega⟩ = (i.val+1:ℕ)/18 := by
  unfold frequency
  push_cast
  ring
lemma tailJetVector_bound (q v : Fin 2) (m n : ℤ) (hm : 1 ≤ m) (hQ : 0<Q m) (c : Fin 2) :
    ‖tailJetVector (damping q) (damping v) m n c‖  ≤ 
      ∑ i : Fin 15, normJetEnvelope (damping q) (damping v) m (frequency ⟨i.val+16,by omega⟩) * fullTailW i c := by
  have hh (i : Fin 15) (x : ℝ) (h1 : (i.val:ℝ)/18 ≤ |x|) (h2 : |x| ≤ (i.val+1:ℕ)/18) :
      ‖jetVector (damping q) (damping v) m x‖  ≤ 
      normJetEnvelope (damping q) (damping v) m (frequency ⟨i.val+16,by omega⟩) := by
    apply (jetVector_norm_bound _ _ _ _ hQ).trans
    rw [←normJetEnvelope_abs _ _ x m (damping_pos q),finiteEndpoint]
    apply normJetEnvelope_monotone hm hQ (abs_nonneg x) h2
    have hi : ((i.val+1:ℕ):ℝ) ≤ 15 := by exact_mod_cast (show i.val+1 ≤ 15 by omega)
    linarith
  fin_cases c
  · exact spectralCVector_bound n _ (continuous_jetVector (damping_pos q) _ _) _ hh
  · exact spectralDVector_bound n _ (continuous_jetVector (damping_pos q) _ _) _ hh
lemma tailJet_pair_bound (q v : Fin 2) (m n : ℤ) (hm : 1 ≤ m) (hQ : 0<Q m) (c : Fin 2) :
    (∑ d : Fin 2, |tailJet (damping q) (damping v) m n c d|)  ≤ 
      ∑ i : Fin 15, normJetEnvelope (damping q) (damping v) m (frequency ⟨i.val+16,by omega⟩) * fullTailW i c := by
  apply le_trans _ (tailJetVector_bound q v m n hm hQ c)
  rw [PiLp.norm_eq_of_L1]
  exact Finset.sum_le_sum (fun d _ => Complex.abs_re_le_norm _)
end AtomicTriangular.Construction
end

end OAI
