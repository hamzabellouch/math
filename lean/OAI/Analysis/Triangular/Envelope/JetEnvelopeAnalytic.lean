import OAI.Analysis.Triangular.Envelope.EnvelopeBoxes

namespace OAI

noncomputable section
open scoped BigOperators
open Complex
namespace AtomicTriangular.Construction
lemma norm_transformedWave (k v t : ℝ) (n : ℤ) :
    ‖transformedWave k v t n‖ = ‖lambda k t‖ * Real.exp (-frequencyDecay k v t*n) := by
  rw [transformedWave,norm_mul,Complex.norm_exp]
  congr 2
  rw [show I*Real.pi*zeta k v t*(n:ℂ) = (I*Real.pi*zeta k v t)*(n:ℂ) by rfl,
    Complex.mul_re,Complex.intCast_re,Complex.intCast_im,mul_zero,sub_zero,wavePhase_re]
  unfold frequencyDecay
  ring
lemma jetMultiplier_pair_bound (k v t : ℝ) (n : ℤ) (hQ : 0<Q n) :
    (∑ d : Fin 2, ‖jetMultiplier k v n d t‖) ≤ normJetEnvelope k v n t := by
  have hqi : ‖(Q n:ℂ)⁻¹‖=(Q n)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ]
  have hb : ‖(D n:ℂ)-I*Real.pi*zeta k v t‖ ≤ |D n|+‖I*Real.pi*zeta k v t‖ := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using norm_sub_le (D n:ℂ) (I*Real.pi*zeta k v t)
  simp only [Fin.sum_univ_two,jetMultiplier,Fin.val_zero,Fin.val_one,one_ne_zero,
    ↓reduceIte,norm_mul,norm_neg,norm_one,mul_one,hqi,norm_transformedWave]
  calc
    _ ≤ (Q n)⁻¹*(‖lambda k t‖*Real.exp (-frequencyDecay k v t*n)) +
        (Q n)⁻¹*(‖lambda k t‖*Real.exp (-frequencyDecay k v t*n))*(|D n|+‖I*Real.pi*zeta k v t‖) := by
      gcongr
    _ = _ := by unfold normJetEnvelope; ring
lemma jet_pair_bound (k v : ℝ) (n : ℤ) (hQ : 0<Q n) (S : Fin 31 → ℂ) :
    (∑ d : Fin 2, |jet k v n d S|) ≤
      ∑ j : Fin 31, normJetEnvelope k v n (frequency j)*‖S j‖ := by
  calc
    _ ≤ ∑ d : Fin 2, ∑ j : Fin 31, ‖jetMultiplier k v n d (frequency j)‖*‖S j‖ := by
      apply Finset.sum_le_sum
      intro d _
      apply (Complex.abs_re_le_norm _).trans
      simpa only [norm_mul] using norm_sum_le (s:=Finset.univ)
        (fun j : Fin 31 => jetMultiplier k v n d (frequency j)*S j)
    _ = ∑ j : Fin 31, (∑ d : Fin 2, ‖jetMultiplier k v n d (frequency j)‖)*‖S j‖ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (jetMultiplier_pair_bound k v (frequency j) n hQ) (norm_nonneg _))
lemma normJetEnvelope_nonneg (k v t : ℝ) (n : ℤ) (hQ : 0<Q n) :
    0≤normJetEnvelope k v n t := by unfold normJetEnvelope; positivity
lemma normJetEnvelope_even (k v t : ℝ) (n : ℤ) (hk : 0<k) :
    normJetEnvelope k v n (-t)=normJetEnvelope k v n t := by
  rw [normJetEnvelope_eq hk,normJetEnvelope_eq hk]
  simp [jetEnvelope,Xwave,waveDen]
lemma normJetEnvelope_abs (k v t : ℝ) (n : ℤ) (hk : 0<k) :
    normJetEnvelope k v n |t|=normJetEnvelope k v n t := by
  rcases le_total 0 t with ht|ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht,normJetEnvelope_even k v t n hk]
lemma normJetEnvelope_monotone {q v : Fin 2} {n : ℤ} (hn : 1≤n) (hQ : 0<Q n)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 5 / 6) :
    normJetEnvelope (damping q) (damping v) n s≤normJetEnvelope (damping q) (damping v) n t := by
  rw [normJetEnvelope_eq (damping_pos q),normJetEnvelope_eq (damping_pos q)]
  exact jetEnvelope_monotone hn hQ hs hst ht
end AtomicTriangular.Construction
end

end OAI
