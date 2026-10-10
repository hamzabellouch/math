import OAI.Analysis.Triangular.Taylor.CoefficientSpectral

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set MeasureTheory
namespace AtomicTriangular.Construction

def jetFunction (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) : C(Spectrum,ℂ) :=
  ⟨fun t => jetMultiplier (damping q) v n d t.val,
    (continuous_jetMultiplier (damping_pos q) v n d).comp continuous_subtype_val⟩
lemma jetFunction_apply (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) (t : Spectrum) :
    jetFunction q v n d t=jetMultiplier (damping q) v n d t.val := rfl

def negativeJet (v : ℝ) (n : ℤ) (d : Fin 2) (a b : ℂ) : ℂ :=
  exp (Real.pi*(v-h)*(n:ℂ))*(Q n:ℂ)⁻¹*
    (if d.val=0 then -a else ((D n:ℂ)-Real.pi*(v-h))*a-b)
lemma zeta_change (k v t : ℝ) : I*Real.pi*zeta k v t =
    (Real.pi*(v-h):ℂ)+I*Real.pi*zeta k h t := by
  unfold zeta
  push_cast
  ring_nf
  simp [I_sq]
  ring
lemma transformedWave_change (k v t : ℝ) (s : ℂ) : transformedWave k v t s=
    exp (Real.pi*(v-h)*s)*transformedWave k h t s := by
  unfold transformedWave
  rw [zeta_change,add_mul,exp_add]
  ring
lemma negativeJet_wave (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) (t : ℝ) :
    negativeJet v n d (finiteWaveJet q 1 t 0 n) (finiteWaveJet q 1 t 1 n)=
      jetMultiplier (damping q) v n d t := by
  simp only [finiteWaveJet,taylorPhase,taylorAmplitude,Fin.val_one,Nat.one_ne_zero,↓reduceIte,pow_zero,pow_one,mul_one]
  unfold negativeJet jetMultiplier
  rw [transformedWave_change]
  unfold transformedWave
  rw [zeta_change (damping q) v t]
  split_ifs <;> ring
lemma negativeJet_linear (T : C(Spectrum,ℂ) →L[ℂ] ℂ) (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    negativeJet v n d (T (waveFunctionJet q 1 0 n)) (T (waveFunctionJet q 1 1 n))=
      T (jetFunction q v n d) := by
  have he : jetFunction q v n d =
      (exp (Real.pi*(v-h)*(n:ℂ))*(Q n:ℂ)⁻¹) •
        (if d.val=0 then -waveFunctionJet q 1 0 n else
          ((D n:ℂ)-Real.pi*(v-h)) • waveFunctionJet q 1 0 n-waveFunctionJet q 1 1 n) := by
    ext t
    simp only [ContinuousMap.smul_apply,smul_eq_mul,jetFunction_apply]
    split_ifs with hd
    · simpa only [negativeJet,hd,↓reduceIte,ContinuousMap.neg_apply,ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul,waveFunctionJet_apply] using (negativeJet_wave q v n d t.val).symm
    · simpa only [negativeJet,hd,↓reduceIte,ContinuousMap.neg_apply,ContinuousMap.sub_apply,ContinuousMap.smul_apply,smul_eq_mul,waveFunctionJet_apply] using (negativeJet_wave q v n d t.val).symm
  rw [he]
  unfold negativeJet
  split_ifs <;> simp only [map_smul,map_neg,map_sub,smul_eq_mul]
lemma finiteSpectral_jet (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    (finiteSpectral (coefficientInput C a w) (jetFunction q v n d)).re=
      ∑ c : Fin 22, a c*jet (damping q) v n d (finiteColumn ⟨c.val,by omega⟩) := by
  rw [finiteSpectral_coefficient_apply]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [mul_re]
  simp only [ofReal_re,ofReal_im,zero_mul,sub_zero]
  congr 1
  unfold jet
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [jetFunction_apply,mul_comm]
lemma spectralP_jet (q : Fin 2) (v : ℝ) (n : ℤ) (d : Fin 2) :
    (spectralP (jetFunction q v n d)).re=jet (damping q) v n d (finiteColumn 22) := by
  unfold spectralP jet
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change fourierCoeff j*jetMultiplier _ _ _ _ _ = jetMultiplier _ _ _ _ _*fourierCoeff j
  ring
end AtomicTriangular.Construction
end

end OAI
