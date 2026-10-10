import OAI.Combinatorics.ParityLifts.UniformPost

namespace OAI

namespace ParityWL.Complexity

noncomputable def trialCode (c : Convention) (M : Machine) : FCode :=
  .seq trialNormalizeProgram.program.code (uniformPostCode (uniformLeafDecisionCode c M))

lemma trialCode_rate : ∃ D P : ℕ, 0<D ∧ 0<P ∧
    ∀ c : Convention, ∀ i : Implementation, ∀ M : Machine, ∀ f g : ℕ → ℝ,
    UniformWLBound M c i f g → ∀ j : ℕ, 0<j → ∀ k : ℕ, 4 ≤ k →
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧ ∀ {N : ℕ} (F : Formula N), ∃ s b,
      Emits (trialCode c M).decision (trialInput j k (encodeFormula F)) s b ∧
      (b=true↔F.Satisfiable) ∧
      (s : ℝ) ≤ C*((encodeFormula F).length+1 : ℝ)^(2*trialNormalizeProgram.degree+2)*
        2^(((D : ℝ)/j+(P : ℝ)*(g k+1)*leafSlope (bagParameter c k) (12*j)+ε)*N) := by
  obtain ⟨P,hP,hLeaf⟩ := uniformLeafCost_rate
  obtain ⟨D,hD,hPost⟩ := uniformPostCode_rate
  refine ⟨2*D,2*P,by positivity,by positivity,?_⟩
  intro c i M f g hm j hj k hk ε hε
  obtain ⟨C,hC,hRun⟩ := uniformLeafMachine_run k hk c i M f g hm
  obtain ⟨W,hW,hWF⟩ := hLeaf k hk c (12*j) M C (g k) hC (hm.2.1 k)
  have hr : 0 ≤ (P : ℝ)*(g k+1)*leafSlope (bagParameter c k) (12*j) :=
    mul_nonneg (by have := hm.2.1 k; positivity) (leafSlope_nonneg _ _)
  obtain ⟨R,hR,hRF⟩ := hPost j hj k (uniformLeafDecisionCode c M) W _ hr hW (by
    intro N F hs hn hw
    obtain ⟨b,hb,he⟩ := hRun F hw
    exact ⟨b,hb.mono (hWF N F hs hn),he⟩)
  obtain ⟨A,hA,hPre⟩ := poly_bit_input_bound trialNormalizeProgram
  obtain ⟨B,hB,hPostBound⟩ := hR.absorb (ε/2) (by positivity)
  let H : ℕ := j+k+3
  let V : ℝ := 500*((trialCode c M).factor+2 : ℝ)*((trialCode c M).depth+2 : ℝ)
  have hV : 0 ≤ V := by
    dsimp only [V]
    exact mul_nonneg (mul_nonneg (by norm_num) (by exact_mod_cast (Nat.zero_le ((trialCode c M).factor+2))))
      (by exact_mod_cast (Nat.zero_le ((trialCode c M).depth+2)))
  let C' : ℝ := (V*(A+B+2)^2+64)*H^(2*trialNormalizeProgram.degree+2)
  refine ⟨C',by dsimp [C',V,H]; positivity,?_⟩
  intro N F
  let bs := encodeFormula F
  let inp := trialInput j k bs
  have hlen : inp.length+1 ≤ H*(bs.length+1) := by
    simp only [inp,trialInput,List.length_append,List.length_replicate,List.length_cons,H]
    nlinarith
  obtain ⟨b,hb,he⟩ := hRF F
  have hn := (trialNormalizeProgram.program.run inp).real
  rw [show trialNormalize inp=((j,k),minimizeList F.bitList) from trialNormalize_encode j k F] at hn
  obtain ⟨s,hs,hcost⟩ := (hn.seq hb).decision
  refine ⟨s,b,hs,he,?_⟩
  let rate : ℝ := (D : ℝ)/j+(P : ℝ)*(g k+1)*leafSlope (bagParameter c k) (12*j)+ε/2
  have hrate : 0 ≤ rate := by dsimp [rate]; positivity
  have hcost' : (s : ℝ) ≤ V*((trialNormalizeProgram.program.time inp : ℝ)+R N+2)^2+44*inp.length+20 := by
    convert hcost using 1
    dsimp only [V,trialCode]; ring
  have hc := decision_numeric_bound V A B rate trialNormalizeProgram.degree inp.length N
    (trialNormalizeProgram.program.time inp) (R N) s hV
    hA.le hB.le hrate (Nat.cast_nonneg _) (hR.1 N) (hPre inp)
    (hPostBound N) hcost'
  -- Account for the fixed unary parameter header independently of N and of the input degree.
  have hpp : (inp.length+1 : ℝ)^(2*trialNormalizeProgram.degree+2) ≤
      (H : ℝ)^(2*trialNormalizeProgram.degree+2)*(bs.length+1 : ℝ)^(2*trialNormalizeProgram.degree+2) := by
    rw [←mul_pow]; gcongr; exact_mod_cast hlen
  -- A larger parameter-dependent coefficient is harmless; the degree is global.
  have hh := hc.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpp (by nlinarith [sq_nonneg (A+B+2),mul_nonneg hV (sq_nonneg (A+B+2))])) (Real.rpow_nonneg (by norm_num) _))
  have heRate : 2*rate=((2*D : ℕ) : ℝ)/j+((2*P : ℕ) : ℝ)*(g k+1)*leafSlope (bagParameter c k) (12*j)+ε := by
    dsimp only [rate]
    push_cast
    ring
  rw [heRate] at hh
  simpa only [C',bs,mul_assoc] using hh

end ParityWL.Complexity

end OAI
