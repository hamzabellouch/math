import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.IntegralProgram

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open LocalSearch Anchoring Completion Sampling Sampling.Comparison FiniteSampling IntegralAssembly IntegralCandidates Surplus GlobalAssembly
lemma bounded_count_log (v : ℚ) (Nstar : ℕ) (hv : 0 < v) :
    ∃ A : ℝ, 0 < A ∧ ∀ n N : ℕ, 1≤N → n≤N →
      (countBound (commonL v Nstar n (Rounding.cap n (gamma/16))):ℝ) ≤
        A*Real.log ((N:ℝ)+2) := by
  let C : ℕ := ⌈20/(gamma/16)⌉₊+2
  let B : ℝ := Nstar+3*Real.log (9*C)/Real.log (1+(v:ℝ)^2)+9
  let D : ℝ := 9/Real.log (1+(v:ℝ)^2)
  obtain ⟨A1,hA1,hfirst⟩ := LogPolynomial.affine_log_bound B D
  let R : ℝ := 2+4*Anchoring.countConstant (1/100)/(gamma/16)
  have hR : 0 ≤ R := by
    have := PhaseSurplusProducer.countConstant_ge_ten
    have := gamma_pos
    dsimp [R]
    positivity
  obtain ⟨A,hA,hsecond⟩ := LogPolynomial.affine_log_bound 1 (R*A1)
  refine ⟨A,hA,?_⟩
  intro n N hN hn
  have hCap := cap_polynomial n N hn
  have hbound := commonL_bound v C Nstar n
    (Rounding.cap n (gamma/16)) N 2
    (by exact_mod_cast hv) hN hn (by dsimp [C]; exact_mod_cast (by omega : 1 ≤ ⌈20/(gamma/16)⌉₊+2))
    (Rounding.cap_pos _ _) (by exact_mod_cast hCap)
  have hL : (commonL v Nstar n (Rounding.cap n (gamma/16)):ℝ) ≤
      A1*Real.log ((N:ℝ)+2) := by
    apply le_trans hbound.le
    have ht := hfirst ((N:ℝ)+2) (by linarith [Nat.cast_nonneg (α := ℝ) N])
    calc
      _ = B+D*Real.log ((N:ℝ)+2) := by dsimp only [B,D]; ring
      _ ≤ _ := ht
  have hC := countBound_bound (commonL v Nstar n (Rounding.cap n (gamma/16)))
  calc
    _ ≤ R*(commonL v Nstar n (Rounding.cap n (gamma/16)):ℝ)+1 := hC
    _ ≤ R*(A1*Real.log ((N:ℝ)+2))+1 := by gcongr
    _ = 1+(R*A1)*Real.log ((N:ℝ)+2) := by ring
    _ ≤ _ := hsecond _ (by linarith [Nat.cast_nonneg (α := ℝ) N])

attribute [local irreducible] output BinaryIntegralDispatch.output BinaryIntegralDispatch.budget
  BinaryIntegralRecovery.Guesses.budget BinaryIntegralRecovery.Guesses.output BinaryMetricAnchor.run

theorem uniform_program (e : ℕ) : ∃ v : ℚ, ∃ C : ℕ, ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [MetricSpace (Fin n)] (δ : Fin n→Fin n→ℕ)
    (_hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F : Finset (Fin n)) (k : ℕ)
    (_hD : D.Nonempty) (_hk : 0<k) (_hkF : k≤F.card)
    (_hbound : ∀ x,∀ f∈F,δ x f≤ Rounding.cap D.card (gamma/16))
    (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f),
    let M := Rounding.cap D.card (gamma/16)
    let N := D.card+F.card
    let g := List.replicate N true
    let δQ := fun i j=>(δ i j:ℚ)
    let K := (Dsp.budget Q).eval (Dsp.pack δQ D F M k g []).length
    ∃ S : Finset (Fin n),
      (∀ seed:Fin K→Bool,run v C Q d (Dsp.pack δQ D F M k g (List.ofFn seed))=
        BinaryFinSet.encode (output v C Q d δQ D F S M k g (List.ofFn seed))) ∧
      (∀ seed:Fin K→Bool,output v C Q d δQ D F S M k g (List.ofFn seed)⊆F ∧
        (output v C Q d δQ D F S M k g (List.ofFn seed)).Nonempty ∧
        (output v C Q d δQ D F S M k g (List.ofFn seed)).card≤k ∧
        realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤5*optimum F D k) ∧
      (1-FailureBudget.failure gamma e N≤ probability
        (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤
          (2-gamma)*(1+gamma/16)*optimum F D k)) ∧
      average (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed)))≤
        ((2-gamma)*(1+gamma/16)+5*FailureBudget.failure gamma e N)*optimum F D k := by
  have hT : 0<200*countConstant (1/100) := by linarith [PhaseSurplusProducer.countConstant_ge_ten]
  have hstrict:=strictnessGap_pos hT
  obtain ⟨v,hv,hv1,hvc,hvs⟩:=ParameterBounds.exists_rational_slack _ _ hstrict hT
  have hvR : (0:ℝ)<v := by exact_mod_cast hv
  obtain ⟨Nstar,hNstar,hsize⟩:=ParameterBounds.exists_size_threshold _ _ hstrict hvR
  obtain ⟨A,_,hlog⟩:=bounded_count_log v Nstar hv
  let C : ℕ := ⌈1/v^2⌉₊
  have hv2 : (0:ℚ)<v^2 := sq_pos_of_pos hv
  have hC : 2≤(1+v^2)^C := by
    have ha : (1:ℚ)≤C*v^2 := (div_le_iff₀ hv2).mp (Nat.le_ceil _)
    have hb:=one_add_mul_le_pow (by linarith : (-2:ℚ)≤v^2) C
    linarith
  obtain ⟨Q,d,hQ⟩:=finite_program A e
  refine ⟨v,C,Q,d,?_⟩
  intro n _ δ hδ D F k hD hk hkF hbound hsep
  dsimp only
  let M:=Rounding.cap D.card (gamma/16)
  let N:=D.card+F.card
  let L:=commonL v Nstar D.card M
  have hNL : Nstar≤L := le_max_left _ _
  have hL : 0<L := by omega
  have hlarge (hl:2*L<k) : Nstar≤N := by dsimp [N];omega
  exact hQ δ hδ D F k L M N C v hD hk hL hkF rfl (Rounding.cap_pos _ _) le_rfl
    hbound hsep hvR hv1 hvc hvs (fun hl=>(hsize _ (hlarge hl)).2)
    (fun hl=>(hsize _ (hlarge hl)).1) (le_max_right _ _) hC (List.replicate N true)
    (by simp only [List.length_replicate];rfl) (hlog D.card N (by dsimp [N];omega) (by dsimp [N];omega))
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralAll
open LocalSearch Anchoring Completion Sampling Sampling.Comparison FiniteSampling IntegralAssembly IntegralCandidates Surplus GlobalAssembly
attribute [local irreducible] output BinaryIntegralDispatch.output BinaryIntegralDispatch.budget
  BinaryIntegralRecovery.Guesses.budget BinaryIntegralRecovery.Guesses.output BinaryMetricAnchor.run

theorem uniform_program_long (e : ℕ) : ∃ v : ℚ, ∃ C : ℕ, ∃ Q : Polynomial ℕ, ∃ d : ℕ,
    ∀ {n : ℕ} [MetricSpace (Fin n)] (δ : Fin n→Fin n→ℕ)
    (_hδ : ∀ i j,(δ i j:ℝ)=dist i j) (D F : Finset (Fin n)) (k : ℕ)
    (_hD : D.Nonempty) (_hk : 0<k) (_hkF : k≤F.card)
    (_hbound : ∀ x,∀ f∈F,δ x f≤ Rounding.cap D.card (gamma/16))
    (_hsep : ∀ w∈D,∀ f∈F,(1:ℝ)≤dist w f)
    (g : List Bool) (_hg : D.card+F.card≤g.length),
    let M := Rounding.cap D.card (gamma/16)
    let N := D.card+F.card
    let δQ := fun i j=>(δ i j:ℚ)
    let K := (Dsp.budget Q).eval (Dsp.pack δQ D F M k g []).length
    ∃ S : Finset (Fin n),
      (∀ seed:Fin K→Bool,run v C Q d (Dsp.pack δQ D F M k g (List.ofFn seed))=
        BinaryFinSet.encode (output v C Q d δQ D F S M k g (List.ofFn seed))) ∧
      (∀ seed:Fin K→Bool,output v C Q d δQ D F S M k g (List.ofFn seed)⊆F ∧
        (output v C Q d δQ D F S M k g (List.ofFn seed)).Nonempty ∧
        (output v C Q d δQ D F S M k g (List.ofFn seed)).card≤k ∧
        realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤5*optimum F D k) ∧
      (1-FailureBudget.failure gamma e N≤ probability
        (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed))≤
          (2-gamma)*(1+gamma/16)*optimum F D k)) ∧
      average (fun seed:Fin K→Bool=>realCost D (output v C Q d δQ D F S M k g (List.ofFn seed)))≤
        ((2-gamma)*(1+gamma/16)+5*FailureBudget.failure gamma e N)*optimum F D k := by
  have hT : 0<200*countConstant (1/100) := by linarith [PhaseSurplusProducer.countConstant_ge_ten]
  have hstrict:=strictnessGap_pos hT
  obtain ⟨v,hv,hv1,hvc,hvs⟩:=ParameterBounds.exists_rational_slack _ _ hstrict hT
  have hvR : (0:ℝ)<v := by exact_mod_cast hv
  obtain ⟨Nstar,hNstar,hsize⟩:=ParameterBounds.exists_size_threshold _ _ hstrict hvR
  obtain ⟨A,_,hlog⟩:=bounded_count_log v Nstar hv
  let C : ℕ := ⌈1/v^2⌉₊
  have hv2 : (0:ℚ)<v^2 := sq_pos_of_pos hv
  have hC : 2≤(1+v^2)^C := by
    have ha : (1:ℚ)≤C*v^2 := (div_le_iff₀ hv2).mp (Nat.le_ceil _)
    have hb:=one_add_mul_le_pow (by linarith : (-2:ℚ)≤v^2) C
    linarith
  obtain ⟨Q,d,hQ⟩:=finite_program A e
  refine ⟨v,C,Q,d,?_⟩
  intro n _ δ hδ D F k hD hk hkF hbound hsep g hg
  dsimp only
  let M:=Rounding.cap D.card (gamma/16)
  let N:=D.card+F.card
  let L:=commonL v Nstar D.card M
  have hNL : Nstar≤L := le_max_left _ _
  have hL : 0<L := by omega
  have hlarge (hl:2*L<k) : Nstar≤N := by dsimp [N];omega
  exact hQ δ hδ D F k L M N C v hD hk hL hkF rfl (Rounding.cap_pos _ _) le_rfl
    hbound hsep hvR hv1 hvc hvs (fun hl=>(hsize _ (hlarge hl)).2)
    (fun hl=>(hsize _ (hlarge hl)).1) (le_max_right _ _) hC g hg (hlog D.card N (by dsimp [N];omega) (by dsimp [N];omega))
end MetricKMedianRecovery.BitMachine.BinaryIntegralAll

end OAI
