import OAI.InformationTheory.SecretKey.Gap

namespace OAI

noncomputable section

namespace ZeroKey

section

open Matrix

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

universe v10089_0 v10089_1

variable {ι : Type v10089_0} {κ : Type v10089_1} [inst10089_0 : Fintype ι] [inst10089_1 : Fintype κ] [inst10089_2 : DecidableEq ι] [inst10089_3 : DecidableEq κ]

lemma purification_filter_identity [Nonempty ι] (P : Matrix ι κ ℂ) :
    referenceFilter (purificationFilter P) (outer (localProbe (ι := ι)) localProbe) =
      outer (vectorize P) (vectorize P) := by
  unfold localProbe purificationFilter
  rw [referenceFilter_vectorize,Matrix.transpose_smul,Matrix.transpose_transpose,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,smul_smul]
  have hc : (Real.sqrt (Fintype.card ι : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)).ne'
  rw [inv_mul_cancel₀ hc,one_smul]

end

section

open Matrix MeasureTheory

open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

universe v10152_0 v10152_1 v10152_2

variable {ι : Type v10152_0} {κ : Type v10152_1} {Ω : Type v10152_2} [inst10152_0 : Fintype ι] [inst10152_1 : Fintype κ] [inst10152_2 : DecidableEq ι] [inst10152_3 : DecidableEq κ]
  [inst10152_4 : MeasurableSpace Ω] {μ : Measure Ω}

def BitDensity.mapReference (τ : BitDensity μ κ)
    (L : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hpos : ∀ Z, Z.PosSemidef → (L Z).PosSemidef)
    (htr : ∀ Z, trace (L Z) = trace Z) : BitDensity μ ι where
  block i j t := L (τ.block i j t)
  positive i j t := hpos _ (τ.positive i j t)
  measurable i j := L.continuous_of_finiteDimensional.measurable.comp (τ.measurable i j)
  integrable i j := by simpa only [htr] using τ.integrable i j
  normalized := by simpa only [htr] using τ.normalized

lemma traceNorm_channel_sub (L : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hpos : ∀ Z, Z.PosSemidef → (L Z).PosSemidef)
    (htr : ∀ Z, trace (L Z) = trace Z)
    {A B : Matrix κ κ ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    traceNorm (L A - L B) ≤ traceNorm (A-B) := by
  rw [← map_sub]
  exact traceNorm_positive_tracePreserving L hpos htr _ (hA.isHermitian.sub hB.isHermitian)

theorem BitDensity.idealBitError_mapReference_le (τ : BitDensity μ κ)
    (L : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hpos : ∀ Z, Z.PosSemidef → (L Z).PosSemidef)
    (htr : ∀ Z, trace (L Z) = trace Z)
    (σ : Ω → Matrix κ κ ℂ) (hσ : Measurable σ)
    (hσp : ∀ t, (σ t).PosSemidef)
    (hσi : Integrable (fun t => (trace (σ t)).re) μ) :
    (τ.mapReference L hpos htr).idealBitError (fun t => L (σ t)) ≤ τ.idealBitError σ := by
  have hm : Measurable (fun t => L (σ t)) := L.continuous_of_finiteDimensional.measurable.comp hσ
  have hi : Integrable (fun t => (trace (L (σ t))).re) μ := by simpa only [htr] using hσi
  have hc (a : Bool) :
      (∫ t, traceNorm (L (τ.block a a t) - (1/2 : ℝ) • L (σ t)) ∂μ) ≤
      ∫ t, traceNorm (τ.block a a t - (1/2 : ℝ) • σ t) ∂μ := by
    have hleft := traceNorm_sub_integrable
      (L.continuous_of_finiteDimensional.measurable.comp (τ.measurable a a))
      (show Measurable (fun t => (1/2 : ℝ) • L (σ t)) from hm.const_smul (1/2 : ℝ)) (fun t => hpos _ (τ.positive a a t))
      (fun t => (hpos _ (hσp t)).smul (show (0:ℝ)≤1/2 by norm_num))
      (show Integrable (fun t => (trace (L (τ.block a a t))).re) μ by simpa only [htr] using τ.integrable a a)
      (by simpa only [Matrix.trace_smul,Complex.smul_re,smul_eq_mul] using hi.const_mul (1/2))
    have hright := traceNorm_sub_integrable (τ.measurable a a) (show Measurable (fun t => (1/2 : ℝ) • σ t) from hσ.const_smul (1/2 : ℝ))
      (τ.positive a a) (fun t => (hσp t).smul (show (0:ℝ)≤1/2 by norm_num))
      (τ.integrable a a)
      (by simpa only [Matrix.trace_smul,Complex.smul_re,smul_eq_mul] using hσi.const_mul (1/2))
    apply integral_mono hleft hright
    intro t
    change traceNorm (L (τ.block a a t) - (1/2 : ℝ) • L (σ t)) ≤ _
    rw [← L.map_smul_of_tower (1/2 : ℝ) (σ t)]
    exact traceNorm_channel_sub L hpos htr (τ.positive a a t)
      ((hσp t).smul (show (0:ℝ)≤1/2 by norm_num))
  have hf := hc false
  have ht := hc true
  unfold BitDensity.idealBitError BitDensity.mass
  simp only [BitDensity.mapReference,htr]
  linarith

end

open Matrix MeasureTheory ProbabilityTheory Function Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

open UnrestrictedQuantum

universe v10227_0 v10227_1 v10227_2 v10227_3 v10227_4 v10227_5 v10227_6 v10227_7 v10227_8 v10227_9 v10227_10

variable {O : Type v10227_0} {M : Type v10227_1} {ι : Type v10227_2} {η : Type v10227_3} [inst10227_0 : MeasurableSpace O] [inst10227_1 : MeasurableSpace M]
  [inst10227_2 : StandardBorelSpace O] [inst10227_3 : Nonempty O] [inst10227_4 : StandardBorelSpace M] [inst10227_5 : Nonempty M]
  [inst10227_6 : Fintype ι] [inst10227_7 : Fintype η] [inst10227_8 : DecidableEq ι] [inst10227_9 : DecidableEq η]
  [inst10227_10 : Nonempty ι] [inst10227_11 : Nonempty η]
  {d : Discussion O M} {A : ℕ → Type v10227_4} {B : ℕ → Type v10227_5}
  [inst10227_12 : ∀ n, AddCommGroup (A n)] [inst10227_13 : ∀ n, Module ℂ (A n)] [inst10227_14 : ∀ n, One (A n)] [inst10227_15 : ∀ n, LE (A n)]
  [inst10227_16 : ∀ n, AddCommGroup (B n)] [inst10227_17 : ∀ n, Module ℂ (B n)] [inst10227_18 : ∀ n, One (B n)] [inst10227_19 : ∀ n, LE (B n)]
  {TA : Type v10227_6} {TB : Type v10227_7} {CA : Type v10227_8} {CB : Type v10227_9}
  [inst10227_20 : AddCommGroup TA] [inst10227_21 : Module ℂ TA] [inst10227_22 : One TA] [inst10227_23 : LE TA]
  [inst10227_24 : AddCommGroup TB] [inst10227_25 : Module ℂ TB] [inst10227_26 : One TB] [inst10227_27 : LE TB]
  [inst10227_28 : AddCommGroup CA] [inst10227_29 : Module ℂ CA] [inst10227_30 : One CA] [inst10227_31 : LE CA]
  [inst10227_32 : AddCommGroup CB] [inst10227_33 : Module ℂ CB] [inst10227_34 : One CB] [inst10227_35 : LE CB]
  {κ : Type v10227_10} [inst10227_36 : Fintype κ] [inst10227_37 : DecidableEq κ]

namespace BitProtocol

variable (p : BitProtocol (ι := ι) (η := η) d A B TA TB CA CB)
  (R : Matrix (ι × η) (ι × η) ℂ) (hR : Density R)
  (P : Matrix (ι × η) κ ℂ) (hP : P * Pᴴ = R)

include hR hP

lemma purifiedDensity_recovery (ν : Measure (ℕ → M)) [SigmaFinite ν]
    (hμν : d.transcriptLaw ≪ ν)
    (L : Matrix κ κ ℂ →ₗ[ℂ] Matrix (ι × η) (ι × η) ℂ)
    (he : ∀ i j S, L ((p.purifiedOutput P i j).value S) = (p.canonicalOutput R i j).value S)
    (i j : Bool) :
    (p.outputDensity R hR ν hμν).block i j =ᵐ[ν]
      fun t => L ((p.purifiedDensity R hR P hP ν hμν).block i j t) := by
  have hAC (S : Set (ℕ → M)) (hS : MeasurableSet S) (hz : ν S = 0) :
      (p.purifiedOutput P i j).value S = 0 := p.purifiedOutput_ac P i j S hS (hμν hz)
  let LC := L.toContinuousLinearMap
  apply (p.canonicalOutput R i j).positiveDensity_eq_ae ν
    (LC.integrable_comp ((p.purifiedOutput P i j).positiveDensity_integrable ν hAC))
  intro S hS
  rw [LC.integral_comp_comm ((p.purifiedOutput P i j).positiveDensity_integrable ν hAC).integrableOn,
    (p.purifiedOutput P i j).positiveDensity_integral ν hAC S hS]
  exact (he i j S).symm

end BitProtocol

theorem BitProtocol.uniform_gap_purification {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (p : BitProtocol (ι := Fin a) (η := Fin b) d A B TA TB CA CB)
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : InClass R)
    (P : Matrix (Fin a × Fin b) κ ℂ) (hP : P * Pᴴ = R)
    (sigma : PositiveMatrixMeasure (ℕ → M) κ)
    (hsigma : (trace (sigma.value Set.univ)).re = 1) :
    1/5 ≤ p.purifiedSecretBitError R hR.1 P hP sigma := by
  let ν := d.transcriptLaw + sigma.traceMeasure
  have hμν : d.transcriptLaw ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right _
  have hsν : sigma.traceMeasure ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' _
  have hsAC (S : Set (ℕ → M)) (hS : MeasurableSet S) (hz : ν S = 0) :
      sigma.value S = 0 := sigma.value_zero_of_traceMeasure_zero S hS (hsν hz)
  obtain ⟨L,hpos,htr,hrec⟩ := p.purifiedOutput_recovery R hR.1 P hP
  let tp := p.purifiedDensity R hR.1 P hP ν hμν
  let tc := p.outputDensity R hR.1 ν hμν
  let sp := sigma.positiveDensity ν
  have hspm := sigma.measurable_positiveDensity ν
  have hspp := sigma.positiveDensity_pos ν
  have hspi := sigma.integrable_positiveDensity_trace ν hsAC
  have hspn := (sigma.integral_positiveDensity_trace ν hsAC).trans hsigma
  obtain ⟨τ,X,Y,hX,hY,hτ,hi,he⟩ := p.canonical_density_representation R hR.1
  have hg := class_factor_gap_dominating_measure hμν R hR τ X Y hX hY hτ
    (fun t => L (sp t)) (L.continuous_of_finiteDimensional.measurable.comp hspm)
    (fun t => hpos _ (hspp t))
    (show Integrable (fun t => (trace (L (sp t))).re) ν by simpa only [htr] using hspi)
    (show (∫ t, (trace (L (sp t))).re ∂ν) = 1 by simpa only [htr] using hspn)
  have heq := BitDensity.idealBitError_congr tc (τ.changeMeasure hμν)
    (fun t => L (sp t)) (fun t => L (sp t))
    (p.outputDensity_eq R hR.1 ν hμν τ hi he) Filter.EventuallyEq.rfl
  have hrc := BitDensity.idealBitError_congr tc (tp.mapReference L hpos htr)
    (fun t => L (sp t)) (fun t => L (sp t))
    (p.purifiedDensity_recovery R hR.1 P hP ν hμν L hrec) Filter.EventuallyEq.rfl
  have hcontract := tp.idealBitError_mapReference_le L hpos htr sp hspm hspp hspi
  change 1/5 ≤ tp.idealBitError sp
  rw [← heq,hrc] at hg
  exact hg.trans hcontract

end ZeroKey

namespace UnrestrictedQuantum

open Matrix MeasureTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe v10518_0 v10518_1 v10518_2 v10518_3 v10518_4

variable {A : Type v10518_0} {B : Type v10518_1} {K : Type v10518_2} {ι : Type v10518_3} {Ω : Type v10518_4} [inst10518_0 : AddCommGroup A] [inst10518_1 : Module ℂ A] [inst10518_2 : One A] [inst10518_3 : LE A]
  [inst10518_4 : AddCommGroup B] [inst10518_5 : Module ℂ B] [inst10518_6 : One B] [inst10518_7 : LE B]
  [inst10518_8 : MeasurableSpace K] [inst10518_9 : MeasurableSingletonClass K] [inst10518_10 : Fintype K] [inst10518_11 : DecidableEq K] [inst10518_12 : Nonempty K]
  [inst10518_13 : Fintype ι] [inst10518_14 : DecidableEq ι]

variable {L : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} {F : Filtration ℕ mΩ} {U : ℕ → Ω → Matrix ι ι ℂ}
  (e : IncomingObservableProcess (L := L) (A := A) μ F U)

namespace IncomingObservableProcess

namespace FiniteReadout

variable {e} (b : e.FiniteReadout (B := B) (K := K))

lemma postprocess_value (f : K → Bool) (i : Bool) (x : Ω) :
    (b.postprocess f).value i x = ∑ k ∈ Finset.univ.filter (fun k => f k = i), b.value k x := by
  have hs : ((Finset.univ.filter (fun k => f k = i) : Finset K) : Set K) = f ⁻¹' {i} := by
    ext k; simp
  change e.state x ((b.instrument x).operation (f ⁻¹' {i}) 1) = _
  rw [← hs]
  exact b.event_finset _ x

end FiniteReadout

end IncomingObservableProcess

end UnrestrictedQuantum

namespace ZeroKey

section

open Matrix MeasureTheory ProbabilityTheory Function unitInterval Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

section

open UnrestrictedQuantum

universe v10619_0 v10619_1 v10619_2 v10619_3 v10619_4 v10619_5 v10619_6 v10619_7 v10619_8 v10619_9 v10619_10

variable {O : Type v10619_0} {M : Type v10619_1} {ι : Type v10619_2} {η : Type v10619_3} [inst10619_0 : MeasurableSpace O] [inst10619_1 : MeasurableSpace M]
  [inst10619_2 : StandardBorelSpace O] [inst10619_3 : Nonempty O] [inst10619_4 : StandardBorelSpace M] [inst10619_5 : Nonempty M]
  [inst10619_6 : Fintype ι] [inst10619_7 : Fintype η] [inst10619_8 : DecidableEq ι] [inst10619_9 : DecidableEq η]
  {K : Type v10619_4} [inst10619_10 : MeasurableSpace K] [inst10619_11 : MeasurableSingletonClass K]
  [inst10619_12 : Fintype K] [inst10619_13 : DecidableEq K] [inst10619_14 : Nonempty K]
  (d : Discussion O M)
  (A : ℕ → Type v10619_5) (B : ℕ → Type v10619_6)
  [inst10619_15 : ∀ n, AddCommGroup (A n)] [inst10619_16 : ∀ n, Module ℂ (A n)] [inst10619_17 : ∀ n, One (A n)] [inst10619_18 : ∀ n, LE (A n)]
  [inst10619_19 : ∀ n, AddCommGroup (B n)] [inst10619_20 : ∀ n, Module ℂ (B n)] [inst10619_21 : ∀ n, One (B n)] [inst10619_22 : ∀ n, LE (B n)]
  (TA : Type v10619_7) (TB : Type v10619_8) (CA : Type v10619_9) (CB : Type v10619_10)
  [inst10619_23 : AddCommGroup TA] [inst10619_24 : Module ℂ TA] [inst10619_25 : One TA] [inst10619_26 : LE TA]
  [inst10619_27 : AddCommGroup TB] [inst10619_28 : Module ℂ TB] [inst10619_29 : One TB] [inst10619_30 : LE TB]
  [inst10619_31 : AddCommGroup CA] [inst10619_32 : Module ℂ CA] [inst10619_33 : One CA] [inst10619_34 : LE CA]
  [inst10619_35 : AddCommGroup CB] [inst10619_36 : Module ℂ CB] [inst10619_37 : One CB] [inst10619_38 : LE CB]

variable {d A B TA TB CA CB}

namespace FiniteProtocol

variable (p : FiniteProtocol (ι := ι) (η := η) (K := K) d A B TA TB CA CB)

lemma canonicalOutput_ac (R : Matrix (ι × η) (ι × η) ℂ) (i j : K)
    (S : Set (ℕ → M)) (hS : MeasurableSet S) (hz : d.transcriptLaw S = 0) :
    (p.canonicalOutput R i j).value S = 0 := by
  have hp : d.probeLaw (d.sampler.publicRecord ⁻¹' S) = 0 := by
    simpa only [Discussion.transcriptLaw,Measure.map_apply d.sampler.measurable_publicRecord hS] using hz
  rw [p.canonicalOutput_event R i j S hS,Measure.restrict_eq_zero.mpr hp,integral_zero_measure]

def outputDensity (R : Matrix (ι × η) (ι × η) ℂ) (ν : Measure (ℕ → M)) (i j : K) :
    (ℕ → M) → Matrix (ι × η) (ι × η) ℂ := (p.canonicalOutput R i j).positiveDensity ν

end FiniteProtocol

end

section

open UnrestrictedQuantum

universe v10740_0 v10740_1 v10740_2 v10740_3 v10740_4 v10740_5 v10740_6 v10740_7 v10740_8 v10740_9 v10740_10

variable {O : Type v10740_0} {M : Type v10740_1} {ι : Type v10740_2} {η : Type v10740_3} [inst10740_0 : MeasurableSpace O] [inst10740_1 : MeasurableSpace M]
  [inst10740_2 : StandardBorelSpace O] [inst10740_3 : Nonempty O] [inst10740_4 : StandardBorelSpace M] [inst10740_5 : Nonempty M]
  [inst10740_6 : Fintype ι] [inst10740_7 : Fintype η] [inst10740_8 : DecidableEq ι] [inst10740_9 : DecidableEq η] [inst10740_10 : Nonempty ι] [inst10740_11 : Nonempty η]
  {Λ : Type v10740_4} [inst10740_12 : MeasurableSpace Λ] [inst10740_13 : MeasurableSingletonClass Λ]
  [inst10740_14 : Fintype Λ] [inst10740_15 : DecidableEq Λ] [inst10740_16 : Nonempty Λ]
  (d : Discussion O M)
  (A : ℕ → Type v10740_5) (B : ℕ → Type v10740_6)
  [inst10740_17 : ∀ n, AddCommGroup (A n)] [inst10740_18 : ∀ n, Module ℂ (A n)] [inst10740_19 : ∀ n, One (A n)] [inst10740_20 : ∀ n, LE (A n)]
  [inst10740_21 : ∀ n, AddCommGroup (B n)] [inst10740_22 : ∀ n, Module ℂ (B n)] [inst10740_23 : ∀ n, One (B n)] [inst10740_24 : ∀ n, LE (B n)]
  (TA : Type v10740_7) (TB : Type v10740_8) (CA : Type v10740_9) (CB : Type v10740_10)
  [inst10740_25 : AddCommGroup TA] [inst10740_26 : Module ℂ TA] [inst10740_27 : One TA] [inst10740_28 : LE TA]
  [inst10740_29 : AddCommGroup TB] [inst10740_30 : Module ℂ TB] [inst10740_31 : One TB] [inst10740_32 : LE TB]
  [inst10740_33 : AddCommGroup CA] [inst10740_34 : Module ℂ CA] [inst10740_35 : One CA] [inst10740_36 : LE CA]
  [inst10740_37 : AddCommGroup CB] [inst10740_38 : Module ℂ CB] [inst10740_39 : One CB] [inst10740_40 : LE CB]

variable {d A B TA TB CA CB}

namespace FiniteProtocol

variable (p : FiniteProtocol (ι := ι) (η := η) (K := Bool × Λ) d A B TA TB CA CB)

def firstBit : BitProtocol (ι := ι) (η := η) d A B TA TB CA CB := p.toBit Prod.fst

omit inst10740_4 inst10740_5 inst10740_10 inst10740_11 in
lemma firstBit_completeReference [StandardBorelSpace M] [Nonempty M] [Nonempty ι] [Nonempty η] (i j : Bool) (x : ℕ → O) :
    p.firstBit.completeReference i j x =
      ∑ a : Λ, ∑ b : Λ, p.completeReference (i,a) (j,b) x := by
  have ha : (p.readoutA.postprocess Prod.fst).value i x = ∑ a : Λ, p.readoutA.value (i,a) x := by
    rw [IncomingObservableProcess.FiniteReadout.postprocess_value]
    cases i <;> simp [Finset.sum_filter,Fintype.sum_prod_type]
  have hb : (p.readoutB.postprocess Prod.fst).value j x = ∑ b : Λ, p.readoutB.value (j,b) x := by
    rw [IncomingObservableProcess.FiniteReadout.postprocess_value]
    cases j <;> simp [Finset.sum_filter,Fintype.sum_prod_type]
  change (p.readoutA.postprocess Prod.fst).value i x ⊗ₖ
    (p.readoutB.postprocess Prod.fst).value j x = _
  rw [ha,hb]
  ext k l
  simp only [Matrix.kroneckerMap_apply,Matrix.sum_apply,Finset.sum_mul,Finset.mul_sum,completeReference,Matrix.kroneckerMap_apply]
  rw [Finset.sum_comm]

lemma firstBit_output_event (R : Matrix (ι × η) (ι × η) ℂ)
    (i j : Bool) (S : Set (ℕ → M)) (hS : MeasurableSet S) :
    (p.firstBit.canonicalOutput R i j).value S =
      ∑ a : Λ, ∑ b : Λ, (p.canonicalOutput R (i,a) (j,b)).value S := by
  rw [p.firstBit.canonicalOutput_event R i j S hS]
  simp_rw [p.firstBit_completeReference,Matrix.mul_sum,Matrix.sum_mul]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
    (integrable_filter (preparationFilter R) (p.completeReference_integrable (i,a) (j,b))).integrableOn))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ =>
    (integrable_filter (preparationFilter R) (p.completeReference_integrable (i,a) (j,b))).integrableOn)]
  apply Finset.sum_congr rfl
  intro b _
  exact (p.canonicalOutput_event R (i,a) (j,b) S hS).symm

lemma firstBit_outputDensity (R : Matrix (ι × η) (ι × η) ℂ) (hR : Density R)
    (ν : Measure (ℕ → M)) [SigmaFinite ν] (hμν : d.transcriptLaw ≪ ν) (i j : Bool) :
    (p.firstBit.outputDensity R hR ν hμν).block i j =ᵐ[ν]
      fun t => ∑ a : Λ, ∑ b : Λ, p.outputDensity R ν (i,a) (j,b) t := by
  have hAC (a b : Bool × Λ) (S : Set (ℕ → M)) (hS : MeasurableSet S) (hz : ν S = 0) :
      (p.canonicalOutput R a b).value S = 0 := p.canonicalOutput_ac R a b S hS (hμν hz)
  have hi (a b : Bool × Λ) : Integrable (p.outputDensity R ν a b) ν :=
    (p.canonicalOutput R a b).positiveDensity_integrable ν (hAC a b)
  apply (p.firstBit.canonicalOutput R i j).positiveDensity_eq_ae ν
    (integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi (i,a) (j,b))))
  intro S hS
  rw [p.firstBit_output_event R i j S hS]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => (hi (i,a) (j,b)).integrableOn))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ => (hi (i,a) (j,b)).integrableOn)]
  apply Finset.sum_congr rfl
  intro b _
  exact ((p.canonicalOutput R (i,a) (j,b)).positiveDensity_integral ν (hAC (i,a) (j,b)) S hS).symm

end FiniteProtocol

end

open UnrestrictedQuantum

universe v10829_0 v10829_1 v10829_2 v10829_3 v10829_4 v10829_5 v10829_6 v10829_7 v10829_8 v10829_9 v10829_10

variable {O : Type v10829_0} {M : Type v10829_1} {ι : Type v10829_2} {η : Type v10829_3} [inst10829_0 : MeasurableSpace O] [inst10829_1 : MeasurableSpace M]
  [inst10829_2 : StandardBorelSpace O] [inst10829_3 : Nonempty O] [inst10829_4 : StandardBorelSpace M] [inst10829_5 : Nonempty M]
  [inst10829_6 : Fintype ι] [inst10829_7 : Fintype η] [inst10829_8 : DecidableEq ι] [inst10829_9 : DecidableEq η] [inst10829_10 : Nonempty ι] [inst10829_11 : Nonempty η]
  {K : Type v10829_4} [inst10829_12 : MeasurableSpace K] [inst10829_13 : MeasurableSingletonClass K]
  [inst10829_14 : Fintype K] [inst10829_15 : DecidableEq K] [inst10829_16 : Nonempty K]
  (d : Discussion O M)
  (A : ℕ → Type v10829_5) (B : ℕ → Type v10829_6)
  [inst10829_17 : ∀ n, AddCommGroup (A n)] [inst10829_18 : ∀ n, Module ℂ (A n)] [inst10829_19 : ∀ n, One (A n)] [inst10829_20 : ∀ n, LE (A n)]
  [inst10829_21 : ∀ n, AddCommGroup (B n)] [inst10829_22 : ∀ n, Module ℂ (B n)] [inst10829_23 : ∀ n, One (B n)] [inst10829_24 : ∀ n, LE (B n)]
  (TA : Type v10829_7) (TB : Type v10829_8) (CA : Type v10829_9) (CB : Type v10829_10)
  [inst10829_25 : AddCommGroup TA] [inst10829_26 : Module ℂ TA] [inst10829_27 : One TA] [inst10829_28 : LE TA]
  [inst10829_29 : AddCommGroup TB] [inst10829_30 : Module ℂ TB] [inst10829_31 : One TB] [inst10829_32 : LE TB]
  [inst10829_33 : AddCommGroup CA] [inst10829_34 : Module ℂ CA] [inst10829_35 : One CA] [inst10829_36 : LE CA]
  [inst10829_37 : AddCommGroup CB] [inst10829_38 : Module ℂ CB] [inst10829_39 : One CB] [inst10829_40 : LE CB]

variable {d A B TA TB CA CB}

namespace FiniteProtocol

variable (p : FiniteProtocol (ι := ι) (η := η) (K := K) d A B TA TB CA CB)

def secretKeyError (R : Matrix (ι × η) (ι × η) ℂ)
    (sigma : PositiveMatrixMeasure (ℕ → M) (ι × η)) : ℝ :=
  let ν := d.transcriptLaw + sigma.traceMeasure
  cqDistance (p.outputDensity R ν)
    (fun a b t => idealFiniteBlocks (sigma.positiveDensity ν t) a b) ν

omit inst10829_10 inst10829_11 in
lemma secretKeyError_nonneg [Nonempty ι] [Nonempty η] (R : Matrix (ι × η) (ι × η) ℂ)
    (sigma : PositiveMatrixMeasure (ℕ → M) (ι × η)) : 0 ≤ p.secretKeyError R sigma := by
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    integral_nonneg fun t => traceNorm_nonneg _

end FiniteProtocol

universe v10864_0

variable {Λ : Type v10864_0} [inst10864_0 : MeasurableSpace Λ] [inst10864_1 : MeasurableSingletonClass Λ]
  [inst10864_2 : Fintype Λ] [inst10864_3 : DecidableEq Λ] [inst10864_4 : Nonempty Λ]

namespace FiniteProtocol

variable (p : FiniteProtocol (ι := ι) (η := η) (K := Bool × Λ) d A B TA TB CA CB)

theorem firstBit_error_le (R : Matrix (ι × η) (ι × η) ℂ) (hR : Density R)
    (sigma : PositiveMatrixMeasure (ℕ → M) (ι × η)) :
    p.firstBit.secretBitError R hR sigma ≤ p.secretKeyError R sigma := by
  let ν := d.transcriptLaw + sigma.traceMeasure
  have hμν : d.transcriptLaw ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right _
  have hsν : sigma.traceMeasure ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' _
  have hsAC (S : Set (ℕ → M)) (hS : MeasurableSet S) (hz : ν S = 0) :
      sigma.value S = 0 := sigma.value_zero_of_traceMeasure_zero S hS (hsν hz)
  have hAC (a b : Bool × Λ) (S : Set (ℕ → M)) (hS : MeasurableSet S) (hz : ν S = 0) :
      (p.canonicalOutput R a b).value S = 0 := p.canonicalOutput_ac R a b S hS (hμν hz)
  have h := cqFirstBit_ideal_le (p.outputDensity R ν)
    (fun a b => (p.canonicalOutput R a b).measurable_positiveDensity ν)
    (fun a b => (p.canonicalOutput R a b).positiveDensity_pos ν)
    (fun a b => (p.canonicalOutput R a b).integrable_positiveDensity_trace ν (hAC a b))
    (sigma.positiveDensity ν) (sigma.measurable_positiveDensity ν)
    (sigma.positiveDensity_pos ν) (sigma.integrable_positiveDensity_trace ν hsAC)
  apply le_trans (le_of_eq ?_) h
  change (p.firstBit.outputDensity R hR ν hμν).idealBitError (sigma.positiveDensity ν) = _
  rw [BitDensity.idealBitError_eq_cq]
  unfold cqBitError
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [p.firstBit_outputDensity R hR ν hμν i j] with t ht
  rw [ht]
  rfl

theorem uniform_key_gap {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (p : FiniteProtocol (ι := Fin a) (η := Fin b) (K := Bool × Λ) d A B TA TB CA CB)
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : InClass R)
    (sigma : PositiveMatrixMeasure (ℕ → M) (Fin a × Fin b))
    (hsigma : (trace (sigma.value Set.univ)).re = 1) :
    1/5 ≤ p.secretKeyError R sigma :=
  (p.firstBit.uniform_gap R hR sigma hsigma).trans (p.firstBit_error_le R hR.1 sigma)

end FiniteProtocol

end

section

open Matrix MeasureTheory ProbabilityTheory Function Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

open UnrestrictedQuantum

universe v11008_0 v11008_1 v11008_2 v11008_3 v11008_4 v11008_5 v11008_6 v11008_7 v11008_8 v11008_9 v11008_10 v11008_11

variable {O : Type v11008_0} {M : Type v11008_1} {ι : Type v11008_2} {η : Type v11008_3} [inst11008_0 : MeasurableSpace O] [inst11008_1 : MeasurableSpace M]
  [inst11008_2 : StandardBorelSpace O] [inst11008_3 : Nonempty O] [inst11008_4 : StandardBorelSpace M] [inst11008_5 : Nonempty M]
  [inst11008_6 : Fintype ι] [inst11008_7 : Fintype η] [inst11008_8 : DecidableEq ι] [inst11008_9 : DecidableEq η] [inst11008_10 : Nonempty ι] [inst11008_11 : Nonempty η]
  {K : Type v11008_4} [inst11008_12 : MeasurableSpace K] [inst11008_13 : MeasurableSingletonClass K]
  [inst11008_14 : Fintype K] [inst11008_15 : DecidableEq K] [inst11008_16 : Nonempty K]
  {d : Discussion O M} {A : ℕ → Type v11008_5} {B : ℕ → Type v11008_6}
  [inst11008_17 : ∀ n, AddCommGroup (A n)] [inst11008_18 : ∀ n, Module ℂ (A n)] [inst11008_19 : ∀ n, One (A n)] [inst11008_20 : ∀ n, LE (A n)]
  [inst11008_21 : ∀ n, AddCommGroup (B n)] [inst11008_22 : ∀ n, Module ℂ (B n)] [inst11008_23 : ∀ n, One (B n)] [inst11008_24 : ∀ n, LE (B n)]
  {TA : Type v11008_7} {TB : Type v11008_8} {CA : Type v11008_9} {CB : Type v11008_10}
  [inst11008_25 : AddCommGroup TA] [inst11008_26 : Module ℂ TA] [inst11008_27 : One TA] [inst11008_28 : LE TA]
  [inst11008_29 : AddCommGroup TB] [inst11008_30 : Module ℂ TB] [inst11008_31 : One TB] [inst11008_32 : LE TB]
  [inst11008_33 : AddCommGroup CA] [inst11008_34 : Module ℂ CA] [inst11008_35 : One CA] [inst11008_36 : LE CA]
  [inst11008_37 : AddCommGroup CB] [inst11008_38 : Module ℂ CB] [inst11008_39 : One CB] [inst11008_40 : LE CB]
  {κ : Type v11008_11} [inst11008_41 : Fintype κ] [inst11008_42 : DecidableEq κ]

namespace FiniteProtocol

variable (p : FiniteProtocol (ι := ι) (η := η) (K := K) d A B TA TB CA CB)

def purifiedSecretKeyError (P : Matrix (ι × η) κ ℂ)
    (sigma : PositiveMatrixMeasure (ℕ → M) κ) : ℝ :=
  let ν := d.transcriptLaw + sigma.traceMeasure
  cqDistance (p.purifiedOutputDensity P ν)
    (fun a b t => idealFiniteBlocks (sigma.positiveDensity ν t) a b) ν

end FiniteProtocol

universe v11066_0

variable {Λ : Type v11066_0} [inst11066_0 : MeasurableSpace Λ] [inst11066_1 : MeasurableSingletonClass Λ]
  [inst11066_2 : Fintype Λ] [inst11066_3 : DecidableEq Λ] [inst11066_4 : Nonempty Λ]

namespace FiniteProtocol

variable (p : FiniteProtocol (ι := ι) (η := η) (K := Bool × Λ) d A B TA TB CA CB)

lemma firstBit_purifiedOutput_event (P : Matrix (ι × η) κ ℂ)
    (i j : Bool) (S : Set (ℕ → M)) (hS : MeasurableSet S) :
    (p.firstBit.purifiedOutput P i j).value S =
      ∑ a : Λ, ∑ b : Λ, (p.purifiedOutput P (i,a) (j,b)).value S := by
  rw [BitProtocol.purifiedOutput,PositiveMatrixMeasure.filter_value,
    p.firstBit.probeOutput_event i j S hS,
    ← integral_filter _ (p.firstBit.completeReference_integrable i j).integrableOn]
  simp_rw [p.firstBit_completeReference,Matrix.mul_sum,Matrix.sum_mul]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
    (integrable_filter (purificationFilter P) (p.completeReference_integrable (i,a) (j,b))).integrableOn))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ =>
    (integrable_filter (purificationFilter P) (p.completeReference_integrable (i,a) (j,b))).integrableOn)]
  apply Finset.sum_congr rfl
  intro b _
  exact (p.purifiedOutput_event P (i,a) (j,b) S hS).symm

lemma firstBit_purifiedOutputDensity (R : Matrix (ι × η) (ι × η) ℂ) (hR : Density R)
    (P : Matrix (ι × η) κ ℂ) (hP : P * Pᴴ = R)
    (ν : Measure (ℕ → M)) [SigmaFinite ν] (hμν : d.transcriptLaw ≪ ν) (i j : Bool) :
    (p.firstBit.purifiedDensity R hR P hP ν hμν).block i j =ᵐ[ν]
      fun t => ∑ a : Λ, ∑ b : Λ, p.purifiedOutputDensity P ν (i,a) (j,b) t := by
  have hAC (a b : Bool × Λ) (S : Set (ℕ → M)) (hS : MeasurableSet S) (hz : ν S = 0) :
      (p.purifiedOutput P a b).value S = 0 := p.purifiedOutput_ac P a b S hS (hμν hz)
  have hi (a b : Bool × Λ) : Integrable (p.purifiedOutputDensity P ν a b) ν :=
    (p.purifiedOutput P a b).positiveDensity_integrable ν (hAC a b)
  apply (p.firstBit.purifiedOutput P i j).positiveDensity_eq_ae ν
    (integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi (i,a) (j,b))))
  intro S hS
  rw [p.firstBit_purifiedOutput_event P i j S hS]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => (hi (i,a) (j,b)).integrableOn))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun b _ => (hi (i,a) (j,b)).integrableOn)]
  apply Finset.sum_congr rfl
  intro b _
  exact ((p.purifiedOutput P (i,a) (j,b)).positiveDensity_integral ν (hAC (i,a) (j,b)) S hS).symm

theorem firstBit_purified_error_le (R : Matrix (ι × η) (ι × η) ℂ) (hR : Density R)
    (P : Matrix (ι × η) κ ℂ) (hP : P * Pᴴ = R)
    (sigma : PositiveMatrixMeasure (ℕ → M) κ) :
    p.firstBit.purifiedSecretBitError R hR P hP sigma ≤ p.purifiedSecretKeyError P sigma := by
  let ν := d.transcriptLaw + sigma.traceMeasure
  have hμν : d.transcriptLaw ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right _
  have hsν : sigma.traceMeasure ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right' _
  have hsAC (S : Set (ℕ → M)) (hS : MeasurableSet S) (hz : ν S = 0) :
      sigma.value S = 0 := sigma.value_zero_of_traceMeasure_zero S hS (hsν hz)
  have hAC (a b : Bool × Λ) (S : Set (ℕ → M)) (hS : MeasurableSet S) (hz : ν S = 0) :
      (p.purifiedOutput P a b).value S = 0 := p.purifiedOutput_ac P a b S hS (hμν hz)
  have h := cqFirstBit_ideal_le (p.purifiedOutputDensity P ν)
    (fun a b => (p.purifiedOutput P a b).measurable_positiveDensity ν)
    (fun a b => (p.purifiedOutput P a b).positiveDensity_pos ν)
    (fun a b => (p.purifiedOutput P a b).integrable_positiveDensity_trace ν (hAC a b))
    (sigma.positiveDensity ν) (sigma.measurable_positiveDensity ν)
    (sigma.positiveDensity_pos ν) (sigma.integrable_positiveDensity_trace ν hsAC)
  apply le_trans (le_of_eq ?_) h
  change (p.firstBit.purifiedDensity R hR P hP ν hμν).idealBitError (sigma.positiveDensity ν) = _
  rw [BitDensity.idealBitError_eq_cq]
  unfold cqBitError
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [p.firstBit_purifiedOutputDensity R hR P hP ν hμν i j] with t ht
  rw [ht]
  rfl

theorem uniform_purified_key_gap {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (p : FiniteProtocol (ι := Fin a) (η := Fin b) (K := Bool × Λ) d A B TA TB CA CB)
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : InClass R)
    (P : Matrix (Fin a × Fin b) κ ℂ) (hP : P * Pᴴ = R)
    (sigma : PositiveMatrixMeasure (ℕ → M) κ)
    (hsigma : (trace (sigma.value Set.univ)).re = 1) :
    1/5 ≤ p.purifiedSecretKeyError P sigma :=
  (p.firstBit.uniform_gap_purification R hR P hP sigma hsigma).trans
    (p.firstBit_purified_error_le R hR.1 P hP sigma)

end FiniteProtocol

end

open Matrix MeasureTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe v11165_0 v11165_1 v11165_2

variable {Ω : Type v11165_0} {ι : Type v11165_1} {K : Type v11165_2} [inst11165_0 : MeasurableSpace Ω] [inst11165_1 : Fintype ι] [inst11165_2 : DecidableEq ι]
  [inst11165_3 : Fintype K] [inst11165_4 : DecidableEq K] {μ : Measure Ω}

namespace KeyDensity

variable (τ υ : KeyDensity μ K ι) (sigma : EveDensity μ ι)

lemma idealError_nonneg : 0 ≤ τ.idealError sigma := cqDistance_nonneg _ _

lemma distance_nonneg : 0 ≤ τ.distance υ := cqDistance_nonneg _ _

omit inst11165_4 in
lemma distance_self [DecidableEq K] : τ.distance τ = 0 := by
  have hz : traceNorm (0 : Matrix ι ι ℂ) = 0 := by
    rw [traceNorm_posSemidef (Matrix.PosSemidef.zero)]; simp
  simp [distance,cqDistance,hz]

lemma idealError_triangle : τ.idealError sigma ≤ τ.distance υ + υ.idealError sigma :=
  cqDistance_triangle τ.block υ.block (fun a b t => idealFiniteBlocks (sigma.block t) a b)
    τ.measurable υ.measurable (idealFinite_measurable sigma.block sigma.measurable)
    τ.positive υ.positive (fun a b t => idealFinite_positive (sigma.block t) (sigma.positive t) a b)
    τ.integrable υ.integrable (idealFinite_trace_integrable sigma.block sigma.integrable)

theorem gap_of_traceNorm_limit (τ : ℕ → KeyDensity μ K ι) (υ : KeyDensity μ K ι)
    (sigma : EveDensity μ ι) (hgap : ∀ n, 1/5 ≤ (τ n).idealError sigma)
    (hlim : Tendsto (fun n => (τ n).distance υ) atTop (nhds 0)) :
    1/5 ≤ υ.idealError sigma := by
  have hle (n : ℕ) := (hgap n).trans ((τ n).idealError_triangle υ sigma)
  have ht : Tendsto (fun n => (τ n).distance υ + υ.idealError sigma)
      atTop (nhds (υ.idealError sigma)) := by simpa using hlim.add_const (υ.idealError sigma)
  exact ge_of_tendsto ht (Filter.Eventually.of_forall hle)

end KeyDensity

namespace PositiveMatrixMeasure

def toEveDensity (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω) [SigmaFinite μ]
    (hAC : ∀ S, MeasurableSet S → μ S = 0 → W.value S = 0)
    (hn : (trace (W.value Set.univ)).re = 1) : EveDensity μ ι where
  block := W.positiveDensity μ
  measurable := W.measurable_positiveDensity μ
  positive := W.positiveDensity_pos μ
  integrable := W.integrable_positiveDensity_trace μ hAC
  normalized := (W.integral_positiveDensity_trace μ hAC).trans hn

end PositiveMatrixMeasure

end ZeroKey

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace ZeroKey

open UnrestrictedQuantum

universe v11244_0 v11244_1 v11244_2 v11244_3 v11244_4 v11244_5 v11244_6 v11244_7 v11244_8 v11244_9 v11244_10 v11244_11

variable {O : Type v11244_0} {M : Type v11244_1} {ι : Type v11244_2} {η : Type v11244_3} [inst11244_0 : MeasurableSpace O] [inst11244_1 : MeasurableSpace M]
  [inst11244_2 : StandardBorelSpace O] [inst11244_3 : Nonempty O] [inst11244_4 : StandardBorelSpace M] [inst11244_5 : Nonempty M]
  [inst11244_6 : Fintype ι] [inst11244_7 : Fintype η] [inst11244_8 : DecidableEq ι] [inst11244_9 : DecidableEq η] [inst11244_10 : Nonempty ι] [inst11244_11 : Nonempty η]
  {K : Type v11244_4} [inst11244_12 : MeasurableSpace K] [inst11244_13 : MeasurableSingletonClass K]
  [inst11244_14 : Fintype K] [inst11244_15 : DecidableEq K] [inst11244_16 : Nonempty K]
  {d : Discussion O M} {A : ℕ → Type v11244_5} {B : ℕ → Type v11244_6}
  [inst11244_17 : ∀ n, AddCommGroup (A n)] [inst11244_18 : ∀ n, Module ℂ (A n)] [inst11244_19 : ∀ n, One (A n)] [inst11244_20 : ∀ n, LE (A n)]
  [inst11244_21 : ∀ n, AddCommGroup (B n)] [inst11244_22 : ∀ n, Module ℂ (B n)] [inst11244_23 : ∀ n, One (B n)] [inst11244_24 : ∀ n, LE (B n)]
  {TA : Type v11244_7} {TB : Type v11244_8} {CA : Type v11244_9} {CB : Type v11244_10}
  [inst11244_25 : AddCommGroup TA] [inst11244_26 : Module ℂ TA] [inst11244_27 : One TA] [inst11244_28 : LE TA]
  [inst11244_29 : AddCommGroup TB] [inst11244_30 : Module ℂ TB] [inst11244_31 : One TB] [inst11244_32 : LE TB]
  [inst11244_33 : AddCommGroup CA] [inst11244_34 : Module ℂ CA] [inst11244_35 : One CA] [inst11244_36 : LE CA]
  [inst11244_37 : AddCommGroup CB] [inst11244_38 : Module ℂ CB] [inst11244_39 : One CB] [inst11244_40 : LE CB]
  {κ : Type v11244_11} [inst11244_41 : Fintype κ] [inst11244_42 : DecidableEq κ]

theorem BitProtocol.uniform_gap_purification_dominated
    {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (p : BitProtocol (ι := Fin a) (η := Fin b) d A B TA TB CA CB)
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : InClass R)
    (P : Matrix (Fin a × Fin b) κ ℂ) (hP : P * Pᴴ = R)
    (ν : Measure (ℕ → M)) [SigmaFinite ν] (hμν : d.transcriptLaw ≪ ν)
    (sigma : EveDensity ν κ) :
    1/5 ≤ (p.purifiedDensity R hR.1 P hP ν hμν).idealBitError sigma.block := by
  obtain ⟨L,hpos,htr,hrec⟩ := p.purifiedOutput_recovery R hR.1 P hP
  let tp := p.purifiedDensity R hR.1 P hP ν hμν
  let tc := p.outputDensity R hR.1 ν hμν
  have hg := p.uniform_gap_dominated R hR ν hμν
    (fun t => L (sigma.block t)) (L.continuous_of_finiteDimensional.measurable.comp sigma.measurable)
    (fun t => hpos _ (sigma.positive t))
    (show Integrable (fun t => (trace (L (sigma.block t))).re) ν by simpa only [htr] using sigma.integrable)
    (show (∫ t, (trace (L (sigma.block t))).re ∂ν) = 1 by simpa only [htr] using sigma.normalized)
  have hrc := BitDensity.idealBitError_congr tc (tp.mapReference L hpos htr)
    (fun t => L (sigma.block t)) (fun t => L (sigma.block t))
    (p.purifiedDensity_recovery R hR.1 P hP ν hμν L hrec) Filter.EventuallyEq.rfl
  have hc := tp.idealBitError_mapReference_le L hpos htr sigma.block
    sigma.measurable sigma.positive sigma.integrable
  change 1/5 ≤ tp.idealBitError sigma.block
  rw [hrc] at hg
  exact hg.trans hc

universe v11305_0

variable {Λ : Type v11305_0} [inst11305_0 : MeasurableSpace Λ] [inst11305_1 : MeasurableSingletonClass Λ]
  [inst11305_2 : Fintype Λ] [inst11305_3 : DecidableEq Λ] [inst11305_4 : Nonempty Λ]

theorem FiniteProtocol.uniform_purified_key_gap_dominated
    {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (p : FiniteProtocol (ι := Fin a) (η := Fin b) (K := Bool × Λ) d A B TA TB CA CB)
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : InClass R)
    (P : Matrix (Fin a × Fin b) κ ℂ) (hP : P * Pᴴ = R)
    (ν : Measure (ℕ → M)) [SigmaFinite ν] (hμν : d.transcriptLaw ≪ ν)
    (sigma : EveDensity ν κ) :
    1/5 ≤ (p.purifiedKeyDensity R hR.1 P hP ν hμν).idealError sigma := by
  let τ := p.purifiedKeyDensity R hR.1 P hP ν hμν
  have hc := cqFirstBit_ideal_le τ.block τ.measurable τ.positive τ.integrable
    sigma.block sigma.measurable sigma.positive sigma.integrable
  have he : (p.firstBit.purifiedDensity R hR.1 P hP ν hμν).idealBitError sigma.block =
      cqBitError (fun i j t => firstBitBlocks (fun a b => τ.block a b t) i j) sigma.block ν := by
    rw [BitDensity.idealBitError_eq_cq]
    unfold cqBitError
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [p.firstBit_purifiedOutputDensity R hR.1 P hP ν hμν i j] with t ht
    rw [ht]
    rfl
  have hg := p.firstBit.uniform_gap_purification_dominated R hR P hP ν hμν sigma
  rw [he] at hg
  exact hg.trans hc

end ZeroKey

end

end OAI
