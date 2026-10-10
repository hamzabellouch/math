import OAI.NumberTheory.DirichletL.Reflection.CoprimeSource

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def finitePhysicalKernelRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb : ℝ)
    (W : ℝ→ℂ) (θ X : ℝ) : ℂ :=
  ∑ x : CoprimeSourceIndex K Pset nset bset,
    actualKernelSourceTerm F K hK (S x.1.val.val) jF (D x.1.val x.1.property) s hc
      u m x.2.1.val x.2.2.val windows QK QP Qn Qb W θ X

def weightedFinitePhysicalKernelRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb : ℝ)
    (W : ℝ→ℂ) (θ X : ℝ) (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ) : ℂ :=
  ∑ x : CoprimeSourceIndex K Pset nset bset,
    (r₀ K*aw₀ x.1.val.val*w₀ x.2.1.val x.2.2.val)*actualKernelSourceTerm F K hK (S x.1.val.val) jF (D x.1.val x.1.property) s hc
      u m x.2.1.val x.2.2.val windows QK QP Qn Qb W θ X

theorem weighted_finite_physical_row_common_measure
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ (K : Ideal Eis) (hK : Admissible K) (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ)
        (Pset nset bset : Finset (Ideal Eis))
        (D : ∀ P : Pset, IsCoprime K P.val →
          ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode),
        (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) → (∀ n ∈ nset, n≠0) → (∀ b ∈ bset, b≠0) →
        ∀ (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
        weightedFinitePhysicalKernelRow F K hK S jF Pset nset bset D s hc unit m windows QK QP Qn Qb W θ X r₀ aw₀ w₀ =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            weightedPhysicalReflectedRow F K hK S jF Pset nset bset D s hc
              (fun K => r₀ K*kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm K:ℝ))
              (fun P => aw₀ P*kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm P:ℝ))
              (fun n b => w₀ n b*kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ)) unit m) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := actual_reflected_finite_source_uniform
    (φ := φ) (σ := σ) (N := N) (a := a) (c := c) (mode := mode)
    a₀ b₀ ha₀ windows M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  obtain ⟨he,hi,hiJ,hm,hp⟩ := hsep F s hc unit m θ X QK QP Qn Qb hX hQK hQP hQn hQb
  refine ⟨?_,hi,hiJ,hm,hp⟩
  intro K hK S jF Pset nset bset D hprod hn hb r₀ aw₀ w₀
  let T := CoprimeSourceIndex K Pset nset bset
  have hh := he (Finset.univ : Finset T) (fun x => r₀ K*aw₀ x.1.val.val*w₀ x.2.1.val x.2.2.val) (fun _ => K) (fun _ => hK)
    (fun x => S x.1.val.val) jF (fun x => D x.1.val x.1.property)
    (fun x => x.2.1.val) (fun x => x.2.2.val)
    (fun x _ => ⟨hn _ x.2.1.property,hb _ x.2.2.property⟩)
  unfold weightedFinitePhysicalKernelRow
  rw [hh]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only [T]
  congr 1
  rw [weightedPhysicalReflectedRow_eq_coprime_source]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hprod x.1.val.val x.1.val.property]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
