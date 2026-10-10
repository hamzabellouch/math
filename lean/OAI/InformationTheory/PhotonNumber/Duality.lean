import OAI.InformationTheory.PhotonNumber.Contraction

namespace OAI

noncomputable section

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation BeamLadder TensorLp ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
theorem ambientDefect_normalize (t : ℝ) (ht : 0<t) (j : Fin n) (lam : ℝ)
    (Z : Fock n →L[ℂ] Fock n) :
    G.ambientDefect t ht j ((G.thermalSpace t ht).observable ((G.thermalSpace t ht).normalize lam Z))=
      (Real.sqrt lam:ℂ)⁻¹*G.weightedColumns.centeredWeak t j Z := by
  let f : (Fock n →L[ℂ] Fock n) →ₗ[ℂ] ℂ :=
    (G.ambientDefect t ht j).toLinearMap.comp (G.thermalSpace t ht).observable
  have hf : f 1=0 := G.ambientDefect_one t ht j
  have hZ : f Z=G.weightedColumns.centeredWeak t j Z := G.ambientDefect_centered t ht j Z
  change f ((Real.sqrt lam:ℂ)⁻¹ • (Z-BKM.mean G.basis G.probability Z •
    (1:Fock n →L[ℂ] Fock n)))=_
  rw [map_smul, map_sub, map_smul, hf, smul_zero, sub_zero, hZ]
  rfl
end EntropyPhotonNumber.SpectralLogData

section
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace TensorLp
open EntropyPhotonNumber
variable {A B I J : Type*}

theorem conditionalLeft_eq_of_operator (x : I → H B) (y : J → H B)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (he : TraceEnsemble.operator x=TraceEnsemble.operator y)
    (Z : H (A × B) →L[ℂ] H (A × B)) : conditionalLeft x hx Z=conditionalLeft y hy Z := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  rw [← (conditionalLeft_entry x hx Z u v).tsum_eq, ← (conditionalLeft_entry y hy Z u v).tsum_eq]
  let bas : HilbertBasis B ℂ (H B) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hh := CrossEnsemble.pairing_eq_of_operator_eq bas hx.summable hx.summable hy.summable hy.summable
    he ((tensorLeft u).adjoint ∘L Z ∘L tensorLeft v)
  simpa only [CrossEnsemble.pairing, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, tensorLeft_apply] using hh

theorem conditionalRight_eq_of_operator (x : I → H A) (y : J → H A)
    (hx : HasSum (fun i => ‖x i‖^2) 1) (hy : HasSum (fun j => ‖y j‖^2) 1)
    (he : TraceEnsemble.operator x=TraceEnsemble.operator y)
    (Z : H (A × B) →L[ℂ] H (A × B)) : conditionalRight x hx Z=conditionalRight y hy Z := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  rw [← (conditionalRight_entry x hx Z u v).tsum_eq, ← (conditionalRight_entry y hy Z u v).tsum_eq]
  let bas : HilbertBasis A ℂ (H A) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hh := CrossEnsemble.pairing_eq_of_operator_eq bas hx.summable hx.summable hy.summable hy.summable
    he ((tensorRight u).adjoint ∘L Z ∘L tensorRight v)
  simpa only [CrossEnsemble.pairing, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, tensorRight_apply] using hh
end TensorLp

namespace EntropyPhotonNumber
open TensorLp KrausBounded BeamLadder Annihilation
variable {n : ℕ}

theorem joint_dual_conjugate (η : ℝ) (hη : η ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n) :
    dual (jointKraus η hη) (jointKraus_norm η hη) Z=conjugate η hη Z := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [conjugate_inner]
  exact (dual_entry _ _ Z x y).unique (by
    simpa only [jointKraus, ContinuousLinearMap.comp_apply, sliceCLM_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe, slice_liftLeft]
      using hasSum_slice_inner (beamUnitary η hη x) (liftLeft Z (beamUnitary η hη y)))

theorem first_dual_conditional (η : ℝ) (hη : η ∈ Set.Icc 0 1) (σ : State n)
    (Z : Fock n →L[ℂ] Fock n) :
    dual (firstKraus η hη σ) (firstKraus_norm η hη σ) Z=
      conditionalLeft (rootColumn σ) (rootColumn_norm σ) (conjugate η hη Z) := by
  let V := fun j => tensorRight (A:=NumberIndex n) (rootColumn σ j)
  let U := jointKraus (n:=n) η hη
  have hV := rightFamily_norm (rootColumn σ) (rootColumn_norm σ) (A:=NumberIndex n)
  have hU := jointKraus_norm (n:=n) η hη
  have hr := dual_reindex (Equiv.prodComm _ _) (composite V U) (composite_norm V U hV hU)
    (fun x => (Equiv.prodComm _ _).hasSum_iff.mpr (composite_norm V U hV hU x)) Z
  change dual (firstKraus η hη σ) _ Z=dual (composite V U) _ Z at hr
  rw [hr, dual_composite V U hV hU]
  change dual V hV (dual (jointKraus η hη) hU Z)=_
  rw [joint_dual_conjugate]
  rfl

namespace WeightedColumns
variable {ρ σ τ : State n}

theorem rawSlice_root (X : WeightedColumns ρ) (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (Z : Fock n →L[ℂ] Fock n) :
    X.rawSlice η hη Z=conditionalLeft (rootColumn ρ) (rootColumn_norm ρ) (conjugate η hη Z) := by
  apply conditionalLeft_eq_of_operator
  exact X.density.trans (rootColumn_operator ρ).symm

theorem rawSliceRight_root (X : WeightedColumns ρ) (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (Z : Fock n →L[ℂ] Fock n) :
    X.rawSliceRight η hη Z=conditionalRight (rootColumn ρ) (rootColumn_norm ρ) (conjugate η hη Z) := by
  apply conditionalRight_eq_of_operator
  exact X.density.trans (rootColumn_operator ρ).symm

theorem rawSlice_dual (X : WeightedColumns ρ) (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (Z : Fock n →L[ℂ] Fock n) :
    X.rawSlice η hη Z=dual (firstKraus η hη ρ) (firstKraus_norm η hη ρ) Z := by
  rw [X.rawSlice_root, first_dual_conditional]

theorem rawFirstSlice_physical (Y : WeightedColumns σ) (D : WeightedColumns τ)
    (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n) :
    rawFirstSlice η θ hη hθ σ τ Z=Y.rawSlice η hη (D.rawSlice θ hθ Z) := by
  rw [Y.rawSlice_root, D.rawSlice_dual]
  unfold rawFirstSlice rawDual rawJointKraus
  rw [dual_composite _ _ (jointKraus_norm η hη) (firstKraus_norm θ hθ τ), joint_dual_conjugate]

theorem rawSecondSlice_physical (X : WeightedColumns ρ) (D : WeightedColumns τ)
    (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (Z : Fock n →L[ℂ] Fock n) :
    rawSecondSlice η θ hη hθ ρ τ Z=X.rawSliceRight η hη (D.rawSlice θ hθ Z) := by
  rw [X.rawSliceRight_root, D.rawSlice_dual]
  unfold rawSecondSlice rawDual rawJointKraus
  rw [dual_composite _ _ (jointKraus_norm η hη) (firstKraus_norm θ hθ τ), joint_dual_conjugate]
end WeightedColumns
end EntropyPhotonNumber

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def scalarTarget (q : (E →L[ℂ] E) →ₗ[ℂ] ℂ) :
    (E →L[ℂ] E) →ₗ[ℂ] (Unit → ℂ) where
  toFun Z _ := q Z
  map_add' X Y := by ext; exact map_add q X Y
  map_smul' c X := by ext; exact q.map_smul c X

def scalarDiagram (S : Space E) (q : (E →L[ℂ] E) →ₗ[ℂ] ℂ) :
    DiagonalForms.System (Option Param) (S.I × S.I) Unit :=
  CenteredTests.system S.basis S.p S.pos S.sum.summable (h S.r) (h_pos S.rpos)
    (fun ij => some (S.pparam ij)) (some (⟨S.r,S.rpos⟩,0))
    (fun j => by simp [Space.pparam, Space.param, frequency])
    (fun _ => none) (scalarTarget q)

def scalarWeight (w : Param → ℝ) : Option Param → ℝ
  | none => 1
  | some p => w p

theorem scalar_comparison (S : Space E) (q : (E →L[ℂ] E) →ₗ[ℂ] ℂ)
    (w : Param → ℝ)
    (hh : ∀ Z, Z ∈ CenteredTests.operatorSpace S.basis S.p →
      Complex.normSq (q Z) ≤ S.pquad w Z) :
    (scalarDiagram S q).Comparison (scalarWeight w) := by
  intro z s
  let Z := CenteredTests.realize S.basis S.p S.base S.base_pos z
  have hz : S.coords Z=z.val := CenteredTests.realize_entries S.basis S.p S.base S.base_pos z
  have hm : Z ∈ CenteredTests.operatorSpace S.basis S.p :=
    CenteredTests.realize_mem S.basis S.p S.base S.base_pos z
  have hh' := hh Z hm
  have ht : (∑ _u ∈ s, Complex.normSq (q Z)) ≤ Complex.normSq (q Z) := by
    have hh := (hasSum_fintype (fun _u : Unit => Complex.normSq (q Z))).summable.sum_le_tsum
      s (fun _ _ => Complex.normSq_nonneg _)
    simpa using hh
  change (∑ _u ∈ s, 1*Complex.normSq (q Z)) ≤ _
  simp only [one_mul]
  convert! ht.trans hh' using 1
  simp only [sourceForm, scalarDiagram, CenteredTests.system, scalarWeight, Space.pquad, hz]

theorem scalar_logMean_bound (S : Space E) (q : (E →L[ℂ] E) →ₗ[ℂ] ℂ)
    (v w : Param → ℝ) (hv : ∀ p, 0 < v p) (hw : ∀ p, 0 < w p)
    (hV : ∀ Z, Z ∈ CenteredTests.operatorSpace S.basis S.p →
      Complex.normSq (q Z) ≤ S.pquad v Z)
    (hW : ∀ Z, Z ∈ CenteredTests.operatorSpace S.basis S.p →
      Complex.normSq (q Z) ≤ S.pquad w Z)
    (Z : E →L[ℂ] E) (hZ : Z ∈ CenteredTests.operatorSpace S.basis S.p) :
    Complex.normSq (q Z) ≤ S.pquad (fun p => logMean (v p) (w p)) Z := by
  let D := scalarDiagram S q
  have hv' : ∀ p, 0 < scalarWeight v p := by intro p; cases p <;> simp [scalarWeight,hv]
  have hw' : ∀ p, 0 < scalarWeight w p := by intro p; cases p <;> simp [scalarWeight,hw]
  have hi := D.comparison_logMean (scalar_comparison S q v hV) (scalar_comparison S q w hW) hv' hw'
  let z : D.tests := ⟨S.coords Z, ⟨Z,hZ,rfl⟩⟩
  have hz : CenteredTests.realize S.basis S.p S.base S.base_pos z=Z := by
    apply CenteredTests.entryMap_injective S.basis S.base S.base_pos
    exact CenteredTests.realize_entries S.basis S.p S.base S.base_pos z
  have hh := hi z Finset.univ
  change (∑ _u : Unit, logMean 1 1*Complex.normSq (q
    (CenteredTests.realize S.basis S.p S.base S.base_pos z))) ≤ _ at hh
  rw [hz] at hh
  simpa only [logMean_self, one_mul, Finset.univ_unique, Finset.sum_singleton,
    sourceForm, D, scalarDiagram, CenteredTests.system, scalarWeight, Space.pquad, z]
    using hh

theorem scalar_arithmetic_BKM (S : Space E) (q : (E →L[ℂ] E) →ₗ[ℂ] ℂ)
    (hV : ∀ Z, Z ∈ CenteredTests.operatorSpace S.basis S.p →
      Complex.normSq (q Z) ≤ S.pquad plusWeight Z)
    (hW : ∀ Z, Z ∈ CenteredTests.operatorSpace S.basis S.p →
      Complex.normSq (q Z) ≤ S.pquad minusWeight Z)
    (Z : E →L[ℂ] E) (hZ : Z ∈ CenteredTests.operatorSpace S.basis S.p) :
    Complex.normSq (q Z) ≤ S.pquad (fun _ => 1/h S.r) Z := by
  have hh := scalar_logMean_bound S q plusWeight minusWeight plusWeight_pos minusWeight_pos hV hW Z hZ
  convert! hh using 1
  apply tsum_congr
  intro a
  congr 1
  exact (EntropyPhotonNumber.logarithmicMean_exp_pair (one_div_pos.mpr (h_pos S.rpos))
    (h S.r*(S.param a).2/2)).symm

end ThermalSpectral

end

open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology Complex MeasureTheory

namespace EnsembleL2
open scoped BigOperators ComplexConjugate
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def meanLM (v : I → E) (hv : Summable (fun i => ‖v i‖^2)) :
    (E →L[ℂ] E) →ₗ[ℂ] ℂ where
  toFun := mean v
  map_add' Z Y := by
    unfold mean
    simp only [add_apply, inner_add_right]
    exact (mean_hasSum v hv Z).summable.tsum_add (mean_hasSum v hv Y).summable
  map_smul' c Z := by
    simp only [mean, smul_apply, inner_smul_right, tsum_mul_left, smul_eq_mul, RingHom.id_apply]
def mixtureFunctional (v : I → E) (w : J → E)
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (t : ℝ) : (E →L[ℂ] E) →ₗ[ℂ] ℂ :=
  (Real.sqrt (t*(1-t)) : ℂ) • (meanLM v hv-meanLM w hw)

omit [CompleteSpace E] in
theorem mixtureFunctional_apply (v : I → E) (w : J → E)
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (t : ℝ) (Z : E →L[ℂ] E) :
    mixtureFunctional v w hv hw t Z = (Real.sqrt (t*(1-t)) : ℂ)*(mean v Z-mean w Z) := rfl

omit [CompleteSpace E] in
theorem mixtureFunctional_square (v : I → E) (w : J → E)
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (Z : E →L[ℂ] E) :
    Complex.normSq (mixtureFunctional v w hv hw t Z)=t*(1-t)*‖mean v Z-mean w Z‖^2 := by
  rw [mixtureFunctional_apply, Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)), Complex.normSq_eq_norm_sq]

theorem mixtureFunctional_adjoint_square (v : I → E) (w : J → E)
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (Z : E →L[ℂ] E) :
    Complex.normSq (mixtureFunctional v w hv hw t Z.adjoint)=
      Complex.normSq (mixtureFunctional v w hv hw t Z) := by
  simp only [mixtureFunctional_square v w hv hw ht, mean_adjoint, ← map_sub,
    Complex.norm_conj]
end EnsembleL2

namespace ThermalSpectral
open EntropyPhotonNumber DiagonalForms.System ThermalMetric
open scoped BigOperators
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem mixture_arithmetic_bounds (S : Space E) (v : I → E) (w : J → E)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1)
    (he : TraceEnsemble.operator S.ensemble=TraceEnsemble.operator (EnsembleL2.mixture v w t))
    (Z : E →L[ℂ] E) (hZ : Z ∈ CenteredTests.operatorSpace S.basis S.p) :
    Complex.normSq (EnsembleL2.mixtureFunctional v w hv.summable hw.summable t Z) ≤ S.pquad plusWeight Z ∧
    Complex.normSq (EnsembleL2.mixtureFunctional v w hv.summable hw.summable t Z) ≤ S.pquad minusWeight Z := by
  let u := EnsembleL2.mixture v w t
  have hu : HasSum (fun a => ‖u a‖^2) 1 := EnsembleL2.mixture_hasSum v w ht hv hw
  have hz : EnsembleL2.mean u Z=0 := by
    rw [← EnsembleL2.mean_eq_of_operator_eq S.basis S.ensemble_hasSum.summable hu.summable he Z,
      S.ensemble_mean]
    exact CenteredTests.mean_eq_zero S.basis S.p (fun j => (S.pos j).le) S.sum hZ
  have hza : EnsembleL2.mean u Z.adjoint=0 := by rw [EnsembleL2.mean_adjoint, hz, map_zero]
  have hc : EnsembleL2.center u Z=Z := by simp only [EnsembleL2.center,hz,zero_smul,sub_zero]
  have hca : EnsembleL2.center u Z.adjoint=Z.adjoint := by simp only [EnsembleL2.center,hza,zero_smul,sub_zero]
  have hm := EnsembleL2.mixture_between_variance v w ht hv hw Z
  have hp := EnsembleL2.mixture_between_variance v w ht hv hw Z.adjoint
  change _ ≤ EnsembleL2.secondMoment u (EnsembleL2.center u Z) at hm
  change _ ≤ EnsembleL2.secondMoment u (EnsembleL2.center u Z.adjoint) at hp
  rw [hc] at hm
  rw [hca] at hp
  rw [← EnsembleL2.mixtureFunctional_square v w hv.summable hw.summable ht Z] at hm
  rw [← EnsembleL2.mixtureFunctional_square v w hv.summable hw.summable ht Z.adjoint,
    EnsembleL2.mixtureFunctional_adjoint_square v w hv.summable hw.summable ht Z] at hp
  constructor
  · change _ ≤ S.quad Space.plus Z
    rw [S.plus_quad_of_ensemble u hu.summable he Z]
    exact hp
  · change _ ≤ S.quad Space.minus Z
    rw [S.minus_quad_of_ensemble u hu.summable he Z]
    exact hm

theorem mixture_BKM_bound (S : Space E) (v : I → E) (w : J → E)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1)
    (he : TraceEnsemble.operator S.ensemble=TraceEnsemble.operator (EnsembleL2.mixture v w t))
    (Z : E →L[ℂ] E) (hZ : Z ∈ CenteredTests.operatorSpace S.basis S.p) :
    Complex.normSq (EnsembleL2.mixtureFunctional v w hv.summable hw.summable t Z) ≤
      S.pquad (fun _ => 1/h S.r) Z :=
  scalar_arithmetic_BKM S _ (fun Y hY => (mixture_arithmetic_bounds S v w ht hv hw he Y hY).1)
    (fun Y hY => (mixture_arithmetic_bounds S v w ht hv hw he Y hY).2) Z hZ
end ThermalSpectral

namespace ThermalDual

variable {I J : Type*} [Fintype I] [Fintype J]

theorem weighted_sum_bound (w a b : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∑ i, w i*a i*b i ≤ Real.sqrt (∑ i, w i*a i^2)*Real.sqrt (∑ i, w i*b i^2) := by
  have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => Real.sqrt (w i)*a i) (fun i => Real.sqrt (w i)*b i)
  have he (i : I) : Real.sqrt (w i)*a i*(Real.sqrt (w i)*b i)=w i*a i*b i := by
    linear_combination a i*b i*(Real.sq_sqrt (hw i))
  simpa only [he, mul_pow, Real.sq_sqrt (hw _)] using hh

theorem weighted_functionals_bound (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (E : I → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    (q : (i : I) → E i →L[ℂ] ℂ) (z : (i : I) → E i) :
    ‖∑ i, (w i:ℂ)*q i (z i)‖ ≤
      Real.sqrt (∑ i, w i*‖q i‖^2)*Real.sqrt (∑ i, w i*‖z i‖^2) := by
  calc
    _ ≤ ∑ i, ‖(w i:ℂ)*q i (z i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, w i*‖q i‖*‖z i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw i), mul_assoc]
      exact mul_le_mul_of_nonneg_left ((q i).le_opNorm (z i)) (hw i)
    _ ≤ _ := weighted_sum_bound w (fun i => ‖q i‖) (fun i => ‖z i‖) hw

theorem modes_triangle (q a b : J → ℝ) (hq : ∀ j, 0 ≤ q j)
    (_ha : ∀ j, 0 ≤ a j) (_hb : ∀ j, 0 ≤ b j) (hh : ∀ j, q j ≤ a j+b j) :
    Real.sqrt (∑ j, q j^2) ≤ Real.sqrt (∑ j, a j^2)+Real.sqrt (∑ j, b j^2) := by
  have hs : ∑ j, q j^2 ≤ ∑ j, (a j+b j)^2 := by
    exact Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (hq j) (hh j) 2)
  have he : (∑ j, (a j+b j)^2)=(∑ j, a j^2)+2*(∑ j, a j*b j)+(∑ j, b j^2) := by
    simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    ring_nf
  rw [he] at hs
  have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
  have hqa := Real.sq_sqrt (show 0 ≤ ∑ j, a j^2 from Finset.sum_nonneg (fun j _ => sq_nonneg (a j)))
  have hqb := Real.sq_sqrt (show 0 ≤ ∑ j, b j^2 from Finset.sum_nonneg (fun j _ => sq_nonneg (b j)))
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith

theorem defect_young {x a m C κ ε : ℝ}
    (hx : 0 ≤ x) (_ha : 0 ≤ a) (_hm : 0 ≤ m) (hC : 0 < C) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hk : κ ≤ ε^2/(4*(ε+2)*C^2))
    (ht : x ≤ a+Real.sqrt (2*κ)*C*m) :
    x^2 ≤ a^2+ε/2*(a^2+m^2) := by
  let t := Real.sqrt (2*κ)*C
  have htpos : 0 ≤ t := mul_nonneg (Real.sqrt_nonneg _) hC.le
  have ht2 : t^2=2*κ*C^2 := by
    dsimp only [t]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hkd : 0 < 4*(ε+2)*C^2 := by positivity
  have hk' := (le_div_iff₀ hkd).mp hk
  have htb : 2*(ε+2)*t^2 ≤ ε^2 := by nlinarith [ht2]
  have htbm := mul_le_mul_of_nonneg_right htb (sq_nonneg m)
  have hy := sq_nonneg (ε*a-2*t*m)
  have ht' : x^2 ≤ (a+t*m)^2 := pow_le_pow_left₀ hx ht 2
  have htx := mul_le_mul_of_nonneg_left ht' hε.le
  have hh : ε*(x^2-(a^2+ε/2*(a^2+m^2))) ≤ 0 := by
    nlinarith
  exact sub_nonpos.mp ((mul_le_mul_iff_of_pos_left hε).mp (by simpa only [mul_zero] using hh))
end ThermalDual

namespace ThermalSpectral
open EntropyPhotonNumber ThermalMetric
variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem mixture_thermal_bound (S : Space E) (v : I → E) (w : J → E)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hw : HasSum (fun j => ‖w j‖^2) 1)
    (he : TraceEnsemble.operator S.ensemble=TraceEnsemble.operator (EnsembleL2.mixture v w t))
    (Z : E →L[ℂ] E) (hZ : Z ∈ CenteredTests.operatorSpace S.basis S.p) :
    ‖EnsembleL2.mixtureFunctional v w hv.summable hw.summable t Z‖ ≤
      mixtureConstant S.r*‖S.observable Z‖ := by
  have hh := (mixture_BKM_bound S v w ht hv hw he Z hZ).trans (S.BKM_thermal_bound Z)
  rw [Complex.normSq_eq_norm_sq] at hh
  have hm := mul_nonneg (mixtureConstant_pos S.rpos).le (norm_nonneg (S.observable Z))
  nlinarith [norm_nonneg (EnsembleL2.mixtureFunctional v w hv.summable hw.summable t Z)]
end ThermalSpectral

namespace ThermalDual

section
open EntropyPhotonNumber ThermalMetric ThermalSpectral
open scoped BigOperators
variable {E I J K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [Fintype K]

theorem dual_bound_from_core (S₀ : Space E) (S : K → Space E)
    (w : K → ℝ) (hw : ∀ i, 0 ≤ w i)
    (L : (i : K) → (E →L[ℂ] E) →ₗ[ℂ] (E →L[ℂ] E))
    (q₀ : lp (fun _ : S₀.I × S₀.I => ℂ) 2 →L[ℂ] ℂ)
    (q : (i : K) → lp (fun _ : (S i).I × (S i).I => ℂ) 2 →L[ℂ] ℂ)
    (v : I → E) (u : J → E) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hv : HasSum (fun i => ‖v i‖^2) 1) (hu : HasSum (fun j => ‖u j‖^2) 1)
    (he : TraceEnsemble.operator S₀.ensemble=TraceEnsemble.operator (EnsembleL2.mixture v u t))
    (c : ℂ)
    (hL : ∀ Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      ∑ i, w i*(S i).pquad thermalWeight (L i Z) ≤ S₀.pquad thermalWeight Z)
    (hq : ∀ Z, Z ∈ CenteredTests.operatorSpace S₀.basis S₀.p →
      q₀ (S₀.observable Z) = (∑ i, (w i:ℂ)*q i ((S i).observable (L i Z)))+
        c*EnsembleL2.mixtureFunctional v u hv.summable hu.summable t Z) :
    ‖q₀.comp (centeredSpace S₀.r S₀.rpos S₀.p S₀.pos S₀.sum.summable).subtypeL‖ ≤
      Real.sqrt (∑ i, w i*‖q i‖^2)+‖c‖*mixtureConstant S₀.r := by
  apply restricted_norm_bound_of_core S₀.basis S₀.p S₀.pos S₀.sum S₀.r S₀.rpos q₀ _
    (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (mixtureConstant_pos S₀.rpos).le))
  intro Z hZ
  change ‖q₀ (S₀.observable Z)‖ ≤ _*‖S₀.observable Z‖
  rw [hq Z hZ]
  have hh := weighted_functionals_bound w hw
    (fun i => lp (fun _ : (S i).I × (S i).I => ℂ) 2) q (fun i => (S i).observable (L i Z))
  have hc : ∑ i, w i*‖(S i).observable (L i Z)‖^2 ≤ ‖S₀.observable Z‖^2 := by
    simpa only [Space.observable_norm_sq] using hL Z hZ
  have hs : Real.sqrt (∑ i, w i*‖(S i).observable (L i Z)‖^2) ≤ ‖S₀.observable Z‖ := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using Real.sqrt_le_sqrt hc
  have hj := mixture_thermal_bound S₀ v u ht hv hu he Z hZ
  calc
    _ ≤ ‖∑ i, (w i:ℂ)*q i ((S i).observable (L i Z))‖+
        ‖c*EnsembleL2.mixtureFunctional v u hv.summable hu.summable t Z‖ := norm_add_le _ _
    _ ≤ Real.sqrt (∑ i, w i*‖q i‖^2)*‖S₀.observable Z‖+
        ‖c‖*(mixtureConstant S₀.r*‖S₀.observable Z‖) :=
      add_le_add (hh.trans (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)))
        (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hj (norm_nonneg _))
    _ = _ := by ring
end

section
variable {I J : Type*} [Fintype I] [Fintype J]

theorem two_sqrt_norm_sq (a b : ℝ) (ha : 0≤a) (hb : 0≤b) (x y : ℂ) :
    ‖(Real.sqrt a:ℂ)*x+(Real.sqrt b:ℂ)*y‖^2 ≤ 2*(a*‖x‖^2+b*‖y‖^2) := by
  have hn := pow_le_pow_left₀ (norm_nonneg ((Real.sqrt a:ℂ)*x+(Real.sqrt b:ℂ)*y))
    (norm_add_le ((Real.sqrt a:ℂ)*x) ((Real.sqrt b:ℂ)*y)) 2
  have hp := sq_nonneg (‖(Real.sqrt a:ℂ)*x‖-‖(Real.sqrt b:ℂ)*y‖)
  have he (r : ℝ) (hr : 0≤r) (z : ℂ) : ‖(Real.sqrt r:ℂ)*z‖^2=r*‖z‖^2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hr]
  nlinarith [he a ha x, he b hb y]

theorem aggregate_bound (w : I → ℝ) (hw : ∀ i, 0≤w i)
    (q0 g : J → ℝ) (q m : I → J → ℝ) (hq : ∀ j, 0≤q0 j)
    (hg : ∀ j, 0≤g j) (C κ : ℝ) (hC : 0≤C) (hκ : κ ∈ Set.Icc 0 1)
    (hm : ∀ j, (1-κ)*g j^2≤2*∑ i, w i*m i j^2)
    (hmode : ∀ j, q0 j≤Real.sqrt (∑ i, w i*q i j^2)+Real.sqrt ((1-κ)*κ)*g j*C) :
    Real.sqrt (∑ j, q0 j^2)≤Real.sqrt (∑ i, w i*∑ j, q i j^2)+
      Real.sqrt (2*κ)*C*Real.sqrt (∑ i, w i*∑ j, m i j^2) := by
  have hqsum j : 0≤∑ i, w i*q i j^2 := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  have hmsum : 0≤∑ i, w i*∑ j, m i j^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (Finset.sum_nonneg (fun j _ => sq_nonneg _)))
  have hh := modes_triangle q0 (fun j => Real.sqrt (∑ i, w i*q i j^2))
    (fun j => Real.sqrt ((1-κ)*κ)*g j*C) hq (fun _ => Real.sqrt_nonneg _)
    (fun j => mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hg j)) hC) hmode
  have hqa : (∑ j, (Real.sqrt (∑ i, w i*q i j^2))^2)=∑ i, w i*∑ j, q i j^2 := by
    simp only [Real.sq_sqrt (hqsum _), Finset.mul_sum]
    exact Finset.sum_comm
  have hgm : (1-κ)*(∑ j, g j^2)≤2*(∑ i, w i*∑ j, m i j^2) := by
    calc
      _ = ∑ j, (1-κ)*g j^2 := Finset.mul_sum ..
      _ ≤ ∑ j, 2*∑ i, w i*m i j^2 := Finset.sum_le_sum (fun j _ => hm j)
      _ = 2*∑ i, w i*∑ j, m i j^2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.mul_sum]
  have hc : (∑ j, (Real.sqrt ((1-κ)*κ)*g j*C)^2) ≤
      (Real.sqrt (2*κ)*C*Real.sqrt (∑ i, w i*∑ j, m i j^2))^2 := by
    simp only [mul_pow, Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hκ.2) hκ.1),
      Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hκ.1), Real.sq_sqrt hmsum]
    calc
      _ = (κ*C^2)*((1-κ)*∑ j, g j^2) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ (κ*C^2)*(2*(∑ i, w i*∑ j, m i j^2)) :=
        mul_le_mul_of_nonneg_left hgm (mul_nonneg hκ.1 (sq_nonneg C))
      _ = _ := by ring
  have hc' := Real.sqrt_le_sqrt hc
  rw [Real.sqrt_sq (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC) (Real.sqrt_nonneg _))] at hc'
  rw [hqa] at hh
  exact hh.trans (add_le_add le_rfl hc')
end

open scoped ComplexConjugate

theorem real_mul_inverse_sqrt {a : ℝ} (ha : 0<a) :
    (a:ℂ)*(Real.sqrt a:ℂ)⁻¹=(Real.sqrt a:ℂ) := by
  have hn : (Real.sqrt a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ha).ne'
  apply (mul_right_cancel₀ hn)
  rw [mul_assoc, inv_mul_cancel₀ hn, mul_one, ← Complex.ofReal_mul, Real.mul_self_sqrt ha.le]
end ThermalDual

end

end OAI
