import OAI.InformationTheory.PhotonNumber.PhysicalMinimum
import OAI.InformationTheory.PhotonNumber.Duality

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open scoped ComplexConjugate
open ContinuousLinearMap
open Set Filter Topology _root_.Complex _root_.OAI.Complex Metric
open MeasureTheory Set Filter Topology _root_.Complex _root_.OAI.Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open Set Filter Topology _root_.Complex _root_.OAI.Complex MeasureTheory

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation BeamLadder TensorLp ThermalMetric ThermalSpectral
open scoped ComplexConjugate
variable {n : ℕ}

def twoPortLambda (η θ : ℝ) : Fin 2 → ℝ := ![θ*η,θ*(1-η)]

def outputReference (η θ : ℝ) (a : Fin 2 → ℝ) (d : ℝ) : ℝ :=
  θ*(η*a 0+(1-η)*a 1)+(1-θ)*d

theorem twoPortLambda_pos {η θ : ℝ} (hη : η ∈ Set.Ioo 0 1) (hθ : 0<θ) (i : Fin 2) :
    0<twoPortLambda η θ i := by
  fin_cases i
  · exact mul_pos hθ hη.1
  · exact mul_pos hθ (sub_pos.mpr hη.2)

theorem physical_defect_convolution (η θ κ d : ℝ) (a : Fin 2 → ℝ)
    (hη : η ∈ Set.Ioo 0 1) (hθ : θ ∈ Set.Ioo 0 1) (hκ : κ ∈ Set.Icc 0 1)
    (hd : 0<d) (ha : ∀ i, 0<a i) (hr0 : 0<outputReference η θ a d)
    (ρ : Fin 2 → State n) (τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η (ρ 0) (ρ 1) m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (G : (i : Fin 2) → SpectralLogData n (ρ i)) (G0 : SpectralLogData n ρ0)
    (D : WeightedColumns τD) (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω)
    (hD : ∀ k l, entry τD.op k l=if k=l then (QuantumTrace.thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (QuantumTrace.thermalWeight n (outputReference η θ a d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (j : Fin n) (Z : Fock n →L[ℂ] Fock n) :
    G0.ambientDefect (outputReference η θ a d) hr0 j
        ((G0.thermalSpace (outputReference η θ a d) hr0).observable Z)=
      (∑ i, (((1-κ)*twoPortLambda η θ i:ℝ):ℂ)*
        (G i).ambientDefect (a i) (ha i) j ((G i).thermalSpace (a i) (ha i) |>.observable
          (normalizedSlices η θ ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 0) (ρ 1) τD
            (fun i => (G i).thermalSpace (a i) (ha i)) (twoPortLambda η θ) i Z)))+
      ((Real.sqrt ((1-κ)*κ):ℂ)*V.weakMean (outputReference η θ a d) j)*
        EnsembleL2.mixtureFunctional (fun k => inverseWeight 3 (V.vector k))
          (fun k => inverseWeight 3 (O.vector k)) V.normalized.summable O.normalized.summable (1-κ) Z := by
  change 0<η ∧ η<1 at hη
  change 0<θ ∧ θ<1 at hθ
  rw [G0.ambientDefect_centered]
  unfold outputReference
  have hp := replaced_threeport_centered_weak η θ κ (a 0) (a 1) d
    ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 0) (ρ 1) τD m γ ω ρ0 h1 h2
    (G 0).weightedColumns (G 1).weightedColumns D M V O G0.weightedColumns hd hr0 hD hO hrepl j Z
  rw [hp]
  have hηc : η ∈ Set.Icc 0 1 := ⟨hη.1.le,hη.2.le⟩
  have hθc : θ ∈ Set.Icc 0 1 := ⟨hθ.1.le,hθ.2.le⟩
  have hl0 : normalizedSlices η θ hηc hθc (ρ 0) (ρ 1) τD
      (fun i => (G i).thermalSpace (a i) (ha i)) (twoPortLambda η θ) 0 Z=
      ((G 0).thermalSpace (a 0) (ha 0)).normalize (twoPortLambda η θ 0)
        ((G 1).weightedColumns.rawSlice η hηc (D.rawSlice θ hθc Z)) := by
    change ((G 0).thermalSpace (a 0) (ha 0)).normalize (twoPortLambda η θ 0)
      (rawFirstSlice η θ hηc hθc (ρ 1) τD Z)=_
    rw [WeightedColumns.rawFirstSlice_physical (G 1).weightedColumns D]
  have hl1 : normalizedSlices η θ hηc hθc (ρ 0) (ρ 1) τD
      (fun i => (G i).thermalSpace (a i) (ha i)) (twoPortLambda η θ) 1 Z=
      ((G 1).thermalSpace (a 1) (ha 1)).normalize (twoPortLambda η θ 1)
        ((G 0).weightedColumns.rawSliceRight η hηc (D.rawSlice θ hθc Z)) := by
    change ((G 1).thermalSpace (a 1) (ha 1)).normalize (twoPortLambda η θ 1)
      (rawSecondSlice η θ hηc hθc (ρ 0) τD Z)=_
    rw [WeightedColumns.rawSecondSlice_physical (G 0).weightedColumns D]
  simp only [Fin.sum_univ_two, hl0, hl1]
  rw [(G 0).ambientDefect_normalize, (G 1).ambientDefect_normalize]
  have hs (i : Fin 2) :
      ((((1-κ)*twoPortLambda η θ i:ℝ):ℂ)*(Real.sqrt (twoPortLambda η θ i):ℂ)⁻¹)=
        ((1-κ:ℝ):ℂ)*(Real.sqrt (twoPortLambda η θ i):ℂ) := by
    rw [Complex.ofReal_mul, mul_assoc, ThermalDual.real_mul_inverse_sqrt (twoPortLambda_pos hη hθ.1 i)]
  simp only [← mul_assoc, hs]
  have hs0 : Real.sqrt (twoPortLambda η θ 0)=Real.sqrt θ*Real.sqrt η := Real.sqrt_mul hθ.1.le η
  have hs1 : Real.sqrt (twoPortLambda η θ 1)=Real.sqrt θ*Real.sqrt (1-η) := Real.sqrt_mul hθ.1.le (1-η)
  have hsq : (Real.sqrt ((1-κ)*κ):ℂ)*(Real.sqrt ((1-κ)*κ):ℂ)=(((1-κ)*κ:ℝ):ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (mul_nonneg (sub_nonneg.mpr hκ.2) hκ.1)]
  rw [hs0, hs1, EnsembleL2.mixtureFunctional_apply]
  have he : 1-(1-κ)=κ := by ring
  rw [he]
  change _=_+_*((Real.sqrt ((1-κ)*κ):ℂ)*(V.expectation Z-O.expectation Z))
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one] at hsq ⊢
  linear_combination -(V.weakMean (θ*(η*a 0+(1-η)*a 1)+(1-θ)*d) j*(V.expectation Z-O.expectation Z))*hsq
end

section
open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

theorem physical_defect_mode_bound (η θ κ ε d : ℝ) (a : Fin 2 → ℝ)
    (hη : η ∈ Set.Ioo 0 1) (hθ : θ ∈ Set.Ioo 0 1) (hκ : κ ∈ Set.Icc 0 1) (hκ1 : κ<1)
    (hd : 0<d) (ha : ∀ i, 0<a i) (hr0 : 0<outputReference η θ a d)
    (ρ : Fin 2 → State n) (τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η (ρ 0) (ρ 1) m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (G : (i : Fin 2) → SpectralLogData n (ρ i)) (G0 : SpectralLogData n ρ0)
    (D : WeightedColumns τD) (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω)
    (hD : ∀ k l, entry τD.op k l=if k=l then (QuantumTrace.thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (QuantumTrace.thermalWeight n (outputReference η θ a d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (hh₁ : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-κ)^2*BKM.quadratic (G 0).basis (G 0).probability
        (BKM.center (G 0).basis (G 0).probability
          (rawFirstSlice η θ ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 1) τD Z)) ≤
      (1+ε)*(1-κ)*twoPortLambda η θ 0*(h (outputReference η θ a d)/h (a 0))*
        BKM.quadratic G0.basis G0.probability Z)
    (hh₂ : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-κ)^2*BKM.quadratic (G 1).basis (G 1).probability
        (BKM.center (G 1).basis (G 1).probability
          (rawSecondSlice η θ ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 0) τD Z)) ≤
      (1+ε)*(1-κ)*twoPortLambda η θ 1*(h (outputReference η θ a d)/h (a 1))*
        BKM.quadratic G0.basis G0.probability Z)
    (hr : (1+ε)*(∑ i, twoPortLambda η θ i*a i) ≤ outputReference η θ a d)
    (hs : (1+ε)*(∑ i, twoPortLambda η θ i*(a i+1)) ≤ outputReference η θ a d+1)
    (j : Fin n) :
    ‖G0.defect (outputReference η θ a d) hr0 j‖ ≤
      Real.sqrt (∑ i, ((1-κ)*twoPortLambda η θ i)*‖(G i).defect (a i) (ha i) j‖^2)+
      Real.sqrt ((1-κ)*κ)*‖V.weakMean (outputReference η θ a d) j‖*
        mixtureConstant (outputReference η θ a d) := by
  change 0<η ∧ η<1 at hη
  change 0<θ ∧ θ<1 at hθ
  let S0 := G0.thermalSpace (outputReference η θ a d) hr0
  let S := fun i => (G i).thermalSpace (a i) (ha i)
  let w := fun i => (1-κ)*twoPortLambda η θ i
  let L := normalizedSlices η θ ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 0) (ρ 1) τD S (twoPortLambda η θ)
  have hw i : 0≤w i := mul_nonneg (sub_nonneg.mpr hκ.2) (twoPortLambda_pos hη hθ.1 i).le
  have hk : 1-κ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr hκ.2, by linarith [hκ.1]⟩
  have he0 : TraceEnsemble.operator S0.ensemble=ρ0.op :=
    S0.ensemble_operator ρ0.op ρ0.positive.isSymmetric G0.eigen
  have hemix : TraceEnsemble.operator S0.ensemble=TraceEnsemble.operator
      (EnsembleL2.mixture (fun k => inverseWeight 3 (V.vector k))
        (fun k => inverseWeight 3 (O.vector k)) (1-κ)) := by
    rw [EnsembleL2.mixture_operator _ _ hk V.normalized.summable O.normalized.summable,
      he0, show 1-(1-κ)=κ by ring]
    exact hrepl.trans (congrArg₂ (·+·) (congrArg (((1-κ:ℝ):ℂ) • ·) V.density.symm)
      (congrArg ((κ:ℂ) • ·) O.density.symm))
  have hephys : TraceEnsemble.operator S0.ensemble=
      ((1-κ:ℝ):ℂ) • (beamOutput θ ⟨hθ.1.le,hθ.2.le⟩
        (beamOutput η ⟨hη.1.le,hη.2.le⟩ (ρ 0) (ρ 1)) τD).op+(κ:ℂ) • ω.op := by
    rw [he0, ← output_eq ⟨hη.1.le,hη.2.le⟩ h1,
      ← output_eq ⟨hθ.1.le,hθ.2.le⟩ h2]
    exact hrepl
  have hhL : ∀ Z, Z ∈ CenteredTests.operatorSpace S0.basis S0.p →
      ∑ i, w i*(S i).pquad ThermalSpectral.thermalWeight (L i Z) ≤ S0.pquad ThermalSpectral.thermalWeight Z := by
    intro Z hZ
    exact physical_thermal_contraction η θ κ ε ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ hκ hκ1
      (ρ 0) (ρ 1) τD ω S0 S (twoPortLambda η θ) (twoPortLambda_pos hη hθ.1)
      (G 0).eigen (G 1).eigen hephys hh₁ hh₂ hr hs Z hZ
  have hh := ThermalDual.dual_bound_from_core S0 S w hw L
    (G0.ambientDefect _ hr0 j) (fun i => (G i).ambientDefect (a i) (ha i) j)
    (fun k => inverseWeight 3 (V.vector k)) (fun k => inverseWeight 3 (O.vector k))
    hk V.normalized O.normalized hemix
    ((Real.sqrt ((1-κ)*κ):ℂ)*V.weakMean (outputReference η θ a d) j) hhL
    (fun Z _ => physical_defect_convolution η θ κ d a hη hθ hκ hd ha hr0
      ρ τD m γ ω ρ0 h1 h2 G G0 D M V O hD hO hrepl j Z)
  change ‖G0.defect (outputReference η θ a d) hr0 j‖ ≤ _ at hh
  change ‖G0.defect (outputReference η θ a d) hr0 j‖ ≤
    Real.sqrt (∑ i, ((1-κ)*twoPortLambda η θ i)*‖(G i).ambientDefect (a i) (ha i) j‖^2)+
      ‖(Real.sqrt ((1-κ)*κ):ℂ)*V.weakMean (outputReference η θ a d) j‖*
        mixtureConstant (outputReference η θ a d) at hh
  simpa only [SpectralLogData.ambientDefect_norm, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)] using hh
end

section
open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp BeamLadder
open scoped ComplexConjugate
variable {n : ℕ}

theorem physical_mean_covariance (η θ d : ℝ) (a : Fin 2 → ℝ)
    (hη : η ∈ Set.Ioo 0 1) (hθ : θ ∈ Set.Ioo 0 1)
    (hd : 0<d) (ha : ∀ i, 0<a i) (hr0 : 0<outputReference η θ a d)
    (ρ : Fin 2 → State n) (τD m γ ω : State n)
    (h1 : IsBeamSplitterOutput η (ρ 0) (ρ 1) m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (G : (i : Fin 2) → SpectralLogData n (ρ i))
    (D : WeightedColumns τD) (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω)
    (hD : ∀ k l, entry τD.op k l=if k=l then (QuantumTrace.thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (QuantumTrace.thermalWeight n (outputReference η θ a d) k:ℂ) else 0)
    (j : Fin n) :
    V.weakMean (outputReference η θ a d) j=
      (Real.sqrt (twoPortLambda η θ 0):ℂ)*conj ((G 0).annihilationMean j)+
      (Real.sqrt (twoPortLambda η θ 1):ℂ)*conj ((G 1).annihilationMean j) := by
  change 0<η ∧ η<1 at hη
  change 0<θ ∧ θ<1 at hθ
  have hh := replaced_threeport_weak η θ 0 (a 0) (a 1) d
    ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩
    (ρ 0) (ρ 1) τD m γ ω γ h1 h2 (G 0).weightedColumns (G 1).weightedColumns
    D M V O V hd hr0 hD hO (by
      simp only [sub_zero,Complex.ofReal_one,Complex.ofReal_zero,one_smul]
      apply ContinuousLinearMap.ext
      intro vector
      simp only [add_apply,smul_apply,zero_smul,add_zero]) j 1
  have hm : V.weakMean (outputReference η θ a d) j=
      (Real.sqrt θ:ℂ)*(Real.sqrt η:ℂ)*(G 0).weightedColumns.weakMean (a 0) j+
      (Real.sqrt θ:ℂ)*(Real.sqrt (1-η):ℂ)*(G 1).weightedColumns.weakMean (a 1) j := by
    have ho : D.rawSlice θ (show θ ∈ Set.Icc 0 1 from ⟨hθ.1.le,hθ.2.le⟩) 1=1 := D.rawSlice_one _ _
    have hi : (G 1).weightedColumns.rawSlice η (show η ∈ Set.Icc 0 1 from ⟨hη.1.le,hη.2.le⟩) 1=1 :=
      (G 1).weightedColumns.rawSlice_one _ _
    have hj : (G 0).weightedColumns.rawSliceRight η (show η ∈ Set.Icc 0 1 from ⟨hη.1.le,hη.2.le⟩) 1=1 :=
      (G 0).weightedColumns.rawSliceRight_one _ _
    simp only [ho,hi,hj,sub_zero,Complex.ofReal_one,one_mul] at hh
    exact hh
  rw [hm, (G 0).weakMean_eq_conj (a 0) (ha 0), (G 1).weakMean_eq_conj (a 1) (ha 1)]
  simp only [twoPortLambda, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Real.sqrt_mul hθ.1.le, Complex.ofReal_mul]

 theorem physical_mean_bound (η θ κ d : ℝ) (a : Fin 2 → ℝ)
    (hη : η ∈ Set.Ioo 0 1) (hθ : θ ∈ Set.Ioo 0 1) (hκ : κ≤1)
    (hd : 0<d) (ha : ∀ i, 0<a i) (hr0 : 0<outputReference η θ a d)
    (ρ : Fin 2 → State n) (τD m γ ω : State n)
    (h1 : IsBeamSplitterOutput η (ρ 0) (ρ 1) m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (G : (i : Fin 2) → SpectralLogData n (ρ i))
    (D : WeightedColumns τD) (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω)
    (hD : ∀ k l, entry τD.op k l=if k=l then (QuantumTrace.thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (QuantumTrace.thermalWeight n (outputReference η θ a d) k:ℂ) else 0)
    (j : Fin n) :
    (1-κ)*‖V.weakMean (outputReference η θ a d) j‖^2≤
      2*∑ i, ((1-κ)*twoPortLambda η θ i)*‖(G i).annihilationMean j‖^2 := by
  rw [physical_mean_covariance η θ d a hη hθ hd ha hr0 ρ τD m γ ω h1 h2 G D M V O hD hO j]
  have hh := mul_le_mul_of_nonneg_left
    (ThermalDual.two_sqrt_norm_sq _ _ (twoPortLambda_pos hη hθ.1 0).le (twoPortLambda_pos hη hθ.1 1).le
      (conj ((G 0).annihilationMean j)) (conj ((G 1).annihilationMean j))) (sub_nonneg.mpr hκ)
  simp only [Complex.norm_conj] at hh
  simp only [Fin.sum_univ_two]
  convert! hh using 1; ring
end

open QuantumTrace Annihilation ThermalMetric ThermalSpectral TensorLp
variable {n : ℕ}
theorem physical_defect_triangle (η θ κ ε d : ℝ) (a : Fin 2 → ℝ)
    (hη : η ∈ Set.Ioo 0 1) (hθ : θ ∈ Set.Ioo 0 1) (hκ : κ ∈ Set.Icc 0 1) (hκ1 : κ<1)
    (hd : 0<d) (ha : ∀ i, 0<a i) (hr0 : 0<outputReference η θ a d)
    (ρ : Fin 2 → State n) (τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η (ρ 0) (ρ 1) m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (G : (i : Fin 2) → SpectralLogData n (ρ i)) (G0 : SpectralLogData n ρ0)
    (D : WeightedColumns τD) (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω)
    (hD : ∀ k l, entry τD.op k l=if k=l then (QuantumTrace.thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (QuantumTrace.thermalWeight n (outputReference η θ a d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (hh₁ : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-κ)^2*BKM.quadratic (G 0).basis (G 0).probability
        (BKM.center (G 0).basis (G 0).probability
          (rawFirstSlice η θ ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 1) τD Z)) ≤
      (1+ε)*(1-κ)*twoPortLambda η θ 0*(h (outputReference η θ a d)/h (a 0))*
        BKM.quadratic G0.basis G0.probability Z)
    (hh₂ : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-κ)^2*BKM.quadratic (G 1).basis (G 1).probability
        (BKM.center (G 1).basis (G 1).probability
          (rawSecondSlice η θ ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 0) τD Z)) ≤
      (1+ε)*(1-κ)*twoPortLambda η θ 1*(h (outputReference η θ a d)/h (a 1))*
        BKM.quadratic G0.basis G0.probability Z)
    (hr : (1+ε)*(∑ i, twoPortLambda η θ i*a i) ≤ outputReference η θ a d)
    (hs : (1+ε)*(∑ i, twoPortLambda η θ i*(a i+1)) ≤ outputReference η θ a d+1)
 :
    Real.sqrt (∑ j, ‖G0.defect (outputReference η θ a d) hr0 j‖^2) ≤ Real.sqrt (∑ i, ((1-κ)*twoPortLambda η θ i)*(∑ j, ‖(G i).defect (a i) (ha i) j‖^2))+
      Real.sqrt (2*κ)*mixtureConstant (outputReference η θ a d)*Real.sqrt (∑ i, ((1-κ)*twoPortLambda η θ i)*(∑ j, ‖(G i).annihilationMean j‖^2)) := by
  exact ThermalDual.aggregate_bound (fun i => (1-κ)*twoPortLambda η θ i)
    (fun i => mul_nonneg (sub_nonneg.mpr hκ.2) (twoPortLambda_pos hη hθ.1 i).le)
    (fun j => ‖G0.defect (outputReference η θ a d) hr0 j‖)
    (fun j => ‖V.weakMean (outputReference η θ a d) j‖)
    (fun i j => ‖(G i).defect (a i) (ha i) j‖) (fun i j => ‖(G i).annihilationMean j‖)
    (fun j => norm_nonneg (G0.defect (outputReference η θ a d) hr0 j)) (fun j => norm_nonneg (V.weakMean (outputReference η θ a d) j)) (mixtureConstant (outputReference η θ a d)) κ
    (mixtureConstant_pos hr0).le hκ
    (physical_mean_bound η θ κ d a hη hθ hκ.2 hd ha hr0 ρ τD m γ ω h1 h2 G D M V O hD hO)
    (physical_defect_mode_bound η θ κ ε d a hη hθ hκ hκ1 hd ha hr0 ρ τD m γ ω ρ0 h1 h2 G G0 D M V O hD hO hrepl hh₁ hh₂ hr hs)

theorem physical_defect_estimate (η θ κ ε d : ℝ) (a : Fin 2 → ℝ)
    (hη : η ∈ Set.Ioo 0 1) (hθ : θ ∈ Set.Ioo 0 1) (hκ : κ ∈ Set.Icc 0 1) (hκ1 : κ<1)
    (hd : 0<d) (ha : ∀ i, 0<a i) (hr0 : 0<outputReference η θ a d)
    (ρ : Fin 2 → State n) (τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η (ρ 0) (ρ 1) m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (G : (i : Fin 2) → SpectralLogData n (ρ i)) (G0 : SpectralLogData n ρ0)
    (D : WeightedColumns τD) (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω)
    (hD : ∀ k l, entry τD.op k l=if k=l then (QuantumTrace.thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (QuantumTrace.thermalWeight n (outputReference η θ a d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (hh₁ : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-κ)^2*BKM.quadratic (G 0).basis (G 0).probability
        (BKM.center (G 0).basis (G 0).probability
          (rawFirstSlice η θ ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 1) τD Z)) ≤
      (1+ε)*(1-κ)*twoPortLambda η θ 0*(h (outputReference η θ a d)/h (a 0))*
        BKM.quadratic G0.basis G0.probability Z)
    (hh₂ : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-κ)^2*BKM.quadratic (G 1).basis (G 1).probability
        (BKM.center (G 1).basis (G 1).probability
          (rawSecondSlice η θ ⟨hη.1.le,hη.2.le⟩ ⟨hθ.1.le,hθ.2.le⟩ (ρ 0) τD Z)) ≤
      (1+ε)*(1-κ)*twoPortLambda η θ 1*(h (outputReference η θ a d)/h (a 1))*
        BKM.quadratic G0.basis G0.probability Z)
    (hr : (1+ε)*(∑ i, twoPortLambda η θ i*a i) ≤ outputReference η θ a d)
    (hs : (1+ε)*(∑ i, twoPortLambda η θ i*(a i+1)) ≤ outputReference η θ a d+1)
    (hε : 0<ε)
    (hk : κ≤ε^2/(4*(ε+2)*mixtureConstant (outputReference η θ a d)^2)) :
    (∑ j, ‖G0.defect (outputReference η θ a d) hr0 j‖^2) ≤ (∑ i, ((1-κ)*twoPortLambda η θ i)*(∑ j, ‖(G i).defect (a i) (ha i) j‖^2))+ε/2*((∑ i, ((1-κ)*twoPortLambda η θ i)*(∑ j, ‖(G i).defect (a i) (ha i) j‖^2))+(∑ i, ((1-κ)*twoPortLambda η θ i)*(∑ j, ‖(G i).annihilationMean j‖^2))) := by
  have hq0 : 0≤∑ j, ‖G0.defect (outputReference η θ a d) hr0 j‖^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hA : 0≤∑ i, ((1-κ)*twoPortLambda η θ i)*(∑ j, ‖(G i).defect (a i) (ha i) j‖^2) := Finset.sum_nonneg (fun i _ => mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hκ.2) (twoPortLambda_pos hη hθ.1 i).le)
    (Finset.sum_nonneg (fun j _ => sq_nonneg _)))
  have hM : 0≤∑ i, ((1-κ)*twoPortLambda η θ i)*(∑ j, ‖(G i).annihilationMean j‖^2) := Finset.sum_nonneg (fun i _ => mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hκ.2) (twoPortLambda_pos hη hθ.1 i).le)
    (Finset.sum_nonneg (fun j _ => sq_nonneg _)))
  have hh := ThermalDual.defect_young (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (mixtureConstant_pos hr0) hκ.1 hε hk (physical_defect_triangle η θ κ ε d a hη hθ hκ hκ1 hd ha hr0 ρ τD m γ ω ρ0 h1 h2 G G0 D M V O hD hO hrepl hh₁ hh₂ hr hs)
  simpa only [Real.sq_sqrt hq0, Real.sq_sqrt hA, Real.sq_sqrt hM] using hh
end EntropyPhotonNumber

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

theorem output_lower_square (j : Fin n) (x : I → JointFock n) (z : J → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hz : Summable (fun j => ‖z j‖^2))
    (he : CrossEnsemble.operator (fun ie : I × NumberIndex n => slice (inverse (x ie.1)) ie.2)
        (fun ie : I × NumberIndex n => slice (inverse (x ie.1)) ie.2)=
      CrossEnsemble.operator (fun j => inverseWeight 3 (z j)) (fun j => inverseWeight 3 (z j))) :
    (∑' i, ‖lowerL j (x i)‖^2) = ∑' i, ‖sandwich 0 3 (by omega) j (z i)‖^2 := by
  have hi := CrossEnsemble.applied_summable hx inverse
  have hl := CrossEnsemble.applied_summable hx (lowerL j)
  have hzi := CrossEnsemble.applied_summable hz (inverseWeight 3)
  have hzl := CrossEnsemble.applied_summable hz (sandwich 0 3 (by omega) j)
  have his := slice_family_summable _ hi
  have hls := slice_family_summable _ hl
  have heL := CrossEnsemble.shifted_both_operator_eq _ _ _ _ his hls hzi hzl
    (up j) (fun k => (Real.sqrt ((k j:ℝ)+1):ℂ))
    (fun ie k => lowerL_inverse_apply j (x ie.1) k ie.2)
    (fun i k => single_lower_inverse_apply j (z i) k) he
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hp := CrossEnsemble.pairing_eq_of_operator_eq bas hls hls hzl hzl heL 1
  rw [← pairing_liftLeft _ _ hl hl, liftLeft_one] at hp
  have hh1 := (EnsembleL2.self_inner_hasSum (fun i => lowerL j (x i)) hl).tsum_eq
  have hh2 := (EnsembleL2.self_inner_hasSum (fun i => sandwich 0 3 (by omega) j (z i)) hzl).tsum_eq
  simpa only [CrossEnsemble.pairing,one_apply_eq_self,hh1,hh2,Complex.ofReal_inj] using hp
end BeamLadder

namespace EnsembleL2
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem real_smul_add_square (c d : ℝ) (x y : E) :
    ‖(c:ℂ) • x+(d:ℂ) • y‖^2=c^2*‖x‖^2+d^2*‖y‖^2+2*c*d*(inner ℂ x y).re := by
  rw [norm_add_sq (𝕜:=ℂ)]
  simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,
    inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  change _+2*((d:ℂ)*((c:ℂ)*inner ℂ x y)).re+_=_
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem real_smul_add_hasSum (c d : ℝ) (x y : I → E) (a b : ℝ) (v : ℂ)
    (hx : HasSum (fun i => ‖x i‖^2) a) (hy : HasSum (fun i => ‖y i‖^2) b)
    (hxy : HasSum (fun i => inner ℂ (x i) (y i)) v) :
    HasSum (fun i => ‖(c:ℂ) • x i+(d:ℂ) • y i‖^2) (c^2*a+d^2*b+2*c*d*v.re) := by
  simpa only [real_smul_add_square,Complex.reCLM_apply] using
    ((hx.mul_left (c^2)).add (hy.mul_left (d^2))).add
      ((hxy.mapL Complex.reCLM).mul_left (2*c*d))
end EnsembleL2

namespace TensorLp
variable {A B I J : Type*}
theorem tensorFamily_inner (x x' : I → H A) (y y' : J → H B)
    (hx : Summable (fun i => ‖x i‖^2)) (hx' : Summable (fun i => ‖x' i‖^2))
    (hy : Summable (fun j => ‖y j‖^2)) (hy' : Summable (fun j => ‖y' j‖^2))
    (a b : ℂ) (hleft : HasSum (fun i => inner ℂ (x i) (x' i)) a)
    (hright : HasSum (fun j => inner ℂ (y j) (y' j)) b) :
    HasSum (fun ij : I × J => inner ℂ (tensor (x ij.1) (y ij.2)) (tensor (x' ij.1) (y' ij.2))) (a*b) := by
  have hs := (EnsembleL2.inner_sum
    (fun ij : I × J => tensor (x ij.1) (y ij.2))
    (fun ij : I × J => tensor (x' ij.1) (y' ij.2))
    (tensorFamily_summable x y hx hy) (tensorFamily_summable x' y' hx' hy')).summable
  simp only [inner_tensor] at hs
  simpa only [inner_tensor] using hleft.mul hright hs
end TensorLp

namespace EntropyPhotonNumber.WeightedColumns
open QuantumTrace Annihilation BeamLadder TensorLp
variable {n : ℕ} {ρ σ τ : State n}

def lowerEnergy (X : WeightedColumns ρ) (j : Fin n) : ℝ :=
  ∑' i, ‖sandwich 0 3 (by omega) j (X.vector i)‖^2

theorem weakMean_hasSum (X : WeightedColumns ρ) (r : ℝ) (j : Fin n) :
    HasSum (fun i => inner ℂ (sandwich 0 3 (by omega) j (X.vector i))
      (inverseWeight 3 (X.vector i))) (X.weakMean r j) := by
  rw [X.weakMean_trace]
  exact (EnsembleL2.inner_sum _ _
    (CrossEnsemble.applied_summable X.summable (sandwich 0 3 (by omega) j))
    X.normalized.summable).summable.hasSum

theorem physical_lowerEnergy (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (r s : ℝ) (j : Fin n) (X : WeightedColumns ρ) (Y : WeightedColumns σ)
    (T : WeightedColumns τ) (hτ : IsBeamSplitterOutput η ρ σ τ) :
    T.lowerEnergy j=η*X.lowerEnergy j+(1-η)*Y.lowerEnergy j+
      2*Real.sqrt η*Real.sqrt (1-η)*(X.weakMean r j*conj (Y.weakMean s j)).re := by
  let xl := fun i => sandwich 0 3 (by omega) j (X.vector i)
  let yl := fun i => sandwich 0 3 (by omega) j (Y.vector i)
  let xb := fun i => inverseWeight 3 (X.vector i)
  let yb := fun i => inverseWeight 3 (Y.vector i)
  have hxl := CrossEnsemble.applied_summable X.summable (sandwich 0 3 (by omega) j)
  have hyl := CrossEnsemble.applied_summable Y.summable (sandwich 0 3 (by omega) j)
  have hmY : HasSum (fun i => inner ℂ (yb i) (yl i)) (conj (Y.weakMean s j)) := by
    convert! (Y.weakMean_hasSum s j).mapL Complex.conjCLE.toContinuousLinearMap using 1
    ext i
    exact (inner_conj_symm _ _).symm
  have hxy := tensorFamily_inner xl xb yb yl hxl X.normalized.summable
    Y.normalized.summable hyl (X.weakMean r j) (conj (Y.weakMean s j))
    (X.weakMean_hasSum r j) hmY
  have ha : HasSum (fun ij : X.Index × Y.Index => ‖tensor (xl ij.1) (yb ij.2)‖^2) (X.lowerEnergy j) := by
    simpa only [mul_one, lowerEnergy] using tensorFamily_norm xl yb _ _ hxl.hasSum Y.normalized
  have hb : HasSum (fun ij : X.Index × Y.Index => ‖tensor (xb ij.1) (yl ij.2)‖^2) (Y.lowerEnergy j) := by
    simpa only [one_mul, lowerEnergy] using tensorFamily_norm xb yl _ _ X.normalized hyl.hasSum
  have hh := EnsembleL2.real_smul_add_hasSum (Real.sqrt η) (Real.sqrt (1-η))
    (fun ij : X.Index × Y.Index => tensor (xl ij.1) (yb ij.2))
    (fun ij : X.Index × Y.Index => tensor (xb ij.1) (yl ij.2)) _ _ _ ha hb hxy
  rw [Real.sq_sqrt hη.1,Real.sq_sqrt (sub_nonneg.mpr hη.2)] at hh
  let v := fun ij : X.Index × Y.Index => beamUnitary η hη (tensorPreimage (X.vector ij.1) (Y.vector ij.2))
  have hv : Summable (fun ij => ‖v ij‖^2) := by
    simpa only [v,LinearIsometryEquiv.norm_map] using tensorPreimage_summable X.vector Y.vector X.summable Y.summable
  have he := physical_weighted_output η hη ρ σ τ hτ X.vector Y.vector T.vector
    X.normalized Y.normalized X.density Y.density T.density
  have ho := output_lower_square j v T.vector hv T.summable he
  change (∑' i, ‖sandwich 0 3 (by omega) j (T.vector i)‖^2)=_
  rw [← ho]
  convert! hh.tsum_eq using 1
  apply tsum_congr
  intro ij
  dsimp [v]
  rw [covariance_lower_apply,tensorPreimage_lowerL,tensorPreimage_lowerR,
    ← map_smul,← map_smul,← map_add,LinearIsometryEquiv.norm_map]
  rfl
end EntropyPhotonNumber.WeightedColumns

namespace EnsembleL2
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem sub_smul_square (x y : E) (μ : ℂ) :
    ‖x-μ • y‖^2=‖x‖^2+‖μ‖^2*‖y‖^2-2*(μ*inner ℂ x y).re := by
  rw [norm_sub_sq (𝕜:=ℂ),norm_smul,mul_pow,inner_smul_right]
  change ‖x‖^2-2*(μ*inner ℂ x y).re+‖μ‖^2*‖y‖^2=_
  ring

theorem centered_square (x y : I → E) (e : ℝ) (μ : ℂ)
    (hx : HasSum (fun i => ‖x i‖^2) e) (hy : HasSum (fun i => ‖y i‖^2) 1)
    (hxy : HasSum (fun i => inner ℂ (x i) (y i)) (conj μ)) :
    HasSum (fun i => ‖x i-μ • y i‖^2) (e-‖μ‖^2) := by
  have hh := (hx.add (hy.mul_left (‖μ‖^2))).sub
    (((hxy.mul_left μ).mapL Complex.reCLM).mul_left 2)
  simpa only [sub_smul_square,Complex.reCLM_apply,Complex.mul_conj,Complex.normSq_eq_norm_sq,
    Complex.ofReal_re,mul_one,show e+‖μ‖^2-2*‖μ‖^2=e-‖μ‖^2 by ring] using hh
end EnsembleL2

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace Annihilation WeightedGenerator ThermalMetric
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

theorem centeredEnergy_lowerEnergy (t : ℝ) (ht : 0<t) :
    G.centeredEnergy=∑ j, (G.weightedColumns.lowerEnergy j-‖G.annihilationMean j‖^2) := by
  apply Finset.sum_congr rfl
  intro j _
  have he := EnsembleL2.centered_square
    (fun i => sandwich 0 3 (by omega) j (G.spectralColumns i))
    (fun i => inverseWeight 3 (G.spectralColumns i)) (G.weightedColumns.lowerEnergy j)
    (G.annihilationMean j)
    (CrossEnsemble.applied_summable G.spectralColumns_summable (sandwich 0 3 (by omega) j)).hasSum
    G.spectralColumns_normalized
    (by
      have hh := G.weightedColumns.weakMean_hasSum t j
      rw [G.weakMean_eq_conj t ht j] at hh
      exact hh)
  rw [← he.tsum_eq]
  apply tsum_congr
  intro i
  congr 2
  simp only [centeredLadder,Bool.false_eq_true,↓reduceIte,ContinuousLinearMap.comp_apply,
    sub_apply,smul_apply,lowering]
  have hu : inverseWeight 1 (inverseWeight 2 (G.spectralColumns i))=inverseWeight 3 (G.spectralColumns i) := by
    change (inverseWeight 1 ∘L inverseWeight 2) (G.spectralColumns i)=_
    rw [← inverseWeight_add]
  rw [hu]
  congr 1
  exact congrArg (fun A : Fock n →L[ℂ] Fock n => A (G.spectralColumns i))
    (sandwich_right_inverse 0 1 2 (by omega) j).symm
end EntropyPhotonNumber.SpectralLogData

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}
theorem weighted_lowering_norm_sum (j : Fin n) (x : Fock n) :
    HasSum (fun k : NumberIndex n => (k j:ℝ)*‖inverseWeight 3 x k‖^2)
      (‖sandwich 0 3 (by omega) j x‖^2) := by
  have hh := lowering_norm_sum j (inverseWeight 2 x)
  have hu : inverseWeight 1 (inverseWeight 2 x)=inverseWeight 3 x := by
    change (inverseWeight 1 ∘L inverseWeight 2) x=_
    rw [← inverseWeight_add]
  have hl : lowering j (inverseWeight 2 x)=sandwich 0 3 (by omega) j x := by
    exact congrArg (fun A : Fock n →L[ℂ] Fock n => A x) (sandwich_right_inverse 0 1 2 (by omega) j).symm
  simpa only [hu,hl] using hh
end Annihilation

namespace EntropyPhotonNumber.WeightedColumns

section
open QuantumTrace Annihilation
variable {n : ℕ} {ρ : State n}

theorem lowerEnergy_hasSum (X : WeightedColumns ρ) (j : Fin n) :
    HasSum (fun k => (k j:ℝ)*(entry ρ.op k k).re) (X.lowerEnergy j) := by
  let f := fun (i : X.Index) (k : NumberIndex n) => (k j:ℝ)*‖inverseWeight 3 (X.vector i) k‖^2
  have hrow (k : NumberIndex n) : HasSum (fun i => f i k) ((k j:ℝ)*(entry ρ.op k k).re) := by
    have hh := (TraceEnsemble.hasSum_quadratic X.normalized.summable (numberKet k)).mul_left (k j:ℝ)
    rw [show TraceEnsemble.operator (fun i => inverseWeight 3 (X.vector i))=ρ.op from X.density] at hh
    simpa only [f,numberKet,lp.inner_single_left,RCLike.inner_apply,map_one,one_mul,mul_one,entry] using hh
  have hcol i : HasSum (f i) (‖sandwich 0 3 (by omega) j (X.vector i)‖^2) :=
    weighted_lowering_norm_sum j (X.vector i)
  have hs : Summable (Function.uncurry f) := by
    apply (summable_prod_of_nonneg (fun ik => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))).mpr
    refine ⟨fun i => (hcol i).summable,?_⟩
    convert CrossEnsemble.applied_summable X.summable (sandwich 0 3 (by omega) j) using 1
    ext i
    exact (hcol i).tsum_eq
  have hss : Summable (fun k => (k j:ℝ)*(entry ρ.op k k).re) := by
    exact hs.prod_symm.prod.congr (fun k => (hrow k).tsum_eq)
  have he : (∑' k, (k j:ℝ)*(entry ρ.op k k).re)=X.lowerEnergy j := by
    calc
      ∑' k, (k j:ℝ)*(entry ρ.op k k).re=∑' k, ∑' i, f i k := tsum_congr (fun k => (hrow k).tsum_eq.symm)
      _ = ∑' i, ∑' k, f i k := hs.tsum_comm
      _ = X.lowerEnergy j := tsum_congr (fun i => (hcol i).tsum_eq)
  simpa only [he] using hss.hasSum
end

section
open QuantumTrace Annihilation
variable {n : ℕ}

theorem lowerEnergy_affine {ρ σ τ : State n} (X : WeightedColumns ρ) (Y : WeightedColumns σ)
    (T : WeightedColumns τ) (s t : ℝ) (he : τ.op=(s:ℂ) • ρ.op+(t:ℂ) • σ.op) (j : Fin n) :
    T.lowerEnergy j=s*X.lowerEnergy j+t*Y.lowerEnergy j := by
  apply (T.lowerEnergy_hasSum j).unique
  convert! ((X.lowerEnergy_hasSum j).mul_left s).add ((Y.lowerEnergy_hasSum j).mul_left t) using 1
  funext k
  simp only [entry,he,add_apply,smul_apply,inner_add_right,inner_smul_right,Complex.add_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem thermal_lowerEnergy {ρ : State n} (X : WeightedColumns ρ) (r : ℝ) (hr : 0<r)
    (he : ∀ k l, entry ρ.op k l=if k=l then (thermalWeight n r k:ℂ) else 0) (j : Fin n) :
    X.lowerEnergy j=r := by
  have hE : HasSum (fun k => (k j:ℝ)*thermalWeight n r k) (X.lowerEnergy j) := by
    simpa only [he,ite_true,Complex.ofReal_re] using X.lowerEnergy_hasSum j
  have hz (k : NumberIndex n) (hk : k ∉ Set.range (up j)) : (k j:ℝ)*thermalWeight n r k=0 := by
    rcases index_cases j k with h | ⟨l,rfl⟩
    · simp only [h,Nat.cast_zero,zero_mul]
    · exact (hk ⟨l,rfl⟩).elim
  have hsh := (up_injective j).hasSum_iff hz |>.mpr hE
  have hsh' : HasSum (fun k => r/(r+1)*((k j:ℝ)*thermalWeight n r k+thermalWeight n r k))
      (X.lowerEnergy j) := by
    convert hsh using 1
    funext k
    simp only [Function.comp_def,up_same,Nat.cast_add,Nat.cast_one,thermalWeight_up]
    ring
  have hh := hsh'.unique ((hE.add (hasSum_thermalWeight n hr)).mul_left (r/(r+1)))
  have hr1 : r+1≠0 := by positivity
  field_simp at hh
  nlinarith
end

section
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ σ τ : State n}

theorem beam_weakMean (η : ℝ) (hη : η ∈ Set.Icc 0 1) (r s u : ℝ) (j : Fin n)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (T : WeightedColumns τ)
    (hτ : IsBeamSplitterOutput η ρ σ τ) :
    T.weakMean u j=(Real.sqrt η:ℂ)*X.weakMean r j+(Real.sqrt (1-η):ℂ)*Y.weakMean s j := by
  rw [T.weakMean_reference u (η*r+(1-η)*s)]
  have hh := physical_product_weak η r s hη ρ σ τ hτ j X.vector Y.vector T.vector
    X.summable Y.summable T.summable X.normalized Y.normalized X.density Y.density T.density 1
  change T.weakMean (η*r+(1-η)*s) j=_ at hh
  change T.weakMean (η*r+(1-η)*s) j=
    (Real.sqrt η:ℂ)*singleWeak r j X.vector (Y.rawSlice η hη 1)+
    (Real.sqrt (1-η):ℂ)*singleWeak s j Y.vector (X.rawSliceRight η hη 1) at hh
  simpa only [Y.rawSlice_one,X.rawSliceRight_one,weakMean] using hh

theorem weakMean_affine (X : WeightedColumns ρ) (Y : WeightedColumns σ) (T : WeightedColumns τ)
    (c d : ℂ) (he : τ.op=c • ρ.op+d • σ.op) (r : ℝ) (j : Fin n) :
    T.weakMean r j=c*X.weakMean r j+d*Y.weakMean r j := by
  apply PhysicalGenerator.weak_pairing_affine r j c d X.vector Y.vector T.vector
    X.summable Y.summable T.summable _ 1
  change TraceEnsemble.operator (fun i => inverseWeight 3 (T.vector i))=
    c • TraceEnsemble.operator (fun i => inverseWeight 3 (X.vector i))+
    d • TraceEnsemble.operator (fun i => inverseWeight 3 (Y.vector i))
  rw [T.density,X.density,Y.density,he]

def centeredLowerEnergy (X : WeightedColumns ρ) (r : ℝ) (j : Fin n) : ℝ :=
  X.lowerEnergy j-‖X.weakMean r j‖^2

theorem sqrt_complex_square (η : ℝ) (hη : η ∈ Set.Icc 0 1) (x y : ℂ) :
    ‖(Real.sqrt η:ℂ)*x+(Real.sqrt (1-η):ℂ)*y‖^2=
      η*‖x‖^2+(1-η)*‖y‖^2+2*Real.sqrt η*Real.sqrt (1-η)*(x*conj y).re := by
  have hh := EnsembleL2.real_smul_add_square (Real.sqrt η) (Real.sqrt (1-η)) x y
  rw [Real.sq_sqrt hη.1,Real.sq_sqrt (sub_nonneg.mpr hη.2)] at hh
  convert! hh using 1
  simp only [RCLike.inner_apply,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

theorem beam_centeredLowerEnergy (η : ℝ) (hη : η ∈ Set.Icc 0 1) (r s u : ℝ) (j : Fin n)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (T : WeightedColumns τ)
    (hτ : IsBeamSplitterOutput η ρ σ τ) :
    T.centeredLowerEnergy u j=η*X.centeredLowerEnergy r j+(1-η)*Y.centeredLowerEnergy s j := by
  rw [centeredLowerEnergy,physical_lowerEnergy η hη r s j X Y T hτ,
    beam_weakMean η hη r s u j X Y T hτ,sqrt_complex_square η hη]
  simp only [centeredLowerEnergy]
  ring

theorem thermal_centeredLowerEnergy (X : WeightedColumns ρ) (r u : ℝ) (hr : 0<r)
    (he : ∀ k l, entry ρ.op k l=if k=l then (thermalWeight n r k:ℂ) else 0) (j : Fin n) :
    X.centeredLowerEnergy u j=r := by
  rw [centeredLowerEnergy,thermal_lowerEnergy X r hr he,
    X.weakMean_reference u r]
  have hm : X.weakMean r j=0 := X.thermal_weak_zero r hr he j 1
  rw [hm,norm_zero,zero_pow (by decide : 2≠0),sub_zero]

theorem replacement_centeredLowerEnergy (X : WeightedColumns ρ) (O : WeightedColumns σ)
    (T : WeightedColumns τ) (κ r : ℝ) (hr : 0<r)
    (hO : ∀ k l, entry σ.op k l=if k=l then (thermalWeight n r k:ℂ) else 0)
    (he : τ.op=((1-κ:ℝ):ℂ) • ρ.op+(κ:ℂ) • σ.op) (j : Fin n) :
    T.centeredLowerEnergy r j=(1-κ)*X.centeredLowerEnergy r j+κ*r+
      κ*(1-κ)*‖X.weakMean r j‖^2 := by
  have ho : O.weakMean r j=0 := O.thermal_weak_zero r hr hO j 1
  rw [centeredLowerEnergy,lowerEnergy_affine X O T (1-κ) κ he,
    thermal_lowerEnergy O r hr hO,weakMean_affine X O T _ _ he,ho,mul_zero,add_zero,
    norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,centeredLowerEnergy]
  ring
end

open QuantumTrace
variable {n : ℕ}

theorem threeport_centered_energy_mode (η θ κ a b d : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (hd : 0<d)
    (hr0 : 0<θ*(η*a+(1-η)*b)+(1-θ)*d)
    (ρ σ τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η ρ σ m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (D : WeightedColumns τD)
    (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω) (T : WeightedColumns ρ0)
    (hD : ∀ k l, entry τD.op k l=if k=l then (thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (thermalWeight n (θ*(η*a+(1-η)*b)+(1-θ)*d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op) (j : Fin n) :
    T.centeredLowerEnergy (θ*(η*a+(1-η)*b)+(1-θ)*d) j-(θ*(η*a+(1-η)*b)+(1-θ)*d)=
      ((1-κ)*θ*η)*(X.centeredLowerEnergy a j-a)+((1-κ)*θ*(1-η))*(Y.centeredLowerEnergy b j-b)+
      κ*(1-κ)*‖V.weakMean (θ*(η*a+(1-η)*b)+(1-θ)*d) j‖^2 := by
  rw [replacement_centeredLowerEnergy V O T κ _ hr0 hO hrepl j,
    beam_centeredLowerEnergy θ hθ (η*a+(1-η)*b) d _ j M D V h2,
    beam_centeredLowerEnergy η hη a b _ j X Y M h1,
    thermal_centeredLowerEnergy D d d hd hD]
  ring
end EntropyPhotonNumber.WeightedColumns

namespace EntropyPhotonNumber.SpectralLogData
open QuantumTrace WeightedColumns
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)

theorem centeredEnergy_eq_sum (t : ℝ) (ht : 0<t) :
    G.centeredEnergy=∑ j, G.weightedColumns.centeredLowerEnergy t j := by
  rw [G.centeredEnergy_lowerEnergy t ht]
  simp only [centeredLowerEnergy,G.weakMean_eq_conj t ht,Complex.norm_conj]
end EntropyPhotonNumber.SpectralLogData

namespace EntropyPhotonNumber
open QuantumTrace WeightedColumns
variable {n : ℕ}

theorem physical_centered_energy_identity (η θ κ a b d : ℝ)
    (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (hd : 0<d) (ha : 0<a) (hb : 0<b)
    (hr0 : 0<θ*(η*a+(1-η)*b)+(1-θ)*d)
    (ρ σ τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η ρ σ m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (G1 : SpectralLogData n ρ) (G2 : SpectralLogData n σ) (G0 : SpectralLogData n ρ0)
    (D : WeightedColumns τD) (M : WeightedColumns m) (V : WeightedColumns γ) (O : WeightedColumns ω)
    (hD : ∀ k l, entry τD.op k l=if k=l then (thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=if k=l then (thermalWeight n (θ*(η*a+(1-η)*b)+(1-θ)*d) k:ℂ) else 0)
    (hrepl : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op) :
    G0.centeredEnergy-(n:ℝ)*(θ*(η*a+(1-η)*b)+(1-θ)*d)=
      ((1-κ)*θ*η)*(G1.centeredEnergy-(n:ℝ)*a)+((1-κ)*θ*(1-η))*(G2.centeredEnergy-(n:ℝ)*b)+
      κ*(1-κ)*(∑ j, ‖V.weakMean (θ*(η*a+(1-η)*b)+(1-θ)*d) j‖^2) := by
  have hh := Finset.sum_congr (s₁:=Finset.univ) rfl (fun j _ =>
    threeport_centered_energy_mode η θ κ a b d hη hθ hd hr0 ρ σ τD m γ ω ρ0 h1 h2
      G1.weightedColumns G2.weightedColumns D M V O G0.weightedColumns hD hO hrepl j)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← G0.centeredEnergy_eq_sum _ hr0,
    ← G1.centeredEnergy_eq_sum a ha,← G2.centeredEnergy_eq_sum b hb] at hh
  convert! hh using 1; ring
end EntropyPhotonNumber

end

namespace EntropyPhotonNumber
open scoped BigOperators ComplexConjugate

section
open TensorLp KrausBounded BeamLadder
variable {n : ℕ}

theorem second_dual_conditional (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρ : State n)
    (Z : Fock n →L[ℂ] Fock n) :
    dual (secondKraus η hη ρ) (secondKraus_norm η hη ρ) Z=
      conditionalRight (rootColumn ρ) (rootColumn_norm ρ) (conjugate η hη Z) := by
  let V := fun j => tensorLeft (B:=NumberIndex n) (rootColumn ρ j)
  let U := jointKraus (n:=n) η hη
  have hV := leftFamily_norm (rootColumn ρ) (rootColumn_norm ρ) (B:=NumberIndex n)
  have hU := jointKraus_norm (n:=n) η hη
  have hr := dual_reindex (Equiv.prodComm _ _) (composite V U) (composite_norm V U hV hU)
    (fun x => (Equiv.prodComm _ _).hasSum_iff.mpr (composite_norm V U hV hU x)) Z
  change dual (secondKraus η hη ρ) _ Z=dual (composite V U) _ Z at hr
  rw [hr, dual_composite V U hV hU]
  change dual V hV (dual (jointKraus η hη) hU Z)=_
  rw [joint_dual_conjugate]
  rfl

theorem dual_composeKraus {I J : Type*} (U : I → Fock n →L[ℂ] Fock n)
    (V : J → Fock n →L[ℂ] Fock n)
    (hU : ∀ x, HasSum (fun i => ‖U i x‖^2) (‖x‖^2))
    (hV : ∀ x, HasSum (fun j => ‖V j x‖^2) (‖x‖^2)) (Z : Fock n →L[ℂ] Fock n) :
    dual (composeKraus U V) (composeKraus_norm U V hU hV) Z=dual V hV (dual U hU Z) := by
  have hr := dual_reindex (Equiv.prodComm _ _) (composite V U) (composite_norm V U hV hU)
    (fun x => (Equiv.prodComm _ _).hasSum_iff.mpr (composite_norm V U hV hU x)) Z
  change dual (composeKraus U V) _ Z=dual (composite V U) _ Z at hr
  rw [hr,dual_composite V U hV hU]

namespace Regularization
open QuantumTrace
variable (R : Regularization n)

theorem firstFlow_dual_raw (σ : State n) (hσ : FiniteEnergy σ) (Z : Fock n →L[ℂ] Fock n) :
    (R.firstFlow σ hσ).dual Z=rawFirstSlice R.η (1-R.δ) R.hη
      ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩ σ R.τD Z := by
  have hθ : 1-R.δ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
  change dual (composeKraus (firstKraus (1-R.δ) hθ R.τD) (firstKraus R.η R.hη σ))
    (composeKraus_norm _ _ (firstKraus_norm _ _ _) (firstKraus_norm _ _ _)) Z=
    rawFirstSlice R.η (1-R.δ) R.hη hθ σ R.τD Z
  rw [dual_composeKraus _ _ (firstKraus_norm _ _ _) (firstKraus_norm _ _ _), first_dual_conditional]
  unfold rawFirstSlice rawDual rawJointKraus
  have hd := dual_composite (jointKraus R.η R.hη)
    (firstKraus (1-R.δ) (show 1-R.δ ∈ Set.Icc 0 1 from ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩) R.τD)
    (jointKraus_norm R.η R.hη) (firstKraus_norm _ _ _) Z
  rw [joint_dual_conjugate] at hd
  exact congrArg (conditionalLeft (rootColumn σ) (rootColumn_norm σ)) hd.symm

theorem secondFlow_dual_raw (ρ : State n) (hρ : FiniteEnergy ρ) (Z : Fock n →L[ℂ] Fock n) :
    (R.secondFlow ρ hρ).dual Z=rawSecondSlice R.η (1-R.δ) R.hη
      ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩ ρ R.τD Z := by
  have hθ : 1-R.δ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
  change dual (composeKraus (firstKraus (1-R.δ) hθ R.τD) (secondKraus R.η R.hη ρ))
    (composeKraus_norm _ _ (firstKraus_norm _ _ _) (secondKraus_norm _ _ _)) Z=
    rawSecondSlice R.η (1-R.δ) R.hη hθ ρ R.τD Z
  rw [dual_composeKraus _ _ (firstKraus_norm _ _ _) (secondKraus_norm _ _ _), second_dual_conditional]
  unfold rawSecondSlice rawDual rawJointKraus
  have hd := dual_composite (jointKraus R.η R.hη)
    (firstKraus (1-R.δ) (show 1-R.δ ∈ Set.Icc 0 1 from ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩) R.τD)
    (jointKraus_norm R.η R.hη) (firstKraus_norm _ _ _) Z
  rw [joint_dual_conjugate] at hd
  exact congrArg (conditionalRight (rootColumn ρ) (rootColumn_norm ρ)) hd.symm
end Regularization
end

open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

theorem spectralLogData_of_sandwich (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j)=(p j:ℂ) • b j) (hm : FiniteMoment 6 ρ)
    (B : Fock n →L[ℂ] Fock n) (hB : B.IsPositive)
    (hBe : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re =
      basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) (inverseWeight 2 x)) :
    ∃ G : SpectralLogData n ρ, G.J=J ∧ HEq G.basis b ∧ HEq G.probability p ∧ G.logSandwich=B := by
  have hc (j : J) : 0≤-Real.log (p j) := by
    apply neg_nonneg.mpr
    exact Real.log_nonpos (hp j).le (hs.tsum_eq ▸ hs.summable.le_tsum j (fun i _ => (hp i).le))
  have hfin (x : Fock n) : Summable (fun j => -Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 x)‖^2) := by
    have heq : (∑' j, ENNReal.ofReal (-Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 x)‖^2))=
        ENNReal.ofReal (inner ℂ x (B x)).re := by
      rw [hBe]; simp only [basisMoment, ENNReal.ofReal_mul (hc _)]
    have hfinite : (∑' j, ENNReal.ofReal (-Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 x)‖^2))≠⊤ :=
      heq ▸ ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal (mul_nonneg (hc _) (sq_nonneg _))] using ENNReal.summable_toReal hfinite
  have hsum (x : Fock n) : HasSum
      (fun j => -Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 x)‖^2) (inner ℂ x (B x)).re := by
    have hh := hBe x
    rw [basisMoment_ofReal b _ hc _ (hfin x)] at hh
    have hn : 0≤(inner ℂ x (B x)).re := hB.re_inner_nonneg_right x
    have hnn : 0≤∑' j, -Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 x)‖^2 :=
      tsum_nonneg (fun j => mul_nonneg (hc j) (sq_nonneg _))
    have heq : (inner ℂ x (B x)).re=∑' j, -Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 x)‖^2 :=
      by simpa only [ENNReal.toReal_ofReal hn, ENNReal.toReal_ofReal hnn] using congrArg ENNReal.toReal hh
    rw [heq]; exact (hfin x).hasSum
  have hb (x : Fock n) : (∑' j, -Real.log (p j)*‖inner ℂ (b j) (inverseWeight 2 x)‖^2) ≤ ‖B‖*‖x‖^2 := by
    rw [(hsum x).tsum_eq]
    calc
      (inner ℂ x (B x)).re ≤ ‖inner ℂ x (B x)‖ := Complex.re_le_norm _
      _ ≤ ‖x‖*‖B x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖*(‖B‖*‖x‖) := mul_le_mul_of_nonneg_left (B.le_opNorm x) (norm_nonneg _)
      _ = ‖B‖*‖x‖^2 := by ring
  obtain ⟨B',hB',hs',he'⟩ := spectral_form_representation b (fun j => -Real.log (p j)) hc
    (inverseWeight 2) (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (inverseWeight_selfAdjoint 2))
    hfin (norm_nonneg B) hb
  have hBB : B'=B := positive_eq_of_quadratic hB' hB (fun x => (hs' x).unique (hsum x))
  subst B'
  obtain ⟨x,hx,hix⟩ := spectral_weighted_columns b p (fun j => (hp j).le) he hm
  let G : SpectralLogData n ρ := {
    J := J
    basis := b
    probability := p
    probability_pos := hp
    probability_sum := hs
    eigen := he
    spectralColumns := x
    spectralColumns_summable := hx
    spectralColumns_inverse := hix
    logSandwich := B
    logSandwich_symmetric := hB.isSymmetric
    logSandwich_parseval := hsum
    logSandwich_preimage := by
      intro j
      have hi : inverseWeight 2 (inverseWeight 1 (x j))=(Real.sqrt (p j):ℂ) • b j := by
        change (inverseWeight 2 ∘L inverseWeight 1) (x j)=_
        rw [← inverseWeight_add]
        exact hix j
      have hh := he' j (inverseWeight 1 (x j)) (Real.sqrt (p j):ℂ) hi
      have hz : inverseWeight 2 ((Real.sqrt (p j):ℂ) • b j)=inverseWeight 5 (x j) := by
        rw [← hi]
        change (inverseWeight 2 ∘L inverseWeight 2 ∘L inverseWeight 1) (x j)=_
        rw [← inverseWeight_add,← inverseWeight_add]
      simpa only [hz] using hh }
  exact ⟨G,rfl,HEq.rfl,HEq.rfl,rfl⟩

namespace GibbsData
variable {k : ℝ} (G : GibbsData n k ρ)
theorem quarticLogarithm_eq_logSandwich : G.quarticLogarithm=G.logSandwich := by
  unfold quarticLogarithm logSandwich
  rw [inversePower_root_four]
end GibbsData

end EntropyPhotonNumber

section
open scoped BigOperators

namespace WeightedGenerator

section
open EntropyPhotonNumber QuantumTrace Annihilation
variable {n : ℕ}
theorem drift_radial (r : ℝ) (f : ℝ → ℝ) (k : NumberIndex n) :
    drift r (fun k => f (numberWeight k)) k =
      (r+1)*(numberWeight k-1)*(f (numberWeight k-1)-f (numberWeight k))+
        r*(numberWeight k-1+n)*(f (numberWeight k+1)-f (numberWeight k)) := by
  have he (j : Fin n) : (r+1)*(k j:ℝ)*(f (numberWeight (down j k))-f (numberWeight k)) =
      ((k j:ℝ)*(r+1))*(f (numberWeight k-1)-f (numberWeight k)) := by
    by_cases hk : k j=0
    · simp [hk]
    · rw [weight_down j k (Nat.pos_of_ne_zero hk)]
      ring
  simp only [drift, he, weight_up, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, numberWeight]
  ring

theorem drift_number (r : ℝ) (k : NumberIndex n) :
    drift r (fun k => (totalNumber k:ℝ)) k = n*r-totalNumber k := by
  have he (k : NumberIndex n) : (totalNumber k:ℝ)=numberWeight k-1 := by
    simp [totalNumber, numberWeight]
  have hh := drift_radial r (fun t => t-1) k
  simp_rw [he]
  rw [hh]
  ring

def driftPolynomial (n : ℕ) (r t : ℝ) : ℝ :=
  (r+1)*t*(t^4-(t+1)^4)+r*(t+n)*((t+2)^4-(t+1)^4)

theorem drift_fourth (r : ℝ) (k : NumberIndex n) :
    drift r (fun k => numberWeight k^4) k=driftPolynomial n r (totalNumber k) := by
  rw [drift_radial r (fun t => t^4) k]
  simp only [driftPolynomial, numberWeight, totalNumber, Nat.cast_sum]
  ring

theorem driftPolynomial_expand (r t : ℝ) :
    driftPolynomial n r t = -4*t^4+(4*r*n+12*r-6)*t^3+
      (18*r*n+24*r-4)*t^2+(28*r*n+14*r-1)*t+15*r*n := by
  unfold driftPolynomial
  ring
end

theorem negative_quartic_bounded (a b c d : ℝ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → -4*t^4+a*t^3+b*t^2+c*t+d ≤ C := by
  let S : ℝ := 1+|a|+|b|+|c|+|d|
  have hS : 1 ≤ S := by dsimp [S]; linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg d]
  have ha : a ≤ |a| := le_abs_self a
  have hb : b ≤ |b| := le_abs_self b
  have hc : c ≤ |c| := le_abs_self c
  have hd : d ≤ |d| := le_abs_self d
  have hsa : 0 ≤ |a| := abs_nonneg a
  have hsb : 0 ≤ |b| := abs_nonneg b
  have hsc : 0 ≤ |c| := abs_nonneg c
  have hsd : 0 ≤ |d| := abs_nonneg d
  refine ⟨S*(S^3+S^2+S+1), ?_⟩
  intro t ht
  have htop : -4*t^4+a*t^3+b*t^2+c*t+d ≤ |a| *t^3+|b| *t^2+|c| *t+|d| := by
    nlinarith [mul_le_mul_of_nonneg_right ha (pow_nonneg ht 3),
      mul_le_mul_of_nonneg_right hb (sq_nonneg t), mul_le_mul_of_nonneg_right hc ht,
      pow_nonneg ht 4]
  have hC : 0 ≤ S*(S^3+S^2+S+1) := by positivity
  by_cases h : t ≤ S
  · have h₁ : |a| *t^3 ≤ S*S^3 := by
      apply mul_le_mul
      · dsimp [S]; linarith
      · exact pow_le_pow_left₀ ht h 3
      · positivity
      · linarith
    have h₂ : |b| *t^2 ≤ S*S^2 := by
      apply mul_le_mul
      · dsimp [S]; linarith
      · exact pow_le_pow_left₀ ht h 2
      · positivity
      · linarith
    have h₃ : |c| *t ≤ S*S := by
      apply mul_le_mul
      · dsimp [S]; linarith
      · exact h
      · exact ht
      · linarith
    have h₄ : |d| ≤ S := by dsimp [S]; linarith
    nlinarith
  · have htS : S ≤ t := (lt_of_not_ge h).le
    have ht1 : 1 ≤ t := hS.trans htS
    have ht2 : t ≤ t^2 := by nlinarith
    have ht3 : t^2 ≤ t^3 := by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht1)]
    have h₁ := mul_le_mul_of_nonneg_left ht3 hsb
    have h₂ := mul_le_mul_of_nonneg_left (ht2.trans ht3) hsc
    have h₃ := mul_le_mul_of_nonneg_left (ht1.trans (ht2.trans ht3)) hsd
    have h₄ : (|a|+|b|+|c|+|d|)*t^3 ≤ t^4 := by
      have hs : |a|+|b|+|c|+|d| ≤ t := by dsimp [S] at htS; linarith
      simpa only [← pow_succ'] using mul_le_mul_of_nonneg_right hs (pow_nonneg ht 3)
    have ht4 : 0 ≤ t^4 := pow_nonneg ht 4
    have hlead : a*t^3+b*t^2+c*t+d ≤ (|a|+|b|+|c|+|d|)*t^3 := by
      nlinarith [mul_le_mul_of_nonneg_right ha (pow_nonneg ht 3),
        mul_le_mul_of_nonneg_right hb (sq_nonneg t), mul_le_mul_of_nonneg_right hc ht]
    nlinarith

theorem driftPolynomial_bounded (n : ℕ) (r : ℝ) :
    ∃ C : ℝ, ∀ k : ℕ, driftPolynomial n r k ≤ C := by
  obtain ⟨C,hC⟩ := negative_quartic_bounded (4*r*n+12*r-6) (18*r*n+24*r-4)
    (28*r*n+14*r-1) (15*r*n)
  exact ⟨C, fun k => (driftPolynomial_expand r k).trans_le (hC k (Nat.cast_nonneg k))⟩
end WeightedGenerator

namespace EntropyPhotonNumber

section
open QuantumTrace Annihilation
variable {n : ℕ}

theorem number_le_weight (k : NumberIndex n) : (totalNumber k:ℝ)≤numberWeight k := by
  simp only [numberWeight,totalNumber,Nat.cast_sum]; linarith

theorem number_weight_eq (k : NumberIndex n) : numberWeight k=1+(totalNumber k:ℝ) := by
  simp only [numberWeight,totalNumber,Nat.cast_sum]

theorem number_div_weight_bound (k : NumberIndex n) : |(totalNumber k:ℝ)/numberWeight k^4|≤1 := by
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_one (pow_pos (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k)) _)).mpr
  exact (number_le_weight k).trans (le_self_pow₀ (numberWeight_one_le k) (by norm_num))

def numberSandwich (n : ℕ) : Fock n →L[ℂ] Fock n :=
  diagonal (fun k => (totalNumber k:ℝ)/numberWeight k^4) 1 (by norm_num) number_div_weight_bound

theorem numberSandwich_positive (n : ℕ) : (numberSandwich n).IsPositive := by
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (diagonal_selfAdjoint _ _ _ _), ?_⟩
  intro x
  have hh := diagonal_quadratic (fun k : NumberIndex n => (totalNumber k:ℝ)/numberWeight k^4) 1 (by norm_num) number_div_weight_bound x
  have hs : (inner ℂ x (numberSandwich n x)).re=∑' k, (totalNumber k:ℝ)/numberWeight k^4*‖x k‖^2 := hh.tsum_eq.symm
  change 0≤(inner ℂ (numberSandwich n x) x).re
  rw [show (inner ℂ (numberSandwich n x) x).re=(inner ℂ x (numberSandwich n x)).re from inner_re_symm (𝕜:=ℂ) _ _, hs]
  exact tsum_nonneg (fun k => by positivity)

theorem numberSandwich_form (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (numberSandwich n x)).re = numberVectorMoment (inverseWeight 2 x) := by
  rw [numberVectorMoment_eq]
  have hh := diagonal_quadratic (fun k : NumberIndex n => (totalNumber k:ℝ)/numberWeight k^4) 1 (by norm_num) number_div_weight_bound x
  change HasSum _ (inner ℂ x (numberSandwich n x)).re at hh
  rw [← hh.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hh.summable]
  apply tsum_congr
  intro k
  congr 1
  simp [numberBasis_apply,numberKet,lp.inner_single_left,inverseWeight_apply,
    norm_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (le_trans zero_le_one (numberWeight_one_le k))]
  ring

theorem numberSandwich_unique (D : Fock n →L[ℂ] Fock n) (hD : D.IsPositive)
    (he : ∀ x, ENNReal.ofReal (inner ℂ x (D x)).re =
      numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) :
    D=numberSandwich n := by
  apply positive_eq_of_quadratic hD (numberSandwich_positive n)
  intro x
  have hh := congrArg ENNReal.toReal (he x)
  rw [inversePower_root_four, ← numberSandwich_form] at hh
  simpa only [ENNReal.toReal_ofReal (show 0≤(inner ℂ x (D x)).re from hD.re_inner_nonneg_right x),
    ENNReal.toReal_ofReal (show 0≤(inner ℂ x (numberSandwich n x)).re from (numberSandwich_positive n).re_inner_nonneg_right x)] using hh

theorem drift_number_div_bound (r : ℝ) (k : NumberIndex n) :
    |WeightedGenerator.drift r (fun k => (totalNumber k:ℝ)) k/numberWeight k^6|≤|(n:ℝ)*r|+1 := by
  rw [WeightedGenerator.drift_number,abs_div,abs_of_pos (pow_pos (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k)) _)]
  apply (div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k)) _)).mpr
  have hw : 1≤numberWeight k^6 := one_le_pow₀ (numberWeight_one_le k)
  have hn : (totalNumber k:ℝ)≤numberWeight k^6 :=
    (number_le_weight k).trans (le_self_pow₀ (numberWeight_one_le k) (by norm_num))
  calc
    |(n:ℝ)*r-totalNumber k|≤|(n:ℝ)*r|+|(totalNumber k:ℝ)| := abs_sub _ _
    _ ≤ (|(n:ℝ)*r|+1)*numberWeight k^6 := by
      have hnabs : |(totalNumber k:ℝ)|=(totalNumber k:ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
      rw [hnabs]
      nlinarith [mul_le_mul_of_nonneg_left hw (abs_nonneg ((n:ℝ)*r))]

theorem thermalGenerator_number (r : ℝ) (ρ : State n) (hm : FiniteMoment 6 ρ) :
    (WeightedGenerator.pairing r (weightedRoot 3 ρ hm) (numberSandwich n)).re=(n:ℝ)*r-energy ρ := by
  have hh := thermalGenerator_drift r ρ hm (fun k => (totalNumber k:ℝ)) 1 (|(n:ℝ)*r|+1)
    (by norm_num) number_div_weight_bound (drift_number_div_bound r)
  have he := (ρ.trace_one.mul_left ((n:ℝ)*r)).sub (finiteMoment_finiteEnergy (by norm_num) hm).hasSum
  change HasSum _ (WeightedGenerator.pairing r (weightedRoot 3 ρ hm) (numberSandwich n)).re at hh
  apply hh.unique
  simpa only [WeightedGenerator.drift_number, sub_mul, mul_one, energy] using he
end

open QuantumTrace Annihilation WeightedGenerator
variable {n : ℕ}

theorem polynomial_weight_six_bound (a b c d e : ℝ) (k : NumberIndex n) :
    |a*(totalNumber k:ℝ)^4+b*(totalNumber k:ℝ)^3+c*(totalNumber k:ℝ)^2+d*(totalNumber k:ℝ)+e|≤
      (|a|+|b|+|c|+|d|+|e|)*numberWeight k^6 := by
  have hp (m : ℕ) (hm : m≤6) : (totalNumber k:ℝ)^m≤numberWeight k^6 :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (number_le_weight k) m).trans
      (pow_le_pow_right₀ (numberWeight_one_le k) hm)
  have h1 : (totalNumber k:ℝ)≤numberWeight k^6 := by simpa using hp 1 (by norm_num)
  have h0 : 1≤numberWeight k^6 := one_le_pow₀ (numberWeight_one_le k)
  calc
    _ ≤ |a*(totalNumber k:ℝ)^4+b*(totalNumber k:ℝ)^3+c*(totalNumber k:ℝ)^2+d*(totalNumber k:ℝ)|+|e| := abs_add_le _ _
    _ ≤ |a*(totalNumber k:ℝ)^4+b*(totalNumber k:ℝ)^3+c*(totalNumber k:ℝ)^2|+|d*(totalNumber k:ℝ)|+|e| := by gcongr; exact abs_add_le _ _
    _ ≤ |a*(totalNumber k:ℝ)^4+b*(totalNumber k:ℝ)^3|+|c*(totalNumber k:ℝ)^2|+|d*(totalNumber k:ℝ)|+|e| := by gcongr; exact abs_add_le _ _
    _ ≤ |a*(totalNumber k:ℝ)^4|+|b*(totalNumber k:ℝ)^3|+|c*(totalNumber k:ℝ)^2|+|d*(totalNumber k:ℝ)|+|e| := by gcongr; exact abs_add_le _ _
    _ = |a| *(totalNumber k:ℝ)^4+|b| *(totalNumber k:ℝ)^3+|c| *(totalNumber k:ℝ)^2+|d| *(totalNumber k:ℝ)+|e| := by simp [abs_mul,abs_pow,abs_of_nonneg (show 0≤(totalNumber k:ℝ) from Nat.cast_nonneg _)]
    _ ≤ |a| *numberWeight k^6+|b| *numberWeight k^6+|c| *numberWeight k^6+|d| *numberWeight k^6+|e| *numberWeight k^6 := by
      exact add_le_add (add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (hp 4 (by norm_num)) (abs_nonneg a))
        (mul_le_mul_of_nonneg_left (hp 3 (by norm_num)) (abs_nonneg b)))
        (mul_le_mul_of_nonneg_left (hp 2 (by norm_num)) (abs_nonneg c)))
        (mul_le_mul_of_nonneg_left h1 (abs_nonneg d))) (by nlinarith [mul_le_mul_of_nonneg_left h0 (abs_nonneg e)])
    _ = _ := by ring

def fourthDriftConstant (n : ℕ) (r : ℝ) : ℝ :=
  |(-4:ℝ)|+|4*r*n+12*r-6|+|18*r*n+24*r-4|+|28*r*n+14*r-1|+|15*r*n|

theorem drift_fourth_div_bound (r : ℝ) (k : NumberIndex n) :
    |drift r (fun k => numberWeight k^4) k/numberWeight k^6|≤fourthDriftConstant n r := by
  rw [drift_fourth,driftPolynomial_expand,abs_div,abs_of_pos (pow_pos (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k)) _)]
  apply (div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k)) _)).mpr
  exact polynomial_weight_six_bound (-4) (4*r*n+12*r-6) (18*r*n+24*r-4) (28*r*n+14*r-1) (15*r*n) k

theorem fourth_diagonal_eq_one :
    diagonal (fun k : NumberIndex n => numberWeight k^4/numberWeight k^4) 1 (by norm_num)
      (fun k => by rw [div_self (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k))))]; norm_num)=
      (1 : Fock n →L[ℂ] Fock n) := by
  ext x k
  simp only [diagonal_apply,div_self (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k)))),Complex.ofReal_one,
    one_mul,one_apply_eq_self]

theorem thermalGenerator_fourth (r : ℝ) (ρ : State n) (hm : FiniteMoment 6 ρ) :
    HasSum (fun k => driftPolynomial n r (totalNumber k)*(entry ρ.op k k).re)
      (WeightedGenerator.pairing r (weightedRoot 3 ρ hm) (1 : Fock n →L[ℂ] Fock n)).re := by
  have hh := thermalGenerator_drift r ρ hm (fun k => numberWeight k^4) 1 (fourthDriftConstant n r)
    (by norm_num) (fun k => by rw [div_self (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (numberWeight_one_le k))))]; norm_num)
    (drift_fourth_div_bound r)
  simpa only [drift_fourth,fourth_diagonal_eq_one] using hh

theorem thermalGenerator_fourth_bound (r : ℝ) : ∃ C : ℝ, ∀ (ρ : State n) (hm : FiniteMoment 6 ρ),
    (WeightedGenerator.pairing r (weightedRoot 3 ρ hm) (1 : Fock n →L[ℂ] Fock n)).re≤C := by
  obtain ⟨C,hC⟩ := driftPolynomial_bounded n r
  refine ⟨C,fun ρ hm => ?_⟩
  have hh := thermalGenerator_fourth r ρ hm
  have hpos (k : NumberIndex n) : 0≤(entry ρ.op k k).re := ρ.positive.re_inner_nonneg_right _
  have hle := hh.summable.tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_right (hC (totalNumber k)) (hpos k))
    (ρ.trace_one.summable.mul_left C)
  simpa only [hh.tsum_eq,tsum_mul_left,ρ.trace_one.tsum_eq,mul_one] using hle
end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate

namespace EntropyPhotonNumber.Regularization
open QuantumTrace Annihilation
variable {n : ℕ} (R : Regularization n)

theorem attenuation_mem : 1-R.δ ∈ Set.Icc 0 1 :=
  ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩

theorem thermal_state_diagonal (r : ℝ) (hr : 0<r) (k l : NumberIndex n) :
    entry (thermalState n r hr).op k l=if k=l then (thermalWeight n r k:ℂ) else 0 := by
  rw [entry,← numberBasis_apply n k,← numberBasis_apply n l]
  change inner ℂ (numberBasis n k) ((diagonalState _ _ _).op (numberBasis n l))=_
  rw [diagonalState_eigen,inner_smul_right,
    orthonormal_iff_ite.mp (numberBasis n).orthonormal k l]
  split_ifs with h
  · subst l; simp only [mul_one]
  · simp only [mul_zero]

theorem minimum_spectral_pairing_balance (ρ σ : State n)
    (hmρ : FiniteMoment 4 ρ) (hmσ : FiniteMoment 4 σ)
    (s1 s2 d r0 : ℝ) (hd : 0<d) (hr0 : 0<r0)
    (heq : r0=(1-R.δ)*(R.η*s1+(1-R.η)*s2)+(1-(1-R.δ))*d)
    (hD : R.τD=thermalState n d hd) (hτ : R.τ0=thermalState n r0 hr0)
    (hκ : 0<R.κ)
    (hmin : ∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' → R.objective ρ σ ≤ R.objective ρ' σ') :
    ∃ (G1 : GibbsData n (R.ζ/R.a1) ρ) (G2 : GibbsData n (R.ζ/R.a2) σ)
      (G0 : SpectralLogData n (R.output ρ σ))
      (h6ρ : FiniteMoment 6 ρ) (h6σ : FiniteMoment 6 σ) (h60 : FiniteMoment 6 (R.output ρ σ)),
      (R.a1:ℂ)*WeightedGenerator.pairing s1 (weightedRoot 3 ρ h6ρ) G1.logSandwich+
      (R.a2:ℂ)*WeightedGenerator.pairing s2 (weightedRoot 3 σ h6σ) G2.logSandwich=
      (R.c:ℂ)*WeightedGenerator.pairing r0 (weightedRoot 3 (R.output ρ σ) h60) G0.logSandwich+
      (R.b1:ℂ)*WeightedGenerator.pairing s1 (weightedRoot 3 ρ h6ρ) (numberSandwich n)+
      (R.b2:ℂ)*WeightedGenerator.pairing s2 (weightedRoot 3 σ h6σ) (numberSandwich n)+
      (R.ζ:ℂ)*(WeightedGenerator.pairing s1 (weightedRoot 3 ρ h6ρ) (1 : Fock n →L[ℂ] Fock n)+
        WeightedGenerator.pairing s2 (weightedRoot 3 σ h6σ) (1 : Fock n →L[ℂ] Fock n)) ∧
      (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
        (1-R.κ)^2*BKM.quadratic G1.basis G1.probability
          (BKM.center G1.basis G1.probability
            (rawFirstSlice R.η (1-R.δ) R.hη R.attenuation_mem σ R.τD Z)) ≤
          (R.a1/R.c)*BKM.quadratic G0.basis G0.probability Z) ∧
      (∀ Z : Fock n →L[ℂ] Fock n, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
        (1-R.κ)^2*BKM.quadratic G2.basis G2.probability
          (BKM.center G2.basis G2.probability
            (rawSecondSlice R.η (1-R.δ) R.hη R.attenuation_mem ρ R.τD Z)) ≤
          (R.a2/R.c)*BKM.quadratic G0.basis G0.probability Z) := by
  have h6D : FiniteMoment 6 R.τD := by rw [hD]; exact thermalState_finiteMoment n 6 d hd
  have h4D : FiniteMoment 4 R.τD := finiteMoment_mono (by norm_num) h6D
  have h6O : FiniteMoment 6 R.τ0 := by rw [hτ]; exact thermalState_finiteMoment n 6 r0 hr0
  obtain ⟨J,b,p,hp,hs,he,G1,G2,B,D1,D2,hB,hD1,hD2,hBe,heD1,heD2,hbal,hh1,hh2⟩ :=
    R.minimum_physical_pairing_balance ρ σ hmρ hmσ h4D hr0 hτ hκ hmin
  have h6ρ : FiniteMoment 6 ρ := finiteMoment_mono (by norm_num) G1.moment
  have h6σ : FiniteMoment 6 σ := finiteMoment_mono (by norm_num) G2.moment
  obtain ⟨h60,hcov⟩ := R.canonical_output_generator ρ σ h6ρ h6σ h6D h6O
    s1 s2 d r0 hd hr0 heq
    (by intro k l; rw [hD]; exact thermal_state_diagonal d hd k l)
    (by intro k l; rw [hτ]; exact thermal_state_diagonal r0 hr0 k l) B
  have hb := hbal s1 s2 (WeightedColumns.canonical ρ h6ρ) (WeightedColumns.canonical σ h6σ)
  have hθ : 1-R.δ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr R.hδ.2,sub_le_self _ R.hδ.1⟩
  change WeightedGenerator.pairing r0 (WeightedColumns.canonical (R.output ρ σ) h60).vector B=
    ((1-R.κ:ℝ):ℂ)*(WeightedGenerator.pairing s1 (WeightedColumns.canonical ρ h6ρ).vector
      ((WeightedColumns.canonical σ h6σ).slice R.η R.hη
        ((WeightedColumns.canonical R.τD h6D).slice (1-R.δ) hθ B))+
      WeightedGenerator.pairing s2 (WeightedColumns.canonical σ h6σ).vector
      ((WeightedColumns.canonical ρ h6ρ).sliceRight R.η R.hη
        ((WeightedColumns.canonical R.τD h6D).slice (1-R.δ) hθ B))) at hcov
  rw [WeightedColumns.canonical_slice R.τD h6D h4D,
    WeightedColumns.canonical_slice σ h6σ hmσ,
    WeightedColumns.canonical_sliceRight ρ h6ρ hmρ] at hcov
  rw [mul_assoc (R.c:ℂ),← hcov] at hb
  rw [G1.quarticLogarithm_eq_logSandwich,G2.quarticLogarithm_eq_logSandwich,
    numberSandwich_unique D1 hD1 heD1,numberSandwich_unique D2 hD2 heD2] at hb
  obtain ⟨G0,hJ,hbasis,hprob,hlog⟩ := spectralLogData_of_sandwich b p hp hs he h60 B hB hBe
  cases hJ
  have hbEq := eq_of_heq hbasis
  have hpEq := eq_of_heq hprob
  subst b
  subst p
  refine ⟨G1,G2,G0,h6ρ,h6σ,h60,?_,?_,?_⟩
  · simpa only [hlog,WeightedColumns.canonical] using hb
  · intro Z hZ
    have hp1 : G1.probability=gibbsWeight G1.eigenval := rfl
    rw [hp1]
    simpa only [R.firstFlow_dual_raw] using hh1 Z hZ
  · intro Z hZ
    have hp2 : G2.probability=gibbsWeight G2.eigenval := rfl
    rw [hp2]
    simpa only [R.secondFlow_dual_raw] using hh2 Z hZ
end EntropyPhotonNumber.Regularization

namespace EntropyPhotonNumber

section
open QuantumTrace ThermalMetric

structure ThermalSetup where
  η : ℝ
  θ : ℝ
  κ : ℝ
  ε : ℝ
  d : ℝ
  r1 : ℝ
  r2 : ℝ
  hη : η ∈ Set.Ioo 0 1
  hθ : θ ∈ Set.Ioo 0 1
  hκ : κ ∈ Set.Ioo 0 1
  hε : 0<ε
  hd : 0<d
  hr1 : 0<r1
  hr2 : 0<r2
  slack_r : (1+ε)*(θ*η*r1+θ*(1-η)*r2)≤θ*(η*r1+(1-η)*r2)+(1-θ)*d
  slack_s : (1+ε)*(θ*η*(r1+1)+θ*(1-η)*(r2+1))≤θ*(η*r1+(1-η)*r2)+(1-θ)*d+1
  small_κ : κ≤ε^2/(4*(ε+2)*mixtureConstant (θ*(η*r1+(1-η)*r2)+(1-θ)*d)^2)

namespace ThermalSetup
variable (P : ThermalSetup)
def r0 : ℝ := P.θ*(P.η*P.r1+(1-P.η)*P.r2)+(1-P.θ)*P.d
def w1 : ℝ := (1-P.κ)*P.θ*P.η
def w2 : ℝ := (1-P.κ)*P.θ*(1-P.η)
theorem r0_pos : 0<P.r0 := by
  unfold r0
  exact add_pos (mul_pos P.hθ.1 (add_pos (mul_pos P.hη.1 P.hr1)
    (mul_pos (sub_pos.mpr P.hη.2) P.hr2))) (mul_pos (sub_pos.mpr P.hθ.2) P.hd)
theorem w1_pos : 0<P.w1 := mul_pos (mul_pos (sub_pos.mpr P.hκ.2) P.hθ.1) P.hη.1
theorem w2_pos : 0<P.w2 := mul_pos (mul_pos (sub_pos.mpr P.hκ.2) P.hθ.1) (sub_pos.mpr P.hη.2)
theorem η_mem : P.η ∈ Set.Icc 0 1 := ⟨P.hη.1.le,P.hη.2.le⟩
theorem θ_mem : P.θ ∈ Set.Icc 0 1 := ⟨P.hθ.1.le,P.hθ.2.le⟩
theorem κ_mem : P.κ ∈ Set.Icc 0 1 := ⟨P.hκ.1.le,P.hκ.2.le⟩
theorem δ_mem : 1-P.θ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr P.hθ.2.le,sub_le_self _ P.hθ.1.le⟩

def reg (n : ℕ) (ζ : ℝ) (hζ : 0<ζ) : Regularization n where
  η := P.η
  δ := 1-P.θ
  κ := P.κ
  hη := P.η_mem
  hδ := P.δ_mem
  hκ := P.κ_mem
  τD := thermalState n P.d P.hd
  τ0 := thermalState n P.r0 P.r0_pos
  finiteD := thermalState_finiteEnergy n P.d P.hd
  finite0 := thermalState_finiteEnergy n P.r0 P.r0_pos
  c := 1/h P.r0
  a1 := (1+P.ε)*P.w1/h P.r1
  a2 := (1+P.ε)*P.w2/h P.r2
  b1 := P.ε*P.w1
  b2 := P.ε*P.w2
  ζ := ζ
  hc := one_div_pos.mpr (h_pos P.r0_pos)
  ha1 := div_pos (mul_pos (by linarith [P.hε]) P.w1_pos) (h_pos P.hr1)
  ha2 := div_pos (mul_pos (by linarith [P.hε]) P.w2_pos) (h_pos P.hr2)
  hb1 := mul_pos P.hε P.w1_pos
  hb2 := mul_pos P.hε P.w2_pos
  hζ := hζ

def middle {n : ℕ} (ρ σ : State n) : State n := beamOutput P.η P.η_mem ρ σ
def raw {n : ℕ} (ρ σ : State n) : State n :=
  beamOutput P.θ P.θ_mem (P.middle ρ σ) (thermalState n P.d P.hd)
theorem raw_finiteMoment {n m : ℕ} {ρ σ : State n} (hρ : FiniteMoment m ρ) (hσ : FiniteMoment m σ) :
    FiniteMoment m (P.raw ρ σ) :=
  beamOutput_finiteMoment _ _ (beamOutput_finiteMoment _ _ hρ hσ) (thermalState_finiteMoment n m P.d P.hd)
theorem output_op {n : ℕ} (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n) :
    ((P.reg n ζ hζ).output ρ σ).op=((1-P.κ:ℝ):ℂ) • (P.raw ρ σ).op+
      (P.κ:ℂ) • (thermalState n P.r0 P.r0_pos).op := by
  simp only [Regularization.output,reg,regularizedOutput,sub_sub_cancel,mixture,raw,middle]
end ThermalSetup

namespace WeightedColumns
variable {n : ℕ} {ρ : State n}
theorem sum_lowerEnergy (X : WeightedColumns ρ) : (∑ j, X.lowerEnergy j)=energy ρ := by
  have hh := hasSum_sum (fun j (_hj : j ∈ (Finset.univ : Finset (Fin n))) => X.lowerEnergy_hasSum j)
  have he : HasSum (fun k => (totalNumber k:ℝ)*(entry ρ.op k k).re) (∑ j, X.lowerEnergy j) := by
    simpa only [totalNumber,Nat.cast_sum,Finset.sum_mul] using hh
  exact he.tsum_eq.symm
end WeightedColumns
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
theorem centeredEnergy_eq_energy (t : ℝ) (ht : 0<t) :
    G.centeredEnergy=energy ρ-(∑ j, ‖G.annihilationMean j‖^2) := by
  rw [G.centeredEnergy_lowerEnergy t ht,Finset.sum_sub_distrib,G.weightedColumns.sum_lowerEnergy]
end SpectralLogData
end

open QuantumTrace ThermalMetric Annihilation
namespace SpectralLogData
variable {n : ℕ} {ρ : State n} (G : SpectralLogData n ρ)
def defectSquared (r : ℝ) (hr : 0<r) : ℝ := ∑ j, ‖G.defect r hr j‖^2
def meanSquared : ℝ := ∑ j, ‖G.annihilationMean j‖^2
theorem defectSquared_nonneg (r : ℝ) (hr : 0<r) : 0≤G.defectSquared r hr := Finset.sum_nonneg (fun _j _ => sq_nonneg _)
theorem meanSquared_nonneg : 0≤G.meanSquared := Finset.sum_nonneg (fun _j _ => sq_nonneg _)
end SpectralLogData
namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)
theorem spectral_defect (hk : 0<k) (r : ℝ) (hr : 0<r) (j : Fin n) :
    ‖(G.toSpectralLogData hk).defect r hr j‖=‖G.defect hk r hr j‖ := rfl
theorem spectral_mean (hk : 0<k) (j : Fin n) :
    (G.toSpectralLogData hk).annihilationMean j=G.annihilationMean j := rfl
end GibbsData
namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)

theorem physical_estimate (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n)
    (G1 : SpectralLogData n ρ) (G2 : SpectralLogData n σ)
    (G0 : SpectralLogData n ((P.reg n ζ hζ).output ρ σ))
    (h6ρ : FiniteMoment 6 ρ) (h6σ : FiniteMoment 6 σ)
    (hh1 : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-P.κ)^2*BKM.quadratic G1.basis G1.probability
        (BKM.center G1.basis G1.probability (rawFirstSlice P.η P.θ P.η_mem P.θ_mem σ (thermalState n P.d P.hd) Z))≤
        ((1+P.ε)*P.w1/h P.r1)/(1/h P.r0)*BKM.quadratic G0.basis G0.probability Z)
    (hh2 : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-P.κ)^2*BKM.quadratic G2.basis G2.probability
        (BKM.center G2.basis G2.probability (rawSecondSlice P.η P.θ P.η_mem P.θ_mem ρ (thermalState n P.d P.hd) Z))≤
        ((1+P.ε)*P.w2/h P.r2)/(1/h P.r0)*BKM.quadratic G0.basis G0.probability Z) :
    G0.defectSquared P.r0 P.r0_pos≤
      P.w1*G1.defectSquared P.r1 P.hr1+P.w2*G2.defectSquared P.r2 P.hr2+
      P.ε/2*(P.w1*G1.defectSquared P.r1 P.hr1+P.w2*G2.defectSquared P.r2 P.hr2+
        (P.w1*G1.meanSquared+P.w2*G2.meanSquared)) := by
  let a : Fin 2 → ℝ := ![P.r1,P.r2]
  have ha : ∀ i, 0<a i := by intro i; fin_cases i; exact P.hr1; exact P.hr2
  let states : Fin 2 → State n := ![ρ,σ]
  let G : (i : Fin 2) → SpectralLogData n (states i) := Fin.cases G1 (Fin.cases G2 (fun i => Fin.elim0 i))
  have hr0 : 0<outputReference P.η P.θ a P.d := P.r0_pos
  let D := WeightedColumns.canonical (thermalState n P.d P.hd) (thermalState_finiteMoment n 6 P.d P.hd)
  let M := WeightedColumns.canonical (P.middle ρ σ) (beamOutput_finiteMoment _ _ h6ρ h6σ)
  let V := WeightedColumns.canonical (P.raw ρ σ) (P.raw_finiteMoment h6ρ h6σ)
  let O := WeightedColumns.canonical (thermalState n P.r0 P.r0_pos) (thermalState_finiteMoment n 6 P.r0 P.r0_pos)
  have hh := physical_defect_estimate P.η P.θ P.κ P.ε P.d a P.hη P.hθ P.κ_mem P.hκ.2 P.hd ha hr0
    states (thermalState n P.d P.hd) (P.middle ρ σ) (P.raw ρ σ) (thermalState n P.r0 P.r0_pos)
    ((P.reg n ζ hζ).output ρ σ) (beamOutput_spec _ _ _ _) (beamOutput_spec _ _ _ _) G G0 D M V O
    (Regularization.thermal_state_diagonal P.d P.hd)
    (Regularization.thermal_state_diagonal P.r0 P.r0_pos) (P.output_op ζ hζ ρ σ) ?_ ?_ ?_ ?_ P.hε P.small_κ
  · simp only [Fin.sum_univ_two] at hh
    change G0.defectSquared P.r0 P.r0_pos≤
      ((1-P.κ)*(P.θ*P.η))*G1.defectSquared P.r1 P.hr1+
      ((1-P.κ)*(P.θ*(1-P.η)))*G2.defectSquared P.r2 P.hr2+
      P.ε/2*(((1-P.κ)*(P.θ*P.η))*G1.defectSquared P.r1 P.hr1+
        ((1-P.κ)*(P.θ*(1-P.η)))*G2.defectSquared P.r2 P.hr2+
        (((1-P.κ)*(P.θ*P.η))*G1.meanSquared+((1-P.κ)*(P.θ*(1-P.η)))*G2.meanSquared)) at hh
    simpa only [w1,w2,mul_assoc] using hh
  · intro Z hZ
    change (1-P.κ)^2*BKM.quadratic G1.basis G1.probability
        (BKM.center G1.basis G1.probability (rawFirstSlice P.η P.θ P.η_mem P.θ_mem σ (thermalState n P.d P.hd) Z))≤
      (1+P.ε)*(1-P.κ)*(P.θ*P.η)*(h P.r0/h P.r1)*BKM.quadratic G0.basis G0.probability Z
    have hc : (1+P.ε)*(1-P.κ)*(P.θ*P.η)*(h P.r0/h P.r1)=((1+P.ε)*P.w1/h P.r1)/(1/h P.r0) := by
      unfold w1
      field_simp [(h_pos P.r0_pos).ne']
    rw [hc]
    exact hh1 Z hZ
  · intro Z hZ
    change (1-P.κ)^2*BKM.quadratic G2.basis G2.probability
        (BKM.center G2.basis G2.probability (rawSecondSlice P.η P.θ P.η_mem P.θ_mem ρ (thermalState n P.d P.hd) Z))≤
      (1+P.ε)*(1-P.κ)*(P.θ*(1-P.η))*(h P.r0/h P.r2)*BKM.quadratic G0.basis G0.probability Z
    have hc : (1+P.ε)*(1-P.κ)*(P.θ*(1-P.η))*(h P.r0/h P.r2)=((1+P.ε)*P.w2/h P.r2)/(1/h P.r0) := by
      unfold w2
      field_simp [(h_pos P.r0_pos).ne']
    rw [hc]
    exact hh2 Z hZ
  · simpa only [Fin.sum_univ_two,twoPortLambda,a,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.head_cons,Matrix.cons_val_fin_one,outputReference] using P.slack_r
  · simpa only [Fin.sum_univ_two,twoPortLambda,a,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.head_cons,Matrix.cons_val_fin_one,outputReference] using P.slack_s

theorem physical_energy (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n)
    (G1 : SpectralLogData n ρ) (G2 : SpectralLogData n σ)
    (G0 : SpectralLogData n ((P.reg n ζ hζ).output ρ σ))
    (h6ρ : FiniteMoment 6 ρ) (h6σ : FiniteMoment 6 σ) :
    ∃ v : ℝ, 0≤v ∧ G0.centeredEnergy-(n:ℝ)*P.r0=
      P.w1*(G1.centeredEnergy-(n:ℝ)*P.r1)+P.w2*(G2.centeredEnergy-(n:ℝ)*P.r2)+P.κ*(1-P.κ)*v := by
  let D := WeightedColumns.canonical (thermalState n P.d P.hd) (thermalState_finiteMoment n 6 P.d P.hd)
  let M := WeightedColumns.canonical (P.middle ρ σ) (beamOutput_finiteMoment _ _ h6ρ h6σ)
  let V := WeightedColumns.canonical (P.raw ρ σ) (P.raw_finiteMoment h6ρ h6σ)
  let O := WeightedColumns.canonical (thermalState n P.r0 P.r0_pos) (thermalState_finiteMoment n 6 P.r0 P.r0_pos)
  refine ⟨∑ j, ‖V.weakMean P.r0 j‖^2,Finset.sum_nonneg (fun _j _ => sq_nonneg _),?_⟩
  exact physical_centered_energy_identity P.η P.θ P.κ P.r1 P.r2 P.d P.η_mem P.θ_mem P.hd P.hr1 P.hr2 P.r0_pos
    ρ σ (thermalState n P.d P.hd) (P.middle ρ σ) (P.raw ρ σ) (thermalState n P.r0 P.r0_pos)
    ((P.reg n ζ hζ).output ρ σ) (beamOutput_spec _ _ _ _) (beamOutput_spec _ _ _ _) G1 G2 G0 D M V O
    (Regularization.thermal_state_diagonal P.d P.hd) (Regularization.thermal_state_diagonal P.r0 P.r0_pos)
    (P.output_op ζ hζ ρ σ)
end ThermalSetup

namespace ThermalDual

theorem decay_from_cancellation (q A M ε K ζ D C : ℝ) (hε : 0<ε) (hζ : 0≤ζ)
    (hK : 0≤K) (hD : D≤C)
    (hq : q≤A+ε/2*(A+M)) (hc : 0=q-(1+ε)*A-ε*M-K+ζ*D) :
    A+M≤(2*C/ε)*ζ := by
  have hh : ε/2*(A+M)≤ζ*C := by nlinarith [mul_le_mul_of_nonneg_left hD hζ]
  calc
    (A+M) ≤ (2*C*ζ)/ε := by apply (le_div_iff₀ hε).mpr; nlinarith only [hh]
    _ = (2*C/ε)*ζ := by ring

end ThermalDual
namespace ThermalSetup
variable {n : ℕ} (P : ThermalSetup)

theorem minimum_decay (C1 C2 : ℝ)
    (hC1 : ∀ (ρ : State n) (hm : FiniteMoment 6 ρ),
      (WeightedGenerator.pairing P.r1 (weightedRoot 3 ρ hm) (1 : Fock n →L[ℂ] Fock n)).re≤C1)
    (hC2 : ∀ (ρ : State n) (hm : FiniteMoment 6 ρ),
      (WeightedGenerator.pairing P.r2 (weightedRoot 3 ρ hm) (1 : Fock n →L[ℂ] Fock n)).re≤C2)
    (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n) (hmρ : FiniteMoment 4 ρ) (hmσ : FiniteMoment 4 σ)
    (hmin : ∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' →
      (P.reg n ζ hζ).objective ρ σ≤(P.reg n ζ hζ).objective ρ' σ') :
    ∃ (G1 : GibbsData n (ζ/((1+P.ε)*P.w1/h P.r1)) ρ)
      (G2 : GibbsData n (ζ/((1+P.ε)*P.w2/h P.r2)) σ),
      P.w1*((∑ j, ‖G1.defect (div_pos hζ (P.reg n ζ hζ).ha1) P.r1 P.hr1 j‖^2)+
        (∑ j, ‖G1.annihilationMean j‖^2))+
      P.w2*((∑ j, ‖G2.defect (div_pos hζ (P.reg n ζ hζ).ha2) P.r2 P.hr2 j‖^2)+
        (∑ j, ‖G2.annihilationMean j‖^2)) ≤ (2*(C1+C2)/P.ε)*ζ := by
  let R := P.reg n ζ hζ
  obtain ⟨G1,G2,G0,h6ρ,h6σ,h60,hbal,hh1,hh2⟩ := R.minimum_spectral_pairing_balance ρ σ hmρ hmσ
    P.r1 P.r2 P.d P.r0 P.hd P.r0_pos (by simp only [R,reg,sub_sub_cancel]; rfl) rfl rfl P.hκ.1 hmin
  let E1 := G1.toSpectralLogData (div_pos R.hζ R.ha1)
  let E2 := G2.toSpectralLogData (div_pos R.hζ R.ha2)
  have hH1 : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-P.κ)^2*BKM.quadratic E1.basis E1.probability
        (BKM.center E1.basis E1.probability (rawFirstSlice P.η P.θ P.η_mem P.θ_mem σ (thermalState n P.d P.hd) Z))≤
        ((1+P.ε)*P.w1/h P.r1)/(1/h P.r0)*BKM.quadratic G0.basis G0.probability Z := by
    intro Z hZ
    simpa only [E1,GibbsData.toSpectralLogData,R,reg,sub_sub_cancel] using hh1 Z hZ
  have hH2 : ∀ Z, Z ∈ CenteredTests.operatorSpace G0.basis G0.probability →
      (1-P.κ)^2*BKM.quadratic E2.basis E2.probability
        (BKM.center E2.basis E2.probability (rawSecondSlice P.η P.θ P.η_mem P.θ_mem ρ (thermalState n P.d P.hd) Z))≤
        ((1+P.ε)*P.w2/h P.r2)/(1/h P.r0)*BKM.quadratic G0.basis G0.probability Z := by
    intro Z hZ
    simpa only [E2,GibbsData.toSpectralLogData,R,reg,sub_sub_cancel] using hh2 Z hZ
  have hdef := P.physical_estimate ζ hζ ρ σ E1 E2 G0 h6ρ h6σ hH1 hH2
  obtain ⟨v,hv,hce⟩ := P.physical_energy ζ hζ ρ σ E1 E2 G0 h6ρ h6σ
  have hbalr := congrArg Complex.re hbal
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hbalr
  have hstat :
      (1+P.ε)*P.w1*((WeightedGenerator.pairing P.r1 (weightedRoot 3 ρ h6ρ) E1.logSandwich).re/h P.r1)+
      (1+P.ε)*P.w2*((WeightedGenerator.pairing P.r2 (weightedRoot 3 σ h6σ) E2.logSandwich).re/h P.r2)=
      (WeightedGenerator.pairing P.r0 (weightedRoot 3 (R.output ρ σ) h60) G0.logSandwich).re/h P.r0+
      P.ε*P.w1*(WeightedGenerator.pairing P.r1 (weightedRoot 3 ρ h6ρ) (numberSandwich n)).re+
      P.ε*P.w2*(WeightedGenerator.pairing P.r2 (weightedRoot 3 σ h6σ) (numberSandwich n)).re+
      ζ*((WeightedGenerator.pairing P.r1 (weightedRoot 3 ρ h6ρ) (1 : Fock n →L[ℂ] Fock n)).re+
        (WeightedGenerator.pairing P.r2 (weightedRoot 3 σ h6σ) (1 : Fock n →L[ℂ] Fock n)).re) := by
    convert hbalr using 1 <;> dsimp only [R,reg,E1,E2,GibbsData.toSpectralLogData] <;> ring
  rw [E1.entropy_production h6ρ P.r1 P.hr1,E2.entropy_production h6σ P.r2 P.hr2,
    G0.entropy_production h60 P.r0 P.r0_pos,thermalGenerator_number,thermalGenerator_number] at hstat
  have he1 : energy ρ=E1.centeredEnergy+E1.meanSquared := by
    have hh := E1.centeredEnergy_eq_energy P.r1 P.hr1
    change E1.centeredEnergy=energy ρ-E1.meanSquared at hh
    linarith
  have he2 : energy σ=E2.centeredEnergy+E2.meanSquared := by
    have hh := E2.centeredEnergy_eq_energy P.r2 P.hr2
    change E2.centeredEnergy=energy σ-E2.meanSquared at hh
    linarith
  rw [he1,he2,hce] at hstat
  have hc : 0=G0.defectSquared P.r0 P.r0_pos-
      (1+P.ε)*(P.w1*E1.defectSquared P.r1 P.hr1+P.w2*E2.defectSquared P.r2 P.hr2)-
      P.ε*(P.w1*E1.meanSquared+P.w2*E2.meanSquared)-P.κ*(1-P.κ)*v+
      ζ*((WeightedGenerator.pairing P.r1 (weightedRoot 3 ρ h6ρ) (1 : Fock n →L[ℂ] Fock n)).re+
        (WeightedGenerator.pairing P.r2 (weightedRoot 3 σ h6σ) (1 : Fock n →L[ℂ] Fock n)).re) := by
    dsimp only [SpectralLogData.defectSquared]
    linear_combination hstat
  have hdec := ThermalDual.decay_from_cancellation _ _ _ _ _ _ _ (C1+C2) P.hε hζ.le
    (mul_nonneg (mul_nonneg P.hκ.1.le (sub_nonneg.mpr P.hκ.2.le)) hv)
    (add_le_add (hC1 ρ h6ρ) (hC2 σ h6σ)) hdef hc
  refine ⟨G1,G2,?_⟩
  change P.w1*(E1.defectSquared P.r1 P.hr1+E1.meanSquared)+
    P.w2*(E2.defectSquared P.r2 P.hr2+E2.meanSquared)≤(2*(C1+C2)/P.ε)*ζ
  nlinarith only [hdec]

theorem uniform_minimum_decay : ∃ C : ℝ, 0<C ∧ ∀ (ζ : ℝ) (hζ : 0<ζ) (ρ σ : State n),
    FiniteMoment 4 ρ → FiniteMoment 4 σ →
    (∀ ρ' σ', FiniteMoment 4 ρ' → FiniteMoment 4 σ' →
      (P.reg n ζ hζ).objective ρ σ≤(P.reg n ζ hζ).objective ρ' σ') →
    ∃ (G1 : GibbsData n (ζ/((1+P.ε)*P.w1/h P.r1)) ρ)
      (G2 : GibbsData n (ζ/((1+P.ε)*P.w2/h P.r2)) σ),
      P.w1*((∑ j, ‖G1.defect (div_pos hζ (P.reg n ζ hζ).ha1) P.r1 P.hr1 j‖^2)+
        (∑ j, ‖G1.annihilationMean j‖^2))+
      P.w2*((∑ j, ‖G2.defect (div_pos hζ (P.reg n ζ hζ).ha2) P.r2 P.hr2 j‖^2)+
        (∑ j, ‖G2.annihilationMean j‖^2)) ≤ C*ζ := by
  obtain ⟨C1,hC1⟩ := thermalGenerator_fourth_bound (n:=n) P.r1
  obtain ⟨C2,hC2⟩ := thermalGenerator_fourth_bound (n:=n) P.r2
  refine ⟨2*(max C1 0+1+max C2 0)/P.ε,div_pos (by positivity) P.hε,?_⟩
  intro ζ hζ ρ σ hmρ hmσ hmin
  exact P.minimum_decay (max C1 0+1) (max C2 0)
    (fun ρ hm => (hC1 ρ hm).trans (by linarith [le_max_left C1 0]))
    (fun ρ hm => (hC2 ρ hm).trans (le_max_left C2 0)) ζ hζ ρ σ hmρ hmσ hmin
end ThermalSetup
end EntropyPhotonNumber

end

end OAI
