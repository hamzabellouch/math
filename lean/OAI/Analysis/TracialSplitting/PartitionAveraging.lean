import OAI.Analysis.TracialSplitting.KrausApproximation

namespace OAI


section

noncomputable section

open scoped ComplexOrder ComplexStarModule

namespace NuclearTrace

open Pureness CurrentMain

section ComplexApproximation

variable {A I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype I]

theorem nuclear_uniform_finite_approximation
    (hA : IsNuclear.{0,0} A) (hT : Nonempty (TracialState A))
    (x : I → A) (hx : ∀ i, ‖x i‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : FiniteCoefficientSystem A, F.output 1 = 1 ∧
      ∀ τ : TracialState A, ∀ i : I, ∀ u : A, ‖u‖ ≤ 1 →
        ‖τ.functional (u*(x i-F.output (x i)))‖ < ε := by
  let y : I ⊕ I → selfAdjoint A := Sum.elim (fun i => ℜ (x i)) (fun i => ℑ (x i))
  have hy : ∀ j, ‖(y j : A)‖ ≤ 1 := by
    intro j
    cases j with
    | inl i => exact (realPart.norm_le _).trans (hx i)
    | inr i => exact (imaginaryPart.norm_le _).trans (hx i)
  obtain ⟨F,hF,hclose⟩ := nuclear_uniform_normalized_finite_approximation hA
    (stateHilbertRepresentation A) (stateHilbertRepresentation_injective A) hT y hy
    (show 0 < ε/2 by positivity)
  refine ⟨F,hF,?_⟩
  intro τ i u hu
  have hr := hclose τ (.inl i) u hu
  have hi := hclose τ (.inr i) u hu
  have he : u*(x i-F.output (x i)) =
      u*((ℜ (x i) : A)-F.output (ℜ (x i)))+
      Complex.I • (u*((ℑ (x i) : A)-F.output (ℑ (x i)))) := by
    conv_lhs => rw [← realPart_add_I_smul_imaginaryPart (x i)]
    simp only [map_add,map_smul,mul_sub,mul_add,mul_smul_comm,smul_sub]
    abel
  rw [he,map_add,map_smul]
  apply (norm_add_le _ _).trans_lt
  rw [norm_smul,Complex.norm_I,one_mul]
  change ‖τ.functional (u*((y (.inl i) : A)-F.output (y (.inl i))))‖+
    ‖τ.functional (u*((y (.inr i) : A)-F.output (y (.inr i))))‖ < ε
  linarith

end ComplexApproximation

section Synthesis

variable {A N : Type} [CStarAlgebra A] [Fintype N] [DecidableEq N]

lemma matrixSynthesis_scalarMatrixUnit (a : N → A) (i j : N) :
    matrixSynthesis a (scalarMatrixUnit i j) = star (a i)*a j := by
  change (∑ k, ∑ l, scalarMatrixUnit i j k l • (star (a k)*a l)) = _
  simp [scalarMatrixUnit,Matrix.single_apply,ite_and]

omit [DecidableEq N] in
lemma matrixSynthesis_map {D : Type} [CStarAlgebra D]
    (ι : A →⋆ₐ[ℂ] D) (a : N → A) (T : CStarMatrix N N ℂ) :
    matrixSynthesis (fun i => ι (a i)) T = ι (matrixSynthesis a T) := by
  change (∑ i, ∑ j, T i j • (star (ι (a i))*ι (a j))) =
    ι (∑ i, ∑ j, T i j • (star (a i)*a j))
  simp only [map_sum,map_smul,map_mul,map_star]

end Synthesis

section NuclearGlobalAveraging

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem nuclear_global_partition_averaging
    (hA : IsNuclear.{0,0} A) (ι : A →⋆ₐ[ℂ] D) (hT : Nonempty (TracialState D))
    (K : Finset (unitary A)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : Type) (_ : Fintype N) (a : N → A),
      (∑ i, star (a i)*a i = 1) ∧ (∑ i, a i*star (a i) = 1) ∧
      ∀ x ∈ K, ∀ (J : Type) [Fintype J] (q : J → D),
      (∀ j, IsStarProjection (q j)) → (∑ j, q j = 1) →
      ∀ τ : TracialState D,
      (∑ j, traceOneNorm τ ((∑ i, star (ι (a i))*q j*ι (a i)) -
        star (ι (x : A))*(∑ i, star (ι (a i))*q j*ι (a i))*ι (x : A)))^2 < ε := by
  classical
  have hTA : Nonempty (TracialState A) := ⟨pullbackTrace (Classical.choice hT) ι⟩
  have hx (x : K) : ‖(x.1 : A)‖ ≤ 1 := by
    have h := CStarRing.norm_coe_unitary_mul x.1 (1 : A)
    simpa only [mul_one] using h.trans_le (IsStarProjection.norm_le (1 : A) (IsStarProjection.one A))
  obtain ⟨F,hF,hclose⟩ := nuclear_uniform_finite_approximation hA hTA
    (fun x : K => (x.1 : A)) hx (show 0 < ε/8 by positivity)
  let φ : CStarMatrix F.Index F.Index ℂ →ₗ[ℂ] A := matrixSynthesis F.coefficient
  have hQ : 0 ≤ CStarMatrix.ofMatrix (fun i j => φ (scalarMatrixUnit i j)) := by
    simpa only [φ,matrixSynthesis_scalarMatrixUnit] using coefficient_choi_nonneg F.coefficient
  have hφ : φ 1 = 1 := by
    have he : F.output 1 = φ (F.input 1) := rfl
    rwa [he,F.input_one] at hF
  obtain ⟨a,ha1,ha2,ha⟩ := choi_bistochastic_family
    (CStarMatrix.ofMatrix (fun i j => φ (scalarMatrixUnit i j))) hQ (by
      change (∑ i, φ (scalarMatrixUnit i i)) = 1
      rw [← map_sum,sum_scalarMatrixUnit_diag,hφ])
  refine ⟨F.Index × F.Index,inferInstance,a,ha1,ha2,?_⟩
  intro x hxK J _ q hq hsum τ
  let T := F.input (x : A)
  have hTnorm : ‖T‖ ≤ 1 := (F.input_norm _).trans (hx ⟨x,hxK⟩)
  let φD : CStarMatrix F.Index F.Index ℂ →ₗ[ℂ] D := ι.toLinearMap.comp φ
  have haD (i j : F.Index) : φD (scalarMatrixUnit i j) =
      ∑ k, star (ι (a (k,i)))*ι (a (k,j)) := by
    change ι (φ (scalarMatrixUnit i j)) = _
    rw [show φ (scalarMatrixUnit i j) = ∑ k, star (a (k,i))*a (k,j) from ha i j]
    simp only [map_sum,map_mul,map_star]
  have ha1D : (∑ i, star (ι (a i))*ι (a i)) = 1 := by
    simpa only [map_sum,map_mul,map_star,map_one] using congrArg ι ha1
  obtain ⟨b,v,hb,hv,hb1,hv1,herr⟩ := choi_coupling φD (fun i => ι (a i))
    haD ha1D T hTnorm (mapUnitary ι x)
  have h := choi_global_partition_pairing τ b v
    (φD T) (mapUnitary ι x) hb1 hv1 herr q hq hsum
  have he : ‖(pullbackTrace τ ι).functional
      (star (x : A)*((x : A)-F.output (x : A)))‖ < ε/8 :=
    hclose (pullbackTrace τ ι) ⟨x,hxK⟩ (star (x : A)) (by simpa only [norm_star] using hx ⟨x,hxK⟩)
  have hpair : (τ.functional (star (ι (x : A))*(ι (x : A)-ι (φ T)))).re < ε/8 := by
    apply (Complex.re_le_norm _).trans_lt
    change ‖τ.functional (ι (star (x : A)*((x : A)-F.output (x : A))))‖ < ε/8 at he
    simpa only [map_mul,map_star,map_sub,φ,T,FiniteCoefficientSystem.output,LinearMap.comp_apply] using he
  simp only [hb,hv,mapUnitary_coe] at h
  change _ ≤ 8*(τ.functional (star (ι (x : A))*(ι (x : A)-ι (φ T)))).re at h
  linarith

end NuclearGlobalAveraging

end NuclearTrace

end

end

end OAI
