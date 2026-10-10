import OAI.MeasureTheory.Falconer.Fourier.MaskJetIsometry
import OAI.MeasureTheory.Falconer.Angular.InverseAngularSymbol
import OAI.MeasureTheory.Falconer.Fourier.BaseJetAmplitude

namespace OAI

/-! # Uniform original-mask symbols for a rotated inverse patch -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

abbrev RootInverseIndex (m j : ℕ) (F : Finset PolicyDescriptor) :=
  ((MaskJetExpansion.product : MaskJetExpansion ({b // b ∈ F} ⊕ {b // b ∈ F})
    (m+3) (Space (m+3))).inverse m j).index

noncomputable def rootInverseTerm (m j : ℕ) (F : Finset PolicyDescriptor)
    (a : RootInverseIndex m j F) :=
  (((MaskJetExpansion.product : MaskJetExpansion ({b // b ∈ F} ⊕ {b // b ∈ F})
    (m+3) (Space (m+3))).inverse m j).term a)

theorem rotated_inverse_coefficient_symbol (m j L : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (F : Finset PolicyDescriptor)
      (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (a : RootInverseIndex m j F),
      let g := normalizedAngular A ((rootInverseTerm m j F a).coefficient ∘ T)
      ContDiff ℝ ∞ g ∧
      (∀ t ≤ L, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t g w‖ ≤ (1:ℝ)^t) ∧
      ChartSymbolControl L (fun (_ : Space (m+3)) (w : Sphere (m+3)) => g w) 1 1 := by
  obtain ⟨C,hC,hcoeff⟩ := inverse_seed_coefficient_budget m j L
  obtain ⟨H,hH,hnormalize⟩ := ambient_angular_normalization (m+1) L
  refine ⟨H*C,one_le_mul_of_one_le_of_one_le hH hC,?_⟩
  intro F T a
  let B := (rootInverseTerm m j F a).coefficient
  have hB : ContDiff ℝ ∞ (B ∘ T) := (rootInverseTerm m j F a).coefficient_smooth.comp T.contDiff
  have hb : ∀ t ≤ L, ∀ w : Sphere (m+3), ‖iteratedFDeriv ℝ t (B ∘ T) w‖ ≤ C*(1:ℝ)^t := by
    intro t ht w
    rw [T.norm_iteratedFDeriv_comp_right,one_pow,mul_one]
    exact hcoeff ({b // b ∈ F} ⊕ {b // b ∈ F}) (fun _ => MaskJetIndex.zero (m+3)) a t ht (sphereMap T w)
  exact hnormalize (B ∘ T) hB C 1 (zero_lt_one.trans_le hC) le_rfl hb

noncomputable def rootInverseLeftJets (m j : ℕ) (F : Finset PolicyDescriptor)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (a : RootInverseIndex m j F) :
    PolicyDescriptor → MaskJetIndex (m+3) :=
  fun b => if hb : b ∈ F then ((rootInverseTerm m j F a).jet (.inl ⟨b,hb⟩)).mapIsometry T.symm
    else MaskJetIndex.zero (m+3)

noncomputable def rootInverseRightJets (m j : ℕ) (F : Finset PolicyDescriptor)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (a : RootInverseIndex m j F) :
    PolicyDescriptor → MaskJetIndex (m+3) :=
  fun b => if hb : b ∈ F then ((rootInverseTerm m j F a).jet (.inr ⟨b,hb⟩)).mapIsometry T.symm
    else MaskJetIndex.zero (m+3)

theorem rootInverseLeftJets_order (m j : ℕ) (F : Finset PolicyDescriptor)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (a : RootInverseIndex m j F) :
    (∑ b ∈ F, (rootInverseLeftJets m j F T a b).order) ≤ 2*j := by
  have h := (MaskJetExpansion.product_hasOrder (ι := {b // b ∈ F} ⊕ {b // b ∈ F})).inverse j a
  change (∑ b, ((rootInverseTerm m j F a).jet b).order) ≤ 0+2*j at h
  rw [Fintype.sum_sum_type] at h
  have he : (∑ b ∈ F, (rootInverseLeftJets m j F T a b).order) =
      ∑ b : {b // b ∈ F}, ((rootInverseTerm m j F a).jet (.inl b)).order := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro b _
    simp only [rootInverseLeftJets,dite_eq_left b.property,MaskJetIndex.mapIsometry]
  rw [he]
  omega

theorem rootInverseRightJets_order (m j : ℕ) (F : Finset PolicyDescriptor)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (a : RootInverseIndex m j F) :
    (∑ b ∈ F, (rootInverseRightJets m j F T a b).order) ≤ 2*j := by
  have h := (MaskJetExpansion.product_hasOrder (ι := {b // b ∈ F} ⊕ {b // b ∈ F})).inverse j a
  change (∑ b, ((rootInverseTerm m j F a).jet b).order) ≤ 0+2*j at h
  rw [Fintype.sum_sum_type] at h
  have he : (∑ b ∈ F, (rootInverseRightJets m j F T a b).order) =
      ∑ b : {b // b ∈ F}, ((rootInverseTerm m j F a).jet (.inr b)).order := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro b _
    simp only [rootInverseRightJets,dite_eq_left b.property,MaskJetIndex.mapIsometry]
  rw [he]
  omega

structure RotatedRootSymbols (m j L : ℕ) (F : Finset PolicyDescriptor)
    (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)) (A : ℝ) where
  left : RootInverseIndex m j F → DescriptorJetSymbol (m+1) (2*j) L F 1
  right : RootInverseIndex m j F → DescriptorJetSymbol (m+1) (2*j) L F 1
  left_jet : ∀ a, (left a).jet = rootInverseLeftJets m j F T a
  right_jet : ∀ a, (right a).jet = rootInverseRightJets m j F T a
  left_angular : ∀ a, (left a).angular = normalizedAngular A ((rootInverseTerm m j F a).coefficient ∘ T)
  right_angular : ∀ a, (right a).angular = fun _ => 1
  left_spatial : ∀ a, (left a).spatial = fun _ => 1
  right_spatial : ∀ a, (right a).spatial = fun _ => 1

theorem exists_rotatedRootSymbols (m j L : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (F : Finset PolicyDescriptor)
      (T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)), Nonempty (RotatedRootSymbols m j L F T A) := by
  obtain ⟨A,hA,hcoeff⟩ := rotated_inverse_coefficient_symbol m j L
  refine ⟨A,hA,?_⟩
  intro F T
  let base := DescriptorJetSymbol.base (n := m+1) F (2*j) L 1 (by norm_num)
    (fun _ => 1) measurable_const (by simp)
  let left (a : RootInverseIndex m j F) : DescriptorJetSymbol (m+1) (2*j) L F 1 :=
    { base with
      jet := rootInverseLeftJets m j F T a
      order_le := rootInverseLeftJets_order m j F T a
      angular := normalizedAngular A ((rootInverseTerm m j F a).coefficient ∘ T)
      angular_smooth := (hcoeff F T a).1
      angular_derivative := (hcoeff F T a).2.1
      angular_control := (hcoeff F T a).2.2 }
  let right (a : RootInverseIndex m j F) : DescriptorJetSymbol (m+1) (2*j) L F 1 :=
    { base with jet := rootInverseRightJets m j F T a, order_le := rootInverseRightJets_order m j F T a }
  exact ⟨⟨left,right,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩⟩

end Falconer

end OAI
