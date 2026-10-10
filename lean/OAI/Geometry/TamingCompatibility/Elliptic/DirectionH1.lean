import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.DerivativeIndex
import OAI.Geometry.TamingCompatibility.Elliptic.ChartGarding

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.EuclideanEnergy
open MeasureTheory
open scoped SchwartzMap LineDeriv
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma direction_norm_sq_bound (L : V →L[ℝ] F) (v : V) (hv : ‖v‖ ≤ 1) :
    ‖L v‖^2 ≤ 4 * ∑ i : Fin 4, ‖L (e i)‖^2 := by
  have hexp : v = ∑ i : Fin 4, v i • e i := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,e] using
      ((EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr v).symm
  have hc (i : Fin 4) : ‖v i‖ ≤ 1 := by
    rw [← EuclideanSpace.basisFun_inner]
    exact (norm_inner_le_norm _ _).trans (by simpa using hv)
  have hn : ‖L v‖ ≤ ∑ i : Fin 4, ‖L (e i)‖ := by
    conv_lhs => rw [hexp,map_sum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
      rw [map_smul,norm_smul]
      exact (mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)).trans_eq (one_mul _))
  have hsq := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin 4 => ‖L (e i)‖)
  simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat] at hsq
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hsq

lemma direction_integral_bound (u : 𝓢(V,F)) (v : V) (hv : ‖v‖ ≤ 1) :
    (∫ x, ‖(∂_{v} u) x‖^2) ≤ 4 * ∑ i : Fin 4, ∫ x, ‖(∂_{e i} u) x‖^2 := by
  have hi (w : V) : Integrable (fun x => ‖(∂_{w} u) x‖^2) :=
    (memLp_two_iff_integrable_sq_norm (SchwartzMap.continuous _).aestronglyMeasurable).mp
      ((∂_{w} u).memLp 2 volume)
  calc
    _ ≤ ∫ x, 4 * ∑ i : Fin 4, ‖(∂_{e i} u) x‖^2 := by
      apply integral_mono (hi v) ((integrable_finsetSum _ fun i _ => hi (e i)).const_mul 4)
      intro x
      simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      exact direction_norm_sq_bound (fderiv ℝ u x) v hv
    _ = _ := by rw [integral_const_mul,integral_finsetSum _ fun i _ => hi (e i)]
end TamingCompatibility.EuclideanEnergy

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume LocalMatrixOperator EuclideanEnergy
open Set MeasureTheory AntiInvariantFrame
open scoped Manifold ContDiff SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma localizedLinear_support (p : A.centers) (a : smoothForms X 2) :
    tsupport (localizedLinear A 2 p a) ⊆ coordinateSupport A p := by
  apply closure_minimal _ (coordinateSupport_compact A p).isClosed
  intro x hx
  by_contra hn
  apply hx
  change formCoordinates 2 (localizedFunction A p a.val x) = 0
  rw [localizedFunction_zero_off A p a.val hn,map_zero]

section L2Norm
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
lemma schwartz_l2_norm_sq (u : 𝓢(Space,F)) :
    ‖u.toLp 2 (volume : Measure Space)‖^2 = ∫ x, ‖u x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [u.coeFn_toLp 2 (volume : Measure Space)] with x hx
  rw [hx,real_inner_self_eq_norm_sq]
end L2Norm

include hs hD in
omit [T2Space X] in

theorem localized_jet_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : smoothForms X 2, antiInvariantPart J a.val = a.val →
      ∀ j : DerivativeIndex, ‖localizeH1 A 2 a j p‖^2 ≤
        C * ((∫ x, GeometricAdjoint.pairing J α ht a.val a.val x ∂geometricVolume A J α) +
          (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a.val)
            (codifferential J α ht a.val) x ∂geometricVolume A J α)) := by
  let P : Space → CoordinateFiber 2 := fun x => formCoordinates 2
    (realPart (coordinateMetric J α ht p.val x) (fun i => (D p).frame i x))
  let Q : Space → CoordinateFiber 2 := fun x => formCoordinates 2
    (imagPart (coordinateMetric J α ht p.val x) (fun i => (D p).frame i x))
  have hg := (coordinateMetric_smooth J α hs ht p.val).mono (D p).domain_subset
  have hP : ContDiffOn ℝ ∞ P (D p).domain :=
    ContDiffOn.continuousLinearMap_comp (formCoordinates 2) (realPart_smooth hg (D p).frame_smooth)
  have hQ : ContDiffOn ℝ ∞ Q (D p).domain :=
    ContDiffOn.continuousLinearMap_comp (formCoordinates 2) (imagPart_smooth hg (D p).frame_smooth)
  obtain ⟨C,hC,hframe⟩ := frame_h1_bound (D p).domain_open (coordinateSupport_compact A p)
    (coordinateSupport_domain A J α ht D hD p) P Q hP hQ
  obtain ⟨K,hK,hgard⟩ := scalar_garding A J α hs ht D hD p
  refine ⟨16*(C*K),mul_pos (by norm_num) (mul_pos hC hK),?_⟩
  intro a hanti j
  let s := scalarSchwartz A J α ht D hD p a.val a.property 2
  let t := scalarSchwartz A J α ht D hD p a.val a.property 3
  have he : (⇑(localizedLinear A 2 p a)) = fun x => s x • P x + t x • Q x := by
    funext x
    change formCoordinates 2 (localizedFunction A p a.val x) = _
    rw [scalar_expansion A J α ht D hD p hanti x,map_add,map_smul,map_smul]
    rfl
  have hb := hframe s t (localizedLinear A 2 p a) (localizedLinear_support A p a) he
  have hga := hgard a.val a.property hanti
  rw [localizeH1_apply,schwartz_l2_norm_sq]
  have hbound : C*((∫ x, gradientEnergy s t x)+(∫ x, (s x)^2+(t x)^2)) ≤
      C*K*((∫ x, GeometricAdjoint.pairing J α ht a.val a.val x ∂geometricVolume A J α) +
          (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a.val)
            (codifferential J α ht a.val) x ∂geometricVolume A J α)) := by
    exact (mul_le_mul_of_nonneg_left hga hC.le).trans_eq (mul_assoc _ _ _).symm
  have hnonneg : 0 ≤ C*((∫ x, gradientEnergy s t x)+(∫ x, (s x)^2+(t x)^2)) :=
    (integral_nonneg fun x => sq_nonneg ‖localizedLinear A 2 p a x‖).trans hb.1
  have htarget := mul_le_mul_of_nonneg_left hbound (show (0:ℝ) ≤ 16 by norm_num)
  cases j with
  | none => exact (hb.1.trans (by nlinarith : _ ≤ 16*(C*((∫ x, gradientEnergy s t x)+
        (∫ x, (s x)^2+(t x)^2))))).trans (by simpa only [mul_assoc] using htarget)
  | some i =>
    change (∫ x, ‖(∂_{stdOrthonormalBasis ℝ Space i} (localizedLinear A 2 p a)) x‖^2) ≤ _
    have hv : ‖stdOrthonormalBasis ℝ Space i‖ ≤ 1 := le_of_eq
      ((stdOrthonormalBasis ℝ Space).orthonormal.norm_eq_one i)
    have hd := direction_integral_bound (localizedLinear A 2 p a)
      (stdOrthonormalBasis ℝ Space i) hv
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hb.2 k)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_ofNat] at hsum
    exact (hd.trans (by nlinarith : _ ≤ 16*(C*((∫ x, gradientEnergy s t x)+
        (∫ x, (s x)^2+(t x)^2))))).trans (by simpa only [mul_assoc] using htarget)
end TamingCompatibility.GeometricChart

end
end

end
end
end

end OAI
