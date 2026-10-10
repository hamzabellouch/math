import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.DirectionH1
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCutoffIntegral

namespace OAI

section
section

section
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap LineDeriv ContDiff
namespace TamingCompatibility.HodgeMatrixEnergy
open EuclideanEnergy
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma value_smooth (f : Field) : ContDiff ℝ ∞ (value f) :=
  (contDiff_piLp 2).mpr (fun j => (f j).smooth (⊤ : ℕ∞))
lemma value_fderiv (f : Field) (x : V) (i : Fin 4) :
    fderiv ℝ (value f) x (e i) = derivative f i x := by
  ext j
  have hp := (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp x
    ((value_smooth f).differentiable (by simp) x).hasFDerivAt
  have he := congrArg (fun L : V →L[ℝ] ℝ => L (e i)) hp.fderiv
  change fderiv ℝ (f j) x (e i) = _ at he
  exact he.symm

lemma frame_deriv_bound {P : V → W →L[ℝ] F} {u : V → F} (f : Field)
    (he : u = fun x => P x (value f x)) {x : V} (hP : DifferentiableAt ℝ P x)
    {C : ℝ} (hbP : ‖P x‖ ≤ C) (hdP : ‖fderiv ℝ P x‖ ≤ C) (i : Fin 4) :
    ‖fderiv ℝ u x (e i)‖^2 ≤ 2*C^2*(gradient f x + ‖value f x‖^2) := by
  have hder : fderiv ℝ u x (e i) = fderiv ℝ P x (e i) (value f x) + P x (derivative f i x) := by
    rw [he, fderiv_clm_apply hP ((value_smooth f).differentiable (by simp) x)]
    simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply,value_fderiv,add_comm]
  have hdp : ‖fderiv ℝ P x (e i)‖ ≤ C := by
    have h := (fderiv ℝ P x).le_opNorm (e i)
    simpa only [show ‖e i‖ = 1 by simp [e],mul_one] using
      h.trans (mul_le_mul_of_nonneg_right hdP (norm_nonneg (e i)))
  have h1 := (fderiv ℝ P x (e i)).le_opNorm (value f x) |>.trans
    (mul_le_mul_of_nonneg_right hdp (norm_nonneg _))
  have h2 := (P x).le_opNorm (derivative f i x) |>.trans
    (mul_le_mul_of_nonneg_right hbP (norm_nonneg _))
  have hs1 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hs2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hg : ‖derivative f i x‖^2 ≤ gradient f x := by
    unfold gradient
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖derivative f j x‖) (Finset.mem_univ i)
  have hg' := mul_le_mul_of_nonneg_left hg (sq_nonneg C)
  rw [hder]
  have hn := norm_add_sq_bound (fderiv ℝ P x (e i) (value f x)) (P x (derivative f i x))
  simp only [mul_pow] at hs1 hs2
  nlinarith

theorem frame_h1_bound {U K : Set V} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (P : V → W →L[ℝ] F) (hP : ContDiffOn ℝ ∞ P U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Field) (u : 𝓢(V,F)), tsupport u ⊆ K →
      (⇑u = fun x => P x (value f x)) →
      ((∫ x, ‖u x‖^2) ≤ C*((∫ x, gradient f x)+(∫ x, ‖value f x‖^2))) ∧
      (∀ i : Fin 4, (∫ x, ‖(∂_{e i} u) x‖^2) ≤
        C*((∫ x, gradient f x)+(∫ x, ‖value f x‖^2))) := by
  have hdP : ContinuousOn (fderiv ℝ P) K := fun x hx =>
    ((hP.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨B₁,h₁⟩ := hK.exists_bound_of_continuousOn (hP.continuousOn.mono hKU)
  obtain ⟨B₂,h₂⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ P) hdP
  let B := max 1 (max B₁ B₂)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb₁ : B₁ ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hb₂ : B₂ ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨2*B^2,by positivity,?_⟩
  intro f u hsu he
  have hint : Integrable (fun x => 2*B^2*(gradient f x+‖value f x‖^2)) :=
    ((gradient_integrable f).add (value_integrable f)).const_mul _
  have hformula : (∫ x, 2*B^2*(gradient f x+‖value f x‖^2)) =
      2*B^2*((∫ x, gradient f x)+(∫ x, ‖value f x‖^2)) := by
    rw [integral_const_mul,integral_add (gradient_integrable f) (value_integrable f)]
  constructor
  · refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hint
      (Filter.Eventually.of_forall (fun x => ?_))).trans_eq hformula
    by_cases hx : x ∈ K
    · have hb := lowerError_bound P f x ((h₁ x hx).trans hb₁)
      rw [he]
      have hn := mul_nonneg (sq_nonneg B) (gradient_nonneg f x)
      have hn' := mul_nonneg (sq_nonneg B) (sq_nonneg ‖value f x‖)
      nlinarith
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsu h)),norm_zero,zero_pow (by decide : 2≠0)]
      exact mul_nonneg (by positivity) (add_nonneg (gradient_nonneg f x) (sq_nonneg _))
  · intro i
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hint
      (Filter.Eventually.of_forall (fun x => ?_))).trans_eq hformula
    by_cases hx : x ∈ K
    · rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      exact frame_deriv_bound f he
        ((hP.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))
        ((h₁ x hx).trans hb₁) ((h₂ x hx).trans hb₂) i
    · rw [image_eq_zero_of_notMem_tsupport
        (fun h => hx (hsu (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))),norm_zero,zero_pow (by decide : 2≠0)]
      exact mul_nonneg (by positivity) (add_nonneg (gradient_nonneg f x) (sq_nonneg _))
end TamingCompatibility.HodgeMatrixEnergy

end
end

section
noncomputable section
namespace TamingCompatibility.HodgeChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume EuclideanEnergy
open Set MeasureTheory HodgeFrame GeometricChart
open scoped Manifold ContDiff SchwartzMap LineDeriv
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

include hs hD in
omit [T2Space X] in

theorem localized_jet_bound (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : smoothForms X 2,
      ∀ j : DerivativeIndex, ‖localizeH1 A 2 a j p‖^2 ≤
        C * ((∫ x, GeometricAdjoint.pairing J α ht a.val a.val x ∂geometricVolume A J α) +
          (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a.val)
            (codifferential J α ht a.val) x +
            GeometricAdjoint.pairing J α ht (codifferential J α ht (starTwo J α ht a.val))
              (codifferential J α ht (starTwo J α ht a.val)) x ∂geometricVolume A J α)) := by
  let P : Space → HodgeNormalSymbol.W →L[ℝ] CoordinateFiber 2 := fun x =>
    formCoordinates 2 ∘L reconstruct (coordinateMetric J α ht p.val x) (fun i => (D p).frame i x)
  have hg := (coordinateMetric_smooth J α hs ht p.val).mono (D p).domain_subset
  have hP : ContDiffOn ℝ ∞ P (D p).domain := by
    apply contDiffOn_clm_apply.mpr
    intro u
    change ContDiffOn ℝ ∞ (fun x => formCoordinates 2 (∑ j, u j •
      basisForm (coordinateMetric J α ht p.val x) (fun i => (D p).frame i x) j)) (D p).domain
    apply (formCoordinates 2).contDiff.comp_contDiffOn
    exact ContDiffOn.sum (fun j _ => (basisForm_smooth hg (D p).frame_smooth j).const_smul (u j))
  obtain ⟨C,hC,hframe⟩ := HodgeMatrixEnergy.frame_h1_bound (D p).domain_open (coordinateSupport_compact A p)
    (coordinateSupport_domain A J α ht (fun q => (D q).toData) hD p) P hP
  obtain ⟨K,hK,hgard⟩ := scalar_garding A J α hs ht D hD p
  refine ⟨16*(C*K),mul_pos (by norm_num) (mul_pos hC hK),?_⟩
  intro a j
  let f := scalarSchwartz A J α ht (fun q => (D q).toData) hD p a.val a.property
  have he : (⇑(localizedLinear A 2 p a)) = fun x => P x (HodgeMatrixEnergy.value f x) := by
    funext x
    change formCoordinates 2 (localizedFunction A p a.val x) =
      formCoordinates 2 (reconstruct _ _ _)
    rw [scalar_expansion A J α ht (fun q => (D q).toData) hD p a.val x,reconstruct_apply]
    rfl
  have hb := hframe f (localizedLinear A 2 p a) (localizedLinear_support A p a) he
  have hga := hgard a.val a.property
  rw [localizeH1_apply,schwartz_l2_norm_sq]
  have hbound : C*((∫ x, HodgeMatrixEnergy.gradient f x)+(∫ x, ‖HodgeMatrixEnergy.value f x‖^2)) ≤
      C*K*((∫ x, GeometricAdjoint.pairing J α ht a.val a.val x ∂geometricVolume A J α) +
          (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a.val)
            (codifferential J α ht a.val) x +
            GeometricAdjoint.pairing J α ht (codifferential J α ht (starTwo J α ht a.val))
              (codifferential J α ht (starTwo J α ht a.val)) x ∂geometricVolume A J α)) :=
    (mul_le_mul_of_nonneg_left hga hC.le).trans_eq (mul_assoc _ _ _).symm
  have hnonneg : 0 ≤ C*((∫ x, HodgeMatrixEnergy.gradient f x)+(∫ x, ‖HodgeMatrixEnergy.value f x‖^2)) :=
    (integral_nonneg fun x => sq_nonneg ‖localizedLinear A 2 p a x‖).trans hb.1
  have htarget := mul_le_mul_of_nonneg_left hbound (show (0:ℝ) ≤ 16 by norm_num)
  cases j with
  | none => exact (hb.1.trans (by nlinarith : _ ≤ 16*(C*((∫ x, HodgeMatrixEnergy.gradient f x)+
        (∫ x, ‖HodgeMatrixEnergy.value f x‖^2))))).trans (by simpa only [mul_assoc] using htarget)
  | some i =>
    change (∫ x, ‖(∂_{stdOrthonormalBasis ℝ Space i} (localizedLinear A 2 p a)) x‖^2) ≤ _
    have hv : ‖stdOrthonormalBasis ℝ Space i‖ ≤ 1 := le_of_eq
      ((stdOrthonormalBasis ℝ Space).orthonormal.norm_eq_one i)
    have hd := direction_integral_bound (localizedLinear A 2 p a)
      (stdOrthonormalBasis ℝ Space i) hv
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hb.2 k)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Nat.cast_ofNat] at hsum
    exact (hd.trans (by nlinarith : _ ≤ 16*(C*((∫ x, HodgeMatrixEnergy.gradient f x)+
        (∫ x, ‖HodgeMatrixEnergy.value f x‖^2))))).trans (by simpa only [mul_assoc] using htarget)
end TamingCompatibility.HodgeChart

end
end

end
end

end OAI
