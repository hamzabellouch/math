import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ChartMetricBounds
import OAI.Geometry.TamingCompatibility.Charts.ChartScalarBound

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldLocalization ManifoldHodge ManifoldVolume LocalMatrixOperator EuclideanEnergy
open Set MeasureTheory
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include hs in
omit [T2Space X] in

theorem scalar_garding (p : A.centers) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : TwoForm X, ∀ ha : IsSmooth a, antiInvariantPart J a = a →
      (∫ z, gradientEnergy (scalarSchwartz A J α ht D hD p a ha 2)
        (scalarSchwartz A J α ht D hD p a ha 3) z) +
      (∫ z, (scalar A J α ht D p a 2 z)^2 + (scalar A J α ht D p a 3 z)^2) ≤
      C * ((∫ x, GeometricAdjoint.pairing J α ht a a x ∂geometricVolume A J α) +
        (∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht a)
          (codifferential J α ht a) x ∂geometricVolume A J α)) := by
  obtain ⟨Cδ,hCδ,hδ⟩ := integral_localDelta_bound A J α ht hs D hD p
  obtain ⟨Cs,hCs,hS⟩ := integral_scalar_bound A J α hs ht D hD p
  obtain ⟨Cf,hCf,hf⟩ := GeometricHilbert.cutoff_energy_bound A J α hs ht (A.partition p).contMDiff
  let K := (D p).energyConstant*Cδ + ((D p).lowerConstant+1)*Cs
  have hK : 0 < K := add_pos (mul_pos (D p).energy_pos hCδ)
    (mul_pos (by linarith [(D p).lower_pos]) hCs)
  refine ⟨K*Cf,mul_pos hK hCf,?_⟩
  intro a ha hanti
  let s := scalarSchwartz A J α ht D hD p a ha 2
  let t := scalarSchwartz A J α ht D hD p a ha 3
  have hg := (D p).garding s t (scalarSchwartz_support A J α ht D hD p a ha 2)
    (scalarSchwartz_support A J α ht D hD p a ha 3)
  have he : (fun y => s y • AntiInvariantFrame.realPart (coordinateMetric J α ht p.val y) (fun i => (D p).frame i y) +
      t y • AntiInvariantFrame.imagPart (coordinateMetric J α ht p.val y) (fun i => (D p).frame i y)) =
      localizedFunction A p a := by
    funext z
    exact (scalar_expansion A J α ht D hD p hanti z).symm
  rw [he] at hg
  change (∫ z, gradientEnergy s t z) ≤ (D p).energyConstant *
    (∫ z, ‖oneVector (localDelta A J α ht p a z)‖^2) + (D p).lowerConstant *
      (∫ z, (scalar A J α ht D p a 2 z)^2 + (scalar A J α ht D p a 3 z)^2) at hg
  let L := ∫ x, GeometricAdjoint.pairing J α ht (cutoffForm A p a) (cutoffForm A p a) x ∂geometricVolume A J α
  let Q := ∫ x, GeometricAdjoint.pairing J α ht (codifferential J α ht (cutoffForm A p a))
      (codifferential J α ht (cutoffForm A p a)) x ∂geometricVolume A J α
  have hL : 0 ≤ L := integral_nonneg (fun x => MetricForms.pairing_self_nonneg _ _)
  have hQ : 0 ≤ Q := integral_nonneg (fun x => MetricForms.pairing_self_nonneg _ _)
  have hδa := hδ a ha hanti
  have hSa := hS a ha hanti
  change _ ≤ Cδ*Q at hδa
  change _ ≤ Cs*L at hSa
  have hfa := hf a ha hanti
  change L+Q ≤ _ at hfa
  have hpre : (∫ z, gradientEnergy s t z) +
      (∫ z, (scalar A J α ht D p a 2 z)^2 + (scalar A J α ht D p a 3 z)^2) ≤ K*(L+Q) := by
    have hd := mul_le_mul_of_nonneg_left hδa (D p).energy_pos.le
    have hs' := mul_le_mul_of_nonneg_left hSa (by linarith [(D p).lower_pos] : 0 ≤ (D p).lowerConstant+1)
    have hplus₁ := mul_nonneg (mul_pos (D p).energy_pos hCδ).le hL
    have hplus₂ := mul_nonneg (mul_pos (by linarith [(D p).lower_pos] : 0 < (D p).lowerConstant+1) hCs).le hQ
    dsimp only [K]
    nlinarith
  exact hpre.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfa hK.le)
end TamingCompatibility.GeometricChart

end
end

section
noncomputable section
namespace TamingCompatibility.EuclideanEnergy
open MeasureTheory Set
open scoped SchwartzMap LineDeriv ContDiff
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
lemma norm_add_sq_bound (u v : F) : ‖u+v‖^2 ≤ 2*(‖u‖^2+‖v‖^2) := by
  have h := norm_add_le u v
  have hs := sq_nonneg (‖u‖-‖v‖)
  nlinarith [norm_nonneg (u+v),norm_nonneg u,norm_nonneg v]

lemma norm_smul_sq_bound (s : ℝ) (u : F) {C : ℝ} (_hC : 0 ≤ C) (hu : ‖u‖ ≤ C) :
    ‖s • u‖^2 ≤ C^2*s^2 := by
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg u) hu 2) (sq_nonneg s)).trans_eq (mul_comm _ _)

lemma two_frame_norm_bound {P Q u : V → F} {C : ℝ} (hC : 0 ≤ C)
    (s t : S) (he : u = fun x => s x • P x + t x • Q x)
    {x : V} (hP : ‖P x‖ ≤ C) (hQ : ‖Q x‖ ≤ C) :
    ‖u x‖^2 ≤ 2*C^2*((s x)^2+(t x)^2) := by
  rw [he]
  have h := norm_add_sq_bound (s x • P x) (t x • Q x)
  have h₁ := norm_smul_sq_bound (s x) (P x) hC hP
  have h₂ := norm_smul_sq_bound (t x) (Q x) hC hQ
  nlinarith

lemma two_frame_deriv_bound {P Q u : V → F} {C : ℝ} (hC : 0 ≤ C)
    (s t : S) (he : u = fun x => s x • P x + t x • Q x)
    {x : V} (hP : DifferentiableAt ℝ P x) (hQ : DifferentiableAt ℝ Q x)
    (hbP : ‖P x‖ ≤ C) (hbQ : ‖Q x‖ ≤ C)
    (hdP : ‖fderiv ℝ P x‖ ≤ C) (hdQ : ‖fderiv ℝ Q x‖ ≤ C) (i : Fin 4) :
    ‖fderiv ℝ u x (e i)‖^2 ≤ 8*C^2*(gradientEnergy s t x + (s x)^2+(t x)^2) := by
  have hs := (s.smooth 1).differentiable (by norm_num) x
  have ht := (t.smooth 1).differentiable (by norm_num) x
  have hder : fderiv ℝ u x (e i) =
      coordinateDeriv i s x • P x + s x • fderiv ℝ P x (e i) +
        (coordinateDeriv i t x • Q x + t x • fderiv ℝ Q x (e i)) := by
    rw [he]
    change (fderiv ℝ (⇑s • P + ⇑t • Q) x) (e i) = _
    rw [fderiv_add (hs.smul hP) (ht.smul hQ),fderiv_smul hs hP,fderiv_smul ht hQ]
    simp only [add_apply,ContinuousLinearMap.smulRight_apply,
      smul_apply,coordinateDeriv,SchwartzMap.lineDerivOp_apply_eq_fderiv]
    abel
  have heN : ‖e i‖ = 1 := by simp [e]
  have hdp : ‖fderiv ℝ P x (e i)‖ ≤ C := by
    simpa only [heN,mul_one] using (fderiv ℝ P x).le_opNorm (e i) |>.trans
      (mul_le_mul_of_nonneg_right hdP (norm_nonneg (e i)))
  have hdq : ‖fderiv ℝ Q x (e i)‖ ≤ C := by
    simpa only [heN,mul_one] using (fderiv ℝ Q x).le_opNorm (e i) |>.trans
      (mul_le_mul_of_nonneg_right hdQ (norm_nonneg (e i)))
  have hp := norm_add_sq_bound (coordinateDeriv i s x • P x) (s x • fderiv ℝ P x (e i))
  have hq := norm_add_sq_bound (coordinateDeriv i t x • Q x) (t x • fderiv ℝ Q x (e i))
  have hp₁ := norm_smul_sq_bound (coordinateDeriv i s x) (P x) hC hbP
  have hp₂ := norm_smul_sq_bound (s x) (fderiv ℝ P x (e i)) hC hdp
  have hq₁ := norm_smul_sq_bound (coordinateDeriv i t x) (Q x) hC hbQ
  have hq₂ := norm_smul_sq_bound (t x) (fderiv ℝ Q x (e i)) hC hdq
  have hg : (coordinateDeriv i s x)^2+(coordinateDeriv i t x)^2 ≤ gradientEnergy s t x := by
    unfold gradientEnergy
    exact Finset.single_le_sum (fun j _ => add_nonneg (sq_nonneg (coordinateDeriv j s x)) (sq_nonneg (coordinateDeriv j t x))) (Finset.mem_univ i)
  have hg' := mul_le_mul_of_nonneg_left hg (sq_nonneg C)
  have hn := norm_add_sq_bound (coordinateDeriv i s x • P x + s x • fderiv ℝ P x (e i))
    (coordinateDeriv i t x • Q x + t x • fderiv ℝ Q x (e i))
  rw [hder]
  have hg0 : 0 ≤ gradientEnergy s t x := Finset.sum_nonneg fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hc₁ := mul_nonneg (sq_nonneg C) (sq_nonneg (s x))
  have hc₂ := mul_nonneg (sq_nonneg C) (sq_nonneg (t x))
  have hc₃ := mul_nonneg (sq_nonneg C) hg0
  nlinarith
end TamingCompatibility.EuclideanEnergy

namespace TamingCompatibility.EuclideanEnergy
open MeasureTheory Set
open scoped SchwartzMap LineDeriv ContDiff
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem frame_h1_bound {U K : Set V} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (P Q : V → F) (hP : ContDiffOn ℝ ∞ P U) (hQ : ContDiffOn ℝ ∞ Q U) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s t : S) (u : 𝓢(V,F)), tsupport u ⊆ K →
      (⇑u = fun x => s x • P x + t x • Q x) →
      ((∫ x, ‖u x‖^2) ≤ C*((∫ x, gradientEnergy s t x)+(∫ x, (s x)^2+(t x)^2))) ∧
      (∀ i : Fin 4, (∫ x, ‖(∂_{e i} u) x‖^2) ≤
        C*((∫ x, gradientEnergy s t x)+(∫ x, (s x)^2+(t x)^2))) := by
  have hdP : ContinuousOn (fderiv ℝ P) K := fun x hx =>
    ((hP.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt_fderiv (by simp)).continuousWithinAt
  have hdQ : ContinuousOn (fderiv ℝ Q) K := fun x hx =>
    ((hQ.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨B₁,h₁⟩ := hK.exists_bound_of_continuousOn (hP.continuousOn.mono hKU)
  obtain ⟨B₂,h₂⟩ := hK.exists_bound_of_continuousOn (hQ.continuousOn.mono hKU)
  obtain ⟨B₃,h₃⟩ := hK.exists_bound_of_continuousOn hdP
  obtain ⟨B₄,h₄⟩ := hK.exists_bound_of_continuousOn hdQ
  let B := max 1 (max B₁ (max B₂ (max B₃ B₄)))
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb₁ : B₁ ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hb₂ : B₂ ≤ B := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hb₃ : B₃ ≤ B := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hb₄ : B₄ ≤ B := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨8*B^2,by positivity,?_⟩
  intro s t u hsu he
  have hg (x : V) : 0 ≤ gradientEnergy s t x :=
    Finset.sum_nonneg fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hint : Integrable (fun x => 8*B^2*(gradientEnergy s t x+(s x)^2+(t x)^2)) :=
    (((gradientEnergy_integrable s t).add (schwartz_sq_integrable s)).add (schwartz_sq_integrable t)).const_mul _
  have hformula : (∫ x, 8*B^2*(gradientEnergy s t x+(s x)^2+(t x)^2)) =
      8*B^2*((∫ x, gradientEnergy s t x)+(∫ x, (s x)^2+(t x)^2)) := by
    rw [integral_const_mul]
    congr 1
    calc (∫ x, gradientEnergy s t x+(s x)^2+(t x)^2) =
        ∫ x, gradientEnergy s t x+((s x)^2+(t x)^2) := by
          congr 1; funext x; ring
      _ = _ := integral_add (gradientEnergy_integrable s t)
        ((schwartz_sq_integrable s).add (schwartz_sq_integrable t))
  constructor
  · refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hint
      (Filter.Eventually.of_forall (fun x => ?_))).trans_eq hformula
    by_cases hx : x ∈ K
    · have h := two_frame_norm_bound hB.le s t he ((h₁ x hx).trans hb₁) ((h₂ x hx).trans hb₂)
      have hgn := mul_nonneg (sq_nonneg B) (hg x)
      have hsn := mul_nonneg (sq_nonneg B) (sq_nonneg (s x))
      have htn := mul_nonneg (sq_nonneg B) (sq_nonneg (t x))
      nlinarith
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsu h)),norm_zero,zero_pow (by decide : 2≠0)]
      exact mul_nonneg (by positivity) (add_nonneg (add_nonneg (hg x) (sq_nonneg _)) (sq_nonneg _))
  · intro i
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _)) hint
      (Filter.Eventually.of_forall (fun x => ?_))).trans_eq hformula
    by_cases hx : x ∈ K
    · rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      exact two_frame_deriv_bound hB.le s t he
        ((hP.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))
        ((hQ.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))
        ((h₁ x hx).trans hb₁) ((h₂ x hx).trans hb₂) ((h₃ x hx).trans hb₃) ((h₄ x hx).trans hb₄) i
    · rw [image_eq_zero_of_notMem_tsupport
        (fun h => hx (hsu (SchwartzMap.tsupport_lineDerivOp_subset _ _ h))),norm_zero,zero_pow (by decide : 2≠0)]
      exact mul_nonneg (by positivity) (add_nonneg (add_nonneg (hg x) (sq_nonneg _)) (sq_nonneg _))
end TamingCompatibility.EuclideanEnergy

end
end

end
end
end

end OAI
