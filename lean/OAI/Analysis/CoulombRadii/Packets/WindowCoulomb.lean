import Mathlib
import OAI.Analysis.CoulombRadii.SpectralTheory.SectorFormBottom

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma window_coulomb_eq (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖)) {R : ℝ} (hR : 0 < R)
    (hs : ∀ y, R < ‖y‖ → g y = 0) {x : Space} (hx : R ≤ ‖x‖) :
    (∫ y, coulombKernel (x-y)*g y^2) = coulombKernel x := by
  have hx0 : x ≠ 0 := by intro he; subst x; simp at hx; linarith
  simpa only [hg,mul_one] using radial_coulomb_integral_eq (schwartz_square_integrable g)
    (g.continuous.measurable.pow_const 2) (fun x => sq_nonneg (g x)) (schwartz_square_le g)
    (fun y => congrArg (fun t : ℝ => t^2) (hrad y)) hR.le (fun y hy => by simp [hs y hy]) hx0 hx

lemma window_coulomb_bound (g : 𝓢(Space,ℝ)) (x : Space) :
    (∫ y, coulombKernel (x-y)*g y^2) ≤
      2*Real.pi*(SchwartzMap.seminorm ℝ 0 0 g)^2 + ∫ y : Space, g y^2 := by
  simpa only [one_pow,mul_one,one_div,one_mul,inv_one] using
    coulomb_convolution_bound (schwartz_square_integrable g) (g.continuous.measurable.pow_const 2)
      (fun y => sq_nonneg (g y)) (schwartz_square_le g) (by norm_num : (0:ℝ)<1) x

lemma packetDensity_coulomb_prod_integrable (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ) (a : Space) :
    Integrable (fun p : Space × Space => coulombKernel (a-p.1)*g (p.1-p.2)^2*ρ p.2)
      (volume.prod volume) := by
  let C := 2*Real.pi*(SchwartzMap.seminorm ℝ 0 0 g)^2+∫ y : Space, g y^2
  have hF : Measurable (fun p : Space × Space => coulombKernel (a-p.1)*g (p.1-p.2)^2*ρ p.2) :=
    ((coulombKernel_measurable.comp (measurable_const.sub measurable_fst)).mul
      ((g.continuous.measurable.comp (measurable_fst.sub measurable_snd)).pow_const 2)).mul
        (hm.comp measurable_snd)
  have hI (y : Space) : Integrable (fun x => coulombKernel (a-x)*g (x-y)^2) :=
    coulomb_convolution_integrable (window_shift_integrable g y)
      (((g.continuous.measurable.comp (measurable_id.sub measurable_const)).pow_const 2))
      (fun x => sq_nonneg _) (fun x => schwartz_square_le g (x-y)) (by norm_num : (0:ℝ)<1) a
  apply (integrable_prod_iff' hF.aestronglyMeasurable).2
  constructor
  · exact Eventually.of_forall fun y => (hI y).mul_const (ρ y)
  · apply (hi.const_mul C).mono' hF.aestronglyMeasurable.prod_swap.norm.integral_prod_right'
    exact Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      have he : (∫ x, ‖coulombKernel (a-x)*g (x-y)^2*ρ y‖) =
          (∫ x, coulombKernel (a-x)*g (x-y)^2)*ρ y := by
        rw [←integral_mul_const]
        exact integral_congr_ae (Eventually.of_forall fun _ =>
          Real.norm_of_nonneg (mul_nonneg (mul_nonneg (coulombKernel_nonneg _) (sq_nonneg _)) (hp y)))
      change (∫ x, ‖coulombKernel (a-x)*g (x-y)^2*ρ y‖) ≤ C*ρ y
      rw [he,window_shift_coulomb_integral]
      exact mul_le_mul_of_nonneg_right (window_coulomb_bound g _) (hp y)

lemma packetDensity_coulomb_integral (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ) (a : Space) :
    (∫ x, coulombKernel (a-x)*packetDensity g ρ x) =
      ∫ y, (∫ x, coulombKernel ((a-y)-x)*g x^2)*ρ y := by
  have hI := packetDensity_coulomb_prod_integrable g ρ hp hm hi a
  calc
    _ = ∫ x, ∫ y, coulombKernel (a-x)*g (x-y)^2*ρ y := by
      unfold packetDensity
      simp_rw [←integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => integral_congr_ae (Eventually.of_forall fun y => by ring))
    _ = ∫ y, ∫ x, coulombKernel (a-x)*g (x-y)^2*ρ y := integral_integral_swap hI
    _ = _ := by simp_rw [integral_mul_const, window_shift_coulomb_integral]

lemma packetDensity_coulomb_eq (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖)) {R : ℝ} (hR : 0 < R)
    (hs : ∀ y, R < ‖y‖ → g y = 0) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ) (a : Space)
    (hsep : ∀ y, ρ y ≠ 0 → R ≤ ‖a-y‖) :
    (∫ x, coulombKernel (a-x)*packetDensity g ρ x) = ∫ y, coulombKernel (a-y)*ρ y := by
  rw [packetDensity_coulomb_integral g ρ hp hm hi a]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    by_cases hy : ρ y = 0
    · simp [hy]
    · change (∫ x, coulombKernel (a-y-x)*g x^2)*ρ y = coulombKernel (a-y)*ρ y
      rw [window_coulomb_eq g hg hrad hR hs (hsep y hy)]

lemma separated_density_coulomb_integrable {ρ : Space → ℝ} (hp : ∀ y, 0 ≤ ρ y)
    (hm : Measurable ρ) (hi : Integrable ρ) {R : ℝ} (hR : 0 < R) (a : Space)
    (hsep : ∀ y, ρ y ≠ 0 → R ≤ ‖a-y‖) :
    Integrable (fun y => coulombKernel (a-y)*ρ y) := by
  apply (hi.const_mul R⁻¹).mono'
  · exact ((coulombKernel_measurable.comp (measurable_const.sub measurable_id)).mul hm).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hp y))]
      by_cases hy : ρ y = 0
      · simp [hy]
      · exact mul_le_mul_of_nonneg_right (by simpa [coulombKernel,one_div] using (one_div_le_one_div_of_le hR (hsep y hy))) (hp y)

lemma coreCoulombPotential_packet_eq {m : ℕ} (u : H1Vector m)
    {A : Set Space} (hu : SpatiallySupported u A)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖)) {R : ℝ} (hR : 0 < R)
    (hs : ∀ y, R < ‖y‖ → g y = 0) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ)
    (hsep : ∀ a ∈ A, ∀ y, ρ y ≠ 0 → R ≤ ‖a-y‖) :
    (∫ x, coreCoulombPotential u x*packetDensity g ρ x) = ∫ x, coreCoulombPotential u x*ρ x := by
  rw [coreCoulombPotential_fubini u _ (packetDensity_integrable g ρ hp hm hi),
    coreCoulombPotential_fubini u ρ hi]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [hu s] with x hx
  by_cases he : u.value s x = 0
  · simp [he]
  · have ha : position x i ∈ A := (by_contra (fun hn => he (hx hn)) : x ∈ allPositions A) i
    change (∫ z, coulombKernel (position x i-z)*packetDensity g ρ z)*‖u.value s x‖^2 = _
    rw [packetDensity_coulomb_eq g hg hrad hR hs ρ hp hm hi (position x i) (hsep _ ha)]

lemma separated_density_nuclear_integrable {M : ℕ} (S : Nuclei M) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ)
    {R : ℝ} (hR : 0 < R)
    (hsep : ∀ j y, ρ y ≠ 0 → R ≤ ‖S.position j-y‖) :
    Integrable (fun x => attraction S x*ρ x) := by
  simp only [attraction,Finset.sum_mul]
  apply integrable_finsetSum
  intro j _
  have h := (separated_density_coulomb_integrable hp hm hi hR (S.position j) (hsep j)).const_mul (S.charge j)
  apply h.congr
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [coulombKernel_sub_comm x]
    ring

lemma attraction_packet_eq {M : ℕ} (S : Nuclei M)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖)) {R : ℝ} (hR : 0 < R)
    (hs : ∀ y, R < ‖y‖ → g y = 0) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ)
    (hsep : ∀ j y, ρ y ≠ 0 → R ≤ ‖S.position j-y‖) :
    (∫ x, attraction S x*packetDensity g ρ x) = ∫ x, attraction S x*ρ x := by
  have hn (j : Fin M) : Integrable (fun x => S.charge j*(coulombKernel (S.position j-x)*ρ x)) :=
    (separated_density_coulomb_integrable hp hm hi hR (S.position j) (hsep j)).const_mul _
  have hsmooth (j : Fin M) : Integrable (fun x => S.charge j*(coulombKernel (S.position j-x)*packetDensity g ρ x)) := by
    have h := (packetDensity_coulomb_prod_integrable g ρ hp hm hi (S.position j)).integral_prod_left
    apply (h.const_mul (S.charge j)).congr
    exact Eventually.of_forall fun x => by
      simp only [packetDensity,←integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun y => by ring)
  simp only [attraction,Finset.sum_mul]
  simp_rw [coulombKernel_sub_comm _ (S.position _),mul_assoc]
  rw [integral_finsetSum _ (fun j _ => hsmooth j),integral_finsetSum _ (fun j _ => hn j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,integral_const_mul,
    packetDensity_coulomb_eq g hg hrad hR hs ρ hp hm hi _ (hsep j)]

lemma coreScreenedField_packet_eq {M m : ℕ} (S : Nuclei M) (u : H1Vector m)
    {A : Set Space} (hu : SpatiallySupported u A)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖)) {R : ℝ} (hR : 0 < R)
    (hs : ∀ y, R < ‖y‖ → g y = 0) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ)
    (hsep : ∀ a ∈ A, ∀ y, ρ y ≠ 0 → R ≤ ‖a-y‖)
    (hnuc : ∀ j y, ρ y ≠ 0 → R ≤ ‖S.position j-y‖) :
    (∫ x, coreScreenedField S u x*packetDensity g ρ x) = ∫ x, coreScreenedField S u x*ρ x := by
  rw [coreScreenedField_packet_integral S u g ρ hp hm hi,
    coreCoulombPotential_packet_eq u hu g hg hrad hR hs ρ hp hm hi hsep,
    attraction_packet_eq S g hg hrad hR hs ρ hp hm hi hnuc]
  simp only [coreScreenedField,sub_mul]
  exact (integral_sub (separated_density_nuclear_integrable S ρ hp hm hi hR hnuc)
    (coreCoulombPotential_mul_integrable u ρ hi)).symm

theorem source_free_trial_in_hole {M m : ℕ} (S : Nuclei M) (u : H1Vector m)
    (hu : Antisymmetric u) (hmu : mass u = 1)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hgc : HasCompactSupport (g : Space → ℝ))
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖))
    {R : ℝ} (hR : 0 < R) (hgs : ∀ y, R < ‖y‖ → g y = 0)
    (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ)
    (ht : Integrable (fun y => ρ y^(5/3:ℝ)))
    (K A : Set Space) (hK : IsCompact K) (hA : IsClosed A)
    (hs : ∀ y, y ∉ K → ρ y = 0) (hsu : SpatiallySupported u A)
    (hsep : Disjoint A (K+tsupport (g : Space → ℝ)))
    (hcore : ∀ a ∈ A, ∀ y, ρ y ≠ 0 → R ≤ ‖a-y‖)
    (hnuc : ∀ j y, ρ y ≠ 0 → R ≤ ‖S.position j-y‖) :
    unrestrictedFormBottom S ≤ ((form S u +
        thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
        (1/2:ℝ)*(∫ y : Space, ρ y)*(∑ b : Fin 3, ∫ x : Space,
          (fderiv ℝ g x (EuclideanSpace.single b 1))^2) -
        (∫ x, coreScreenedField S u x*ρ x) +
        (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2)) : ℝ) : EReal) := by
  have H := trial_in_hole S u hu hmu g hg hgc hrad ρ hp hm ht K A hK hA hs hsu hsep
  rw [coreScreenedField_packet_eq S u hsu g hg hrad hR hgs ρ hp hm
    (compact_density_integrable ρ hp hm ht K hK hs) hcore hnuc] at H
  exact H

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal

end

end OAI
