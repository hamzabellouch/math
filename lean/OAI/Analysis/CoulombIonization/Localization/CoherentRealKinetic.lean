import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.CoherentLimitInsertion
import OAI.Analysis.CoulombIonization.Localization.FermiDensity

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

def packetDirichlet (g : Space → ℝ) : ℝ :=
  ∑ a : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single a 1))^2

lemma packetDirichlet_nonneg (g : Space → ℝ) : 0 ≤ packetDirichlet g :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

lemma real_derivative_sq_integrable {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (v : Space) :
    Integrable (fun x : Space => (fderiv ℝ g x v)^2) := by
  have hc : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  exact (hc.memLp_of_hasCompactSupport (hcg.fderiv_apply ℝ v) (p := 2)).integrable_sq

lemma real_coherentPacket_kinetic {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (hgn : ∫ x : Space, (g x)^2 = 1) (z p : Space) :
    (∑ a : Fin 3, ∫ x : Space, ‖fderiv ℝ (coherentPacket (fun y => (g y : ℂ)) z p) x
      (EuclideanSpace.single a 1)‖^2) = packetDirichlet g + ‖p‖^2 := by
  have hg2 : Integrable (fun x : Space => (g x)^2) :=
    (hg.continuous.memLp_of_hasCompactSupport hcg (p := 2)).integrable_sq
  have hs (a : Fin 3) : (∫ x : Space, ‖fderiv ℝ (coherentPacket (fun y => (g y : ℂ)) z p) x
      (EuclideanSpace.single a 1)‖^2) =
      (∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single a 1))^2) + (inner ℝ p (EuclideanSpace.single a 1))^2 := by
    simp_rw [real_coherentPacket_derivative_sq (hg.differentiable (by simp))]
    rw [integral_add ((real_derivative_sq_integrable hg hcg _).comp_sub_right z)
      ((hg2.comp_sub_right z).mul_const _),integral_mul_const,
      integral_sub_right_eq_self (fun x : Space => (fderiv ℝ g x (EuclideanSpace.single a 1))^2) z,
      integral_sub_right_eq_self (fun x : Space => (g x)^2) z,hgn,one_mul]
  simp_rw [hs]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← sum_coordinate_sq]
  apply Finset.sum_congr rfl
  intro a _
  simp [EuclideanSpace.inner_single_right]

lemma coherentSpinKinetic_fermi {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) :
    coherentSpinKinetic (fun x => (g x : ℂ)) (fermiMeasure ρ) =
      tfKinetic*(∫ z, (ρ z)^(5/3 : ℝ)) + (packetDirichlet g / 2)*(∫ z, ρ z) := by
  let := fermiMeasure_finite hn hJ hs hb
  have hgc : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hcgc : HasCompactSupport (fun x => (g x : ℂ)) := hcg.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  let K : Set (Space × Space) := J ×ˢ closedBall 0 ((3*Real.pi^2*B)^(1/3 : ℝ))
  have hK : IsCompact K := hJ.prod (isCompact_closedBall _ _)
  have hμ : ∀ᵐ q ∂fermiMeasure ρ, q ∈ K := fermiMeasure_mem hm hn hs hb
  have hi (a : Fin 3) : Integrable (fun q : Space × Space => ∫ x : Space,
      ‖fderiv ℝ (coherentPacket (fun x => (g x : ℂ)) q.1 q.2) x (EuclideanSpace.single a 1)‖^2)
      (fermiMeasure ρ) := (coherentPacket_derivative_sq_integrable hgc hcgc (fermiMeasure ρ)
        hK hμ (EuclideanSpace.single a 1)).integral_prod_left
  unfold coherentSpinKinetic
  rw [← integral_finsetSum _ (fun a _ => hi a)]
  simp_rw [real_coherentPacket_kinetic hg hcg hgn]
  rw [integral_add (integrable_const _) (fermiMeasure_integrable_continuous hn hJ hs hb (by fun_prop)),
    integral_const,smul_eq_mul,mul_add,fermiMeasure_kinetic hm hn hJ hs hb]
  have hmass := fermiMeasure_mass hm hn hJ hs hb
  rw [← hmass]
  ring

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma potential_const_mul (c : ℝ) (f : Space → ℝ) (a : Space) :
    CoulombAnalysis.tfPotential (fun x => c*f x) a = c*CoulombAnalysis.tfPotential f a := by
  simp only [CoulombAnalysis.tfPotential,mul_div_assoc,integral_const_mul]

lemma coreDensityInteraction_const_mul {N : ℕ} (ψ : FormVector N) (c : ℝ) (f : Space → ℝ) :
    coreDensityInteraction ψ (fun x => c*f x) = c*coreDensityInteraction ψ f := by
  simp only [coreDensityInteraction,potential_const_mul,Finset.mul_sum]
  congr 1
  funext s
  congr 1
  funext i
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

lemma coulomb_double_const_mul (c : ℝ) (f : Space → ℝ) :
    (∫ r : Space × Space, (c*f r.1)*(c*f r.2)/‖r.1-r.2‖) =
      c^2*(∫ r : Space × Space, f r.1*f r.2/‖r.1-r.2‖) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  ring

lemma real_complex_tsupport (g : Space → ℝ) :
    tsupport (fun x : Space => (g x : ℂ)) = tsupport g := by
  unfold tsupport
  congr 1
  ext x
  simp only [Function.mem_support,ne_eq,Complex.ofReal_eq_zero]

def packetRegion (g : Space → ℝ) (J : Set Space) : Set Space :=
  (fun r : Space × Space => r.1+r.2) '' (tsupport g ×ˢ J)

lemma coherentSupport_fermi_subset (g : Space → ℝ) (J : Set Space) (r : ℝ) :
    coherentSpatialSupport (fun x => (g x : ℂ)) (J ×ˢ closedBall 0 r) ⊆ packetRegion g J := by
  rintro x ⟨⟨q,u⟩,⟨hq,hu⟩,rfl⟩
  exact ⟨(u,q.1),⟨by simpa only [real_complex_tsupport] using hu,hq.1⟩,rfl⟩

theorem price_le_smeared_packet_insertion {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (packetRegion g J))
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam*N +
      tfKinetic*(∫ z, (ρ z)^(5/3 : ℝ)) + (packetDirichlet g/2)*(∫ z, ρ z) +
      (1/2:ℝ)*(∫ r : Space × Space, smearedPacketDensity g ρ r.1*smearedPacketDensity g ρ r.2/‖r.1-r.2‖) -
      Z*CoulombAnalysis.tfPotential (smearedPacketDensity g ρ) 0 +
      lam*(∫ z, ρ z) + coreDensityInteraction ψ (smearedPacketDensity g ρ) := by
  let := fermiMeasure_finite hn hJ hs hb
  have hgc : ContDiff ℝ ∞ (fun x : Space => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hcgc : HasCompactSupport (fun x : Space => (g x : ℂ)) :=
    hcg.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hgg : (∫ x : Space, ‖(g x : ℂ)‖^2) = 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,sq_abs] using hgn
  have hf := price_le_coherent_insertion hψ hgc hcgc hgg (fermiMeasure ρ)
    (fermiMeasure_le ρ) (hJ.prod (isCompact_closedBall _ _)) (fermiMeasure_mem hm hn hs hb)
    A hcore (hsep.mono_right (coherentSupport_fermi_subset g J _)) hZ hlam
  let d := coherentDensity (fun x => (g x : ℂ)) (fermiMeasure ρ)
  have he : smearedPacketDensity g ρ = fun x => 2*d x :=
    funext (fun x => (coherentDensity_fermi hm hn hJ hs hb hg.continuous x).symm)
  have hmass : ∫ z, ρ z = 2*(∫ x : Space, d x) := by
    rw [← smearedPacketDensity_mass hm hn hJ hs hb hg.continuous hcg hgn,he,integral_const_mul]
  rw [he,coulomb_double_const_mul,potential_const_mul,coreDensityInteraction_const_mul,hmass]
  rw [coherentSpinKinetic_fermi hm hn hJ hs hb hg hcg hgn] at hf
  rw [hmass] at hf
  dsimp only [d]
  linarith

theorem price_le_radial_packet_insertion {N : ℕ} {ψ : FormVector N} (hψ : FormAdmissible ψ)
    {ρ g : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x : Space, (g x)^2 = 1) (hr : CoulombAnalysis.IsRadial (fun x => (g x)^2))
    {R : ℝ} (hR : 0 < R) (hgs : ∀ y, g y ≠ 0 → ‖y‖ ≤ R)
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (hsep : Disjoint A (packetRegion g J))
    (hnuc : ∀ z ∈ J, R ≤ ‖z‖) (hcs : ∀ a ∈ A, ∀ z ∈ J, R ≤ ‖a-z‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    priceEnergy (energy Z) lam ≤ formEnergy Z ψ + lam*N +
      tfKinetic*(∫ z, (ρ z)^(5/3 : ℝ)) + (packetDirichlet g/2)*(∫ z, ρ z) +
      (1/2:ℝ)*(∫ r : Space × Space, ρ r.1*ρ r.2/‖r.1-r.2‖) -
      Z*CoulombAnalysis.tfPotential ρ 0 + lam*(∫ z, ρ z) + coreDensityInteraction ψ ρ := by
  have hab (z : Space) : |ρ z| ≤ B := by rw [abs_of_nonneg (hn z)]; exact hb z
  have h1 : Integrable ρ := bounded_compact_integrable hm hJ hs hab
  have hs2 (y : Space) (hy : (g y)^2 ≠ 0) : ‖y‖ ≤ R := hgs y (fun hz => hy (by simp [hz]))
  have hmean (a : Space) (ha : ∀ z, ρ z ≠ 0 → R ≤ ‖a-z‖) :
      CoulombAnalysis.tfPotential (smearedPacketDensity g ρ) a = CoulombAnalysis.tfPotential ρ a :=
    spatialSmearing_potential_eq (hg.continuous.pow 2) (square_compact hcg) hr hgn hm h1 hR hs2 a ha
  have hzero : CoulombAnalysis.tfPotential (smearedPacketDensity g ρ) 0 = CoulombAnalysis.tfPotential ρ 0 :=
    hmean 0 (fun z hz => by simpa only [zero_sub,norm_neg] using hnuc z (hs hz))
  have hcross : coreDensityInteraction ψ (smearedPacketDensity g ρ) = coreDensityInteraction ψ ρ := by
    unfold coreDensityInteraction
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases ha : x j ∈ A
    · rw [hmean (x j) (fun z hz => hcs (x j) ha z (hs hz))]
    · have hz := (hcore x j ha s).1
      simp only [hz,norm_zero,zero_pow (by norm_num : 2 ≠ 0),zero_mul]
  have hf := price_le_smeared_packet_insertion hψ hm hn hJ hs hb hg hcg hgn A hcore hsep hZ hlam
  rw [hzero,hcross] at hf
  have hd := smearedPacketDensity_direct_le hm hn hJ hs hb hg.continuous hcg hgn hr
  linarith

end CoulombAtom

end

end OAI
