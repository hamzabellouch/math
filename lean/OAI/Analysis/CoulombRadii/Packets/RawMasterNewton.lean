import Mathlib
import OAI.Analysis.CoulombRadii.Packets.OriginalPotentialTower
import OAI.Analysis.CoulombRadii.Packets.MasterNewton
import OAI.Analysis.CoulombRadii.Variational.PhysicalDensityWeighted

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma integrable_packet_coulomb (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    {c r₀ s : ℝ} (hc : 0<c) (hr : 0<r₀) (hs : 0<s) (z y : Position) :
    Integrable (fun w => coulombKernel (y-w)*packetKernel g c r₀ s z w) := by
  apply Coulomb.coulomb_convolution_integrable (integrable_packetKernel g hm hc hr hs z)
    (((continuous_packetKernel g.continuous hc hr hs).comp (continuous_const.prodMk continuous_id)).measurable)
    (packetKernel_nonneg g hc hr hs z)
    (M := (packetWidth c r₀ s z^3)⁻¹*(SchwartzMap.seminorm ℝ 0 0 g)^2)
    (fun w => mul_le_mul_of_nonneg_left (Coulomb.schwartz_square_le g _)
      (by have ht := packetWidth_pos hc hr hs z; positivity)) (by norm_num : (0:ℝ)<1) y

lemma rawPacketPotential_sum {n : ℕ} (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    {c r₀ s : ℝ} (hc : 0<c) (hr : 0<r₀) (hs : 0<s)
    (x : Configuration n) (y : Position) :
    potentialOf (rawPacketDensity g c r₀ s x) y=∑ i : Fin n,potentialOf (packetKernel g c r₀ s (x i)) y := by
  unfold potentialOf rawPacketDensity
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => integrable_packet_coulomb g hm hc hr hs (x i) y)

theorem rawPacketPotential_near_deficit {n : ℕ} (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    (hrad : ∀ w,g w=g (EuclideanSpace.single 0 ‖w‖))
    (hgs : ∀ w,1<‖w‖ → g w=0)
    {c r₀ s : ℝ} (hc : 0<c) (hr : 0<r₀) (hs : 0<s)
    (hq : c*(1+packetExponent)*s^packetExponent≤1/2)
    (x : Configuration n) (y : Position) (hxy : ∀ i,x i≠y) :
    0≤(∑ i : Fin n,coulombKernel (y-x i))-potentialOf (rawPacketDensity g c r₀ s x) y ∧
    (∑ i : Fin n,coulombKernel (y-x i))-potentialOf (rawPacketDensity g c r₀ s x) y≤
      ∑ i : Fin n,(Metric.closedBall y (2*packetWidth c r₀ s y)).indicator
        (fun z => coulombKernel (y-z)) (x i) := by
  rw [rawPacketPotential_sum g hm hc hr hs,←Finset.sum_sub_distrib]
  refine ⟨Finset.sum_nonneg (fun i _ => ?_),Finset.sum_le_sum (fun i _ => ?_)⟩
  · exact (packet_potential_near_deficit g hm hrad hgs hc hr hs hq (hxy i).symm).1
  · exact (packet_potential_near_deficit g hm hrad hgs hc hr hs hq (hxy i).symm).2

lemma integrable_rawLaw_of_weight {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ,MemLp (ψ σ) 2 volume) (F : Configuration n → ℝ)
    (hi : Integrable (fun x => F x*configurationDensity ψ x)) :
    Integrable F (rawLaw ψ) := by
  have HH := (integrable_withDensity_iff_integrable_smul₀'
    (integrable_configurationDensity hψ).aemeasurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (g := F))
  apply HH.mpr
  simpa only [ENNReal.toReal_ofReal (configurationDensity_nonneg ψ _),smul_eq_mul,mul_comm] using hi

lemma integrable_rawLaw_oneBody {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ,MemLp (ψ σ) 2 volume) (W : Position → ℝ)
    (hi : ∀ σ i,Integrable (fun x : Configuration n => W (x i)*‖ψ σ x‖^2)) :
    Integrable (fun x => ∑ i : Fin n,W (x i)) (rawLaw ψ) := by
  apply integrable_rawLaw_of_weight hψ
  simp only [Finset.sum_mul,configurationDensity,Finset.mul_sum]
  exact integrable_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun i _ => hi σ i))

lemma fromH1_raw_potential_integral {n : ℕ} (u : Coulomb.H1Vector n) (y : Position) :
    (∫ x, (∑ i : Fin n,coulombKernel (y-x i)) ∂rawLaw (fromH1Wave u))=Coulomb.coreCoulombPotential u y := by
  have hψ (σ : Spins n) : MemLp (fromH1Wave u σ) 2 volume :=
    (u.value_L2 σ).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  rw [integral_rawLaw hψ]
  unfold rawExpectation configurationDensity
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun σ _ => by
    simp only [Finset.sum_mul]
    exact integrable_finsetSum _ (fun i _ => fromH1_coulomb_weight_integrable u y σ i))]
  unfold Coulomb.coreCoulombPotential
  apply Finset.sum_congr rfl
  intro σ _
  rw [show (fun x : Configuration n => (∑ i,coulombKernel (y-x i))*‖fromH1Wave u σ x‖^2)=
    fun x => ∑ i : Fin n,coulombKernel (y-x i)*‖fromH1Wave u σ x‖^2 by funext x; rw [Finset.sum_mul]]
  rw [integral_finsetSum _ (fun i _ => fromH1_coulomb_weight_integrable u y σ i)]
  apply Finset.sum_congr rfl
  intro i _
  have H := (flattenConfiguration_measurePreserving n).integral_comp'
    (fun x => Coulomb.coulombKernel (Coulomb.position x i-y)*‖u.value σ x‖^2)
  change (∫ x : Configuration n,Coulomb.coulombKernel (x i-y)*‖fromH1Wave u σ x‖^2)=_ at H
  simpa only [coulombKernel,Coulomb.coulombKernel,norm_sub_rev] using H

theorem physical_master_near_deficit {N : ℕ} (u : Coulomb.H1Vector (N+1))
    (ha : Coulomb.Antisymmetric u) (hn : Coulomb.mass u=1)
    (g : 𝓢(Position,ℝ)) (hm : (∫ w,g w^2)=1)
    (hrad : ∀ w,g w=g (EuclideanSpace.single 0 ‖w‖))
    (hgs : ∀ w,1<‖w‖ → g w=0)
    {c r₀ s : ℝ} (hc : 0<c) (hr : 0<r₀) (hs : 0<s)
    (hq : c*(1+packetExponent)*s^packetExponent≤1/2) (y : Position) :
    0≤Coulomb.coreCoulombPotential u y-
      potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y ∧
    Coulomb.coreCoulombPotential u y-
      potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y≤
      ∫ z in Metric.closedBall y (2*packetWidth c r₀ s y),coulombKernel (y-z)*density (fromH1Wave u) z := by
  have hd := fromH1_domain u ha
  have hn' : normSquared (fromH1Wave u)=1 := (fromH1_mass u).trans hn
  have := rawLaw_isProbability hd.2.2.1 hn'
  have hgc : HasCompactSupport (g : Position → ℝ) :=
    HasCompactSupport.intro (isCompact_closedBall (0:Position) 1) (fun z hz =>
      hgs z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  have hraw := integrable_rawLaw_oneBody hd.2.2.1 (fun z => coulombKernel (y-z))
    (fromH1_coulomb_weight_integrable u y)
  have hnear := integrable_rawLaw_oneBody hd.2.2.1
    ((Metric.closedBall y (2*packetWidth c r₀ s y)).indicator (fun z => coulombKernel (y-z)))
    (fromH1_coulomb_near_weight_integrable u y _)
  have hms := integrable_rawPacketPotential g.continuous hgc hm hc hr hs (rawLaw (fromH1Wave u)) y
  have hpt : ∀ᵐ x ∂rawLaw (fromH1Wave u),
      0≤(∑ i : Fin (N+1),coulombKernel (y-x i))-potentialOf (rawPacketDensity g c r₀ s x) y ∧
      (∑ i : Fin (N+1),coulombKernel (y-x i))-potentialOf (rawPacketDensity g c r₀ s x) y≤
        ∑ i : Fin (N+1),(Metric.closedBall y (2*packetWidth c r₀ s y)).indicator
          (fun z => coulombKernel (y-z)) (x i) := by
    filter_upwards [rawLaw_no_fixed_particle hd.1 hd.2.2.1 hn' y] with x hx
    exact rawPacketPotential_near_deficit g hm hrad hgs hc hr hs hq x y hx
  have he : Coulomb.coreCoulombPotential u y-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y=
      ∫ x,((∑ i : Fin (N+1),coulombKernel (y-x i))-potentialOf (rawPacketDensity g c r₀ s x) y) ∂rawLaw (fromH1Wave u) := by
    rw [integral_sub hraw hms,fromH1_raw_potential_integral,mixturePacketPotential g.continuous hgc hm hc hr hs]
  rw [he]
  refine ⟨integral_nonneg_of_ae (hpt.mono (fun _ hx => hx.1)),?_⟩
  calc
    _≤∫ x,(∑ i : Fin (N+1),(Metric.closedBall y (2*packetWidth c r₀ s y)).indicator
          (fun z => coulombKernel (y-z)) (x i)) ∂rawLaw (fromH1Wave u) :=
      integral_mono_ae (hraw.sub hms) hnear (hpt.mono (fun _ hx => hx.2))
    _=_ := by
      rw [integral_rawLaw hd.2.2.1,rawExpectation_oneBody_eq_density hd.1 _
        (fromH1_coulomb_near_weight_integrable u y _),←integral_indicator measurableSet_closedBall]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        by_cases hz : z∈Metric.closedBall y (2*packetWidth c r₀ s y) <;> simp [hz]
end NeutralAtom
end

end
end

end OAI
