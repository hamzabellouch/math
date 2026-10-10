import Mathlib
import OAI.MathematicalPhysics.BFSS.MeasuredFields
import OAI.MathematicalPhysics.BFSS.OrbitCutoffs

namespace OAI

/-! Measured normal patches and complete finite-patch norm exhaustion. -/

namespace BFSSNormalMeasure
open Set
variable {ι X : Type*} [Fintype ι]

lemma disjoint_cutoff_sum (φ : ι → X → ℝ)
    (hb : ∀ i x, 0 ≤ φ i x ∧ φ i x ≤ 1)
    (hd : Pairwise (fun i j => Disjoint (Function.support (φ i)) (Function.support (φ j)))) :
    (∀ x, 0 ≤ ∑ i, φ i x ∧ (∑ i, φ i x) ≤ 1) ∧
    (∀ i x, φ i x = 1 → (∑ j, φ j x) = 1) := by
  classical
  have hsingle (i : ι) (x : X) (hi : φ i x ≠ 0) : (∑ j, φ j x) = φ i x := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      by_contra hjn
      exact Set.disjoint_left.mp (hd hji) hjn hi
    · simp
  constructor
  · intro x
    refine ⟨Finset.sum_nonneg (fun i _ => (hb i x).1),?_⟩
    by_cases he : ∃ i, φ i x ≠ 0
    · obtain ⟨i,hi⟩ := he
      rw [hsingle i x hi]
      exact (hb i x).2
    · have hz : ∀ i, φ i x = 0 := by simpa only [not_exists,not_not] using he
      simp only [hz,Finset.sum_const_zero]
      norm_num
  · intro i x hi
    rw [hsingle i x (by rw [hi]; exact one_ne_zero),hi]
end BFSSNormalMeasure
namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open Matrix MeasureTheory Set
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.gaugeAction AlgebraData.normalSlice AlgebraData.normalMeasuredField coreToL2

structure MeasuredNormalPatch (q : Boson N) where
  density : M.normalSlice q → ℝ
  cutoff : Boson N → ℝ
  neighborhood : Set (Boson N)
  integrationDomain : Set (Boson N)
  integration_support : Function.support cutoff ⊆ integrationDomain
  integration : ∀ (h : ℝ), 0 < h → ∀ F : Boson N → ℝ, Continuous F → HasCompactSupport F →
    (∀ U : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction U x) = F x) →
    (∀ x ∈ Function.support F, h • x ∈ integrationDomain) →
    (∫ x, F x) = (h ^ M.orbitDimension q)⁻¹ *
      ∫ z : M.normalSlice q, density (h • z) * F (h⁻¹ • q+(z : Boson N))
  c : ℝ
  K : ℝ
  density_continuous : Continuous density
  density_nonneg : ∀ z, 0 ≤ density z
  density_zero_pos : 0 < density 0
  density_invariant : ∀ U : M.gaugeStabilizer q, ∀ z,
    density (M.stabilizerNormalIsometry q U z) = density z
  cutoff_continuous : Continuous cutoff
  cutoff_bounds : ∀ x, 0 ≤ cutoff x ∧ cutoff x ≤ 1
  cutoff_invariant : ∀ U : unitary (ColorMatrix N), ∀ x, cutoff (M.gaugeAction U x) = cutoff x
  neighborhood_open : IsOpen neighborhood
  orbit_neighborhood : M.gaugeOrbit q ⊆ neighborhood
  cutoff_one : ∀ x ∈ neighborhood, cutoff x = 1
  c_pos : 0 < c
  K_nonneg : 0 ≤ K
  norm_eq : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : G.invariantCore,
    (∫ z, ‖M.normalMeasuredField q h density cutoff f.val z‖^2) =
      ∫ x, cutoff (h • x)*‖f.val x‖^2
  norm_le : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : G.invariantCore,
    (∫ z, ‖M.normalMeasuredField q h density cutoff f.val z‖^2) ≤ ‖coreToL2 f.val‖^2
  moment_bound : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : G.invariantCore,
    c/2 * (∫ z : M.normalSlice q, ‖z‖^2*‖M.normalMeasuredField q h density cutoff f.val z‖^2) ≤
      M.deformedCoreEnergy h 1 f.val + K*‖coreToL2 f.val‖^2
  tail_bound : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : G.invariantCore,
    ∀ R : ℝ, 0 ≤ R → c/2*R^2 *
      (∫ z : M.normalSlice q in {z | R < ‖z‖}, ‖M.normalMeasuredField q h density cutoff f.val z‖^2) ≤
      M.deformedCoreEnergy h 1 f.val + K*‖coreToL2 f.val‖^2

theorem exists_measuredNormalPatch (hN : 2 ≤ N) (q : Boson N) (hq : q ∈ M.massiveZeros)
    (V : Set (Boson N)) (hV : IsOpen V) (hqV : M.gaugeOrbit q ⊆ V)
    (hVi : ∀ U : unitary (ColorMatrix N), ∀ x, M.gaugeAction U x ∈ V ↔ x ∈ V) :
    ∃ P : G.MeasuredNormalPatch q, Function.support P.cutoff ⊆ V := by
  obtain ⟨J,V₀,c,K,hJ,hJn,hJ0,hJi,hV₀,hqV₀,hV₀i,hint,hc,hK,hbounds⟩ :=
    G.normalMeasuredCore_uniform_bounds hN q hq
  have hI : ∀ U : unitary (ColorMatrix N), ∀ x,
      M.gaugeAction U x ∈ V₀ ∩ V ↔ x ∈ V₀ ∩ V := by
    intro U x
    simp only [mem_inter_iff,hV₀i,hVi]
  obtain ⟨φ,W,hφ,hφb,hφi,hφs,hW,hqW,hφW,_⟩ :=
    M.gauge_neighborhood_plateau hN q (V₀ ∩ V) (hV₀.inter hV)
      ⟨hqV₀ (M.self_mem_gaugeOrbit q),hqV (M.self_mem_gaugeOrbit q)⟩ hI
  have hs₀ : Function.support φ ⊆ V₀ := hφs.trans inter_subset_left
  have hb := fun h hh h1 f => hbounds h hh h1 φ hφ hφb hφi hs₀ f
  refine ⟨{
    density := J
    cutoff := φ
    neighborhood := W
    integrationDomain := V₀
    integration_support := hs₀
    integration := hint
    c := c
    K := K
    density_continuous := hJ
    density_nonneg := hJn
    density_zero_pos := hJ0
    density_invariant := hJi
    cutoff_continuous := hφ
    cutoff_bounds := hφb
    cutoff_invariant := hφi
    neighborhood_open := hW
    orbit_neighborhood := hqW
    cutoff_one := hφW
    c_pos := hc
    K_nonneg := hK
    norm_eq := fun h hh h1 f => (hb h hh h1 f).1
    norm_le := fun h hh h1 f => (hb h hh h1 f).2.1
    moment_bound := fun h hh h1 f => (hb h hh h1 f).2.2.1
    tail_bound := fun h hh h1 f => (hb h hh h1 f).2.2.2
  },hφs.trans inter_subset_right⟩
end
end BFSSQuantum.AlgebraData.GaugeData
namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open Matrix MeasureTheory Set
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
attribute [local irreducible] AlgebraData.gaugeAction AlgebraData.normalSlice AlgebraData.normalMeasuredField coreToL2

theorem normalPatch_norm_exhaustion (hN : 2 ≤ N) :
    ∃ S : Finset (Boson N),
      (∀ q ∈ S, q ∈ M.massiveZeros) ∧
      M.massiveZeros = ⋃ q ∈ S, M.gaugeOrbit q ∧
      Pairwise (fun i j : S => Disjoint (M.gaugeOrbit i.val) (M.gaugeOrbit j.val)) ∧
      ∃ P : (q : S) → G.MeasuredNormalPatch q.val,
        Pairwise (fun i j => Disjoint (Function.support (P i).cutoff) (Function.support (P j).cutoff)) ∧
        ∃ δ c K : ℝ, 0 < δ ∧ 0 < c ∧ 0 ≤ K ∧
          ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : G.invariantCore,
            0 ≤ ‖coreToL2 f.val‖^2 -
              ∑ q : S, ∫ z, ‖M.normalMeasuredField q.val h (P q).density (P q).cutoff f.val z‖^2 ∧
            c/2*δ^2*(‖coreToL2 f.val‖^2 -
              ∑ q : S, ∫ z, ‖M.normalMeasuredField q.val h (P q).density (P q).cutoff f.val z‖^2) ≤
              h^2*(M.deformedCoreEnergy h 1 f.val + K*‖coreToL2 f.val‖^2) := by
  classical
  obtain ⟨T,hTf,hT,hcov,hdis⟩ := M.massiveZeros_disjoint_orbits hN
  let S : Finset (Boson N) := hTf.toFinset
  have hSset : (S : Set (Boson N)) = T := hTf.coe_toFinset
  have hS (q : Boson N) (hq : q ∈ S) : q ∈ M.massiveZeros :=
    hT (hSset ▸ (show q ∈ (S : Set (Boson N)) from hq))
  have hcovS : M.massiveZeros = ⋃ q ∈ S, M.gaugeOrbit q := by
    simpa only [←hSset,Finset.mem_coe] using hcov
  have hdisS : Pairwise (fun i j : S => Disjoint (M.gaugeOrbit i.val) (M.gaugeOrbit j.val)) := by
    intro i j hij
    apply hdis (hSset ▸ i.prop) (hSset ▸ j.prop)
    exact fun he => hij (Subtype.ext he)
  have hp (q : S) : ∃ P : G.MeasuredNormalPatch q.val,
      Function.support P.cutoff ⊆ M.orbitChamber (fun i : S => i.val) q :=
    G.exists_measuredNormalPatch hN q.val (hS q.val q.prop) _
      (M.orbitChamber_open _ q) (M.orbitChamber_contains _ hN hdisS q)
      (M.orbitChamber_gauge _ q)
  choose P hPs using hp
  have hPd : Pairwise (fun i j => Disjoint (Function.support (P i).cutoff) (Function.support (P j).cutoff)) := by
    intro i j hij
    exact (M.orbitChamber_disjoint (fun i : S => i.val) hij).mono (hPs i) (hPs j)
  let W : Set (Boson N) := ⋃ q : S, (P q).neighborhood
  have hW : IsOpen W := isOpen_iUnion (fun q => (P q).neighborhood_open)
  have hZW : M.massiveZeros ⊆ W := by
    intro x hx
    obtain ⟨q,hq,hxq⟩ := Set.mem_iUnion₂.mp (hcovS ▸ hx)
    exact Set.mem_iUnion.mpr ⟨⟨q,hq⟩,(P ⟨q,hq⟩).orbit_neighborhood hxq⟩
  obtain ⟨δ,c,K,hδ,hc,hK,he⟩ := M.massive_core_cutoff_exhaustion hN W hW hZW
  refine ⟨S,hS,hcovS,hdisS,P,hPd,δ,c,K,hδ,hc,hK,?_⟩
  let χ : Boson N → ℝ := fun x => ∑ q : S, (P q).cutoff x
  have hχ : Continuous χ := continuous_finsetSum _ (fun q _ => (P q).cutoff_continuous)
  obtain ⟨hχb,hχone⟩ := BFSSNormalMeasure.disjoint_cutoff_sum (fun q => (P q).cutoff)
    (fun q => (P q).cutoff_bounds) hPd
  have hχW : ∀ x ∈ W, χ x = 1 := by
    intro x hx
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hx
    exact hχone q x ((P q).cutoff_one x hq)
  intro h hh h1 f
  have hsmul : Continuous (fun x : Boson N => h • x) :=
    (continuous_const : Continuous (fun _ : Boson N => h)).smul continuous_id
  have hi (q : S) : Integrable (fun x => (P q).cutoff (h • x)*‖f.val x‖^2) :=
    weighted_core_square_integrable _ ((P q).cutoff_continuous.comp hsmul) f.val
  have hn : (∑ q : S, ∫ z, ‖M.normalMeasuredField q.val h (P q).density (P q).cutoff f.val z‖^2) =
      ∫ x, χ (h • x)*‖f.val x‖^2 := by
    simp_rw [MeasuredNormalPatch.norm_eq _ h hh h1 f]
    rw [←integral_finsetSum _ (fun q _ => hi q)]
    apply integral_congr_ae
    filter_upwards [] with x
    exact (Finset.sum_mul ..).symm
  rw [hn]
  exact he h hh h1 χ hχ hχb hχW f.val
end
end BFSSQuantum.AlgebraData.GaugeData

end OAI
