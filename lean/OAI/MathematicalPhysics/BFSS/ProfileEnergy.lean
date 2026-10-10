import Mathlib
import OAI.MathematicalPhysics.BFSS.KineticMeasures
import OAI.MathematicalPhysics.BFSS.CovariantFields

namespace OAI

/-! Profile integral identities and ambient-to-normal energy comparison. -/

namespace BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch
noncomputable section
open MeasureTheory Set
variable {N : ℕ} {M : AlgebraData N} {G : M.GaugeData} {q : Boson N}
variable (P : G.MeasuredNormalPatch q)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2

lemma local_density_integral {h : ℝ} (hh : 0 < h) (F : Boson N → ℝ)
    (hF : Continuous F) (hK : HasCompactSupport F)
    (hI : ∀ U : unitary (ColorMatrix N), ∀ x, F (M.gaugeAction U x) = F x) :
    (∫ x, P.cutoff (h • x)*F x) =
      (h^M.orbitDimension q)⁻¹ * ∫ z : M.normalSlice q,
        P.density (h • z)*P.cutoff (q+h • (z : Boson N))*F (h⁻¹ • q+(z : Boson N)) := by
  have hsm : Continuous (fun x : Boson N => h • x) :=
    Continuous.smul (M := ℝ) (X := Boson N) continuous_const continuous_id
  have hFc : Continuous (fun x : Boson N => P.cutoff (h • x)*F x) :=
    (P.cutoff_continuous.comp hsm).mul hF
  have hFk : HasCompactSupport (fun x : Boson N => P.cutoff (h • x)*F x) := hK.mul_left
  have hFi (U : unitary (ColorMatrix N)) (x : Boson N) :
      P.cutoff (h • M.gaugeAction U x)*F (M.gaugeAction U x) = P.cutoff (h • x)*F x := by
    rw [←M.gaugeAction_smul,P.cutoff_invariant,hI]
  have hFs (x : Boson N) (hx : x ∈ Function.support (fun x => P.cutoff (h • x)*F x)) :
      h • x ∈ P.integrationDomain := by
    apply P.integration_support
    intro hz
    exact hx (by simp only [hz,zero_mul])
  rw [P.integration h hh _ hFc hFk hFi hFs]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  rw [smul_add,smul_smul,mul_inv_cancel₀ hh.ne',one_smul]
  ring
end
end BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory
variable {N : ℕ} (M : AlgebraData N)
attribute [local irreducible] normalSlice gaugeAction coreToL2

lemma normalMeasuredField_fermionic (q : Boson N) {h : ℝ} (hh : 0 < h) (m : ℝ)
    (J : M.normalSlice q → ℝ) (φ : Boson N → ℝ) (f : SmoothCore N)
    (hJ : ∀ z, 0 ≤ J z) (hφ : ∀ x, 0 ≤ φ x) (z : M.normalSlice q) :
    inner ℝ (M.normalMeasuredField q h J φ f z)
      (M.deformedFermionField h m (h⁻¹ • q+(z : Boson N)) (M.normalMeasuredField q h J φ f z)) =
      (h^M.orbitDimension q)⁻¹ *
        (J (h • z)*φ (q+h • (z : Boson N))*M.fermionicDensity h m f (h⁻¹ • q+(z : Boson N))) := by
  simp only [normalMeasuredField,normalCoreField,map_smul,real_inner_smul_left,
    real_inner_smul_right,fermionicDensity]
  have h1 := Real.sq_sqrt (mul_nonneg (hJ (h • z)) (hφ (q+h • (z : Boson N))))
  have h2 := Real.sq_sqrt (inv_nonneg.mpr (pow_nonneg hh.le (M.orbitDimension q)))
  calc
    _ = (Real.sqrt (J (h • z)*φ (q+h • (z : Boson N))))^2 *
        (Real.sqrt ((h^M.orbitDimension q)⁻¹))^2 *
        inner ℝ (f (h⁻¹ • q+(z : Boson N)))
          (M.deformedFermionField h m (h⁻¹ • q+(z : Boson N)) (f (h⁻¹ • q+(z : Boson N)))) := by ring
    _ = _ := by rw [h1,h2]; ring
end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch
noncomputable section
open MeasureTheory Set
variable {N : ℕ} {M : AlgebraData N} {G : M.GaugeData} {q : Boson N}
variable (P : G.MeasuredNormalPatch q)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2

lemma profile_fermionic_integral (hN : 2 ≤ N) {h : ℝ} (hh : 0 < h) (m : ℝ) (f : G.invariantCore) :
    (∫ x : M.NormalCoordinates q, inner ℝ (P.profile h f x)
      (M.deformedFermionField h m (h⁻¹ • q+(M.normalCoordinateIsometry q x : Boson N)) (P.profile h f x))) =
      ∫ x : Boson N, P.cutoff (h • x)*M.fermionicDensity h m f.val x := by
  have he : (∫ x : M.NormalCoordinates q, inner ℝ (P.profile h f x)
      (M.deformedFermionField h m (h⁻¹ • q+(M.normalCoordinateIsometry q x : Boson N)) (P.profile h f x))) =
      ∫ z : M.normalSlice q, inner ℝ (M.normalMeasuredField q h P.density P.cutoff f.val z)
        (M.deformedFermionField h m (h⁻¹ • q+(z : Boson N))
          (M.normalMeasuredField q h P.density P.cutoff f.val z)) := by
    rw [←(M.normalCoordinateIsometry q).measurePreserving.integral_comp
      (M.normalCoordinateIsometry q).toHomeomorph.measurableEmbedding]
    apply integral_congr_ae
    filter_upwards [P.profile_ae h f] with x hx
    rw [hx,M.normalMeasuredCoordinates_eq]
  rw [he,P.local_density_integral hh _ (M.fermionicDensity_continuous h m f.val)
    (M.fermionicDensity_compactSupport h m f.val)
    (fun U x => G.invariantCore_fermionicDensity_unitary hN f U h m x),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  exact M.normalMeasuredField_fermionic q hh m P.density P.cutoff f.val P.density_nonneg
    (fun x => (P.cutoff_bounds x).1) z

lemma profile_bosonic_integral (hN : 2 ≤ N) (hq : q ∈ M.massiveZeros)
    {h : ℝ} (hh : 0 < h) (f : G.invariantCore) :
    (∫ x : M.NormalCoordinates q, M.normalEffectivePotential q h (M.normalCoordinateIsometry q x : Boson N)*
      ‖P.profile h f x‖^2) = ∫ x : Boson N, P.cutoff (h • x)*M.bosonicDensity h 1 f.val x := by
  have he : (∫ x : M.NormalCoordinates q, M.normalEffectivePotential q h (M.normalCoordinateIsometry q x : Boson N)*
      ‖P.profile h f x‖^2) = ∫ z : M.normalSlice q,
      M.deformedBosonicPotential h 1 (h⁻¹ • q+(z : Boson N))*
        ‖M.normalMeasuredField q h P.density P.cutoff f.val z‖^2 := by
    rw [←(M.normalCoordinateIsometry q).measurePreserving.integral_comp
      (M.normalCoordinateIsometry q).toHomeomorph.measurableEmbedding]
    apply integral_congr_ae
    filter_upwards [P.profile_ae h f] with x hx
    rw [hx,M.normalMeasuredCoordinates_eq,M.normalEffectivePotential_eq q hq hh]
  rw [he,P.local_density_integral hh _ (M.bosonicDensity_continuous h 1 f.val)
    (M.bosonicDensity_compactSupport h 1 f.val)
    (fun U x => G.invariantCore_bosonicDensity_unitary hN f U h 1 x),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [M.normalMeasuredField_norm_sq q hh P.density P.cutoff f.val P.density_nonneg
    (fun x => (P.cutoff_bounds x).1)]
  simp only [AlgebraData.bosonicDensity,smul_add,smul_smul,mul_inv_cancel₀ hh.ne',one_smul]
  ring
end
end BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Finset
variable {N : ℕ} (M : AlgebraData N)

def coreEnergyDensity (h m : ℝ) (f : SmoothCore N) (x : Boson N) : ℝ :=
  (1/2 : ℝ)*kineticDensity f x + (M.bosonicDensity h m f x + M.fermionicDensity h m f x)

lemma coreEnergyDensity_continuous (h m : ℝ) (f : SmoothCore N) :
    Continuous (M.coreEnergyDensity h m f) :=
  (continuous_const.mul (kineticDensity_continuous f)).add
    ((M.bosonicDensity_continuous h m f).add (M.fermionicDensity_continuous h m f))

lemma coreEnergyDensity_compactSupport (h m : ℝ) (f : SmoothCore N) :
    HasCompactSupport (M.coreEnergyDensity h m f) :=
  ((kineticDensity_compactSupport f).mul_left).add
    ((M.bosonicDensity_compactSupport h m f).add (M.fermionicDensity_compactSupport h m f))

lemma coreEnergyDensity_integral (h m : ℝ) (f : SmoothCore N) :
    (∫ x, M.coreEnergyDensity h m f x) = M.deformedCoreEnergy h m f := by
  have hk : Integrable (kineticDensity f) := (kineticDensity_continuous f).integrable_of_hasCompactSupport (kineticDensity_compactSupport f)
  change (∫ x, (1/2 : ℝ)*kineticDensity f x +
    (M.deformedBosonicPotential h m x*‖f x‖^2 + inner ℝ (f x) (M.deformedFermionField h m x (f x)))) = _
  rw [integral_add (f := fun x => (1/2 : ℝ)*kineticDensity f x)
    (g := fun x => M.deformedBosonicPotential h m x*‖f x‖^2 + inner ℝ (f x) (M.deformedFermionField h m x (f x)))
    (hk.const_mul (1/2 : ℝ)) ((M.bosonic_core_integrable h m f).add (M.fermion_core_integrable h m f)),
    integral_const_mul,kineticDensity_integral,AlgebraData.deformedCoreEnergy,M.averaged_core_energy]

lemma coreEnergyDensity_uniform_lower (hN : 2 ≤ N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SmoothCore N, ∀ x,
      -K*‖f x‖^2 ≤ M.coreEnergyDensity h 1 f x := by
  obtain ⟨c,K,hc,hK,hb⟩ := M.deformedPotential_fermion_uniform_distance hN
  refine ⟨K,hK,?_⟩
  intro h hh h1 f x
  have ht := hb h hh h1 x (f x)
  have hz : 0 ≤ c/2*(M.massiveDistance h x)^2*‖f x‖^2 := by positivity
  have hk := kineticDensity_nonneg f x
  dsimp only [coreEnergyDensity,bosonicDensity,fermionicDensity]
  nlinarith only [ht,hz,hk]

lemma cutoff_energy_le (h m K : ℝ) (f : SmoothCore N)
    (hK : ∀ x, -K*‖f x‖^2 ≤ M.coreEnergyDensity h m f x)
    (χ : Boson N → ℝ) (hχ : Continuous χ) (hχb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    (∫ x, χ (h • x)*M.coreEnergyDensity h m f x) ≤
      M.deformedCoreEnergy h m f + K*(‖coreToL2 f‖^2 - ∫ x, χ (h • x)*‖f x‖^2) := by
  have hsm : Continuous (fun x : Boson N => h • x) :=
    Continuous.smul (M := ℝ) (X := Boson N) continuous_const continuous_id
  have hw := hχ.comp hsm
  have hae : Integrable (M.coreEnergyDensity h m f) := (M.coreEnergyDensity_continuous h m f).integrable_of_hasCompactSupport
    (M.coreEnergyDensity_compactSupport h m f)
  have hwe : Integrable (fun x => χ (h • x)*M.coreEnergyDensity h m f x) := (hw.mul (M.coreEnergyDensity_continuous h m f)).integrable_of_hasCompactSupport
    (M.coreEnergyDensity_compactSupport h m f).mul_left
  have hwn := weighted_core_square_integrable _ hw f
  have hn := coreNormSq_integrable f
  calc
    _ ≤ ∫ x, M.coreEnergyDensity h m f x + K*(‖f x‖^2 - χ (h • x)*‖f x‖^2) := by
      apply integral_mono hwe (hae.add ((hn.sub hwn).const_mul K))
      intro x
      have hp := mul_nonneg (sub_nonneg.mpr (hχb (h • x)).2)
        (show 0 ≤ M.coreEnergyDensity h m f x+K*‖f x‖^2 by linarith [hK x])
      change χ (h • x)*M.coreEnergyDensity h m f x ≤
        M.coreEnergyDensity h m f x + K*(‖f x‖^2 - χ (h • x)*‖f x‖^2)
      nlinarith only [hp]
    _ = _ := by
      rw [integral_add (g := fun x => K*(‖f x‖^2 - χ (h • x)*‖f x‖^2)) hae ((hn.sub hwn).const_mul K),
        integral_const_mul,integral_sub (g := fun x => χ (h • x)*‖f x‖^2) hn hwn,
        M.coreEnergyDensity_integral,←coreToL2_norm_sq]
end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch
noncomputable section
open MeasureTheory Set
variable {N : ℕ} {M : AlgebraData N} {G : M.GaugeData} {q : Boson N}
variable (P : G.MeasuredNormalPatch q)
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2

def ambientEnergy (h : ℝ) (f : G.invariantCore) : ℝ :=
  ∫ x : Boson N, P.cutoff (h • x)*M.coreEnergyDensity h 1 f.val x

lemma ambientEnergy_eq (h : ℝ) (f : G.invariantCore) :
    P.ambientEnergy h f =
      (1/2 : ℝ)*(∫ x, P.cutoff (h • x)*kineticDensity f.val x) +
      (∫ x, P.cutoff (h • x)*M.bosonicDensity h 1 f.val x) +
      (∫ x, P.cutoff (h • x)*M.fermionicDensity h 1 f.val x) := by
  have hw : Continuous (fun x : Boson N => P.cutoff (h • x)) := P.cutoff_continuous.comp
    (Continuous.smul (M := ℝ) (X := Boson N) continuous_const continuous_id)
  have hk : Integrable (fun x => P.cutoff (h • x)*kineticDensity f.val x) := (hw.mul (kineticDensity_continuous f.val)).integrable_of_hasCompactSupport
    (kineticDensity_compactSupport f.val).mul_left
  have hb : Integrable (fun x => P.cutoff (h • x)*M.bosonicDensity h 1 f.val x) := (hw.mul (M.bosonicDensity_continuous h 1 f.val)).integrable_of_hasCompactSupport
    (M.bosonicDensity_compactSupport h 1 f.val).mul_left
  have hf : Integrable (fun x => P.cutoff (h • x)*M.fermionicDensity h 1 f.val x) := (hw.mul (M.fermionicDensity_continuous h 1 f.val)).integrable_of_hasCompactSupport
    (M.fermionicDensity_compactSupport h 1 f.val).mul_left
  unfold ambientEnergy AlgebraData.coreEnergyDensity
  simp only [mul_add]
  have he (x : Boson N) : P.cutoff (h • x)*((1/2 : ℝ)*kineticDensity f.val x) =
      (1/2 : ℝ)*(P.cutoff (h • x)*kineticDensity f.val x) := by ring
  simp_rw [he]
  rw [integral_add (g := fun x => P.cutoff (h • x)*M.bosonicDensity h 1 f.val x +
      P.cutoff (h • x)*M.fermionicDensity h 1 f.val x) (hk.const_mul (1/2 : ℝ)) (hb.add hf),
    integral_add hb hf,integral_const_mul]
  ring

lemma ambientEnergy_profile_eq (hN : 2 ≤ N) (hq : q ∈ M.massiveZeros)
    {h : ℝ} (hh : 0 < h) (f : G.invariantCore) :
    P.ambientEnergy h f =
      (1/2 : ℝ)*(∫ x, P.cutoff (h • x)*kineticDensity f.val x) +
      (∫ x : M.NormalCoordinates q, M.normalEffectivePotential q h
        (M.normalCoordinateIsometry q x : Boson N)*‖P.profile h f x‖^2) +
      (∫ x : M.NormalCoordinates q, inner ℝ (P.profile h f x)
        (M.deformedFermionField h 1 (h⁻¹ • q+(M.normalCoordinateIsometry q x : Boson N)) (P.profile h f x))) := by
  rw [P.ambientEnergy_eq,P.profile_bosonic_integral hN hq hh,P.profile_fermionic_integral hN hh]
end
end BFSSQuantum.AlgebraData.GaugeData.MeasuredNormalPatch

namespace BFSSQuantum.AlgebraData.GaugeData
noncomputable section
open MeasureTheory Finset Set Filter Topology
variable {N : ℕ} {M : AlgebraData N} (G : M.GaugeData)
variable {ι : Type*} [Fintype ι] (q : ι → Boson N) (P : (i : ι) → G.MeasuredNormalPatch (q i))
attribute [local irreducible] AlgebraData.normalSlice AlgebraData.gaugeAction coreToL2

theorem normalPatch_energy_comparison (hN : 2 ≤ N)
    (hd : Pairwise (fun i j => Disjoint (Function.support (P i).cutoff) (Function.support (P j).cutoff))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : G.invariantCore,
      (∑ i, (P i).ambientEnergy h f) ≤ M.deformedCoreEnergy h 1 f.val +
        K*(‖coreToL2 f.val‖^2 - ∑ i, ‖(P i).profile h f‖^2) := by
  classical
  obtain ⟨K,hK,hbound⟩ := M.coreEnergyDensity_uniform_lower hN
  refine ⟨K,hK,?_⟩
  intro h hh h1 f
  have hsm : Continuous (fun x : Boson N => h • x) :=
    Continuous.smul (M := ℝ) (X := Boson N) continuous_const continuous_id
  let χ : Boson N → ℝ := fun x => ∑ i, (P i).cutoff x
  have hχ : Continuous χ := continuous_finsetSum _ (fun i _ => (P i).cutoff_continuous)
  have hχb := (BFSSNormalMeasure.disjoint_cutoff_sum (fun i => (P i).cutoff)
    (fun i => (P i).cutoff_bounds) hd).1
  have he := M.cutoff_energy_le h 1 K f.val (hbound h hh h1 f.val) χ hχ hχb
  have hnorm : (∫ x, χ (h • x)*‖f.val x‖^2) = ∑ i, ‖(P i).profile h f‖^2 := by
    simp only [χ,sum_mul]
    rw [integral_finsetSum Finset.univ (f := fun i x => (P i).cutoff (h • x)*‖f.val x‖^2) (fun i _ => weighted_core_square_integrable _
      ((P i).cutoff_continuous.comp hsm) f.val)]
    apply Finset.sum_congr rfl
    intro i hi
    exact ((P i).profile_norm_eq hh h1 f).symm
  have henergy : (∫ x, χ (h • x)*M.coreEnergyDensity h 1 f.val x) = ∑ i, (P i).ambientEnergy h f := by
    simp only [χ,sum_mul,MeasuredNormalPatch.ambientEnergy]
    rw [integral_finsetSum]
    intro i hi
    exact (((P i).cutoff_continuous.comp
      hsm).mul
      (M.coreEnergyDensity_continuous h 1 f.val)).integrable_of_hasCompactSupport
        (M.coreEnergyDensity_compactSupport h 1 f.val).mul_left
  rwa [hnorm,henergy] at he
end
end BFSSQuantum.AlgebraData.GaugeData

end OAI
