import Mathlib
import OAI.NumberTheory.PrimePackets.LocalMoments
import OAI.NumberTheory.PrimePackets.PacketAlgebra

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing Filter
open scoped ENNReal

 
theorem haar_dvr_zero {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    [MeasurableSpace R] [MeasurableAdd R]
    (μ : Measure R) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (hM : ∀ k : ℕ, MeasurableSet ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R)) :
    μ {0} = 0 := by
  let := Fintype.ofFinite (IsLocalRing.ResidueField R)
  have hq : (1 : ℝ≥0∞) < Nat.card (IsLocalRing.ResidueField R) := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card (IsLocalRing.ResidueField R))
  have hlim := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.mpr hq)
  apply le_antisymm _ zero_le
  apply ge_of_tendsto' hlim
  intro k
  calc
    μ {0} ≤ μ ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) := by
      apply measure_mono
      intro x hx
      simp only [mem_singleton_iff] at hx
      simp [hx]
    _ = _ := by rw [haar_dvr_ideal_pow μ k (hM k), ENNReal.inv_pow]

end PrimeDegreePackets


namespace PrimeDegreePackets

section Action
variable {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [MeasurableSpace X] [MulAction G X] [MeasurableSMul₂ G X]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]

 

def orbitContainmentProbability (L : Set X) (x : X) : ℝ≥0∞ :=
  ∫⁻ g, L.indicator (fun _ => (1 : ℝ≥0∞)) (g • x) ∂ν

omit [MeasurableMul G] [IsProbabilityMeasure ν] [ν.IsMulRightInvariant] in
lemma orbitContainmentProbability_eq_measure (L : Set X) (hL : MeasurableSet L) (x : X) :
    orbitContainmentProbability ν L x = ν {g : G | g • x ∈ L} := by
  unfold orbitContainmentProbability
  have heq : (fun (g : G) => L.indicator (fun _ => (1 : ℝ≥0∞)) (g • x)) =
      {g : G | g • x ∈ L}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    rfl
  rw [heq]
  exact lintegral_indicator_fun_one (hL.preimage (measurable_id.smul_const x))

omit [MeasurableSpace X] [MeasurableSMul₂ G X] [IsProbabilityMeasure ν] in
lemma orbitContainmentProbability_smul (L : Set X) (x : X) (g : G) :
    orbitContainmentProbability ν L (g • x) = orbitContainmentProbability ν L x := by
  unfold orbitContainmentProbability
  simp_rw [← mul_smul]
  exact lintegral_mul_right_eq_self (fun h => L.indicator (fun _ => (1 : ℝ≥0∞)) (h • x)) g

 

theorem orbitContainmentProbability_mul_shell_measure
    (μ : Measure X) [IsFiniteMeasure μ] [SMulInvariantMeasure G X μ]
    (S L : Set X) (hS : MeasurableSet S) (hL : MeasurableSet L)
    (hinv : ∀ (g : G) (x : X), g • x ∈ S ↔ x ∈ S)
    (x₀ : X) (htrans : ∀ x ∈ S, ∃ g : G, g • x₀ = x) :
    orbitContainmentProbability ν L x₀ * μ S = μ (L ∩ S) := by
  have hconstant (x : X) (hx : x ∈ S) :
      orbitContainmentProbability ν L x = orbitContainmentProbability ν L x₀ := by
    obtain ⟨g, rfl⟩ := htrans x hx
    exact orbitContainmentProbability_smul ν L x₀ g
  have hfun : Measurable (fun (z : X × G) =>
      L.indicator (fun _ => (1 : ℝ≥0∞)) (z.2 • z.1)) :=
    (measurable_const.indicator hL).comp (measurable_snd.smul measurable_fst)
  calc
    orbitContainmentProbability ν L x₀ * μ S =
        ∫⁻ x in S, orbitContainmentProbability ν L x ∂μ := by
      rw [← setLIntegral_const]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hS] with x hx
      exact (hconstant x hx).symm
    _ = ∫⁻ g, ∫⁻ x in S, L.indicator (fun _ => (1 : ℝ≥0∞)) (g • x) ∂μ ∂ν :=
      lintegral_lintegral_swap hfun.aemeasurable
    _ = ∫⁻ _g, μ (L ∩ S) ∂ν := by
      apply lintegral_congr
      intro g
      have heq : (fun x => L.indicator (fun _ => (1 : ℝ≥0∞)) (g • x)) =
          ((g • ·) ⁻¹' L).indicator (fun _ => (1 : ℝ≥0∞)) := by
        ext x
        rfl
      rw [heq, show (fun _ : X => (1 : ℝ≥0∞)) = (1 : X → ℝ≥0∞) from rfl,
        lintegral_indicator_one (hL.preimage (measurable_const_smul g)),
        Measure.restrict_apply (hL.preimage (measurable_const_smul g))]
      have hset : (g • ·) ⁻¹' L ∩ S = (g • ·) ⁻¹' (L ∩ S) := by
        ext x
        simp only [mem_inter_iff, mem_preimage, hinv]
      rw [hset, measure_preimage_smul]
    _ = μ (L ∩ S) := by simp

end Action
end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem lintegral_eq_tsum_shells {X κ : Type*} [MeasurableSpace X] [Countable κ]
    (μ : Measure X) (S : κ → Set X) (hS : ∀ k, MeasurableSet (S k))
    (hdisj : Pairwise (fun k l => Disjoint (S k) (S l)))
    (hfull : μ (⋃ k, S k)ᶜ = 0)
    (F : X → ℝ≥0∞) (w : κ → ℝ≥0∞) (hF : ∀ k x, x ∈ S k → F x = w k) :
    ∫⁻ x, F x ∂μ = ∑' k, w k * μ (S k) := by
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ k, S k := by
    rw [ae_iff]
    exact hfull
  calc
    _ = ∫⁻ x in ⋃ k, S k, F x ∂μ := by
      rw [Measure.restrict_eq_self_of_ae_mem hae]
    _ = ∑' k, ∫⁻ x in S k, F x ∂μ := lintegral_iUnion hS hdisj F
    _ = _ := by
      apply tsum_congr
      intro k
      rw [← setLIntegral_const]
      apply setLIntegral_congr_fun (hS k)
      exact hF k

 
theorem restricted_lintegral_eq_tsum_shells {X κ : Type*}
    [MeasurableSpace X] [Countable κ]
    (μ : Measure X) (S : κ → Set X) (hS : ∀ k, MeasurableSet (S k))
    (hdisj : Pairwise (fun k l => Disjoint (S k) (S l)))
    (hfull : μ (⋃ k, S k)ᶜ = 0)
    (L : Set X) (F : X → ℝ≥0∞) (w : κ → ℝ≥0∞)
    (hF : ∀ k x, x ∈ S k → F x = w k) :
    ∫⁻ x in L, F x ∂μ = ∑' k, w k * μ (L ∩ S k) := by
  have hr : (μ.restrict L) (⋃ k, S k)ᶜ = 0 :=
    le_antisymm ((Measure.restrict_le_self (μ := μ) (s := L) _).trans hfull.le) zero_le
  have he := lintegral_eq_tsum_shells (μ.restrict L) S hS hdisj hr F w hF
  simpa only [Measure.restrict_apply (hS _), inter_comm] using he

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma units_smulInvariant_addHaar {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
    [MeasurableSpace R] [BorelSpace R]
    (μ : Measure R) [μ.IsAddHaarMeasure] : SMulInvariantMeasure Rˣ R μ := by
  constructor
  intro u S hS
  let f : R ≃ₗ[R] R := LinearEquiv.smulOfUnit u
  have hf : MeasurePreserving f μ μ :=
    f.toAddMonoidHom.measurePreserving (by
      change Continuous (fun x : R => (u : R) * x)
      fun_prop) f.surjective rfl
  exact hf.measure_preimage hS.nullMeasurableSet

lemma measurableSMul_units {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
    [MeasurableSpace R] [BorelSpace R]
    [MeasurableSpace Rˣ] [BorelSpace Rˣ] : MeasurableSMul₂ Rˣ R := by
  infer_instance

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators
section
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]

lemma productDVRShell_full_measure
    (μ : ∀ i, Measure (R i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsAddLeftInvariant] :
    Measure.pi μ (⋃ k : ι → ℕ, productDVRShell R k)ᶜ = 0 := by
  have hzero (i : ι) : μ i {0} = 0 :=
    haar_dvr_zero (μ i) (fun k => (IsLocalRing.isOpen_maximalIdeal_pow (R i) k).measurableSet)
  have hnull (i : ι) : Measure.pi μ {x : ∀ i, R i | x i = 0} = 0 :=
    Measure.pi_eval_preimage_null μ (hzero i)
  have hset : (⋃ k : ι → ℕ, productDVRShell R k)ᶜ = ⋃ i, {x : ∀ i, R i | x i = 0} := by
    ext x
    rw [mem_compl_iff, mem_iUnion_productDVRShell_iff R x]
    simp
  rw [hset]
  exact measure_iUnion_null hnull

 

def localShellProbability
    [MeasurableSpace (∀ i, R i)ˣ]
    (ν : Measure (∀ i, R i)ˣ) (L : Set (∀ i, R i)) (k : ι → ℕ) : ℝ≥0∞ :=
  orbitContainmentProbability ν L (productDVRShell_nonempty R k).choose

end
end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators
section
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, SecondCountableTopology (R i)]
    [MeasurableSpace (∀ i, R i)ˣ] [BorelSpace (∀ i, R i)ˣ]
    (μ : ∀ i, Measure (R i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsAddHaarMeasure]
    (ν : Measure (∀ i, R i)ˣ) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]

lemma localShellProbability_mul_mass (L : Set (∀ i, R i)) (hL : MeasurableSet L)
    (k : ι → ℕ) :
    localShellProbability R ν L k * (localZinv R / shellNorm R k) =
      Measure.pi μ (L ∩ productDVRShell R k) := by
  let : SMulInvariantMeasure (∀ i, R i)ˣ (∀ i, R i) (Measure.pi μ) :=
    units_smulInvariant_addHaar (Measure.pi μ)
  rw [← product_shell_mass R μ k]
  apply orbitContainmentProbability_mul_shell_measure ν (Measure.pi μ)
    (productDVRShell R k) L (measurableSet_productDVRShell R k) hL
    (productDVRShell_smul_iff R k)
  intro x hx
  exact productDVRShell_transitive R k (productDVRShell_nonempty R k).choose_spec hx

 
theorem local_weight_integral_identity (L : Set (∀ i, R i)) (hL : MeasurableSet L)
    (s : ℝ) :
    (∫⁻ x in L, shellNorm R (fun i => (addVal (R i) (x i)).toNat) ^ s ∂Measure.pi μ) =
      localZinv R * ∑' k : ι → ℕ,
        localShellProbability R ν L k * shellNorm R k ^ (s - 1) := by
  rw [restricted_lintegral_eq_tsum_shells (Measure.pi μ) (productDVRShell R)
    (measurableSet_productDVRShell R) (productDVRShell_pairwiseDisjoint R)
    (productDVRShell_full_measure R μ) L _ (fun k => shellNorm R k ^ s) (by
      intro k x hx
      congr 2
      funext i
      rw [hx i, ENat.toNat_natCast])]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro k
  rw [← localShellProbability_mul_mass R μ ν L hL k,
    ENNReal.rpow_sub s 1 (shellNorm_ne_zero R k) (shellNorm_ne_top R k),
    ENNReal.rpow_one, div_eq_mul_inv, div_eq_mul_inv]
  ac_rfl

end
end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators
section
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, SecondCountableTopology (R i)]
    [MeasurableSpace (∀ i, R i)ˣ] [BorelSpace (∀ i, R i)ˣ]
    (μ : ∀ i, Measure (R i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsAddHaarMeasure]
    (ν : Measure (∀ i, R i)ˣ) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]

include μ in
 
theorem local_weight_sum (p : ℕ) [Fact p.Prime] [∀ i, Algebra (PadicInt p) (R i)]
    (L : Submodule (PadicInt p) (∀ i, R i)) [Finite ((∀ i, R i) ⧸ L)]
    (hL : MeasurableSet (L : Set (∀ i, R i))) :
    (∑' k : ι → ℕ, localShellProbability R ν L k / shellNorm R k) =
      (L.cardQuot : ℝ≥0∞)⁻¹ / localZinv R := by
  apply (ENNReal.eq_div_iff (localZinv_ne_zero R) (localZinv_ne_top R)).mpr
  have hid := local_weight_integral_identity R μ ν L hL 0
  simpa only [ENNReal.rpow_zero, lintegral_one, Measure.restrict_apply_univ,
    haar_submodule_eq_inv_cardQuot (Measure.pi μ) L hL, zero_sub,
    ENNReal.rpow_neg_one, div_eq_mul_inv] using hid.symm

include μ in
 

theorem local_weight_moment (p : ℕ) [Fact p.Prime] [∀ i, Algebra (PadicInt p) (R i)]
    (L : Submodule (PadicInt p) (∀ i, R i)) [Finite ((∀ i, R i) ⧸ L)]
    (hL : MeasurableSet (L : Set (∀ i, R i)))
    (hsat : Ideal.span (L : Set (∀ i, R i)) = ⊤)
    (e f : ι → ℕ) (he0 : ∀ i, 0 < e i) (hf0 : ∀ i, 0 < f i)
    (he : ∀ i, addVal (R i) (algebraMap (PadicInt p) (R i) p) = e i)
    (hcard : ∀ i, Nat.card (IsLocalRing.ResidueField (R i)) = p ^ f i)
    (n : ℕ) (hn : 0 < n) (hdegree : ∑ i, f i * e i = n) :
    (∑' k : ι → ℕ,
      localShellProbability R ν L k * shellNorm R k ^ (1 / (2 * (n : ℝ)) - 1)) ≤
      (L.cardQuot : ℝ≥0∞)⁻¹ * ((localZinv R)⁻¹ *
        (1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p))) := by
  have hid := local_weight_integral_identity R μ ν L hL (1 / (2 * (n : ℝ)))
  have hmoment := finite_index_saturated_module_norm_moment p R (Measure.pi μ)
    L hL hsat e f he0 hf0 he n hn hdegree
  have hm : (∫⁻ x in (L : Set (∀ i, R i)),
      shellNorm R (fun i => (addVal (R i) (x i)).toNat) ^ (1 / (2 * (n : ℝ)))
        ∂Measure.pi μ) ≤ (L.cardQuot : ℝ≥0∞)⁻¹ *
      (1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p)) := by
    simpa only [shellNorm_eq_prime_pow R p f _ hcard] using hmoment
  have heq := (ENNReal.eq_div_iff (localZinv_ne_zero R) (localZinv_ne_top R)).mpr hid.symm
  rw [heq]
  calc
    _ ≤ ((L.cardQuot : ℝ≥0∞)⁻¹ *
      (1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p))) / localZinv R :=
      ENNReal.div_le_div hm le_rfl
    _ = _ := by simp only [div_eq_mul_inv]; ac_rfl

end
end PrimeDegreePackets

open Filter
open scoped BigOperators Topology
namespace PrimeDegreePackets

def localMajorant (n p : ℕ) : ℝ :=
  ((1 - (p : ℝ)⁻¹) ^ n)⁻¹ * (1 + 4 * n / Real.sqrt p)

lemma localMajorant_nonneg (n p : ℕ) (hp : 1 ≤ p) : 0 ≤ localMajorant n p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hi : (p : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hp0).mpr hp1
  unfold localMajorant
  positivity

lemma localMajorant_tendsto_one (n : ℕ) :
    Tendsto (localMajorant n) atTop (𝓝 1) := by
  have hcast : Tendsto (fun p : ℕ => (p : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun p : ℕ => (p : ℝ)⁻¹) atTop (𝓝 0) := hcast.inv_tendsto_atTop
  have hs : Tendsto (fun p : ℕ => (Real.sqrt (p : ℝ))⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp hcast).inv_tendsto_atTop
  have ha := ((tendsto_const_nhds.sub hi).pow n).inv₀ (by simp : (1 - (0 : ℝ)) ^ n ≠ 0)
  have hb : Tendsto (fun p : ℕ => 1 + (4 * n) * (Real.sqrt (p : ℝ))⁻¹)
      atTop (𝓝 (1 + (4 * n) * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hs)
  change Tendsto (fun p : ℕ => ((1 - (p : ℝ)⁻¹) ^ n)⁻¹ *
    (1 + 4 * (n : ℝ) / Real.sqrt p)) atTop (𝓝 1)
  simpa [div_eq_mul_inv] using ha.mul hb

 

theorem finite_product_subpolynomial (f : ℕ → ℝ)
    (hf0 : ∀ p, 1 ≤ p → 0 ≤ f p) (hf : Tendsto f atTop (𝓝 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Finset ℕ, (∀ p ∈ S, 1 ≤ p) →
      (∏ p ∈ S, f p) ≤ C * (∏ p ∈ S, (p : ℝ)) ^ ε := by
  have hlarge : ∀ᶠ p : ℕ in atTop, f p ≤ (p : ℝ) ^ ε := by
    have hpow : Tendsto (fun p : ℕ => (p : ℝ) ^ ε) atTop atTop :=
      (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
    filter_upwards [hf.eventually_le_const (by norm_num : (1 : ℝ) < 2),
      hpow.eventually (eventually_ge_atTop (2 : ℝ))] with p hfp hpp
    exact hfp.trans hpp
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  let g : ℕ → ℝ := fun p => max 1 (f p)
  have hg : ∀ p, 1 ≤ g p := fun p => le_max_left _ _
  have hgpos : ∀ p, 0 < g p := fun p => lt_of_lt_of_le zero_lt_one (hg p)
  refine ⟨∏ p ∈ Finset.range N, g p, Finset.prod_pos (fun p _ => hgpos p), ?_⟩
  intro S hS
  have hpow : ∀ p ∈ S, 1 ≤ (p : ℝ) ^ ε := by
    intro p hp
    exact Real.one_le_rpow (by exact_mod_cast hS p hp) hε.le
  calc
    (∏ p ∈ S, f p) ≤ ∏ p ∈ S, (if p < N then g p else 1) * (p : ℝ) ^ ε := by
      apply Finset.prod_le_prod₀ (fun p hp => hf0 p (hS p hp))
      intro p hp
      by_cases hpN : p < N
      · simp only [ite_eq_left hpN]
        exact (le_max_right 1 (f p)).trans (le_mul_of_one_le_right (hgpos p).le (hpow p hp))
      · simpa only [ite_eq_right hpN, one_mul] using hN p (Nat.le_of_not_gt hpN)
    _ = (∏ p ∈ S with p < N, g p) * (∏ p ∈ S, (p : ℝ) ^ ε) := by
      rw [Finset.prod_mul_distrib, ← Finset.prod_filter]
    _ ≤ (∏ p ∈ Finset.range N, g p) * (∏ p ∈ S, (p : ℝ) ^ ε) := by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun p hp => (hpow p hp).trans' zero_le_one))
      apply Finset.prod_le_prod_of_subset_of_one_le₀
      · intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      · intro p _
        exact (hgpos p).le
      · intro p _ _
        exact hg p
    _ = (∏ p ∈ Finset.range N, g p) * (∏ p ∈ S, (p : ℝ)) ^ ε := by
      congr 1
      exact Real.finsetProd_rpow S _ (fun p _ => Nat.cast_nonneg p) ε

 

theorem localMajorant_product_le (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (q : ℝ),
      (∀ p ∈ S, 1 ≤ p) → (∏ p ∈ S, (p : ℝ)) ≤ q →
      (∏ p ∈ S, localMajorant n p) ≤ C * q ^ ε := by
  obtain ⟨C, hC, hprod⟩ := finite_product_subpolynomial (localMajorant n)
    (localMajorant_nonneg n) (localMajorant_tendsto_one n) ε hε
  refine ⟨C, hC, ?_⟩
  intro S q hS hq
  apply (hprod S hS).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)) hq hε.le

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma localZinv_inv_le {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)] (p n : ℕ) (f : ι → ℕ) (hf : ∀ i, 0 < f i)
    (hcard : ∀ i, Nat.card (IsLocalRing.ResidueField (R i)) = p ^ f i)
    (hnum : Fintype.card ι ≤ n) :
    (localZinv R)⁻¹ ≤ ((1 - (p : ℝ≥0∞)⁻¹) ^ n)⁻¹ := by
  apply ENNReal.inv_le_inv.mpr
  calc
    _ ≤ (1 - (p : ℝ≥0∞)⁻¹) ^ Fintype.card ι :=
      pow_le_pow_of_le_one zero_le tsub_le_self hnum
    _ = ∏ _i : ι, (1 - (p : ℝ≥0∞)⁻¹) := by simp
    _ ≤ localZinv R := by
      apply Finset.prod_le_prod
      intro i _
      apply tsub_le_tsub_left
      apply ENNReal.inv_le_inv.mpr
      exact_mod_cast (hcard i ▸ Nat.le_pow (hf i) : p ≤ Nat.card (IsLocalRing.ResidueField (R i)))

lemma localEulerFactor_le_majorant {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)] (p n : ℕ) (hp : 1 < p)
    (f : ι → ℕ) (hf : ∀ i, 0 < f i)
    (hcard : ∀ i, Nat.card (IsLocalRing.ResidueField (R i)) = p ^ f i)
    (hnum : Fintype.card ι ≤ n) :
    (localZinv R)⁻¹ * (1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p)) ≤
      ENNReal.ofReal (localMajorant n p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hi : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr ((inv_lt_one₀ hp0).mpr hp1)
  have hbase : ENNReal.ofReal (1 - (p : ℝ)⁻¹) = 1 - (p : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_inv_of_pos hp0, ENNReal.ofReal_natCast]
  calc
    _ ≤ ((1 - (p : ℝ≥0∞)⁻¹) ^ n)⁻¹ *
      (1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p)) :=
        mul_le_mul_left (localZinv_inv_le R p n f hf hcard hnum) _
    _ = ENNReal.ofReal (localMajorant n p) := by
      unfold localMajorant
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (pow_pos hi n),
        ENNReal.ofReal_pow hi.le, hbase,
        ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_one]
      congr 2
      rw [show 4 * (n : ℝ) / Real.sqrt p = n * (4 / Real.sqrt p) by ring,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

end PrimeDegreePackets
end
end

end OAI
