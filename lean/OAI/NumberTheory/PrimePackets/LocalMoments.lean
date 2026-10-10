import Mathlib
import OAI.NumberTheory.PrimePackets.HaarBounds

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
namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators

 

theorem saturated_local_norm_moment (p : ℕ) [Fact p.Prime]
    {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)]
    [∀ i, IsDiscreteValuationRing (R i)] [∀ i, Algebra (PadicInt p) (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    {A : Type*} [AddGroup A] [TopologicalSpace A] [MeasurableSpace A]
    [OpensMeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (φ : ∀ i, A →+ R i) (hφ : ∀ i, Continuous (φ i))
    (hsat : ∀ i, Ideal.span (Set.range (φ i)) = ⊤)
    (e f : ι → ℕ) (he0 : ∀ i, 0 < e i) (hf0 : ∀ i, 0 < f i)
    (he : ∀ i, addVal (R i) (algebraMap (PadicInt p) (R i) p) = e i)
    (n : ℕ) (hn : 0 < n) (hdegree : ∑ i, f i * e i = n) :
    (∫⁻ x, ((p : ℝ≥0∞) ^ (∑ i, f i * (addVal (R i) (φ i x)).toNat)) ^
      (1 / (2 * (n : ℝ))) ∂μ) ≤
      1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p) := by
  have hM (i : ι) (k : ℕ) :
      MeasurableSet {x | φ i x ∈ IsLocalRing.maximalIdeal (R i) ^ k} :=
    ((IsLocalRing.isOpen_maximalIdeal_pow (R i) k).preimage (hφ i)).measurableSet
  have htail (i : ι) (k : ℕ) (_hk : 1 ≤ k) :
      μ {x | k ≤ (addVal (R i) (φ i x)).toNat} ≤
        (ENNReal.ofReal (p : ℝ))⁻¹ ^ (k ⌈/⌉ e i) := by
    simpa only [ENNReal.ofReal_natCast, ENNReal.inv_pow] using
      haar_natVal_projection_tail p μ (φ i) (hsat i) (e i) (he0 i) (he i) k (hM i k)
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  simpa only [ENNReal.ofReal_natCast] using
    local_norm_moment_of_valuation_tails μ e f he0 hf0 n hn hdegree
      (fun i x => (addVal (R i) (φ i x)).toNat)
      (fun i => measurable_dvr_natVal (hφ i)) p hp htail

 

theorem saturated_local_zero_components (p : ℕ) [Fact p.Prime]
    {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)]
    [∀ i, IsDiscreteValuationRing (R i)] [∀ i, Algebra (PadicInt p) (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    {A : Type*} [AddGroup A] [TopologicalSpace A] [MeasurableSpace A]
    [OpensMeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (φ : ∀ i, A →+ R i) (hφ : ∀ i, Continuous (φ i))
    (hsat : ∀ i, Ideal.span (Set.range (φ i)) = ⊤)
    (e : ι → ℕ) (he0 : ∀ i, 0 < e i)
    (he : ∀ i, addVal (R i) (algebraMap (PadicInt p) (R i) p) = e i) :
    μ {x | ∃ i, φ i x = 0} = 0 := by
  have hzero (i : ι) : μ {x | φ i x = 0} = 0 := by
    apply haar_dvr_zero_fiber p μ (φ i) (hsat i) (e i) (he0 i) (he i)
    intro k
    exact ((IsLocalRing.isOpen_maximalIdeal_pow (R i) k).preimage (hφ i)).measurableSet
  simpa only [Set.ofPred_exists] using measure_iUnion_null hzero

end PrimeDegreePackets


namespace PrimeDegreePackets

 
theorem haar_submodule_eq_inv_cardQuot {R A : Type*} [Ring R] [AddCommGroup A]
    [Module R A] [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (L : Submodule R A) [Finite (A ⧸ L)] (hL : MeasurableSet (L : Set A)) :
    μ (L : Set A) = (L.cardQuot : ℝ≥0∞)⁻¹ := by
  have : L.toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (inferInstanceAs (Finite (A ⧸ L)))
  have hc : (L.cardQuot : ℝ≥0∞) ≠ 0 := by
    rw [Submodule.cardQuot_apply]
    exact_mod_cast Nat.card_pos.ne'
  rw [← one_div (L.cardQuot : ℝ≥0∞)]
  apply (ENNReal.eq_div_iff hc (by simp)).mpr
  exact L.toAddSubgroup.index_mul_measure hL μ |>.trans (by simp)

section
variable {R A : Type*} [Ring R] [AddCommGroup A] [Module R A]
    [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (L : Submodule R A) [Finite (A ⧸ L)]

 
def normalizedSubmoduleHaar : Measure L :=
  (L.cardQuot : ℝ≥0∞) • μ.comap ((↑) : L → A)

lemma normalizedSubmoduleHaar_probability (hL : MeasurableSet (L : Set A)) :
    IsProbabilityMeasure (normalizedSubmoduleHaar μ L) := by
  constructor
  have hemb : MeasurableEmbedding ((↑) : L → A) :=
    MeasurableEmbedding.subtype_coe hL
  have hcmap : (μ.comap ((↑) : L → A)) univ = μ (L : Set A) := by
    rw [hemb.comap_apply]
    congr 1
    ext x
    simp
  rw [normalizedSubmoduleHaar, Measure.smul_apply, hcmap, smul_eq_mul,
    haar_submodule_eq_inv_cardQuot μ L hL]
  have hc : (L.cardQuot : ℝ≥0∞) ≠ 0 := by
    rw [Submodule.cardQuot_apply]
    exact_mod_cast Nat.card_pos.ne'
  exact ENNReal.mul_inv_cancel hc (by simp)

omit [IsProbabilityMeasure μ] [Finite (A ⧸ L)] in
lemma normalizedSubmoduleHaar_leftInvariant (hL : MeasurableSet (L : Set A)) :
    (normalizedSubmoduleHaar μ L).IsAddLeftInvariant := by
  let : MeasurableAdd L := {
    measurable_const_add := fun c => ((measurable_const_add (c : A)).comp measurable_subtype_coe).subtype_mk
    measurable_add_const := fun c => ((measurable_add_const (c : A)).comp measurable_subtype_coe).subtype_mk }
  have : (μ.comap L.subtype.toAddMonoidHom).IsAddLeftInvariant :=
    Measure.IsAddLeftInvariant.comap μ (MeasurableEmbedding.subtype_coe hL)
  exact isAddLeftInvariant_smul (μ := μ.comap L.subtype.toAddMonoidHom) _

omit [MeasurableAdd A] [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant] [Finite (A ⧸ L)] in
lemma lintegral_normalizedSubmoduleHaar (hL : MeasurableSet (L : Set A))
    (F : A → ℝ≥0∞) :
    ∫⁻ x : L, F x ∂normalizedSubmoduleHaar μ L =
      (L.cardQuot : ℝ≥0∞) * ∫⁻ x in (L : Set A), F x ∂μ := by
  have he : (∫⁻ x : L, F x ∂μ.comap ((↑) : L → A)) =
      ∫⁻ x in (L : Set A), F x ∂μ := lintegral_subtype_comap hL F
  rw [normalizedSubmoduleHaar, lintegral_smul_measure, he, smul_eq_mul]

omit [MeasurableAdd A] [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant] in
lemma ambient_lintegral_eq_normalized (hL : MeasurableSet (L : Set A))
    (F : A → ℝ≥0∞) :
    ∫⁻ x in (L : Set A), F x ∂μ =
      (L.cardQuot : ℝ≥0∞)⁻¹ * ∫⁻ x : L, F x ∂normalizedSubmoduleHaar μ L := by
  rw [lintegral_normalizedSubmoduleHaar μ L hL F, ← mul_assoc]
  have hc : (L.cardQuot : ℝ≥0∞) ≠ 0 := by
    rw [Submodule.cardQuot_apply]
    exact_mod_cast Nat.card_pos.ne'
  rw [ENNReal.inv_mul_cancel hc (by simp), one_mul]

end
end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators

lemma projection_saturation {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)]
    (p : ℕ) [Fact p.Prime] [∀ i, Algebra (PadicInt p) (R i)]
    (L : Submodule (PadicInt p) (∀ i, R i))
    (hsat : Ideal.span (L : Set (∀ i, R i)) = ⊤) (i : ι) :
    Ideal.span (Set.range (((Pi.evalRingHom R i).toAddMonoidHom).comp L.subtype.toAddMonoidHom)) = ⊤ := by
  have hmap := congrArg (Ideal.map (Pi.evalRingHom R i)) hsat
  rw [Ideal.map_span, Ideal.map_top] at hmap
  convert hmap using 1
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_image, AddMonoidHom.comp_apply,
    Pi.evalRingHom_apply]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, y.property, hy⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, hy⟩, hyx⟩

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Set IsDiscreteValuationRing
open scoped ENNReal BigOperators

 

theorem finite_index_saturated_module_norm_moment (p : ℕ) [Fact p.Prime]
    {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)]
    [∀ i, IsDiscreteValuationRing (R i)] [∀ i, Algebra (PadicInt p) (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, SecondCountableTopology (R i)]
    (μ : Measure (∀ i, R i)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (L : Submodule (PadicInt p) (∀ i, R i)) [Finite ((∀ i, R i) ⧸ L)]
    (hL : MeasurableSet (L : Set (∀ i, R i)))
    (hsat : Ideal.span (L : Set (∀ i, R i)) = ⊤)
    (e f : ι → ℕ) (he0 : ∀ i, 0 < e i) (hf0 : ∀ i, 0 < f i)
    (he : ∀ i, addVal (R i) (algebraMap (PadicInt p) (R i) p) = e i)
    (n : ℕ) (hn : 0 < n) (hdegree : ∑ i, f i * e i = n) :
    (∫⁻ x in (L : Set (∀ i, R i)), ((p : ℝ≥0∞) ^
       (∑ i, f i * (addVal (R i) (x i)).toNat)) ^ (1 / (2 * (n : ℝ))) ∂μ) ≤
      (L.cardQuot : ℝ≥0∞)⁻¹ *
        (1 + (n : ℝ≥0∞) * ENNReal.ofReal (4 / Real.sqrt p)) := by
  let ν := normalizedSubmoduleHaar μ L
  let : IsProbabilityMeasure ν := normalizedSubmoduleHaar_probability μ L hL
  let : ν.IsAddLeftInvariant := normalizedSubmoduleHaar_leftInvariant μ L hL
  let : MeasurableAdd L := {
    measurable_const_add := fun c => ((measurable_const_add (c : ∀ i, R i)).comp measurable_subtype_coe).subtype_mk
    measurable_add_const := fun c => ((measurable_add_const (c : ∀ i, R i)).comp measurable_subtype_coe).subtype_mk }
  rw [ambient_lintegral_eq_normalized μ L hL]
  apply mul_le_mul_right
  exact saturated_local_norm_moment p R ν
    (fun i => (Pi.evalRingHom R i).toAddMonoidHom.comp L.subtype.toAddMonoidHom)
    (fun i => (continuous_apply i).comp continuous_subtype_val)
    (projection_saturation R p L hsat)
    e f he0 hf0 he n hn hdegree

end PrimeDegreePackets

open MeasureTheory Set IsDiscreteValuationRing
namespace PrimeDegreePackets

section DVR
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [MeasurableSpace R] [MeasurableAdd R]
    [Finite (IsLocalRing.ResidueField R)]
    (μ : Measure R) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]

 
theorem haar_dvr_ideal_pow (k : ℕ)
    (hM : MeasurableSet ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R)) :
    μ ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) =
      ((Nat.card (IsLocalRing.ResidueField R) : ℝ≥0∞) ^ k)⁻¹ := by
  have : Finite (R ⧸ IsLocalRing.maximalIdeal R ^ k) :=
    IsLocalRing.finite_quotient_iff.mpr ⟨k, le_rfl⟩
  rw [haar_submodule_eq_inv_cardQuot μ _ hM, cardQuot_pow_of_prime]
  · rw [Nat.cast_pow]
    rfl
  · exact fun h => IsDiscreteValuationRing.not_isField R
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)

omit [MeasurableSpace R] [MeasurableAdd R] [Finite (IsLocalRing.ResidueField R)] in
 
lemma dvr_shell_eq_sdiff (k : ℕ) :
    {x : R | addVal R x = k} =
      ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) \
      ((IsLocalRing.maximalIdeal R ^ (k + 1) : Ideal R) : Set R) := by
  ext x
  simp only [Set.mem_sdiff, SetLike.mem_coe, mem_ofPred_eq, mem_maximalIdeal_pow_iff_addVal]
  induction addVal R x using ENat.recTopCoe with
  | top => simp
  | coe v => simp only [ENat.natCast_le_natCast, ENat.natCast_inj]; omega

 
theorem haar_dvr_shell (k : ℕ)
    (hM : ∀ k : ℕ, MeasurableSet ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R)) :
    μ {x : R | addVal R x = k} =
      (1 - (Nat.card (IsLocalRing.ResidueField R) : ℝ≥0∞)⁻¹) /
      (Nat.card (IsLocalRing.ResidueField R) : ℝ≥0∞) ^ k := by
  have hsub : ((IsLocalRing.maximalIdeal R ^ (k + 1) : Ideal R) : Set R) ⊆
      ((IsLocalRing.maximalIdeal R ^ k : Ideal R) : Set R) := by
    intro x hx
    change x ∈ IsLocalRing.maximalIdeal R ^ (k + 1) at hx
    change x ∈ IsLocalRing.maximalIdeal R ^ k
    rw [mem_maximalIdeal_pow_iff_addVal] at hx ⊢
    exact (ENat.natCast_le_natCast.mpr (Nat.le_succ k)).trans hx
  have hq : (Nat.card (IsLocalRing.ResidueField R) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rw [dvr_shell_eq_sdiff, measure_sdiff hsub (hM _).nullMeasurableSet (measure_ne_top μ _),
    haar_dvr_ideal_pow μ k (hM k), haar_dvr_ideal_pow μ (k + 1) (hM _),
    pow_succ, ENNReal.mul_inv (by simp) (by simp [hq]), div_eq_mul_inv, ENNReal.sub_mul (by simp [hq])]
  simp [mul_comm]

end DVR
end PrimeDegreePackets


namespace PrimeDegreePackets

section Algebra
variable {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)]
    [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]

 
def productDVRShell (k : ι → ℕ) : Set (∀ i, R i) :=
  {x | ∀ i, addVal (R i) (x i) = k i}

lemma productDVRShell_eq_pi (k : ι → ℕ) :
    productDVRShell R k = Set.univ.pi (fun i => {x : R i | addVal (R i) x = k i}) := by
  ext x
  simp [productDVRShell]

lemma productDVRShell_nonempty (k : ι → ℕ) : (productDVRShell R k).Nonempty := by
  choose π hπ using (fun i => exists_irreducible (R i))
  exact ⟨fun i => π i ^ k i, fun i => (hπ i).addVal_pow _⟩

lemma productDVRShell_smul_iff (k : ι → ℕ) (u : (∀ i, R i)ˣ) (x : ∀ i, R i) :
    u • x ∈ productDVRShell R k ↔ x ∈ productDVRShell R k := by
  have hu (i : ι) : addVal (R i) (u.val i) = 0 :=
    addVal_eq_zero_of_unit (MulEquiv.piUnits u i)
  change (∀ i, addVal (R i) (u.val i * x i) = k i) ↔ _
  simp only [addVal_mul, hu, zero_add]
  rfl

lemma productDVRShell_transitive (k : ι → ℕ) {x y : ∀ i, R i}
    (hx : x ∈ productDVRShell R k) (hy : y ∈ productDVRShell R k) :
    ∃ u : (∀ i, R i)ˣ, u • x = y := by
  have h (i : ι) : Associated (x i) (y i) :=
    (addVal_eq_iff_associated _ _).mp ((hx i).trans (hy i).symm)
  choose u hu using h
  refine ⟨MulEquiv.piUnits.symm u, ?_⟩
  funext i
  change (u i : R i) * x i = y i
  simpa only [mul_comm] using hu i

lemma productDVRShell_pairwiseDisjoint : Pairwise (fun k l => Disjoint (productDVRShell R k) (productDVRShell R l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hl
  apply hkl
  funext i
  exact ENat.natCast_inj.mp ((hx i).symm.trans (hl i))

lemma mem_iUnion_productDVRShell_iff (x : ∀ i, R i) :
    x ∈ ⋃ k : ι → ℕ, productDVRShell R k ↔ ∀ i, x i ≠ 0 := by
  simp only [mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩ i hi
    have := hk i
    rw [hi, addVal_zero] at this
    exact ENat.top_ne_natCast (k i) this
  · intro hx
    refine ⟨fun i => (addVal (R i) (x i)).toNat, ?_⟩
    intro i
    exact (ENat.natCast_toNat (fun h => hx i (addVal_eq_top_iff.mp h))).symm

end Algebra

section Measurability
variable {ι : Type*} [Fintype ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] [∀ i, IsDomain (R i)] [∀ i, IsDiscreteValuationRing (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, CompactSpace (R i)] [∀ i, T2Space (R i)]
    [∀ i, MeasurableSpace (R i)] [∀ i, BorelSpace (R i)]

omit [Fintype ι] in
lemma measurableSet_dvr_shell (i : ι) (k : ℕ) :
    MeasurableSet {x : R i | addVal (R i) x = k} := by
  have hset : {x : R i | addVal (R i) x = k} =
      ((IsLocalRing.maximalIdeal (R i) ^ k : Ideal (R i)) : Set (R i)) \
      ((IsLocalRing.maximalIdeal (R i) ^ (k + 1) : Ideal (R i)) : Set (R i)) := by
    ext x
    simp only [Set.mem_sdiff, SetLike.mem_coe, mem_ofPred_eq, mem_maximalIdeal_pow_iff_addVal]
    induction addVal (R i) x using ENat.recTopCoe with
    | top => simp
    | coe v => simp only [ENat.natCast_le_natCast, ENat.natCast_inj]; omega
  rw [hset]
  exact (IsLocalRing.isOpen_maximalIdeal_pow (R i) k).measurableSet.diff
    (IsLocalRing.isOpen_maximalIdeal_pow (R i) (k + 1)).measurableSet

lemma measurableSet_productDVRShell (k : ι → ℕ) : MeasurableSet (productDVRShell R k) := by
  rw [productDVRShell_eq_pi]
  exact MeasurableSet.univ_pi (fun i => measurableSet_dvr_shell R i (k i))

end Measurability
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

def shellNorm (k : ι → ℕ) : ℝ≥0∞ :=
  ∏ i, (Nat.card (IsLocalRing.ResidueField (R i)) : ℝ≥0∞) ^ k i

def localZinv : ℝ≥0∞ :=
  ∏ i, (1 - (Nat.card (IsLocalRing.ResidueField (R i)) : ℝ≥0∞)⁻¹)

lemma product_shell_mass
    (μ : ∀ i, Measure (R i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, (μ i).IsAddLeftInvariant] (k : ι → ℕ) :
    Measure.pi μ (productDVRShell R k) = localZinv R / shellNorm R k := by
  rw [productDVRShell_eq_pi, Measure.pi_pi]
  have hM (i : ι) (j : ℕ) :
      MeasurableSet ((IsLocalRing.maximalIdeal (R i) ^ j : Ideal (R i)) : Set (R i)) :=
    (IsLocalRing.isOpen_maximalIdeal_pow (R i) j).measurableSet
  simp_rw [haar_dvr_shell _ _ (hM _)]
  exact ENNReal.prod_div_distrib_of_ne_top (by simp)

omit [∀ i, BorelSpace (R i)] [∀ i, MeasurableSpace (R i)] in
lemma localZinv_ne_zero : localZinv R ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have hq : (1 : ℝ≥0∞) < Nat.card (IsLocalRing.ResidueField (R i)) := by
    let := Fintype.ofFinite (IsLocalRing.ResidueField (R i))
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card (IsLocalRing.ResidueField (R i)))
  apply ne_of_gt
  exact tsub_pos_iff_lt.mpr (ENNReal.inv_lt_one.mpr hq)

omit [∀ i, IsTopologicalRing (R i)] [∀ i, CompactSpace (R i)]
    [∀ i, T2Space (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, MeasurableSpace (R i)] in
lemma localZinv_ne_top : localZinv R ≠ ∞ := by
  apply ENNReal.prod_ne_top
  intro i _
  exact ne_of_lt ((tsub_le_self).trans_lt (by simp))

omit [∀ i, BorelSpace (R i)] [∀ i, MeasurableSpace (R i)] in
lemma shellNorm_ne_zero (k : ι → ℕ) : shellNorm R k ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply pow_ne_zero
  exact_mod_cast (Nat.card_pos : 0 < Nat.card (IsLocalRing.ResidueField (R i))).ne'

omit [∀ i, IsTopologicalRing (R i)] [∀ i, CompactSpace (R i)]
    [∀ i, T2Space (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, MeasurableSpace (R i)] in
lemma shellNorm_ne_top (k : ι → ℕ) : shellNorm R k ≠ ∞ := by
  apply ENNReal.prod_ne_top
  intro i _
  exact ENNReal.pow_ne_top (by simp)

omit [∀ i, IsTopologicalRing (R i)] [∀ i, CompactSpace (R i)]
    [∀ i, T2Space (R i)] [∀ i, BorelSpace (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, MeasurableSpace (R i)] in
lemma shellNorm_eq_prime_pow (p : ℕ) (f k : ι → ℕ)
    (hcard : ∀ i, Nat.card (IsLocalRing.ResidueField (R i)) = p ^ f i) :
    shellNorm R k = (p : ℝ≥0∞) ^ (∑ i, f i * k i) := by
  simp only [shellNorm, hcard, Nat.cast_pow, ← pow_mul]
  exact Finset.prod_pow_eq_pow_sum Finset.univ (fun i => f i * k i) (p : ℝ≥0∞)

end
end PrimeDegreePackets
end
end

end OAI
