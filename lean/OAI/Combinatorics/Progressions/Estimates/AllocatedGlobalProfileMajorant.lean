import OAI.Combinatorics.Progressions.Probability.AllocatedProbabilityProfileMass
import OAI.Combinatorics.Progressions.Probability.AllocatedProbabilityWindowMesh
import OAI.Combinatorics.Progressions.Probability.AllocatedSiteWindowProbability
import OAI.Combinatorics.Progressions.Probability.AllocatedWindowProbability

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "longScale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)
local notation "covolumes" => (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (O j))

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter

local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

omit [Fintype α] in
theorem allocatedGridlessWindow_le_profile_majorant
    (selected : {a // allocatedGridAxis (I := I) U b S.value a} → Prop) [DecidablePred selected]
    (W : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, Finset (CoefficientJetAxisRow O a.val))
    (p : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, PMF (CoefficientJetAxisRow O a.val))
    (hW : ∀ a, selected a → (W a).Nonempty)
    (F : AllocatedLongJetRows B U b S O → ℝ) (A : ℝ≥0) (f g : (output → ℝ) → ℝ)
    (hF : ∀ z (r : ∀ j, O j → Q j → ZMod d),
      coefficientDeckJetDensity root dirs rows d r * |F z| ≤
        (A : ℝ) * |f (allocatedLongJetRealCoordinates B U b S z) -
          g (allocatedLongJetRealCoordinates B U b S z)| / longScale)
    (y : EuclideanJetLayers U O) :
    |allocatedChartGridMultiplier B U b S O hb o bW d
        (allocatedGridWindowWeight B U b S O selected W p) y *
      allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d F y| ≤
      (∏ a : {a // allocatedGridAxis (I := I) U b S.value a},
        if selected a then ((W a).card : ℝ) else 1) *
      allocatedProbabilityProfileMajorant B U b S o
        (allocatedGridWindowPMF B U b S O selected W p hW) A f g d y := by
  let weight := allocatedGridWindowWeight B U b S O selected W p
  let aux := allocatedGridWindowPMF B U b S O selected W p hW
  let N : ℝ := ∏ a : {a // allocatedGridAxis (I := I) U b S.value a},
    if selected a then ((W a).card : ℝ) else 1
  have hc := coveredJetArrayScale_pos (O := O) U
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    have hquarter : ∀ a, |mixedJetAmbientPoint U b o z.1 a| ≤ 1 / 4 := by
      intro a
      exact (hz a.1 (mem_univ _) a.2.1 (mem_univ _)).1 a.2.2
    rw [allocatedChartGridMultiplier_apply B U b S O hb o bW d weight z hz,
      allocatedGridlessCoveredProfile,
      restrictedChartDensity_apply chart region 1 _
        (mixedCoveredJetChart_injOn U o b hb bW d quarter
          (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz,
      one_mul]
    change _ ≤ N * allocatedProbabilityProfileTorusKernel B U b S o aux A f g
      (coveredJetAmbientTorus U d (chart z))
    rw [coveredJetAmbientTorus_chart, allocatedProbabilityProfileTorusKernel,
      smallBoxTorusKernel_local _ (allocatedProbabilityProfileAmbientKernel_support B U b S o aux A f g)
        _ (fun a => lt_of_le_of_lt (hquarter a) (by norm_num)),
      allocatedProbabilityProfileAmbientKernel_point, allocatedProbabilityProfileRawDensity,
      smallBoxCutoff_one _ hquarter, mul_one]
    have hw := allocatedGridWindowWeight_nonneg B U b S O selected W p
      ((coefficientJetAxisSplit O I n grid z.1).1)
    have hd := coefficientDeckJetDensity_nonneg root dirs rows d z.2
    rw [abs_mul, abs_of_nonneg hw, abs_mul, abs_div, abs_of_nonneg hd, abs_of_pos hc]
    calc
      _ = weight ((coefficientJetAxisSplit O I n grid z.1).1) *
          (coefficientDeckJetDensity root dirs rows d z.2 *
            |F ((coefficientJetAxisSplit O I n grid z.1).2)|) / coveredJetArrayScale (O := O) U := by ring
      _ ≤ weight ((coefficientJetAxisSplit O I n grid z.1).1) *
          ((A : ℝ) * |f (allocatedLongJetRealCoordinates B U b S ((coefficientJetAxisSplit O I n grid z.1).2)) -
            g (allocatedLongJetRealCoordinates B U b S ((coefficientJetAxisSplit O I n grid z.1).2))| / longScale) /
          coveredJetArrayScale (O := O) U :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hF _ _) hw) hc.le
      _ = _ := by
        dsimp only [weight]
        rw [allocatedGridWindowWeight_eq_probability B U b S O selected W p hW]
        change (N * allocatedProbabilityGridDensity B U b S aux
          (fun a => coefficientJetAxisEquiv O I n z.1 a.val)) *
          ((A : ℝ) * |f (allocatedLongJetRealCoordinates B U b S
              (fun a => coefficientJetAxisEquiv O I n z.1 a.val)) -
            g (allocatedLongJetRealCoordinates B U b S
              (fun a => coefficientJetAxisEquiv O I n z.1 a.val))| / longScale) /
          coveredJetArrayScale (O := O) U = _
        ring
  · rw [allocatedGridlessCoveredProfile, restrictedChartDensity_zero chart region 1 _ hy,
      mul_zero, abs_zero]
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun a _ => by split_ifs <;> positivity)
    · exact allocatedProbabilityProfileMajorant_nonneg B U b S o aux hb bW d A f g y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical NNReal

universe uα

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] activeAmbientAxisDecidableEq

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d]
variable (x : G → IntegerScalarCubeBox α S.value) (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "activeAxes" => {a : {a // grid a} // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "siteH" => (fun a : activeAxes => allocatedNaturalSiteRadius (G := G) B
  (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a)))
  (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "chart" => mixedCoveredJetChart U o b hb bW d

variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (e : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} →
  ScalarSiteExpansion.{uα,uα} (Finset α))

local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell
local notation "windows" => allocatedGridSiteWindow B rowSets U b S
local notation "weight" => allocatedGridWindowWeight B U b S rowTypes (allocatedActiveGrid B U b S) windows laws
local notation "χ" => allocatedChartGridMultiplier B U b S rowTypes hb o bW d weight
local notation "profile" => allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f
local notation "volumeN" => allocatedActiveNaturalVolume B U b S rowSets
local notation "globalPrefactor" => allocatedGlobalWindowPrefactor B U b hR hσ S rowSets d x q y₀ hcell hb o bW f

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : rowTypes j => ν j))
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)

local notation "aux" => allocatedGridWindowPMF B U b S rowTypes (allocatedActiveGrid B U b S)
  windows laws (fun a _ => allocatedGridSiteWindow_nonempty B rowSets U b S a)
local notation "windowCount" => (∏ a : {a // grid a},
  ite (allocatedActiveGrid B U b S a) (Finset.card (windows a) : ℝ) 1)
local notation "reference" => allocatedLongJetReference B U b S rowTypes
local notation "longScale" => (∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x y₀

noncomputable def allocatedGlobalProfileMajorant (A : ℝ≥0) (y : EuclideanJetLayers U rowTypes) : ℝ :=
  (windowCount / volumeN) *
    allocatedProbabilityProfileMajorant B U b S o aux A f (fun _ => 0) d y

local notation "majorant" => allocatedGlobalProfileMajorant B U b hR hσ S rowSets d x q y₀ hcell o f

include hb bW in
theorem allocatedGlobalWindowPrefactor_le_profile_majorant (A : ℝ≥0)
    (hA : ∀ (z : AllocatedLongJetRows B U b S rowTypes) (r : ∀ j, rowTypes j → E j → ZMod d),
      |∏ a, allocatedLongJetMask B U b S x rows q (residue) a (z a)| *
        coefficientDeckJetDensity root dirs rows d r ≤ A)
    (y : EuclideanJetLayers U rowTypes) :
    ‖globalPrefactor y‖ ≤ majorant A y := by
  have hs : 0 < longScale := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
  have hbound := allocatedGridlessWindow_le_profile_majorant B U b S x
    (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀)
    rows hb o bW d (allocatedActiveGrid B U b S) windows laws
    (fun a _ => allocatedGridSiteWindow_nonempty B rowSets U b S a)
    (allocatedLongProfileDensity B U b S x rows q (residue) f) A f (fun _ => 0) ?_ y
  · rw [allocatedGlobalWindowPrefactor_norm B U b hR hσ S rowSets d x q y₀ hcell hb o bW f]
    change |χ y * profile y| / volumeN ≤ (windowCount / volumeN) *
      allocatedProbabilityProfileMajorant B U b S o aux A f (fun _ => 0) d y
    calc
      _ ≤ (windowCount * allocatedProbabilityProfileMajorant B U b S o aux A f (fun _ => 0) d y) /
          volumeN := div_le_div_of_nonneg_right hbound (allocatedActiveNaturalVolume_pos B U b hR S rowSets).le
      _ = _ := by ring
  · intro z r
    simp only [principalAxisJoin_restrict, allocatedLongProfileDensity, sub_zero,
      abs_div, abs_mul, abs_of_pos hs]
    calc
      _ = ((|∏ a, allocatedLongJetMask B U b S x rows q (residue) a (z a)| *
          coefficientDeckJetDensity root dirs rows d r) *
          |f (allocatedLongJetRealCoordinates B U b S z)|) / longScale := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hA z r) (abs_nonneg _)) hs.le

include hb bW in
theorem allocatedGlobalProfileMajorant_integrable_mass (A : ℝ≥0)
    (hi : Integrable (allocatedUnmaskedLongProfileDensity B U b S (fun z => |f z|)) reference)
    {Cf Kf : ℝ≥0} (hf : LipschitzWith Kf f) (hfb : ∀ z, |f z| ≤ Cf)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    Integrable (majorant A) haar ∧
      (∫ y, majorant A y ∂haar) ≤ allocatedSiteFamilyWindowVolume (G := G) B rowSets *
        ((A : ℝ) * ∫ z, allocatedUnmaskedLongProfileDensity B U b S (fun z => |f z|) z ∂reference) := by
  have hi' : Integrable (allocatedUnmaskedLongProfileDensity B U b S (fun z => |f z - 0|)) reference := by
    simpa only [sub_zero] using hi
  have hm := allocatedProbabilityProfileMajorant_integrable_mass B U b S o aux hb bW d ν (Cg := 0)
    A f (fun _ => 0) hi' hf (LipschitzWith.const 0) hfb (fun _ => by simp) C V hC hV
  have hn := allocatedActiveNaturalVolume_pos B U b hR S rowSets
  have hN : 0 ≤ windowCount := Finset.prod_nonneg (fun a _ => by split_ifs <;> positivity)
  have hfac : 0 ≤ windowCount / volumeN := div_nonneg hN hn.le
  have hwin : windowCount / volumeN ≤ allocatedSiteFamilyWindowVolume (G := G) B rowSets :=
    (div_le_iff₀ hn).mpr (allocatedActiveSiteWindow_volume B rowSets U b S hR)
  constructor
  · exact hm.1.const_mul (windowCount / volumeN)
  · change (∫ y, (windowCount / volumeN) *
        allocatedProbabilityProfileMajorant B U b S o aux A f (fun _ => 0) d y ∂haar) ≤ _
    rw [integral_const_mul]
    have hm' : (∫ y, allocatedProbabilityProfileMajorant B U b S o aux A f (fun _ => 0) d y ∂haar) ≤
        (A : ℝ) * ∫ z, allocatedUnmaskedLongProfileDensity B U b S (fun z => |f z|) z ∂reference := by
      simpa only [sub_zero] using hm.2
    exact (mul_le_mul_of_nonneg_left hm' hfac).trans
      (mul_le_mul_of_nonneg_right hwin (mul_nonneg A.coe_nonneg
        (integral_nonneg (fun z => div_nonneg (abs_nonneg _)
          (Finset.prod_nonneg (fun a _ => (allocatedLongJetOutputScale_pos B U b S a).le))))))

omit [NeZero d] [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedGlobalProfileMajorant_lipschitz_lift (A : ℝ≥0)
    {Cf Kf : ℝ≥0} (hf : LipschitzWith Kf f) (hfb : ∀ z, |f z| ≤ Cf)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    ∃ ψ : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℝ,
      (∀ y, majorant A y = ψ (coveredJetAmbientTorus U d y)) ∧
      LipschitzWith (Real.toNNReal (windowCount / volumeN) *
        allocatedProfileErrorLip B U b S (O := rowTypes) A Cf 0 Kf 0 C V) ψ ∧
      (∀ z, 0 ≤ ψ z ∧ ψ z ≤ (windowCount / volumeN) *
        allocatedProfileErrorCap B U b S (O := rowTypes) A Cf 0 V) := by
  let k := allocatedProbabilityProfileTorusKernel B U b S o aux A f (fun _ => 0)
  let c : ℝ := windowCount / volumeN
  have hc : 0 ≤ c := div_nonneg
    (Finset.prod_nonneg (fun a _ => by split_ifs <;> positivity))
    (allocatedActiveNaturalVolume_pos B U b hR S rowSets).le
  have hp := allocatedProbabilityProfileTorusKernel_bounds B U b S o aux A f (fun _ => 0) (Cg := 0)
    hf (LipschitzWith.const 0) hfb (fun _ => by simp) C V hC hV
  refine ⟨fun z => c * k z, fun _ => rfl, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro z t
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hc]
    have hl := hp.2.dist_le_mul z t
    rw [Real.dist_eq] at hl
    calc
      _ ≤ c * ((allocatedProfileErrorLip B U b S (O := rowTypes) A Cf 0 Kf 0 C V : ℝ) * dist z t) :=
        mul_le_mul_of_nonneg_left hl hc
      _ = _ := by rw [NNReal.coe_mul, Real.coe_toNNReal _ hc]; ring
  · intro z
    exact ⟨mul_nonneg hc (hp.1 z).1, mul_le_mul_of_nonneg_left (hp.1 z).2 hc⟩

end Erdos3.VectorPolynomial

end

end OAI
