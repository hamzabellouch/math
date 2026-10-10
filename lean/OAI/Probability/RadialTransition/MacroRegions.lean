import OAI.Probability.RadialTransition.BoxEnsembles

namespace OAI

universe uX uY

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

def macroRegion (q : ℕ) (k : Cell) : Set Position := {x | macroOf q (cellOf x) = k}

def macroOrigin (q : ℕ) (k : Cell) : Position := WithLp.toLp 2 (fun d => (q:ℝ)*(k d:ℝ)/4)

lemma measurableSet_macroRegion (q : ℕ) (k : Cell) : MeasurableSet (macroRegion q k) := by
  exact (Set.to_countable {i : Cell | macroOf q i = k}).measurableSet.preimage measurable_cellOf

lemma macroRegion_translate {q : ℕ} (hq : 0 < q) (k : Cell) :
    macroRegion q k = translateSet (macroOrigin q k) (halfCube ((q:ℝ)/4)) := by
  ext x
  have hq' : (0:ℤ) < q := by exact_mod_cast hq
  constructor
  · intro hx d
    have hd : cellOf x d / (q:ℤ) = k d := congrFun hx d
    have hb := (Int.ediv_eq_iff_of_pos hq').mp hd
    have hl := Int.floor_le (4*x d)
    have hu := Int.lt_floor_add_one (4*x d)
    have hbl : ((k d:ℤ)*(q:ℤ):ℝ) ≤ (⌊4*x d⌋:ℝ) := by exact_mod_cast hb.1
    have hbu : (⌊4*x d⌋:ℝ)+1 ≤ ((k d:ℤ)*(q:ℤ)+(q:ℤ):ℝ) := by exact_mod_cast hb.2
    change 0 ≤ x d-(q:ℝ)*(k d:ℝ)/4 ∧ x d-(q:ℝ)*(k d:ℝ)/4 < (q:ℝ)/4
    push_cast at hbl hbu
    constructor <;> linarith
  · intro hx
    funext d
    apply (Int.ediv_eq_iff_of_pos hq').mpr
    have hd : 0 ≤ x d-(q:ℝ)*(k d:ℝ)/4 ∧ x d-(q:ℝ)*(k d:ℝ)/4 < (q:ℝ)/4 := hx d
    constructor
    · apply Int.le_floor.mpr
      push_cast
      linarith
    · apply Int.floor_lt.mpr
      push_cast
      linarith

lemma volume_macroRegion {q : ℕ} (hq : 0 < q) (k : Cell) :
    volume (macroRegion q k) = ENNReal.ofReal ((q:ℝ)/4)^3 := by
  rw [macroRegion_translate hq, volume_translateSet _ _ (measurableSet_halfCube _), volume_halfCube]

lemma macroRegion_subset_halfCube {m q : ℕ} (hq : 0 < q) (i : GridIndex m) :
    macroRegion q (gridEmbed i) ⊆ halfCube (((m:ℝ)*q)/4) := by
  intro x hx
  rw [macroRegion_translate hq] at hx
  intro d
  have hd : 0 ≤ x d-(q:ℝ)*(i d:ℝ)/4 ∧ x d-(q:ℝ)*(i d:ℝ)/4 < (q:ℝ)/4 := hx d
  have hi : (i d:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast (i d).isLt
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hin : (0:ℝ) ≤ (i d:ℝ) := by positivity
  constructor <;> nlinarith

lemma halfCube_macro_cover {m q : ℕ} (hq : 0 < q) (x : Position)
    (hx : x ∈ halfCube (((m:ℝ)*q)/4)) : ∃ i : GridIndex m, macroOf q (cellOf x) = gridEmbed i := by
  obtain ⟨k,hk⟩ := halfCube_grid_cover (m*q) x (by simpa only [Nat.cast_mul] using hx)
  obtain ⟨⟨i,j⟩,he⟩ := blockEmbed_surjective hq k
  refine ⟨i, ?_⟩
  rw [hk, ← he, blockEmbed_macro hq]

lemma halfCube_macro_union {m q : ℕ} (hq : 0 < q) :
    (⋃ i : GridIndex m, macroRegion q (gridEmbed i)) = halfCube (((m:ℝ)*q)/4) := by
  ext x
  simp only [mem_iUnion]
  exact ⟨fun ⟨i,hi⟩ => macroRegion_subset_halfCube hq i hi,
    fun hx => halfCube_macro_cover hq x hx⟩

def regionMeasure (A : Set Position) : Measure A := volume.comap Subtype.val

lemma regionMeasure_map {A : Set Position} (hA : MeasurableSet A) :
    Measure.map Subtype.val (regionMeasure A) = volume.restrict A := map_comap_subtype_coe hA volume

lemma regionMeasure_univ {A : Set Position} (hA : MeasurableSet A) :
    regionMeasure A univ = volume A := by
  rw [regionMeasure, comap_subtype_coe_apply hA]
  simp only [Set.image_univ, Subtype.range_coe]

lemma regionMeasure_finite {A : Set Position} (hA : MeasurableSet A) (hAfin : volume A ≠ ⊤) :
    IsFiniteMeasure (regionMeasure A) := ⟨by rw [regionMeasure_univ hA]; exact lt_top_iff_ne_top.mpr hAfin⟩

lemma macroRegion_partition {m q : ℕ} (hq : 0 < q) :
    volume.restrict (halfCube (((m:ℝ)*q)/4)) =
      ∑ i : GridIndex m, Measure.map Subtype.val (regionMeasure (macroRegion q (gridEmbed i))) := by
  have hd : Pairwise (fun i j : GridIndex m => Disjoint (macroRegion q (gridEmbed i)) (macroRegion q (gridEmbed j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hij (gridEmbed_injective m (hx.symm.trans hy))
  rw [← halfCube_macro_union hq, Measure.restrict_iUnion hd (fun i => measurableSet_macroRegion _ _), Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact (regionMeasure_map (measurableSet_macroRegion _ _)).symm

section MapGrand
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

omit [BorelSpace X] [SecondCountableTopology X] in
lemma pairGrand_within (v : X → X → ℝ) (μ : Measure X) (β z : ℝ) :
    pairGrand v μ β z = boltzmannPartition (particleBase μ z) (fun x => β*pairWithin v x) := by
  simp only [pairGrand, boltzmannPartition, multisetEnergy_particle, neg_mul]

lemma pairGrand_map (v : Y → Y → ℝ) (hv : Measurable (Function.uncurry v))
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → Y) (hf : Measurable f) (β z : ℝ) :
    pairGrand v (Measure.map f μ) β z = pairGrand (fun x y => v (f x) (f y)) μ β z := by
  simp only [pairGrand_within, boltzmannPartition]
  have hfun : AEStronglyMeasurable (fun y : ParticleState Y => Real.exp (-(β*pairWithin v y)))
      (Measure.map (mapParticle f) (particleBase μ z)) :=
    (Real.measurable_exp.comp ((measurable_const.mul (measurable_pairWithin v hv)).neg)).aestronglyMeasurable
  rw [← particleBase_map μ z hf, integral_map (measurable_mapParticle hf).aemeasurable hfun]
  rfl
end MapGrand

lemma grandOn_halfCube {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B β : ℝ} (hs : StableWith φ B) (hβ : 0 ≤ β) (L z : ℝ) :
    grandOn φ (halfCube L) β z = grandOn φ (cube L) β z := by
  rw [← pairGrand_radial hφ hb hs hβ (by rw [volume_halfCube]; finiteness),
    ← pairGrand_radial hφ hb hs hβ (by rw [volume_cube]; finiteness), restrict_halfCube]

lemma deletedPair_macro_factorization {m q : ℕ} (hq : 0 < q)
    {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B β : ℝ} (hs : StableWith φ B) (hβ : 0 ≤ β) (z : ℝ) :
    pairGrand (deletedPair (macroOf q) φ 0) (volume.restrict (halfCube (((m:ℝ)*q)/4))) β z =
      (grandOn φ (cube ((q:ℝ)/4)) β z)^(m^3) := by
  let X (i : GridIndex m) := macroRegion q (gridEmbed i)
  let ν (i : GridIndex m) := regionMeasure (X i)
  let : ∀ i, IsFiniteMeasure (ν i) := fun i => regionMeasure_finite (measurableSet_macroRegion _ _)
    (by rw [volume_macroRegion hq]; finiteness)
  let pos : ∀ i, X i → Position := fun _ => Subtype.val
  have hp (i : GridIndex m) : Measurable (pos i) := measurable_subtype_coe
  let v : ∀ i j, X i → X j → ℝ := fun i j x y => deletedPair (macroOf q) φ 0 (pos i x) (pos j y)
  have hcross (i j : GridIndex m) (hij : i ≠ j) (x : X i) (y : X j) : v i j x y = 0 := by
    have hx : macroOf q (cellOf (pos i x)) = gridEmbed i := x.property
    have hy : macroOf q (cellOf (pos j y)) = gridEmbed j := y.property
    have hn : gridEmbed i ≠ gridEmbed j := fun h => hij (gridEmbed_injective m h)
    simp only [v, deletedPair, hx, hy, hn, ite_false, radialPair, Pi.zero_apply, add_zero]
  have hintra (i : GridIndex m) : v i i = fun x y => radialPair φ (pos i x) (pos i y) := by
    funext x y
    have hx : macroOf q (cellOf (pos i x)) = gridEmbed i := x.property
    have hy : macroOf q (cellOf (pos i y)) = gridEmbed i := y.property
    simp only [v, deletedPair, hx, hy, ite_true, radialPair, Pi.zero_apply, add_zero]
  have hdecomp : volume.restrict (halfCube (((m:ℝ)*q)/4)) =
      ∑ i : GridIndex m, Measure.map (pos i) (ν i) := macroRegion_partition (m := m) hq
  have hfactor := pairGrand_eq_cell (fun i : GridIndex m => ↥(X i)) ν pos hp (deletedPair (macroOf q) φ 0) (measurable_deletedPair (macroOf q) hφ (show Continuous (0 : Potential) from continuous_const))
    (deletedPair_symm _ _ _) hdecomp β z
  rw [hfactor, boltzmannPartition_no_cross ν v hcross]
  have he (i : GridIndex m) : boltzmannPartition (particleBase (ν i) z) (fun x => β*pairWithin (v i i) x) =
      grandOn φ (cube ((q:ℝ)/4)) β z := by
    rw [hintra, ← pairGrand_within, ← pairGrand_map (radialPair φ) (continuous_radialPair hφ).measurable (ν i) (pos i) (hp i)]
    have hmap : Measure.map (pos i) (ν i) = volume.restrict (macroRegion q (gridEmbed i)) := regionMeasure_map (measurableSet_macroRegion _ _)
    rw [hmap, pairGrand_radial hφ hb hs hβ (by rw [volume_macroRegion hq]; finiteness),
      macroRegion_translate hq, grandOn_translate, grandOn_halfCube hφ hb hs hβ]
  simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

end RadialTransition

end

end OAI
