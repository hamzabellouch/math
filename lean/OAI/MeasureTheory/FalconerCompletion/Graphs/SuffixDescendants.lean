import Mathlib
import OAI.MeasureTheory.Falconer.Geometry.BinBands
import OAI.MeasureTheory.Falconer.Geometry.BinOffsets
import OAI.MeasureTheory.Falconer.Geometry.Bins
import OAI.MeasureTheory.Falconer.Geometry.FiniteBinComparison
import OAI.MeasureTheory.Falconer.Measures.FiniteMeasureProducts
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.InteriorPolicy
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.FalconerCompletion.Fourier.MinimalMask
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAmbient2

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer
open scoped ENNReal
variable {d : ℕ}
noncomputable def suffixDescendants (a p : ℕ) (X : CellPath d) : Finset (CellPath d) := by
  classical
  exact (dyadicPaths p).filter fun P => P.take a=X

lemma suffixDescendants_subset {a p : ℕ} {X P : CellPath d} (hP : P ∈ suffixDescendants a p X) :
    treeCell P ⊆ treeCell X := by
  classical
  rcases Finset.mem_filter.mp hP with ⟨hP,he⟩
  simpa only [he] using treeCell_subset_take P a

lemma suffixDescendants_cover {a p : ℕ} (hap : a ≤ p) {X : CellPath d}
    (hX : X ∈ dyadicPaths a) :
    (⋃ P ∈ suffixDescendants a p X, treeCell P)=treeCell X := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨P,hP,hx⟩ := Set.mem_iUnion₂.mp hx
    exact suffixDescendants_subset hP hx
  · intro x hx
    have hxroot : x ∈ treeCell ([] : CellPath d) := by
      simpa only [List.take_zero] using treeCell_subset_take X 0 hx
    rw [←treeCell_cover_root p] at hxroot
    obtain ⟨P,hP,hxP⟩ := Set.mem_iUnion₂.mp hxroot
    have hlP : P.length=p := (mem_dyadicPaths _ _).mp hP
    have hlX : X.length=a := (mem_dyadicPaths _ _).mp hX
    have he : P.take a=X := by
      by_contra hne
      have hh := treeCell_disjoint (p:=P.take a) (q:=X)
        (by simp [List.length_take,hlP,hlX,Nat.min_eq_left hap]) hne
      exact Set.disjoint_left.mp hh (treeCell_subset_take P a hxP) hx
    exact Set.mem_iUnion₂.mpr ⟨P,Finset.mem_filter.mpr ⟨hP,he⟩,hxP⟩

lemma suffixDescendants_disjoint {a p : ℕ} {X P Q : CellPath d}
    (hP : P ∈ suffixDescendants a p X) (hQ : Q ∈ suffixDescendants a p X) (hne : P ≠ Q) :
    Disjoint (treeCell P) (treeCell Q) := by
  classical
  apply treeCell_disjoint _ hne
  exact ((mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hP).1).trans
    ((mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hQ).1).symm

lemma suffix_descendant_measure_split (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    {a p : ℕ} (hap : a≤p) {X : CellPath d} (hX : X.length=a) :
    ρ.restrict (treeCell X) = ∑ P ∈ suffixDescendants a p X, ρ.restrict (treeCell P) := by
  classical
  rw [←suffixDescendants_cover hap ((mem_dyadicPaths _ _).mpr hX)]
  rw [Measure.restrict_biUnion_finset (fun i hi j hj hne => suffixDescendants_disjoint hi hj hne)
    measurableSet_treeCell]
  ext S hS
  simp only [Measure.sum_apply _ hS,Measure.finsetSum_apply]
  rw [tsum_fintype]
  change (∑ P ∈ (suffixDescendants a p X).attach, (ρ.restrict (treeCell P.val)) S) = _
  exact Finset.sum_attach _ (fun P => (ρ.restrict (treeCell P)) S)
namespace PositiveDistanceState

noncomputable def suffixRectangles (e : PositiveDistanceState d) (p : ℕ) : Finset (CellPath d × CellPath d) :=
  (suffixDescendants e.a p e.X).product (suffixDescendants e.a p e.Y)

noncomputable def suffixRetained (e : PositiveDistanceState d) (p : ℕ) : Finset (CellPath d × CellPath d) := by
  classical
  exact (e.suffixRectangles p).filter fun c =>
    ∃ x ∈ (treeCell c.1), ∃ y ∈ (treeCell c.2), (x,y) ∈ e.good

abbrev suffixData (e : PositiveDistanceState d) (c : CellPath d × CellPath d) : PositiveDistanceState d :=
  {e with X := c.1,Y := c.2}

noncomputable def suffixFullDistance (e : PositiveDistanceState d) (c : CellPath d × CellPath d) : Measure ℝ :=
  Measure.map (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => dist z.1 z.2) (e.suffixData c).cellPair

instance suffixFullDistance_finite (e : PositiveDistanceState d) [IsFiniteMeasure e.ρ]
    (c : CellPath d × CellPath d) : IsFiniteMeasure (e.suffixFullDistance c) := by
  unfold suffixFullDistance
  infer_instance

theorem suffix_retained_spec (e : PositiveDistanceState d) {p : ℕ} {c : CellPath d × CellPath d}
    (hc : c ∈ e.suffixRetained p) :
    c.1.length = p ∧ c.2.length = p ∧ c.1.take e.a = e.X ∧ c.2.take e.a = e.Y ∧
      ∃ x ∈ (treeCell c.1), ∃ y ∈ (treeCell c.2), (x,y) ∈ e.good := by
  classical
  obtain ⟨hc,hw⟩ := Finset.mem_filter.mp hc
  obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hc
  exact ⟨(mem_dyadicPaths _ _).mp (Finset.mem_filter.mp h₁).1,
    (mem_dyadicPaths _ _).mp (Finset.mem_filter.mp h₂).1,
    (Finset.mem_filter.mp h₁).2,(Finset.mem_filter.mp h₂).2,hw⟩

theorem cellPair_split_suffix (e : PositiveDistanceState d) [IsFiniteMeasure e.ρ]
    {p : ℕ} (hap : e.a ≤ p)
    (hX : e.X.length = e.a) (hY : e.Y.length = e.a) :
    e.cellPair = ∑ c ∈ e.suffixRectangles p, (e.suffixData c).cellPair := by
  change (e.ρ.restrict (treeCell e.X)).prod
    (e.ρ.restrict (treeCell e.Y)) = _
  rw [suffix_descendant_measure_split e.ρ hap hX,
    suffix_descendant_measure_split e.ρ hap hY,finite_measure_prod_sum]
  simp only [suffixRectangles,cellPair]
  exact (Finset.sum_product (suffixDescendants e.a p e.X)
    (suffixDescendants e.a p e.Y)
    (fun c : CellPath d × CellPath d => (e.ρ.restrict (treeCell c.1)).prod
      (e.ρ.restrict (treeCell c.2)))).symm

theorem pair_zero_of_no_witness (e : PositiveDistanceState d) [IsFiniteMeasure e.ρ] (c : CellPath d × CellPath d)
    (hw : ¬ ∃ x ∈ (treeCell c.1),
      ∃ y ∈ (treeCell c.2), (x,y) ∈ e.good) : (e.suffixData c).pair = 0 := by
  apply Measure.restrict_eq_zero.mpr
  change ((e.ρ.restrict (treeCell c.1)).prod
    (e.ρ.restrict (treeCell c.2))) e.good = 0
  rw [Measure.prod_restrict,Measure.restrict_apply e.measurable_good]
  have he : e.good ∩ ((treeCell c.1) ×ˢ (treeCell c.2)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hw ⟨z.1,hz.2.1,z.2,hz.2.2,hz.1⟩
  rw [he,measure_empty]

theorem pair_split_retained (e : PositiveDistanceState d) [IsFiniteMeasure e.ρ]
    {p : ℕ} (hap : e.a ≤ p)
    (hX : e.X.length = e.a) (hY : e.Y.length = e.a) :
    e.pair = ∑ c ∈ e.suffixRetained p, (e.suffixData c).pair := by
  classical
  rw [pair,e.cellPair_split_suffix hap hX hY,finite_measure_restrict_sum]
  change (∑ c ∈ e.suffixRectangles p, (e.suffixData c).pair) = _
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro c hc hn
  apply e.pair_zero_of_no_witness c
  intro hw
  exact hn (Finset.mem_filter.mpr ⟨hc,hw⟩)

theorem distance_split_retained (e : PositiveDistanceState d) [IsFiniteMeasure e.ρ]
    {p : ℕ} (hap : e.a ≤ p)
    (hX : e.X.length = e.a) (hY : e.Y.length = e.a) :
    e.distance = ∑ c ∈ e.suffixRetained p, (e.suffixData c).distance := by
  rw [distance,e.pair_split_retained hap hX hY,Measure.map_finset_sum (by fun_prop)]
  rfl

theorem suffix_full_pair_le_coarse (e : PositiveDistanceState d) [IsFiniteMeasure e.ρ]
    {p : ℕ} (hap : e.a ≤ p)
    (hX : e.X.length = e.a) (hY : e.Y.length = e.a)
    (hgood : ∀ c ∈ e.suffixRetained p, ∀ x ∈ (treeCell c.1),
      ∀ y ∈ (treeCell c.2),
      (x,y) ∈ ({e with t := p,i := e.i+1} : PositiveDistanceState d).good) :
    (∑ c ∈ e.suffixRetained p, (e.suffixData c).cellPair) ≤
      ({e with t := p,i := e.i+1} : PositiveDistanceState d).pair := by
  classical
  let child : PositiveDistanceState d := {e with t := p,i := e.i+1}
  have hle : (∑ c ∈ e.suffixRetained p, (e.suffixData c).cellPair) ≤ e.cellPair := by
    rw [e.cellPair_split_suffix hap hX hY]
    intro s
    simp only [Measure.finsetSum_apply]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have he : (∑ c ∈ e.suffixRetained p, (e.suffixData c).cellPair).restrict child.good =
      ∑ c ∈ e.suffixRetained p, (e.suffixData c).cellPair := by
    rw [finite_measure_restrict_sum]
    apply Finset.sum_congr rfl
    intro c hc
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [(e.suffixData c).ae_cellPair_mem] with z hz
    exact hgood c hc z.1 hz.1 z.2 hz.2
  rw [← he]
  exact Measure.restrict_mono_measure hle child.good

theorem suffix_full_distance_le_coarse (e : PositiveDistanceState d) [IsFiniteMeasure e.ρ]
    {p : ℕ} (hap : e.a ≤ p)
    (hX : e.X.length = e.a) (hY : e.Y.length = e.a)
    (hgood : ∀ c ∈ e.suffixRetained p, ∀ x ∈ (treeCell c.1),
      ∀ y ∈ (treeCell c.2),
      (x,y) ∈ ({e with t := p,i := e.i+1} : PositiveDistanceState d).good) :
    (∑ c ∈ e.suffixRetained p, e.suffixFullDistance c) ≤
      ({e with t := p,i := e.i+1} : PositiveDistanceState d).distance := by
  have hh := Measure.map_mono (e.suffix_full_pair_le_coarse hap hX hY hgood)
    (continuous_fst.dist continuous_snd).measurable
  rw [Measure.map_finset_sum (by fun_prop)] at hh
  exact hh

theorem suffix_distance_variation (_e : PositiveDistanceState d)
    {p : ℕ} {c : CellPath d × CellPath d} (hP : c.1.length=p) (hQ : c.2.length=p)
    {z z' : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)}
    (hz : z.1 ∈ treeCell c.1 ∧ z.2 ∈ treeCell c.2)
    (hz' : z'.1 ∈ treeCell c.1 ∧ z'.2 ∈ treeCell c.2) :
    |dist z.1 z.2-dist z'.1 z'.2| ≤ 2*(d+1:ℝ)/(2:ℝ)^p := by
  have h₁ := ambientGridCell_dist_le hz'.1 hz.1
  have h₂ := ambientGridCell_dist_le hz'.2 hz.2
  change dist z.1 z'.1 ≤ (d+1:ℝ)/(2:ℝ)^c.1.length at h₁
  change dist z.2 z'.2 ≤ (d+1:ℝ)/(2:ℝ)^c.2.length at h₂
  rw [hP] at h₁
  rw [hQ] at h₂
  have hh := dist_dist_dist_le z.1 z.2 z'.1 z'.2
  rw [Real.dist_eq] at hh
  exact hh.trans ((add_le_add h₁ h₂).trans_eq (by ring))

theorem distance_bin_witness (e : PositiveDistanceState d) [IsFiniteMeasure e.ρ]
    (w : ℝ) (k : ℤ) (hm : e.distance (realBin w k) ≠ 0) :
    ∃ z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d), dist z.1 z.2 ∈ realBin w k ∧
      z.1 ∈ (treeCell e.X) ∧ z.2 ∈ (treeCell e.Y) := by
  rw [e.distance_apply (realBin_measurable w k)] at hm
  obtain ⟨z,hz,hcells⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hm
    (e.ae_cellPair_mem.filter_mono (ae_mono Measure.restrict_le_self))
  exact ⟨z,hz.1,hcells⟩

theorem shared_bin_full_coarse_collision (e : PositiveDistanceState d) [IsFiniteMeasure e.ρ]
    {p : ℕ} (hpt : p ≤ e.t)
    {c b : CellPath d × CellPath d} (hc : c ∈ e.suffixRetained p) (hb : b ∈ e.suffixRetained p)
    (hbin : ∃ k : ℤ, (e.suffixData c).distance (realBin e.width k) ≠ 0 ∧
      (e.suffixData b).distance (realBin e.width k) ≠ 0) :
    ((e.suffixFullDistance c).prod (e.suffixFullDistance b))
      {z : ℝ × ℝ | |z.1-z.2| ≤ 100*(d+1:ℝ)/(2:ℝ)^p} =
        (e.suffixFullDistance c univ)*(e.suffixFullDistance b univ) := by
  obtain ⟨hC₁,hC₂,_⟩ := e.suffix_retained_spec hc
  obtain ⟨hB₁,hB₂,_⟩ := e.suffix_retained_spec hb
  obtain ⟨k,hkc,hkb⟩ := hbin
  obtain ⟨x,hxbin,hx⟩ := (e.suffixData c).distance_bin_witness e.width k hkc
  obtain ⟨y,hybin,hy⟩ := (e.suffixData b).distance_bin_witness e.width k hkb
  have hxy := realBin_diameter e.width k hxbin hybin
  have hw : e.width ≤ 1/(2:ℝ)^p := by
    simp only [width,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
    exact inv_le_inv₀ (by positivity) (by positivity) |>.mpr
      (pow_le_pow_right₀ (by norm_num) hpt)
  have hgood : ∀ᵐ z ∂(e.suffixData c).cellPair.prod (e.suffixData b).cellPair,
      |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*(d+1:ℝ)/(2:ℝ)^p := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (e.suffixData c).ae_cellPair_mem,
      Measure.quasiMeasurePreserving_snd.ae (e.suffixData b).ae_cellPair_mem] with z hz hz'
    have h₁ := e.suffix_distance_variation hC₁ hC₂ hz hx
    have h₂ := e.suffix_distance_variation hB₁ hB₂ hz' hy
    obtain ⟨ha,hb⟩ := abs_le.mp h₁
    obtain ⟨hc,hd⟩ := abs_le.mp h₂
    obtain ⟨he,hf⟩ := abs_le.mp hxy
    apply abs_le.mpr
    simp only [div_eq_mul_inv,one_mul] at ha hb hc hd hw ⊢
    have hdpos : 0 ≤ (d:ℝ) := Nat.cast_nonneg d
    constructor <;> nlinarith [show 0 < ((2:ℝ)^p)⁻¹ by positivity]
  rw [suffixFullDistance,suffixFullDistance,Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) (by measurability)]
  change ((e.suffixData c).cellPair.prod (e.suffixData b).cellPair)
    {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*(d+1:ℝ)/(2:ℝ)^p} = _
  rw [measure_congr (Filter.eventuallyEqSet_univ.mpr hgood),← univ_prod_univ,Measure.prod_prod]
  simp only [Measure.map_apply (continuous_fst.dist continuous_snd).measurable MeasurableSet.univ,preimage_univ]

lemma suffix_normalization_ratio (e : PositiveDistanceState d) (p : ℕ) :
    e.normalization * ENNReal.ofReal ((2:ℝ)^(-((e.t:ℝ)-p))) =
      ({e with t := p,i := e.i+1} : PositiveDistanceState d).normalization := by
  change ENNReal.ofReal ((2:ℝ)^((e.t:ℝ)-e.a)/e.levelMass^4) *
    ENNReal.ofReal ((2:ℝ)^(-((e.t:ℝ)-p))) =
      ENNReal.ofReal ((2:ℝ)^((p:ℝ)-e.a)/e.levelMass^4)
  rw [←ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [div_mul_eq_mul_div,←Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 2
  ring

lemma coincidence_le_bin_sq (e : PositiveDistanceState d) [IsFiniteMeasure e.ρ] :
    e.coincidence ≤ e.normalization * (((bandOffsets (100*(d+1:ℝ))).card:ℝ≥0∞)*
      (binL2Norm e.distance e.width)^2) := by
  have hh := real_bin_shifted_band_bound e.distance e.distance
    (show 0<e.width by unfold width; positivity) (100*(d+1:ℝ)) 0
  simp only [sub_zero,←pow_two] at hh
  rw [e.distance_collision] at hh
  exact mul_le_mul' le_rfl hh

theorem uniform_actual_suffix_reduction {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ e : PositiveDistanceState d, e.sig=sig → e.J=J → N₀≤e.N →
      IsFiniteMeasure e.ρ → ∀ K : ℝ, 1000*(d+1:ℝ)<K → CentreSeparated e.X e.Y e.a K →
      e.X.length=e.a → e.Y.length=e.a → 0<e.q → e.i+1≤e.J →
      e.t≤e.N → e.a+100*e.q<e.t →
      let A := adjustedProfile (d:=d) e.mass e.N
      let p := policyDepth A e.N e.q e.a e.t
      e.a+e.t<2*p →
      e.coincidence ≤
        ((bandOffsets (100*(d+1:ℝ))).card:ℝ≥0∞)*((bandOffsets 3).card:ℝ≥0∞)*
          ENNReal.ofReal (((2:ℝ)^e.N)^(A p-intervalMin A p e.t+e.C*sig))*
            ({e with t := p,i := e.i+1} : PositiveDistanceState d).coincidence := by
  obtain ⟨N₁,h₁⟩ := uniform_actual_suffix_local_bins (d:=d) hsig
  obtain ⟨N₂,h₂⟩ := uniform_suffix_good_transport (d:=d) hsig hJ
  refine ⟨max N₁ N₂,?_⟩
  intro e hsig' hJ' hN hf K hK hsep hX hY hq hi ht hw A p hsuffix
  let := hf
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq ht hw)
  have hap : e.a≤p := by dsimp only [p]; omega
  have hpt : p≤e.t := by dsimp only [p]; omega
  let child : PositiveDistanceState d := {e with t := p,i := e.i+1}
  let E : Set (ℝ×ℝ) := {z | |z.1-z.2| ≤ 100*(d+1:ℝ)/(2:ℝ)^p}
  let loss : ℝ := A p-intervalMin A p e.t+e.C*sig
  let B : ℝ≥0∞ := ENNReal.ofReal ((2:ℝ)^(-((e.t:ℝ)-p))*((2:ℝ)^e.N)^loss)
  let F : ℝ≥0∞ := ((bandOffsets 3).card:ℝ≥0∞)*B
  have hnorm (c : CellPath d×CellPath d) (hc : c∈e.suffixRetained p) :
      (binL2Norm (e.suffixData c).distance e.width)^2 ≤ F*(e.suffixFullDistance c univ)^2 := by
    obtain ⟨hP,hQ,hPX,hQY,x,hx,y,hy,hgood⟩ := e.suffix_retained_spec hc
    have hh := h₁ e hsig' ((le_max_left _ _).trans hN) K hK hsep hX hY hf
      (hJ' ▸ hJ) (by omega) hq ht hw hsuffix c.1 c.2 hP hQ hPX hQY x hx y hy hgood
    have he : e.suffixFullDistance c univ = e.ρ (treeCell c.1)*e.ρ (treeCell c.2) := by
      rw [suffixFullDistance,Measure.map_apply (continuous_fst.dist continuous_snd).measurable
        MeasurableSet.univ,preimage_univ]
      change (e.ρ.restrict (treeCell c.1)).prod (e.ρ.restrict (treeCell c.2)) univ = _
      rw [←univ_prod_univ,Measure.prod_prod,Measure.restrict_apply_univ,Measure.restrict_apply_univ]
    rw [he]
    exact hh
  have hdom : (∑ c∈e.suffixRetained p,e.suffixFullDistance c)≤child.distance := by
    apply e.suffix_full_distance_le_coarse hap hX hY
    intro c hc x' hx' y' hy'
    obtain ⟨hP,hQ,hPX,hQY,x,hx,y,hy,hgood⟩ := e.suffix_retained_spec hc
    exact h₂ e hsig' hJ' ((le_max_right _ _).trans hN) hf K hK hsep hX hY hq
      p hap hpt ht c.1 c.2 hP hQ hPX hQY x hx y hy hgood x' hx' y' hy'
  have hbin := finite_bin_collision_comparison (e.suffixRetained p)
    (fun c => (e.suffixData c).distance) e.suffixFullDistance e.width E F hnorm
    (fun c hc b hb hcommon => e.shared_bin_full_coarse_collision hpt hc hb hcommon)
  rw [←e.distance_split_retained hap hX hY] at hbin
  have htotal : (binL2Norm e.distance e.width)^2 ≤ F*(child.distance.prod child.distance) E :=
    hbin.trans (mul_le_mul' le_rfl (Measure.prod_mono hdom hdom E))
  have hbound := e.coincidence_le_bin_sq.trans
    (mul_le_mul' le_rfl (mul_le_mul' le_rfl htotal))
  have hE : (child.distance.prod child.distance) E = (child.pair.prod child.pair)
      {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*(d+1)*child.width} := by
    have he : 100*(d+1:ℝ)/(2:ℝ)^p = 100*(d+1:ℝ)*child.width := by
      simp only [child,width,Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast,div_eq_mul_inv]
    dsimp only [E]
    rw [he,child.distance_collision]
  rw [hE] at hbound
  apply hbound.trans_eq
  dsimp only [F,B]
  rw [ENNReal.ofReal_mul (by positivity : 0≤(2:ℝ)^(-((e.t:ℝ)-p)))]
  calc
    _ = ((bandOffsets (100*(d+1:ℝ))).card:ℝ≥0∞)*((bandOffsets 3).card:ℝ≥0∞)*
        ENNReal.ofReal (((2:ℝ)^e.N)^loss) *
        (e.normalization*ENNReal.ofReal ((2:ℝ)^(-((e.t:ℝ)-p)))) *
        (child.pair.prod child.pair) _ := by ring
    _ = _ := by rw [e.suffix_normalization_ratio]; exact mul_assoc _ _ _
end PositiveDistanceState
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
