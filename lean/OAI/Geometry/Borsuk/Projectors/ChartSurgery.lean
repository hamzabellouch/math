import Mathlib
import OAI.Geometry.Borsuk.Support.BalancedChart
import OAI.Geometry.Borsuk.Support.MixedHits
import OAI.Geometry.Borsuk.Projectors.CompactTargetHits
import OAI.Geometry.Borsuk.MatrixGeometry.TraceHomotopy
import OAI.Geometry.Borsuk.Projectors.CompactLocalHomotopy

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section ChartSurgery
variable {ν ι κ : Type*} [Fintype ν] [LinearOrder ν] [Nonempty ν] [Fintype ι] [DecidableEq ι] [Fintype κ]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "Y" => EuclideanSpace ℝ ι

lemma Admissible.chart_surgery_impossible {f : E → ι → ℝ} (hf : Admissible f)
    (hdim : Fintype.card (UpperTriangle ν) = Fintype.card ι) (hn : 1 < Fintype.card ι)
    {I : Finset ι} (hI : I.Nonempty) [Nonempty ↥(Iᶜ : Finset ι)]
    (hmax : ∀ u : E, ‖u‖ = 1 → I ⊆ positiveSupport f u → positiveSupport f u = I)
    {w : E} (hw : ‖w‖ = 1) (hwi : ∀ i ∈ I, 0 < f w i)
    {r : ι → ℝ} (hr : ∀ i ∈ I, 0 < r i) (hro : ∀ i ∉ I, r i = 0) (hrs : ∑ i, r i = 1)
    (c : κ → E) (hc : ∀ j, c j ∈ commonPositiveCone f I) (hcn : ∀ j, ‖c j‖ = 1)
    (hd : Pairwise (fun i j => Disjoint (interior (signChamber (activeVectors f I) (c i)))
      (interior (signChamber (activeVectors f I) (c j)))))
    (hcover : orientedLevel f w r ⊆ ⋃ j, interior (signChamber (activeVectors f I) (c j)))
    {ε : ℝ} (hε : 0 < ε) (g : κ → M → EuclideanSpace ℝ ↥(Iᶜ : Finset ι))
    (hg : ∀ j, Continuous (g j)) (hgs : ∀ j, ∀ Q ∈ matrixFibre (c j), ∑ i, g j Q i = 1)
    (hge : ∀ j, ∀ Q ∈ matrixFibre (c j), ‖g j Q - negativeCoordinates f I Q‖ < ε)
    (z : EuclideanSpace ℝ ↥(Iᶜ : Finset ι)) (hz : ∀ i, ε < z i) (hzs : ∑ i, z i = 1)
    (hgm : ∀ j, ∀ Q ∈ matrixFibre (c j), g j Q ≠ z) : False := by
  classical
  let S : κ → Set (traceSphere ν) := fun j => {A | A.val ∈ purityChart f I w (c j)}
  let U : Set (traceSphere ν) := ⋃ j, S j
  let C : Set (traceSphere ν) := {A | ∃ p : levelFibre f w r, balancedModel p = A ∧
    ∃ t ∈ Icc (0:ℝ) 1, levelHomotopy f I w r c g (t,p) = z}
  let K : ℝ × traceSphere ν → Y := finiteOpenGlue (fun j => {p | p.2 ∈ S j})
    (fun j p => mixedHomotopy f I w (c j) (g j) p.1 p.2.val)
  let H : traceSphere ν → Y := fun A => WithLp.toLp 2 (signedExtension f A.val)
  let y : Y := blockVector I (1/2:ℝ) r (1/2:ℝ) z
  let B : Set Y := {v | ∃ d : ℝ, 0 < d ∧ v = d • y}
  have hSo : ∀ j, IsOpen (S j) := fun j =>
    hf.purityChart_isOpen I w (c j) Subtype.val continuous_subtype_val (fun A => A.property.1)
  have hSd : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun A hA hB => Set.disjoint_left.mp (hd hij) hA.2.2.2.2.2 hB.2.2.2.2.2)
  have hKd : Pairwise (fun i j => Disjoint {p : ℝ × traceSphere ν | p.2 ∈ S i}
      {p : ℝ × traceSphere ν | p.2 ∈ S j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun p ha hb => Set.disjoint_left.mp (hSd hij) ha hb)
  have hKe (j : κ) (A : traceSphere ν) (hA : A ∈ S j) (t : ℝ) :
      K (t,A) = mixedHomotopy f I w (c j) (g j) t A.val :=
    finiteOpenGlue_eq hKd _ hA
  have hK : ContinuousOn K (Icc (0:ℝ) 1 ×ˢ U) :=
    finiteOpenGlue_continuousOn_prod hSo hSd _
      (fun j => hf.mixedHomotopy_continuousOn hI (hc j) (hcn j) (g j) (hg j))
  have hC : IsCompact C := hf.level_hits_compact hI c hc hcn hd hcover g hg z
  have hCU : C ⊆ U := by
    rintro A ⟨p,rfl,t,ht,he⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover p.property.1)
    have hF : fibreHomotopy f I (c j) (g j) t p.val.1 p.val.2 = z :=
      (levelHomotopy_eq hd g hj t).symm.trans he
    have hunit : IsUnit (rankOne p.val.1 + p.val.2) := by
      by_contra hnu
      exact hf.fibreHomotopy_boundary_misses hI (hc j) (hcn j) p.property.1.1
        (interior_subset hj) (g j) hε (hge j) z hz ht p.property.2 hnu hF
    apply mem_iUnion.mpr
    refine ⟨j,?_⟩
    exact balancedFibre_chart p.property.1.1 (hf.orientedLevel_inner_pos hI hw hwi hr p.property.1)
      (orientedLevel_cone hr p.property.1) hj p.property.2 hunit
  have hH : Continuous H := (PiLp.continuous_toLp 2 _).comp
    (hf.signedExtension_continuousOn.comp_continuous continuous_subtype_val (fun A => A.property.1))
  have hHz : ∀ A : traceSphere ν, H A ≠ 0 := by
    intro A h
    have hzero : signedExtension f A.val = 0 := WithLp.toLp_injective 2 h
    exact traceSphere_ne_zero A.property ((hf.signedExtension_eq_zero_iff A.property.1).mp hzero)
  have hK0 : ∀ A ∈ U, K (0,A) = H A := by
    intro A hA
    obtain ⟨j,hj⟩ := mem_iUnion.mp hA
    rw [hKe j A hj 0]
    exact hf.mixedHomotopy_zero hmax (g j) A.property.1 hj
  have hKz : ∀ t ∈ Icc (0:ℝ) 1, ∀ A ∈ U, K (t,A) ≠ 0 := by
    intro t ht A hA
    obtain ⟨j,hj⟩ := mem_iUnion.mp hA
    rw [hKe j A hj t]
    exact hf.mixedHomotopy_nonzero hI (g j) t hj
  have houtside : ∀ A ∉ U, H A ∉ B := by
    rintro A hAU ⟨d,hdp,he⟩
    obtain ⟨hunit,hline,hAw,hm,hlevel⟩ := hf.original_ray_level hI hmax hw hwi hr hro hrs
      (fun i => hε.trans (hz i)) hzs A.property hdp he
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover hlevel)
    exact hAU (mem_iUnion.mpr ⟨j,hunit,hline,hAw,hm,orientedLevel_cone hr hlevel,hj⟩)
  have hhits : ∀ t ∈ Icc (0:ℝ) 1, ∀ A ∈ U, K (t,A) ∈ B → A ∈ C := by
    rintro t ht A hAU ⟨d,hdp,he⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hAU
    rw [hKe j A hj t] at he
    obtain ⟨hl,hF,hA⟩ := hf.mixedHomotopy_hit hI hmax (hc j) (hcn j) (g j) (hgs j)
      hro hrs hzs ht hdp A.property hj he
    let p : levelFibre f w r := ⟨(lineRepresentative w A.val,negativeFibre A.val),hl,purityChart_fibre hj⟩
    refine ⟨p,Subtype.ext hA.symm,t,ht,?_⟩
    exact (levelHomotopy_eq hd g hj.2.2.2.2.2 t).trans hF
  have hend : ∀ A ∈ U, K (1,A) ∉ B := by
    rintro A hAU ⟨d,hdp,he⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hAU
    rw [hKe j A hj 1] at he
    obtain ⟨-,hF,-⟩ := hf.mixedHomotopy_hit hI hmax (hc j) (hcn j) (g j) (hgs j)
      hro hrs hzs ⟨zero_le_one,le_rfl⟩ hdp A.property hj he
    rw [fibreHomotopy_one f I (hcn j) (purityChart_unit hj) (g j) (purityChart_fibre hj)] at hF
    exact hgm j _ (centeredFibre_mem (hcn j) (purityChart_unit hj) (purityChart_fibre hj)) hF
  let : CompactSpace (traceSphere ν) := isCompact_iff_compactSpace.mp traceSphere_compact
  obtain ⟨G,hG,hG0,hGz,hGm⟩ := compact_local_homotopy (isOpen_iUnion hSo) hC hCU H hH hHz
    K hK hK0 hKz B houtside hhits hend
  have hy : y ≠ 0 := blockVector_nonzero hI (by norm_num) hr z
  obtain ⟨A,d,hd,he⟩ := hf.traceHomotopy_ray hdim hn G hG hG0 hGz hy
  exact hGm A ⟨d,hd,he⟩

end ChartSurgery
end BorsukNine

end OAI
