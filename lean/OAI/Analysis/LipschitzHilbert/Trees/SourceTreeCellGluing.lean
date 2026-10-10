import OAI.Analysis.LipschitzHilbert.Trees.SourceWhitneyGluing
import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeCells

namespace OAI

/-! Countable gluing on the actual horizontal Whitney cells and
half-open transverse cells. A finite rectangle bound suffices. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid
variable {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
variable (hne : tiles.Nonempty) (hpos : ∀ i∈tiles, 0<ell i)

abbrev ProductCellIndex := CellIndex tiles x ell × ℤ

def productCell (b W : ℝ) (i : ProductCellIndex tiles x ell) : Set (ℝ×ℝ) :=
  partitionCell b W (i.1.val,i.2)

theorem productCell_measurable (b W : ℝ) (i : ProductCellIndex tiles x ell) :
    MeasurableSet (productCell tiles x ell b W i) := partitionCell_measurable b W _

theorem productCell_disjoint (b W : ℝ) (hW : 0<W) :
    Pairwise (fun i j : ProductCellIndex tiles x ell =>
      Disjoint (productCell tiles x ell b W i) (productCell tiles x ell b W j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  by_cases he : i.1=j.1
  · have hn : i.2≠j.2 := by
      intro hn
      exact hij (Prod.ext he hn)
    exact Set.disjoint_left.mp (transverseCell_disjoint b W hW hn) hzi.2 hzj.2
  · have hv : i.1.val≠j.1.val := fun h => he (Subtype.ext h)
    exact Set.disjoint_left.mp
      (whitney_disjoint tiles x ell i.1.property j.1.property hv) hzi.1 hzj.1

include hne hpos in
theorem productCell_iUnion (b W : ℝ) (hW : 0<W) :
    (⋃ i : ProductCellIndex tiles x ell, productCell tiles x ell b W i)=univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨i,hi⟩ := exists_cellIndex tiles x ell hne hpos z.1
  exact mem_iUnion.mpr ⟨(i,⌊(z.2-b)/W+1/2⌋),hi,mem_transverseCell_floor b W z.2 hW⟩

variable {V : Type*} [NormedAddCommGroup V]

/-- Any finite collection is dominated by its finite rectangle of
horizontal and transverse indices. -/
theorem product_finite_bound
    (F : ProductCellIndex tiles x ell → ℝ) (hF : ∀ i, 0≤F i) (C : ℝ)
    (hrect : ∀ (S : Finset (CellIndex tiles x ell)) (T : Finset ℤ),
      (∑ i∈S×ˢT, F i)≤C) (A : Finset (ProductCellIndex tiles x ell)) :
    (∑ i∈A, F i)≤C := by
  classical
  apply le_trans _ (hrect (A.image Prod.fst) (A.image Prod.snd))
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hi,Finset.mem_image_of_mem _ hi⟩
  · intro i _ _
    exact hF i

/-- Integrability of the pasted function follows from the proved local
integrals and their uniform finite-rectangle bound. -/
theorem product_paste_integrable_bound (b W : ℝ) (hW : 0<W)
    (F : CellIndex tiles x ell → ℝ×ℝ → V)
    (hF : ∀ i : ProductCellIndex tiles x ell,
      IntegrableOn (F i.1) (productCell tiles x ell b W i) (volume.prod volume))
    (C : ℝ) (hrect : ∀ (S : Finset (CellIndex tiles x ell)) (T : Finset ℤ),
      (∑ i∈S×ˢT, ∫ z in productCell tiles x ell b W i, ‖F i.1 z‖ ∂volume.prod volume)≤C) :
    Integrable (paste tiles x ell hne hpos F) (volume.prod volume) ∧
      (∫ z, ‖paste tiles x ell hne hpos F z‖ ∂volume.prod volume)≤C := by
  let G := paste tiles x ell hne hpos F
  have heq (i : ProductCellIndex tiles x ell) {z : ℝ×ℝ}
      (hz : z∈productCell tiles x ell b W i) : G z=F i.1 z := by
    dsimp [G,paste]
    rw [indexAt_eq_of_mem tiles x ell hne hpos i.1 hz.1]
  have hlocal (i : ProductCellIndex tiles x ell) :
      IntegrableOn G (productCell tiles x ell b W i) (volume.prod volume) :=
    (hF i).congr_fun (fun z hz => (heq i hz).symm) (productCell_measurable tiles x ell b W i)
  have hint (i : ProductCellIndex tiles x ell) :
      (∫ z in productCell tiles x ell b W i, ‖G z‖ ∂volume.prod volume)=
        ∫ z in productCell tiles x ell b W i, ‖F i.1 z‖ ∂volume.prod volume :=
    setIntegral_congr_fun (productCell_measurable tiles x ell b W i)
      (fun _ hz => congrArg norm (heq i hz))
  have hbound (A : Finset (ProductCellIndex tiles x ell)) :
      (∑ i∈A, ∫ z in productCell tiles x ell b W i, ‖G z‖ ∂volume.prod volume)≤C := by
    simpa only [hint] using product_finite_bound tiles x ell
      (fun i => ∫ z in productCell tiles x ell b W i, ‖F i.1 z‖ ∂volume.prod volume)
      (fun _ => integral_nonneg (fun _ => norm_nonneg _)) C hrect A
  have hs : Summable (fun i : ProductCellIndex tiles x ell =>
      ∫ z in productCell tiles x ell b W i, ‖G z‖ ∂volume.prod volume) :=
    summable_of_sum_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hbound
  have hi := integrableOn_iUnion_of_summable_integral_norm hlocal hs
  rw [productCell_iUnion tiles x ell hne hpos b W hW,integrableOn_univ] at hi
  refine ⟨hi,?_⟩
  have hpart := integral_iUnion (μ:=volume.prod volume) (f:=fun z => ‖G z‖)
    (productCell_measurable tiles x ell b W) (productCell_disjoint tiles x ell b W hW)
    hi.norm.integrableOn
  rw [productCell_iUnion tiles x ell hne hpos b W hW,setIntegral_univ] at hpart
  rw [hpart]
  exact Real.tsum_le_of_sum_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hbound

end LipschitzHilbert.SourceWhitney

end

end OAI
