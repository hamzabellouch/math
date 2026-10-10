import OAI.NumberTheory.DukePrimeDegree.Dynamics.TransverseReturnCoordinates
import Mathlib.Topology.Compactness.Lindelof

namespace OAI

/-! # Countably many small upper-root boxes

Both the relative group displacement and the transverse logarithmic
coordinates are controlled on each box. The radius can be chosen before
the atlas, as required by the height-dependent injectivity estimates.
-/

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

private theorem exists_small_upperRoot_product (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ (S : Set (UpperRootTransverse n)) (T : Set (UpperRootTime n)),
      IsOpen S ∧ IsOpen T ∧ upperRootIdentity n ∈ S ∧
      (completeRootChain n).zeroTime ∈ T ∧
      (∀ z ∈ S ×ˢ T, ∀ w ∈ S ×ˢ T,
        (upperRootParam n z)⁻¹*upperRootParam n w ∈ matrixBall n r) ∧
      ∀ z ∈ S ×ˢ T, ∀ i, |transverseLogDiagonal z.1 i| ≤ 1 := by
  let z₀ := (upperRootIdentity n,(completeRootChain n).zeroTime)
  have hc : Continuous (fun p :
      (UpperRootTransverse n × UpperRootTime n) ×
        (UpperRootTransverse n × UpperRootTime n) =>
      (upperRootParam n p.1)⁻¹*upperRootParam n p.2) :=
    ((upperRootParam_isOpenEmbedding n).continuous.comp continuous_fst).inv.mul
      ((upperRootParam_isOpenEmbedding n).continuous.comp continuous_snd)
  have hball : (fun p :
      (UpperRootTransverse n × UpperRootTime n) ×
        (UpperRootTransverse n × UpperRootTime n) =>
      (upperRootParam n p.1)⁻¹*upperRootParam n p.2) ⁻¹' matrixBall n r ∈
        𝓝 (z₀,z₀) := by
    apply hc.continuousAt.preimage_mem_nhds
    simpa only [inv_mul_cancel] using
      (matrixBall_isOpen n r).mem_nhds (one_mem_matrixBall n hr)
  obtain ⟨U,V,hU,hzU,hV,hzV,hUV⟩ := mem_nhds_prod_iff'.mp hball
  let D : Set (UpperRootTransverse n × UpperRootTime n) :=
    {z | ∀ i, |transverseLogDiagonal z.1 i| < 1}
  have hD : IsOpen D := by
    simp only [D,ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt
      (((continuous_apply i).comp (continuous_transverseLogDiagonal n)).comp
        continuous_fst).abs continuous_const
  have hzD : z₀ ∈ D := by
    intro i
    change |Real.log (|(1 : Matrix (Fin n) (Fin n) ℝ) i i|)| < 1
    simp
  have hnhds : U ∩ V ∩ D ∈ 𝓝 z₀ :=
    ((hU.inter hV).inter hD).mem_nhds ⟨⟨hzU,hzV⟩,hzD⟩
  obtain ⟨S,T,hS,hzS,hT,hzT,hST⟩ := mem_nhds_prod_iff'.mp hnhds
  refine ⟨S,T,hS,hT,hzS,hzT,?_,?_⟩
  · intro z hz w hw
    exact @hUV (z,w) (show (z,w) ∈ U ×ˢ V from
      ⟨(@hST z hz).1.1,(@hST w hw).1.2⟩)
  · intro z hz i
    exact ((hST hz).2 i).le

theorem exists_small_upperRootBox_at (n : ℕ) (x : X n)
    {r : ℝ} (hr : 0 < r) :
    ∃ (g : G n) (B : UpperRootBox n g), x ∈ B.range ∧
      (∀ z w : B.domain,
        (upperRootParam n z.val)⁻¹*upperRootParam n w.val ∈ matrixBall n r) ∧
      ∀ z : B.domain, ∀ i, |transverseLogDiagonal z.val.1 i| ≤ 1 := by
  classical
  obtain ⟨S,T,hS,hT,hzS,hzT,hrel,hlog⟩ := exists_small_upperRoot_product n hr
  induction x using Quotient.inductionOn with
  | h g =>
    let z₀ := (upperRootIdentity n,(completeRootChain n).zeroTime)
    obtain ⟨B,hB⟩ := exists_upperRootBox_at_coordinates n g z₀
    let C : UpperRootBox n g := B.shrink (B.transverse ∩ S) (B.time ∩ T)
      (B.transverse_open.inter hS) (B.time_open.inter hT) inter_subset_left inter_subset_left
    refine ⟨g,C,⟨⟨z₀,⟨hB.1,hzS⟩,⟨hB.2,hzT⟩⟩,?_⟩,?_,?_⟩
    · change Quotient.mk _ (g*upperRootParam n z₀)=Quotient.mk _ g
      rw [upperRootParam_zero,mul_one]
    · intro z w
      exact hrel z.val ⟨z.prop.1.2,z.prop.2.2⟩ w.val ⟨w.prop.1.2,w.prop.2.2⟩
    · intro z i
      exact hlog z.val ⟨z.prop.1.2,z.prop.2.2⟩ i

theorem exists_countable_small_upperRoot_atlas (n : ℕ)
    {r : ℝ} (hr : 0 < r) :
    ∃ (g : ℕ → G n) (B : ∀ i, UpperRootBox n (g i)),
      (∀ x : X n, ∃ i, x ∈ (B i).range) ∧
      (∀ i, ∀ z w : (B i).domain,
        (upperRootParam n z.val)⁻¹*upperRootParam n w.val ∈ matrixBall n r) ∧
      ∀ i, ∀ z : (B i).domain, ∀ j, |transverseLogDiagonal z.val.1 j| ≤ 1 := by
  classical
  choose g B hx hrel hlog using fun x : X n => exists_small_upperRootBox_at n x hr
  have hopen (x : X n) : IsOpen (B x).range := (B x).embedding.isOpen_range
  obtain ⟨f,hf⟩ := (HereditarilyLindelofSpace.isLindelof (univ : Set (X n))).indexed_countable_subcover
    (fun x => (B x).range) hopen (by
      intro x _
      exact mem_iUnion.mpr ⟨x,hx x⟩)
  refine ⟨fun i => g (f i),fun i => B (f i),?_,fun i => hrel (f i),fun i => hlog (f i)⟩
  intro x
  exact mem_iUnion.mp (hf (mem_univ x))

end DukePrimeDegree

end

end OAI
