import OAI.Computability.UniqueGames.Inverse.KMSBasisComparisonLemmas
import OAI.Computability.UniqueGames.Inverse.MatrixChartIntervalsLemmas

namespace OAI

section

/-! Local ordered-basis retention in the precise KMS vertex representation. -/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

private theorem relativeDensity_eq_expect_subtype {Ω : Type*} [Fintype Ω]
    (S : Finset Ω) (P : Ω → Prop) :
    KMS.relativeDensity S (Finset.univ.filter P) =
      𝔼 x : {x : Ω // P x}, if x.val ∈ S then (1 : ℝ) else 0 := by
  unfold KMS.relativeDensity
  rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp)
    (fun x => if x ∈ S then (1 : ℝ) else 0)]
  rw [Finset.sum_boole, Fintype.card_subtype]
  have hsets : S ∩ Finset.univ.filter P =
      (Finset.univ.filter P).filter (fun x => x ∈ S) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hsets]

/-- The ordered-basis test conditioned on its good event samples every full
Grassmann neighbor uniformly. The target observable is the original lifted
indicator, so this identity directly feeds the matrix-test retention bound. -/
theorem outsideNeighbor_retention {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    (𝔼 p : OutsideNeighborFactors X,
      liftedIndicator S (rankOneUpdate X p.1.val p.2.val)) =
        KMS.relativeDensity S (KMS.neighbors (rangeVertex X hX)) := by
  let e : MatrixChart.GrassmannNeighbors X.range ≃
      {W : KMS.Vertex n ell // KMS.Adjacent (rangeVertex X hX) W} :=
    MatrixChart.kmsNeighborsEquiv (rangeVertex X hX)
  let : Fintype (MatrixChart.GrassmannNeighbors X.range) :=
    Fintype.ofEquiv {W : KMS.Vertex n ell // KMS.Adjacent (rangeVertex X hX) W} e.symm
  let g : MatrixChart.GrassmannNeighbors X.range → ℝ :=
    fun W => if (e W).val ∈ S then 1 else 0
  calc
    _ = 𝔼 p : OutsideNeighborFactors X, g (outsideNeighborSample X hX p) := by
      apply Finset.expect_congr rfl
      intro p _
      unfold liftedIndicator
      rw [inLift_iff_rangeVertex_mem S _
        (injective_rankOneUpdate X hX p.1.val p.2.property)]
      have hv : rangeVertex (rankOneUpdate X p.1.val p.2.val)
          (injective_rankOneUpdate X hX p.1.val p.2.property) =
            (e (outsideNeighborSample X hX p)).val := by
        apply Subtype.ext
        rfl
      rw [hv]
      by_cases hp : (e (outsideNeighborSample X hX p)).val ∈ S <;> simp [g, hp]
    _ = 𝔼 W : MatrixChart.GrassmannNeighbors X.range, g W :=
      expect_outsideNeighborSample X hX g
    _ = 𝔼 W : {W : KMS.Vertex n ell // KMS.Adjacent (rangeVertex X hX) W},
        if W.val ∈ S then (1 : ℝ) else 0 :=
      Fintype.expect_equiv e _ _ (fun _ => rfl)
    _ = _ := (relativeDensity_eq_expect_subtype S
      (KMS.Adjacent (rangeVertex X hX))).symm

end
end UniqueGamesTheorem.Inverse.KMSBasisComparison

end

end OAI
