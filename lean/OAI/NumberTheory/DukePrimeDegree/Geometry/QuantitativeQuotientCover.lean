import OAI.NumberTheory.DukePrimeDegree.Geometry.ConjugationRadius
import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientNeighborhoods

namespace OAI

/-! # Finite quotient covers with quantitative size control

Entrywise grids of bounded representatives give open covers of the
logarithmic quotient balls. Each member has uniformly small relative
lifts, and the number of members has an explicit grid bound.
-/

noncomputable section
open Set Matrix
open scoped Topology Matrix.Norms.Operator
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_quantitative_quotient_cover {n : ℕ} (hn : 0 < n)
    (R r : ℝ) (hr : 0 < r) :
    let δ := min 1 (r/(4*(n:ℝ)*Real.exp (R+1)))
    ∃ (N : ℕ) (V : Fin N → Set (X n)),
      (N:ℝ) ≤ (2*Real.exp (R+1)+2)^(n*n)/δ^(n*n) ∧
      (∀ i, IsOpen (V i)) ∧
      {x | quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ R} ⊆ ⋃ i, V i ∧
      ∀ i, ∀ x ∈ V i, ∀ y ∈ V i,
        ∃ g ∈ matrixBall n r, rightAction x g = y := by
  classical
  let B := Real.exp (R+1)
  let δ := min 1 (r/(4*(n:ℝ)*B))
  have hB : 0 < B := Real.exp_pos _
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδr : δ ≤ r/(4*(n:ℝ)*B) := min_le_right _ _
  have hbudget : (n:ℝ)*B*(2*δ) ≤ r/2 := by
    have H := (le_div_iff₀ (show 0 < 4*(n:ℝ)*B by positivity)).mp hδr
    nlinarith
  obtain ⟨s,_,hcard,hcover⟩ := cube_grid_cover (n*n) hB.le hδ hδ1
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let q (g : G n) (t : Fin (n*n)) : ℝ :=
    g.val (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
  let U (i : Fin (Fintype.card s)) : Set (G n) :=
    {g | matrixLogLength g < R+1 ∧ ∀ t, |q g t-(e i).val t| < δ}
  let V (i : Fin (Fintype.card s)) : Set (X n) :=
    Quotient.mk (QuotientGroup.rightRel (integralGroup n)) '' U i
  refine ⟨Fintype.card s,V,?_,?_,?_,?_⟩
  · simpa only [Fintype.card_coe] using hcard
  · intro i
    apply (quotient_covering n).isOpenMap
    apply IsOpen.inter (isOpen_lt (continuous_matrixLogLength n) continuous_const)
    change IsOpen {g : G n | ∀ t, |q g t-(e i).val t| < δ}
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro t
    apply isOpen_lt _ continuous_const
    dsimp [q]
    fun_prop
  · intro x hx
    obtain ⟨g,hg,hlen⟩ := exists_rightAction_length_lt
      (Quotient.mk _ (1 : G n)) x (by norm_num : (0:ℝ)<1)
    have hgR : matrixLogLength g < R+1 := by
      have H : quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ R := hx
      linarith
    have hgB : ∀ t, |q g t| ≤ B := by
      intro t
      exact (matrix_entry_abs_le_operator_norm g.val _ _).trans
        ((specialLinear_norm_le_exp_length hn g).trans
          (Real.exp_le_exp.mpr hgR.le))
    obtain ⟨c,hc,hgc⟩ := hcover (q g) hgB
    apply mem_iUnion.mpr
    refine ⟨e.symm ⟨c,hc⟩,g,?_,?_⟩
    · exact ⟨hgR,by simpa using hgc⟩
    · change Quotient.mk _ ((1 : G n)*g) = x at hg
      simpa only [one_mul] using hg
  · intro i x hx y hy
    obtain ⟨g,hg,rfl⟩ := hx
    obtain ⟨h,hh,rfl⟩ := hy
    have hginv : ∀ j k, |(g⁻¹).val j k| ≤ B := by
      intro j k
      apply (matrix_entry_abs_le_operator_norm _ j k).trans
      apply (specialLinear_norm_le_exp_length hn g⁻¹).trans
      rw [matrixLogLength_inv]
      exact Real.exp_le_exp.mpr hg.1.le
    have hdiff : ∀ j k, |h.val j k-g.val j k| ≤ 2*δ := by
      intro j k
      have hg' := hg.2 (finProdFinEquiv (j,k))
      have hh' := hh.2 (finProdFinEquiv (j,k))
      simp only [q,Equiv.symm_apply_apply] at hg' hh'
      calc
        _ = |(h.val j k-(e i).val (finProdFinEquiv (j,k))) +
            ((e i).val (finProdFinEquiv (j,k))-g.val j k)| := by congr 1; ring
        _ ≤ |h.val j k-(e i).val (finProdFinEquiv (j,k))| +
            |(e i).val (finProdFinEquiv (j,k))-g.val j k| := abs_add_le _ _
        _ ≤ 2*δ := by rw [abs_sub_comm ((e i).val _)]; linarith
    refine ⟨g⁻¹*h,?_,?_⟩
    · intro j k
      exact ((left_div_entry_bound g h hB.le hginv hdiff j k).trans hbudget).trans_lt
        (by linarith)
    · change Quotient.mk _ (g*(g⁻¹*h)) = Quotient.mk _ h
      congr 1
      group

end DukePrimeDegree

end

end OAI
