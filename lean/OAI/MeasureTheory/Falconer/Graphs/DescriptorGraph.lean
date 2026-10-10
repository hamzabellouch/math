import OAI.MeasureTheory.Falconer.Estimates.SuffixScales
import OAI.MeasureTheory.Falconer.Graphs.EligibleDyadicGraph

namespace OAI

/-! # Actual descriptor counts supply the local graph witnesses -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem parallelGoodSet_local_test (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (X P : List (Fin d → Bool)) (hX : X.length = a)
    (w : Sphere d) (W T : ℝ) (hT : 0 ≤ T)
    (hw : w ∈ Regularization.parallelGoodSet Q ρ g p (X++P) W T) :
    DyadicParallelTest (Q.descendant X) ((Q.descendant X).occupiedPaths ρ (p-a))
      (g-a) P w W ⌈T⌉₊ := by
  have hscale : (Q.descendant X).side/(2:ℝ)^(g-a) = 1/(2:ℝ)^g := by
    rw [Q.descendant_side,hX,hQ,div_div,← pow_add,Nat.add_sub_of_le hag]
  let S := ((Q.descendant X).occupiedPaths ρ (p-a)).filter fun z =>
    z.take (g-a) = P.take (g-a) ∧
    ‖((Q.descendant X).descendant z).center-((Q.descendant X).descendant P).center‖ ≤
      Real.sqrt d*((Q.descendant X).side/(2:ℝ)^(g-a)) ∧
    ‖perpendicularPart (w:Space d)
      (((Q.descendant X).descendant z).center-((Q.descendant X).descendant P).center)‖ ≤ W
  have hinj : Function.Injective (fun z : List (Fin d → Bool) => X++z) := by
    intro u v huv
    exact List.append_cancel_left huv
  have hsub : S.image (fun z => X++z) ⊆
      (Regularization.parallelTestCells Q ρ g p (X++P)).filter (fun z =>
        ‖perpendicularPart (w:Space d) ((Q.descendant z).center-(Q.descendant (X++P)).center)‖ ≤ W) := by
    intro z hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hu,_,hdist,hperp⟩ := Finset.mem_filter.mp hu
    obtain ⟨hu,hocc⟩ := Finset.mem_filter.mp hu
    have hulen := (mem_cubePaths _ _ _).mp hu
    apply Finset.mem_filter.mpr
    constructor
    · simp only [Regularization.parallelTestCells,Regularization.occupiedCenterCells,
        Finset.mem_filter]
      refine ⟨?_,?_,?_⟩
      · apply (mem_cubePaths _ _ _).mpr
        simp only [List.length_append,hX,hulen]
        omega
      · simpa only [Q.descendant_append] using hocc
      · rw [mem_ball,dist_eq_norm,Q.descendant_append,Q.descendant_append]
        apply hdist.trans_lt
        rw [hscale]
        have hs := sqrt_dimension_le d
        have hr : Real.sqrt d < 10*((d:ℝ)+1) := by
          nlinarith [Nat.cast_nonneg (α := ℝ) d]
        simpa only [div_eq_mul_inv,one_mul] using
          mul_lt_mul_of_pos_right hr (by positivity : 0 < 1/(2:ℝ)^g)
    · simpa only [Q.descendant_append] using hperp
  have hcard : S.card ≤ Regularization.parallelTestCount Q ρ g p (X++P) W w := by
    calc
      S.card = (S.image (fun z => X++z)).card :=
        (Finset.card_image_of_injective S hinj).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hcount : (Regularization.parallelTestCount Q ρ g p (X++P) W w : ℝ) ≤ T := by
    unfold Regularization.parallelGoodSet at hw
    split_ifs at hw with hocc
    · simpa only [ENNReal.toReal_natCast,ENNReal.toReal_ofReal hT] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hw
    · exact False.elim hw
  exact hcard.trans ((Nat.cast_le (α := ℝ)).mp (hcount.trans (Nat.le_ceil T)))

theorem descriptorEndpointGood_graph_test (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (X P : List (Fin d → Bool)) (hX : X.length = a) (hP : P.length = p-a)
    {x : Space d} (hx : x ∈ ((Q.descendant X).descendant P).carrier)
    (w : Sphere d)
    (hw : (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i (.parallel g p)) :
    DyadicParallelTest (Q.descendant X) ((Q.descendant X).occupiedPaths ρ (p-a))
      (g-a) P w (angularTestWidth N σ J i p)
      ⌈((2:ℝ)^N)^(PlanarFalconer.height
        (fun n : ℕ => m n-((d:ℝ)/2)*(n:ℝ)/N) g p+1000*((d:ℝ)+1)*σ)⌉₊ := by
  apply parallelGoodSet_local_test Q hQ ρ hag hgp X P hX w _ _ (by positivity)
  apply (descriptorEndpointGood_on_cell Q ρ m N σ J i (.parallel g p) (X++P) ?_
    (by simpa only [Q.descendant_append] using hx) w).mp hw
  simp only [PlanarFalconer.descriptorAnchor,List.length_append,hX,hP]
  omega

theorem descriptorMask_graph_test (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    {a g p : ℕ} (hag : a ≤ g) (hgp : g ≤ p)
    (X P : List (Fin d → Bool)) (hX : X.length = a) (hP : P.length = p-a)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S,
      dist w c ≤ descriptorMaskRadius N σ (.parallel g p)/2)
    {x : Space d} (hx : x ∈ ((Q.descendant X).descendant P).carrier) (w : Sphere d)
    (hw : descriptorMask Q ρ m N σ J i (.parallel g p) S x w ≠ 0) :
    DyadicParallelTest (Q.descendant X) ((Q.descendant X).occupiedPaths ρ (p-a))
      (g-a) P w (angularTestWidth N σ J (i+1) p)
      ⌈((2:ℝ)^N)^(PlanarFalconer.height
        (fun n : ℕ => m n-((d:ℝ)/2)*(n:ℝ)/N) g p+1000*((d:ℝ)+1)*σ)⌉₊ :=
  descriptorEndpointGood_graph_test Q hQ ρ m N σ J (i+1) hag hgp X P hX hP hx w
    (descriptorMask_support Q ρ m N σ J i (.parallel g p) S hcover w hw)

end Falconer

end OAI
