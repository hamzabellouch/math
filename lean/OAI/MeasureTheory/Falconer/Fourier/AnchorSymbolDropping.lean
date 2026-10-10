import OAI.MeasureTheory.Falconer.Angular.InheritedAngularSymbols

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem spatialAnchorMask_eq_on_child (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (n : ℕ) (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d)
    (P : CellPath) (hn : n ≤ P.length) {x y : Plane}
    (hx : x ∈ (Q.descendant P).carrier) (hy : y ∈ (Q.descendant P).carrier) (dir : UnitCircle) :
    spatialAnchorMask Q ρ n G d hd x dir = spatialAnchorMask Q ρ n G d hd y dir := by
  classical
  have hp : (P.take n).length = n := by simp [List.length_take, Nat.min_eq_left hn]
  have hxP := Q.descendant_subset_take hQ P n hx
  have hyP := Q.descendant_subset_take hQ P n hy
  unfold spatialAnchorMask
  apply Finset.sum_congr rfl
  intro c hc
  have hlen : c.length = n := (mem_dyadicPaths n c).mp (Finset.mem_filter.mp hc).1
  by_cases he : c = P.take n
  · subst c; simp [hxP,hyP]
  · have hh := Q.descendants_disjoint hQ (hlen.trans hp.symm) he
    have hxc : x ∉ (Q.descendant c).carrier := fun h => Set.disjoint_left.mp hh h hxP
    have hyc : y ∉ (Q.descendant c).carrier := fun h => Set.disjoint_left.mp hh h hyP
    simp [hxc,hyc]

 theorem descriptorAngleMask_eq_on_child (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (P : CellPath) (hb : descriptorAnchor b ≤ P.length)
    {x y : Plane} (hx : x ∈ (Q.descendant P).carrier) (hy : y ∈ (Q.descendant P).carrier) :
    descriptorAngleMask Q ρ m N lam sig J i b x = descriptorAngleMask Q ρ m N lam sig J i b y := by
  funext θ
  exact spatialAnchorMask_eq_on_child Q hQ ρ _ _ _ _ P hb hx hy _

 theorem inheritedMaskProduct_zero_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : ι → Plane)
    (K : ℕ) (hK : ∑ a ∈ S, k a ≤ K) (θ : ℝ) :
    ‖inheritedMaskProduct S b k Q ρ m N lam sig J i x θ‖ ≤ symbolDerivativeConstant K^K := by
  let D := ∑ a ∈ S, (sourceAngularRadius N sig (descriptorLength (b a)))⁻¹
  have hp a : 0 ≤ (sourceAngularRadius N sig (descriptorLength (b a)))⁻¹ :=
    inv_nonneg.mpr (sourceAngularRadius_pos _ _ _).le
  have hD : 0 ≤ D := Finset.sum_nonneg (fun a _ => hp a)
  have hh := inheritedMaskProduct_bound S b k Q hQ ρ m N lam sig J i x K 0 hK D hD
    (fun a ha => Finset.single_le_sum (fun a _ => hp a) ha) θ
  simpa using hh

 theorem inheritedMaskProduct_split {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath)
    {x z : Plane} (hx : x ∈ (Q.descendant P).carrier) (hz : z ∈ (Q.descendant P).carrier) :
    inheritedMaskProduct S b k Q ρ m N lam sig J i (fun _ => x) =
      fun θ => inheritedMaskProduct (S.filter fun a => descriptorAnchor (b a) ≤ P.length)
        b k Q ρ m N lam sig J i (fun _ => z) θ *
      inheritedMaskProduct (S.filter fun a => P.length < descriptorAnchor (b a))
        b k Q ρ m N lam sig J i (fun _ => x) θ := by
  classical
  funext θ
  have he : inheritedMaskProduct (S.filter fun a => descriptorAnchor (b a) ≤ P.length)
      b k Q ρ m N lam sig J i (fun _ => x) θ =
      inheritedMaskProduct (S.filter fun a => descriptorAnchor (b a) ≤ P.length)
      b k Q ρ m N lam sig J i (fun _ => z) θ := by
    apply Finset.prod_congr rfl
    intro a ha
    have ha := (Finset.mem_filter.mp ha).2
    rw [descriptorAngleMask_eq_on_child Q hQ ρ m N lam sig J i (b a) P ha hx hz]
  rw [← he]
  unfold inheritedMaskProduct
  symm
  convert Finset.prod_filter_mul_prod_filter_not S (fun a => descriptorAnchor (b a) ≤ P.length)
    (fun a => normalizedMaskFactor (descriptorAngleMask Q ρ m N lam sig J i (b a) x)
      (sourceAngularRadius N sig (descriptorLength (b a))) (k a) θ) using 1
  simp

 theorem inheritedMaskProduct_removed_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath) (z : Plane)
    (K : ℕ) (hK : ∑ a ∈ S, k a ≤ K) (θ : ℝ) :
    ‖inheritedMaskProduct (S.filter fun a => descriptorAnchor (b a) ≤ P.length)
      b k Q ρ m N lam sig J i (fun _ => z) θ‖ ≤ symbolDerivativeConstant K^K := by
  apply inheritedMaskProduct_zero_bound _ _ _ Q hQ _ _ _ _ _ _ _ _ K _ θ
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => Nat.zero_le _)).trans hK

end PlanarFalconer

end OAI
