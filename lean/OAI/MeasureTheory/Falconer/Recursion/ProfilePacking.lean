import OAI.MeasureTheory.Falconer.Estimates.RegularClasses
import OAI.MeasureTheory.Falconer.Geometry.DyadicBallCount

namespace OAI

/-! # Local occupied-cell counts from the original class profiles -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

noncomputable def occupiedCenterCells (Q : DyadicCube d) (ν : Measure (Space d))
    (p : ℕ) (x : Space d) (r : ℝ) : Finset (CellPath d) := by
  classical
  exact (cubePaths d p).filter fun q => 0 < ν (Q.descendant q).carrier ∧
    (Q.descendant q).center ∈ ball x r

theorem occupied_center_count_le (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ν : Measure (Space d)) [IsFiniteMeasure ν] {g p : ℕ} (hgp : g ≤ p)
    (x : Space d) {r C lo hi : ℝ} (hC : 0 ≤ C) (hr : r ≤ C*(Q.side/(2:ℝ)^g))
    (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hfine : ∀ q ∈ cubePaths d p, 0 < ν (Q.descendant q).carrier →
      lo ≤ (ν (Q.descendant q).carrier).toReal)
    (hcoarse : ∀ q ∈ cubePaths d g, 0 < ν (Q.descendant q).carrier →
      (ν (Q.descendant q).carrier).toReal ≤ hi) :
    ((occupiedCenterCells Q ν p x r).card:ℝ) ≤
      ((2*Nat.ceil (2*C+2*Real.sqrt d)+1)^d:ℕ)*hi/lo := by
  classical
  let S := occupiedCenterCells Q ν p x r
  let T := S.image (List.take g)
  have hS : S ⊆ cubePaths d p := Finset.filter_subset _ _
  have hT : T ⊆ cubePaths d g := by
    intro c hc
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
    have hl := (mem_cubePaths _ _ _).mp (hS hq)
    simp only [mem_cubePaths,List.length_take,hl,min_eq_left hgp]
  have hpos {q : CellPath d} (hq : q ∈ S) : 0 < ν (Q.descendant q).carrier :=
    (Finset.mem_filter.mp hq).2.1
  have hparent (q : CellPath d) : (Q.descendant q).carrier ⊆
      (Q.descendant (q.take g)).carrier := descendant_subset_take Q hQ q g
  have hcard : (T.card:ℝ) ≤ ((2*Nat.ceil (2*C+2*Real.sqrt d)+1)^d:ℕ) := by
    exact_mod_cast dyadic_ancestor_ball_count Q hQ S
      (fun q hq => (mem_cubePaths _ _ _).mp (hS hq)) hgp x hC hr
      (fun q hq => (mem_ball.mp (Finset.mem_filter.mp hq).2.2).le)
  have hcover : leafUnion Q S ⊆ leafUnion Q T := by
    intro z hz
    obtain ⟨q,hq,hz⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨q.take g,Finset.mem_image.mpr ⟨q,hq,rfl⟩,hparent q hz⟩
  have hsum : (S.card:ℝ)*lo ≤ (T.card:ℝ)*hi := by
    calc
      _ = ∑ _q ∈ S, lo := by simp
      _ ≤ ∑ q ∈ S, (ν (Q.descendant q).carrier).toReal :=
        Finset.sum_le_sum (fun q hq => hfine q (hS hq) (hpos hq))
      _ = (ν (leafUnion Q S)).toReal := (restriction_total_mass_real Q hQ ν hS).symm
      _ ≤ (ν (leafUnion Q T)).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hcover)
      _ = ∑ q ∈ T, (ν (Q.descendant q).carrier).toReal := restriction_total_mass_real Q hQ ν hT
      _ ≤ ∑ _q ∈ T, hi := by
        apply Finset.sum_le_sum
        intro c hc
        apply hcoarse c (hT hc)
        obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
        exact (hpos hq).trans_le (measure_mono (hparent q))
      _ = _ := by simp
  exact (le_div_iff₀ hlo).mpr (hsum.trans (mul_le_mul_of_nonneg_right hcard hhi))

theorem sourceClass_local_count (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) (x : Space d) {C : ℝ} (hC : 0 ≤ C) :
    ((occupiedCenterCells Q (sourceClass Q μ N B p₀) p x (C/(2:ℝ)^g)).card:ℝ) ≤
      ((2*Nat.ceil (2*(C/Q.side)+2*Real.sqrt d)+1)^d:ℕ)*((2:ℝ)^N)^
        (sourceProfile Q μ N B p₀ p-sourceProfile Q μ N B p₀ g+2*((d:ℝ)+1)*lam) := by
  have : IsProbabilityMeasure (sourceClass Q μ N B p₀) :=
    regularization_class_probability Q hQ μ N B hp₀
  let R : ℝ := (2:ℝ)^N
  have hRp : 0 < R := by dsimp [R]; positivity
  have hh := occupied_center_count_le Q hQ (sourceClass Q μ N B p₀) hgp x
    (C := C/Q.side) (by positivity) (r := C/(2:ℝ)^g)
    (div_mul_div_cancel₀ (ne_of_gt hQ)).ge
    (lo := R^(-((d:ℝ)+1)*lam)*R^(-sourceProfile Q μ N B p₀ p)) (by positivity)
    (hi := R^(((d:ℝ)+1)*lam)*R^(-sourceProfile Q μ N B p₀ g)) (by positivity)
    (fun q hq hpos => (sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp₀ hpN
      ((mem_cubePaths _ _ _).mp hq) hpos).1)
    (fun q hq hpos => (sourceClass_occupied_comparison Q hQ μ hN hB hwidth hlarge hp₀ (hgp.trans hpN)
      ((mem_cubePaths _ _ _).mp hq) hpos).2)
  apply hh.trans_eq
  rw [mul_div_assoc]
  congr 1
  rw [← Real.rpow_add hRp,← Real.rpow_add hRp,← Real.rpow_sub hRp]
  congr 1
  ring

end Falconer.Regularization

end OAI
