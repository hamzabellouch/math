import OAI.MeasureTheory.Falconer.Recursion.IntermediateProfiles

namespace OAI

/-!
# Profile lower bounds from the original mass law

An original s-ball estimate yields the lower profile bound after paying
for class normalization and the dimension-dependent interpolation loss.
-/

namespace Falconer.Regularization
open MeasureTheory Set
open scoped ENNReal
variable {d : ℕ}

theorem sourceClass_occupied_comparison (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p : CellPath d} (hp : p ∈ regularizationLeaves Q μ N)
    {n : ℕ} (hn : n ≤ N) {P : CellPath d} (hP : P.length = n)
    (hpos : 0 < sourceClass Q μ N B p (Q.descendant P).carrier) :
    ((2:ℝ)^N)^(-((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile Q μ N B p n) ≤
      (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ∧
    (sourceClass Q μ N B p (Q.descendant P).carrier).toReal ≤
      ((2:ℝ)^N)^(((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile Q μ N B p n) := by
  classical
  have : IsProbabilityMeasure (sourceClass Q μ N B p) := regularization_class_probability Q hQ μ N B hp
  apply sourceClass_all_depth_comparison Q hQ μ hN hB hwidth hlarge hp hn
  apply normalizedClass_occupied_prefix Q hQ μ hn
    (show regularizationLeaves Q μ N ⊆ cubePaths d N from Finset.filter_subset _ _)
    (regularizationLabel Q μ N B) (regularizationLabel Q μ N B p) hP
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top (sourceClass Q μ N B p) _)

theorem normalizedClass_real_le (Q : DyadicCube d) (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (L : Finset (CellPath d)) (F : CellPath d → List ℕ) (T : List ℕ) {t : ℝ} (ht : 0 < t)
    (hmass : t ≤ (classMeasure Q μ L F T univ).toReal) (S : Set (Space d)) :
    (normalizedClass Q μ L F T S).toReal ≤ (μ S).toReal/t := by
  rw [normalizedClass_real]
  have hr : ((μ.restrict (leafUnion Q (classLeaves L F T))) S).toReal ≤ (μ S).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (Measure.restrict_apply_le _ _)
  have hm : t ≤ (μ (leafUnion Q (classLeaves L F T))).toReal := by
    simpa only [classMeasure,Measure.restrict_apply_univ] using hmass
  exact div_le_div₀ ENNReal.toReal_nonneg hr ht hm

theorem sourceProfile_frostman_lower (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p : CellPath d} (hp : p ∈ regularizationLeaves Q μ N)
    (hmass : ((2:ℝ)^N)^(-lam) ≤
      (classMeasure Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
        (regularizationLabel Q μ N B p) Set.univ).toReal)
    (hcell : ∀ n ≤ N, ∀ P : CellPath d, P.length = n →
      (μ (Q.descendant P).carrier).toReal ≤
        ((2:ℝ)^N)^lam * ((2:ℝ)^N)^(-s*(n:ℝ)/(N:ℝ)))
    {n : ℕ} (hn : n ≤ N) :
    s*(n:ℝ)/(N:ℝ)-((d:ℝ)+3)*lam ≤ sourceProfile Q μ N B p n := by
  classical
  let R : ℝ := (2:ℝ)^N
  have hR : 1 < R := one_lt_pow₀ (by norm_num : (1:ℝ) < 2) hN.ne'
  have hRp : 0 < R := (zero_lt_one.trans hR)
  have hpN : p.length = N := (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1
  have hPn : (p.take n).length = n := by simp [List.length_take,hpN,hn]
  have hpC : p ∈ classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B)
      (regularizationLabel Q μ N B p) := Finset.mem_filter.mpr ⟨hp, rfl⟩
  have hcomp := sourceClass_all_depth_comparison Q hQ μ hN hB hwidth hlarge hp hn
    (Finset.mem_image.mpr ⟨p,hpC,rfl⟩)
  have hnorm := normalizedClass_real_le Q μ (regularizationLeaves Q μ N)
    (regularizationLabel Q μ N B) (regularizationLabel Q μ N B p)
    (Real.rpow_pos_of_pos hRp (-lam)) hmass (Q.descendant (p.take n)).carrier
  have hu := hnorm.trans (div_le_div_of_nonneg_right (hcell n hn (p.take n) hPn) (by positivity))
  have hpow : R^(-((d:ℝ)+1)*lam-sourceProfile Q μ N B p n) ≤ R^(2*lam-s*(n:ℝ)/(N:ℝ)) := by
    have hh := hcomp.1.trans hu
    change R^(-((d:ℝ)+1)*lam)*R^(-sourceProfile Q μ N B p n) ≤
      (R^lam*R^(-s*(n:ℝ)/(N:ℝ)))/R^(-lam) at hh
    rw [← Real.rpow_add hRp,← Real.rpow_add hRp,← Real.rpow_sub hRp] at hh
    convert hh using 1
    congr 1
    ring
  have he := (Real.rpow_le_rpow_left_iff hR).mp hpow
  nlinarith

end Falconer.Regularization

end OAI
