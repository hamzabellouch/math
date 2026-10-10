import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Recursion.DivisionBlocksControl

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory Filter
open scoped ENNReal Topology
variable {d : ℕ}
theorem regularization_label_count (μ : Measure (EuclideanSpace ℝ (Fin d))) (N B : ℕ) :
    ((regularizationLeaves μ N).image (regularizationLabel μ N B)).card ≤
      (d*N+1)^(N/B+1)*((d+2)*N+1) := by
  exact (blockLabel_card_le (regularizationLeaves_subset μ N) B
    (weightLeafLabel ((d+2)*N) (fun p => (μ (treeCell p)).toReal)) _).trans
    (Nat.mul_le_mul_left _ (weightLeafLabel_card_le _ _ _))

noncomputable def retainedClassLabels (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (N B : ℕ) (t : ℝ≥0∞) : Finset (List ℕ) := by
  classical
  let L := regularizationLeaves μ N
  let F := regularizationLabel μ N B
  exact (L.image F).filter fun T => t ≤ classMeasure μ L F T univ

noncomputable def retainedClassUnion (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (N B : ℕ) (t : ℝ≥0∞) : Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ T ∈ retainedClassLabels μ N B t,
    leafUnion (classLeaves (regularizationLeaves μ N) (regularizationLabel μ N B) T)

theorem retainedClassLabels_count (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (N B : ℕ) (t : ℝ≥0∞) : (retainedClassLabels μ N B t).card ≤
      (d*N+1)^(N/B+1)*((d+2)*N+1) := by
  exact (Finset.card_filter_le _ _).trans (regularization_label_count μ N B)

theorem retainedClass_mass_lower (μ : Measure (EuclideanSpace ℝ (Fin d)))
    {N B : ℕ} {t : ℝ≥0∞} {T : List ℕ} (hT : T ∈ retainedClassLabels μ N B t) :
    t ≤ classMeasure μ (regularizationLeaves μ N) (regularizationLabel μ N B) T univ :=
  (Finset.mem_filter.mp hT).2

theorem retainedClassUnion_measurable (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (N B : ℕ) (t : ℝ≥0∞) : MeasurableSet (retainedClassUnion μ N B t) :=
  Finset.measurableSet_biUnion _ (fun _ _ => leafUnion_measurable _)

theorem retainedClassUnion_mass (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (N B : ℕ) (t : ℝ≥0∞) : μ (retainedClassUnion μ N B t) =
      ∑ T ∈ retainedClassLabels μ N B t,
        classMeasure μ (regularizationLeaves μ N) (regularizationLabel μ N B) T univ := by
  classical
  simp only [classMeasure,Measure.restrict_apply_univ]
  apply measure_biUnion_finset
  · intro T _ U _ hne
    apply leafUnion_disjoint (N := N)
    · exact fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    · exact fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    · exact classLeaves_disjoint _ _ hne
  · intro T _; exact leafUnion_measurable _

theorem retainedClass_mass_sum_le_one
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (N B : ℕ) (t : ℝ≥0∞) :
    (∑ T ∈ retainedClassLabels μ N B t,
      classMeasure μ (regularizationLeaves μ N) (regularizationLabel μ N B) T univ) ≤ 1 := by
  rw [← retainedClassUnion_mass μ N B t]
  exact prob_le_one

theorem retainedClass_discard_mass
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (hcarry : μ (treeCell [])ᶜ = 0) (N B : ℕ) (t : ℝ≥0∞) :
    μ (retainedClassUnion μ N B t)ᶜ ≤
      (2:ℝ≥0∞)^(d*N) * ((2:ℝ≥0∞)^((d+2)*N))⁻¹ +
      (((d*N+1)^(N/B+1)*((d+2)*N+1):ℕ):ℝ≥0∞)*t := by
  classical
  let L := regularizationLeaves μ N
  let F := regularizationLabel μ N B
  let D := (L.image F).filter fun T => classMeasure μ L F T univ < t
  let bad := ⋃ T ∈ D, leafUnion (classLeaves L F T)
  have hcover : (retainedClassUnion μ N B t)ᶜ ⊆
      (leafUnion (dyadicPaths N \ L) ∪ bad) ∪ (treeCell [])ᶜ := by
    intro z hz
    by_cases hQz : z ∈ (treeCell [])
    · obtain ⟨p,hp,hzp⟩ := mem_iUnion₂.mp ((leafUnion_all N).symm ▸ hQz)
      by_cases hpL : p ∈ L
      · have hbad : classMeasure μ L F (F p) univ < t := by
          by_contra h
          apply hz
          exact mem_iUnion₂.mpr ⟨F p, Finset.mem_filter.mpr
            ⟨Finset.mem_image.mpr ⟨p,hpL,rfl⟩,not_lt.mp h⟩,
            mem_iUnion₂.mpr ⟨p,by exact Finset.mem_filter.mpr ⟨hpL,rfl⟩,hzp⟩⟩
        exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨F p, Finset.mem_filter.mpr
          ⟨Finset.mem_image.mpr ⟨p,hpL,rfl⟩,hbad⟩,
          mem_iUnion₂.mpr ⟨p,by exact Finset.mem_filter.mpr ⟨hpL,rfl⟩,hzp⟩⟩))
      · exact Or.inl (Or.inl (mem_iUnion₂.mpr ⟨p,Finset.mem_sdiff.mpr ⟨hp,hpL⟩,hzp⟩))
    · exact Or.inr hQz
  calc
    _ ≤ μ ((leafUnion (dyadicPaths N \ L) ∪ bad) ∪ (treeCell [])ᶜ) := measure_mono hcover
    _ ≤ μ (leafUnion (dyadicPaths N \ L) ∪ bad) + μ (treeCell [])ᶜ := measure_union_le _ _
    _ = μ (leafUnion (dyadicPaths N \ L) ∪ bad) := by rw [hcarry,add_zero]
    _ ≤ μ (leafUnion (dyadicPaths N \ L)) + μ bad := measure_union_le _ _
    _ ≤ (2:ℝ≥0∞)^(d*N) * ((2:ℝ≥0∞)^((d+2)*N))⁻¹ + ((L.image F).card:ℝ≥0∞)*t :=
      add_le_add (discarded_leaves_mass μ N _) (discarded_classes_mass μ L F t)
    _ ≤ _ := by
      apply add_le_add_right
      apply mul_le_mul_left
      exact_mod_cast regularization_label_count μ N B
theorem exists_bounded_regularization_control {lam : ℝ} (hlam : 0 < lam) :
    ∃ H N₀ : ℕ, 0 < H ∧ (H:ℝ) ≤ 1/lam+2 ∧ ∀ N ≥ N₀,
      0 < N ∧ 0 < N/H ∧ N/(N/H)+1 ≤ 2*H ∧
      ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) ∧
      (2:ℝ)^(N/(N/H)+2) ≤ ((2:ℝ)^N)^lam := by
  let H := Nat.floor (1/lam)+1
  have hH : 0 < H := by dsimp [H]; omega
  have hHlo : 1/lam < (H:ℝ) := by simpa only [H,Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (1/lam)
  have hHhi : (H:ℝ) ≤ 1/lam+2 := by
    have hh := Nat.floor_le (by positivity : 0 ≤ 1/lam)
    dsimp [H]
    push_cast
    linarith
  have hHl : 1 ≤ lam*(H:ℝ) := by
    have hh := (div_lt_iff₀ hlam).mp hHlo
    nlinarith
  obtain ⟨M,hM⟩ := exists_nat_gt (((2*H+1:ℕ):ℝ)/lam)
  refine ⟨H,max H M,hH,hHhi,?_⟩
  intro N hN
  have hHN : H ≤ N := (le_max_left _ _).trans hN
  have hMN : M ≤ N := (le_max_right _ _).trans hN
  have hc := division_blocks_control hH hHN
  refine ⟨lt_of_lt_of_le hH hHN,hc.1,hc.2,division_block_width hlam.le hHl,?_⟩
  have hreal : ((2*H+1:ℕ):ℝ) ≤ (N:ℝ)*lam := by
    have hm := (div_lt_iff₀ hlam).mp hM
    have hn : (M:ℝ) ≤ N := by exact_mod_cast hMN
    nlinarith
  have hcount : ((N/(N/H)+2:ℕ):ℝ) ≤ (N:ℝ)*lam := by
    have hh : N/(N/H)+2 ≤ 2*H+1 := by omega
    have hhR : ((N/(N/H)+2:ℕ):ℝ) ≤ ((2*H+1:ℕ):ℝ) := by exact_mod_cast hh
    exact hhR.trans hreal
  rw [← Real.rpow_natCast (2:ℝ) (N/(N/H)+2),← Real.rpow_natCast (2:ℝ) N,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hcount
theorem regularization_fixed_count_bound (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))
    {H N : ℕ} (hH : 0 < H) (hN : H ≤ N) :
    ((regularizationLeaves μ N).image (regularizationLabel μ N (N/H))).card ≤
      ((d+2)*N+1)^(2*H+1) := by
  have hc := regularization_label_count μ N (N/H)
  have hs := (division_blocks_control hH hN).2
  calc
    _ ≤ (d*N+1)^(N/(N/H)+1)*((d+2)*N+1) := hc
    _ ≤ ((d+2)*N+1)^(2*H)*((d+2)*N+1) := by
      apply Nat.mul_le_mul_right
      exact (Nat.pow_le_pow_left (by nlinarith) _).trans (Nat.pow_le_pow_right (by omega) hs)
    _ = _ := (pow_succ _ _).symm

theorem fixed_polynomial_subpower (k : ℕ) {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (((d+2:ℝ)*(N:ℝ)+1)^k) ≤ ((2:ℝ)^N)^e := by
  have hb : 1 < (2:ℝ)^e := Real.one_lt_rpow (by norm_num) he
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k hb).const_mul ((d+3:ℝ)^k)
  have hevent : ∀ᶠ N : ℕ in atTop, (d+3:ℝ)^k*((N:ℝ)^k/((2:ℝ)^e)^N) < 1 := by
    exact ht.eventually (gt_mem_nhds (by simp : (d+3:ℝ)^k*0 < (1:ℝ)))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 N₀,?_⟩
  intro N hN
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast ((le_max_left 1 N₀).trans hN)
  have hh := hN₀ N ((le_max_right 1 N₀).trans hN)
  rw [← mul_div_assoc] at hh
  have hp : 0 < ((2:ℝ)^e)^N := by positivity
  have hpol : ((d+2:ℝ)*(N:ℝ)+1)^k ≤ (d+3:ℝ)^k*(N:ℝ)^k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) k
  have hbound := hpol.trans ((div_lt_one hp).mp hh).le
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm e (N:ℝ),
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hbound
  exact hbound

theorem regularization_class_count_subpower (H : ℕ) (hH : 0 < H)
    {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      (((regularizationLeaves μ N).image (regularizationLabel μ N (N/H))).card:ℝ) ≤
        ((2:ℝ)^N)^e := by
  obtain ⟨N₁,hN₁⟩ := fixed_polynomial_subpower (2*H+1) he
  refine ⟨max H N₁,?_⟩
  intro N hN μ
  have hh := regularization_fixed_count_bound μ hH ((le_max_left H N₁).trans hN)
  have hhR : (((regularizationLeaves μ N).image (regularizationLabel μ N (N/H))).card:ℝ) ≤
      ((d+2:ℝ)*(N:ℝ)+1)^(2*H+1) := by exact_mod_cast hh
  exact hhR.trans (hN₁ N ((le_max_right H N₁).trans hN))

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}
theorem sourceClass_occupied_comparison (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p : (CellPath d)} (hp : p ∈ regularizationLeaves μ N)
    {n : ℕ} (hn : n ≤ N) {P : (CellPath d)} (hP : P.length = n)
    (hpos : 0 < sourceClass μ N B p (treeCell P)) :
    ((2:ℝ)^N)^(-((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile μ N B p n) ≤
      (sourceClass μ N B p (treeCell P)).toReal ∧
    (sourceClass μ N B p (treeCell P)).toReal ≤
      ((2:ℝ)^N)^(((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile μ N B p n) := by
  classical
  have : IsProbabilityMeasure (sourceClass μ N B p) := sourceClass_probability μ N B hp
  apply sourceClass_all_depth_comparison μ hN hB hwidth hlarge hp hn
  apply normalizedClass_occupied_prefix μ hn
    (show regularizationLeaves μ N ⊆ dyadicPaths N from Finset.filter_subset _ _)
    (regularizationLabel μ N B) (regularizationLabel μ N B p) hP
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top (sourceClass μ N B p) _)

theorem sourceProfile_upper (μ : Measure (EuclideanSpace ℝ (Fin d))) {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) (p : (CellPath d)) {u : ℝ} (hu : 0 ≤ u) (huN : u ≤ N) :
    sourceProfile μ N B p u ≤ (d:ℝ)*u/(N:ℝ) := by
  classical
  have hh := regularizedProfile_increment hN
    (show regularizationLeaves μ N ⊆ dyadicPaths N from Finset.filter_subset _ _)
    (regularizationLabel μ N B) hB p (le_refl 0) hu huN
  rw [regularizedProfile_zero,sub_zero,sub_zero] at hh
  exact hh.2

theorem normalizedClass_real_le (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
    (L : Finset (CellPath d)) (F : (CellPath d) → List ℕ) (T : List ℕ) {t : ℝ} (ht : 0 < t)
    (hmass : t ≤ (classMeasure μ L F T univ).toReal) (S : Set (EuclideanSpace ℝ (Fin d))) :
    (normalizedClass μ L F T S).toReal ≤ (μ S).toReal/t := by
  rw [normalizedClass_real]
  have hr : ((μ.restrict (leafUnion (classLeaves L F T))) S).toReal ≤ (μ S).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (Measure.restrict_apply_le _ _)
  have hm : t ≤ (μ (leafUnion (classLeaves L F T))).toReal := by
    simpa only [classMeasure,Measure.restrict_apply_univ] using hmass
  exact div_le_div₀ ENNReal.toReal_nonneg hr ht hm

theorem sourceProfile_frostman_lower (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam s : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p : (CellPath d)} (hp : p ∈ regularizationLeaves μ N)
    (hmass : ((2:ℝ)^N)^(-lam) ≤
      (classMeasure μ (regularizationLeaves μ N) (regularizationLabel μ N B)
        (regularizationLabel μ N B p) Set.univ).toReal)
    (hcell : ∀ n ≤ N, ∀ P : (CellPath d), P.length = n →
      (μ (treeCell P)).toReal ≤
        ((2:ℝ)^N)^lam * ((2:ℝ)^N)^(-s*(n:ℝ)/(N:ℝ)))
    {n : ℕ} (hn : n ≤ N) :
    s*(n:ℝ)/(N:ℝ)-((d:ℝ)+3)*lam ≤ sourceProfile μ N B p n := by
  classical
  let R : ℝ := (2:ℝ)^N
  have hR : 1 < R := one_lt_pow₀ (by norm_num : (1:ℝ) < 2) hN.ne'
  have hRp : 0 < R := (zero_lt_one.trans hR)
  have hpN : p.length = N := (mem_dyadicPaths _ _).mp (Finset.mem_filter.mp hp).1
  have hPn : (p.take n).length = n := by simp [List.length_take,hpN,hn]
  have hpC : p ∈ classLeaves (regularizationLeaves μ N) (regularizationLabel μ N B)
      (regularizationLabel μ N B p) := by simp [classLeaves,hp]
  have hcomp := sourceClass_all_depth_comparison μ hN hB hwidth hlarge hp hn
    (Finset.mem_image.mpr ⟨p,hpC,rfl⟩)
  have hnorm := normalizedClass_real_le μ (regularizationLeaves μ N)
    (regularizationLabel μ N B) (regularizationLabel μ N B p)
    (Real.rpow_pos_of_pos hRp (-lam)) hmass (treeCell (p.take n))
  have hu := hnorm.trans (div_le_div_of_nonneg_right (hcell n hn (p.take n) hPn) (by positivity))
  have hpow : R^(-((d:ℝ)+1)*lam-sourceProfile μ N B p n) ≤ R^(2*lam-s*(n:ℝ)/(N:ℝ)) := by
    have hh := hcomp.1.trans hu
    change R^(-((d:ℝ)+1)*lam)*R^(-sourceProfile μ N B p n) ≤
      (R^lam*R^(-s*(n:ℝ)/(N:ℝ)))/R^(-lam) at hh
    rw [← Real.rpow_add hRp,← Real.rpow_add hRp,← Real.rpow_sub hRp] at hh
    rw [show lam + -s*(n:ℝ)/(N:ℝ) - -lam = 2*lam-s*(n:ℝ)/(N:ℝ) by ring] at hh
    exact hh
  have he := (Real.rpow_le_rpow_left_iff hR).mp hpow
  nlinarith
theorem sourceProfile_affine_on_blocks (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))
    (N B : ℕ) (p : (CellPath d)) {i : ℕ} (hi : i < N/B+1) :
    ∃ a b : ℝ, ∀ u : ℝ, (blockDepth N B (i+1):ℝ) ≤ u → u ≤ (blockDepth N B i:ℝ) →
      sourceProfile μ N B p u = a*u+b := by
  let d := fun j => (blockDepth N B j:ℝ)
  let c := fun j => blockSlope (regularizationLeaves μ N) (regularizationLabel μ N B) N B j p
  refine ⟨c i,sourceProfile μ N B p (d (i+1))-c i*d (i+1),?_⟩
  intro u hlo hhi
  have hh := finiteRampProfile_affine_block d c
    (fun _ _ h => Nat.cast_le.mpr (blockDepth_antitone N B h)) hi (le_refl (d (i+1))) hlo hhi
  change sourceProfile μ N B p u - sourceProfile μ N B p (d (i+1)) = _ at hh
  linarith

theorem sourceProfile_adjusted_lipschitz (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : (CellPath d))
    {u v : ℝ} (hu : 0 ≤ u) (huN : u ≤ N) (hv : 0 ≤ v) (hvN : v ≤ N) :
    |(sourceProfile μ N B p v-(d:ℝ)/2*v/(N:ℝ))-(sourceProfile μ N B p u-(d:ℝ)/2*u/(N:ℝ))| ≤ (d:ℝ)/2*|v-u|/(N:ℝ) := by
  classical
  rcases le_total u v with huv | hvu
  · rw [abs_of_nonneg (sub_nonneg.mpr huv)]
    exact regularizedProfile_adjusted_increment hN
      (show regularizationLeaves μ N ⊆ dyadicPaths N from Finset.filter_subset _ _)
      (regularizationLabel μ N B) hB p hu huv hvN
  · rw [abs_sub_comm (sourceProfile μ N B p v-(d:ℝ)/2*v/(N:ℝ)),abs_sub_comm v u,
      abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact regularizedProfile_adjusted_increment hN
      (show regularizationLeaves μ N ⊆ dyadicPaths N from Finset.filter_subset _ _)
      (regularizationLabel μ N B) hB p hv hvu huN
theorem dyadic_rpow_scale {N : ℕ} (hN : 0 < N) (n : ℕ) (s : ℝ) :
    ((2:ℝ)^N)^(-s*(n:ℝ)/(N:ℝ)) = (((2:ℝ)^n)^s)⁻¹ := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hN' : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N:ℝ)*(-s*(n:ℝ)/(N:ℝ)) = -((n:ℝ)*s) := by field_simp
  rw [he,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
theorem fixed_constant_absorbed {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C ≤ ((2:ℝ)^N)^lam := by
  have hb : 1 < (2:ℝ)^lam := Real.one_lt_rpow (by norm_num) hlam
  obtain ⟨N₀,hN₀⟩ := pow_unbounded_of_one_lt C hb
  refine ⟨N₀,fun N hN => ?_⟩
  have hh := hN₀.le.trans (pow_le_pow_right₀ hb.le hN)
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm,
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hh
  exact hh

theorem retained_label_real_mass_lower (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] {N B : ℕ} {p : (CellPath d)} {lam : ℝ}
    (hp : regularizationLabel μ N B p ∈ retainedClassLabels μ N B
      (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))) :
    ((2:ℝ)^N)^(-lam) ≤ (classMeasure μ (regularizationLeaves μ N)
      (regularizationLabel μ N B) (regularizationLabel μ N B p) univ).toReal := by
  have hm := retainedClass_mass_lower μ hp
  simp only [classMeasure,Measure.restrict_apply_univ] at hm ⊢
  have hh := ENNReal.toReal_mono (measure_ne_top μ _) hm
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ ((2:ℝ)^N)^(-lam))] using hh

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

lemma treeCell_subset_ball (p : CellPath d) :
    treeCell p ⊆ ball (ambientGridCenter p.length (fun i => (pathIndex p i : ℤ)))
      ((d+2:ℝ)/(2:ℝ)^p.length) := by
  intro x hx
  have hh := ambientGridCell_dist_le (ambientGridCenter_mem p.length (fun i => (pathIndex p i : ℤ))) hx
  exact hh.trans_lt ((div_lt_div_iff_of_pos_right (by positivity)).mpr (by linarith))

lemma dyadic_cell_frostman_profile_bound (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
    {s C : ℝ} (hC : 0 ≤ C)
    (hball : ∀ x : EuclideanSpace ℝ (Fin d), ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s))
    {N : ℕ} (hN : 0 < N) (p : CellPath d) :
    (μ (treeCell p)).toReal ≤ (C*(d+2:ℝ)^s)*((2:ℝ)^N)^(-s*(p.length:ℝ)/(N:ℝ)) := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    ((measure_mono (treeCell_subset_ball p)).trans (hball _ _ (by positivity)))
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ C*((d+2:ℝ)/(2:ℝ)^p.length)^s)] at hh
  apply hh.trans_eq
  rw [dyadic_rpow_scale hN,Real.div_rpow (by positivity) (by positivity)]
  ring

lemma thin_leaf_loss_identity (N : ℕ) :
    (2:ℝ≥0∞)^(d*N)*((2:ℝ≥0∞)^((d+2)*N))⁻¹ = ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ)) := by
  have hleft : (2:ℝ≥0∞)^(d*N)*((2:ℝ≥0∞)^((d+2)*N))⁻¹ ≠ ⊤ := by finiteness
  rw [← ENNReal.ofReal_toReal hleft]
  apply congrArg ENNReal.ofReal
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_inv,ENNReal.toReal_ofNat]
  rw [Real.rpow_neg (by positivity),Real.rpow_two, Nat.add_mul, pow_add]
  have he : (2:ℝ)^(2*N) = ((2:ℝ)^N)^2 := by rw [mul_comm 2 N,pow_mul]
  rw [he]
  field_simp

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
