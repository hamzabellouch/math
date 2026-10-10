import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Measures.RegularizationLabelCount

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def treeCenter (p : CellPath d) : EuclideanSpace ℝ (Fin d) :=
  ambientGridCenter p.length (fun i => (pathIndex p i : ℤ))

lemma treeCenter_mem (p : CellPath d) : treeCenter p ∈ treeCell p :=
  ambientGridCenter_mem _ _

noncomputable def occupiedCenterCells (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (p : ℕ) (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) : Finset (CellPath d) := by
  classical
  exact (dyadicPaths p).filter fun q => 0 < ν (treeCell q) ∧ treeCenter q ∈ ball x r

lemma treeCenter_ball_card {g : ℕ} (T : Finset (CellPath d)) (hT : T ⊆ dyadicPaths g)
    (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 ≤ r)
    (hdist : ∀ p ∈ T, dist (treeCenter p) x ≤ r) :
    (T.card : ℝ) ≤ (2*(2:ℝ)^g*r+5)^d := by
  classical
  let f : CellPath d → (Fin d → ℤ) := fun p i => pathIndex p i
  have hf : Set.InjOn f T := by
    intro p hp q hq he
    apply pathIndex_injective (((mem_dyadicPaths _ _).mp (hT hp)).trans
      ((mem_dyadicPaths _ _).mp (hT hq)).symm)
    funext i
    have hei : (pathIndex p i : ℤ) = pathIndex q i := congrFun he i
    exact_mod_cast hei
  have hh := ambientGridCenter_ball_card g (T.image f) x hr (fun a ha => by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    have he : p.length = g := (mem_dyadicPaths _ _).mp (hT hp)
    simpa only [treeCenter,he] using hdist p hp)
  rwa [Finset.card_image_of_injOn hf] at hh

theorem occupied_center_count_le (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ν] {g p : ℕ} (hgp : g ≤ p)
    (x : EuclideanSpace ℝ (Fin d)) {r C₀ lo hi : ℝ} (hC₀ : 0 ≤ C₀)
    (hr : r ≤ C₀/(2:ℝ)^g) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hfine : ∀ q ∈ dyadicPaths p, 0 < ν (treeCell q) → lo ≤ (ν (treeCell q)).toReal)
    (hcoarse : ∀ q ∈ dyadicPaths g, 0 < ν (treeCell q) → (ν (treeCell q)).toReal ≤ hi) :
    ((occupiedCenterCells ν p x r).card:ℝ) ≤ (2*C₀+2*(d:ℝ)+7)^d*hi/lo := by
  classical
  let S := occupiedCenterCells ν p x r
  let T := S.image (List.take g)
  have hS : S ⊆ dyadicPaths p := Finset.filter_subset _ _
  have hT : T ⊆ dyadicPaths g := by
    intro c hc
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
    have hl := (mem_dyadicPaths _ _).mp (hS hq)
    simp [mem_dyadicPaths,List.length_take,hl,hgp]
  have hpos {q : CellPath d} (hq : q ∈ S) : 0 < ν (treeCell q) :=
    (Finset.mem_filter.mp hq).2.1
  have hparent (q : CellPath d) : treeCell q ⊆ treeCell (q.take g) := treeCell_subset_take q g
  have hcard : (T.card:ℝ) ≤ (2*C₀+2*(d:ℝ)+7)^d := by
    have hh := treeCenter_ball_card T hT x (r := (C₀+(d+1:ℝ))/(2:ℝ)^g) (by positivity) (by
      intro c hc
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
      have hlen : (q.take g).length = g := (mem_dyadicPaths _ _).mp
        (hT (Finset.mem_image.mpr ⟨q,hq,rfl⟩))
      have hcell := ambientGridCell_dist_le (hparent q (treeCenter_mem q)) (treeCenter_mem (q.take g))
      change dist (treeCenter (q.take g)) (treeCenter q) ≤ (d+1:ℝ)/(2:ℝ)^(q.take g).length at hcell
      rw [hlen] at hcell
      have hx := (Finset.mem_filter.mp hq).2.2
      have hdist : dist (treeCenter q) x ≤ C₀/(2:ℝ)^g := (mem_ball.mp hx).le.trans hr
      calc
        _ ≤ dist (treeCenter (q.take g)) (treeCenter q)+dist (treeCenter q) x := dist_triangle _ _ _
        _ ≤ (d+1:ℝ)/(2:ℝ)^g+C₀/(2:ℝ)^g := add_le_add hcell hdist
        _ = _ := by ring)
    have he : 2*(2:ℝ)^g*((C₀+(d+1:ℝ))/(2:ℝ)^g)+5 = 2*C₀+2*(d:ℝ)+7 := by
      field_simp
      ring
    simpa only [he] using hh
  have hcover : leafUnion S ⊆ leafUnion T := by
    intro z hz
    obtain ⟨q,hq,hz⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨q.take g,Finset.mem_image.mpr ⟨q,hq,rfl⟩,hparent q hz⟩
  have hsum : (S.card:ℝ)*lo ≤ (T.card:ℝ)*hi := by
    calc
      _ = ∑ _q ∈ S, lo := by simp
      _ ≤ ∑ q ∈ S, (ν (treeCell q)).toReal :=
        Finset.sum_le_sum (fun q hq => hfine q (hS hq) (hpos hq))
      _ = (ν (leafUnion S)).toReal := (restriction_total_mass_real ν hS).symm
      _ ≤ (ν (leafUnion T)).toReal := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hcover)
      _ = ∑ q ∈ T, (ν (treeCell q)).toReal := restriction_total_mass_real ν hT
      _ ≤ ∑ _q ∈ T, hi := by
        apply Finset.sum_le_sum
        intro c hc
        apply hcoarse c (hT hc)
        obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
        exact (hpos hq).trans_le (measure_mono (hparent q))
      _ = _ := by simp
  exact (le_div_iff₀ hlo).mpr (hsum.trans (mul_le_mul_of_nonneg_right hcard hhi))

theorem sourceClass_local_count (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath d} (hp₀ : p₀ ∈ regularizationLeaves μ N)
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) (x : EuclideanSpace ℝ (Fin d))
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ((occupiedCenterCells (sourceClass μ N B p₀) p x (C₀/(2:ℝ)^g)).card:ℝ) ≤
      (2*C₀+2*(d:ℝ)+7)^d*((2:ℝ)^N)^
        (sourceProfile μ N B p₀ p-sourceProfile μ N B p₀ g+2*(d+1:ℝ)*lam) := by
  have : IsProbabilityMeasure (sourceClass μ N B p₀) := sourceClass_probability μ N B hp₀
  let R : ℝ := (2:ℝ)^N
  have hRp : 0 < R := by dsimp [R]; positivity
  have hh := occupied_center_count_le (sourceClass μ N B p₀) hgp x hC₀ le_rfl
    (lo := R^(-(d+1:ℝ)*lam)*R^(-sourceProfile μ N B p₀ p)) (by positivity)
    (hi := R^((d+1:ℝ)*lam)*R^(-sourceProfile μ N B p₀ g)) (by positivity)
    (fun q hq hpos => (sourceClass_occupied_comparison μ hN hB hwidth hlarge hp₀ hpN
      ((mem_dyadicPaths p q).mp hq) hpos).1)
    (fun q hq hpos => (sourceClass_occupied_comparison μ hN hB hwidth hlarge hp₀ (hgp.trans hpN)
      ((mem_dyadicPaths g q).mp hq) hpos).2)
  apply hh.trans_eq
  rw [mul_div_assoc]
  congr 1
  rw [← Real.rpow_add hRp,← Real.rpow_add hRp,← Real.rpow_sub hRp]
  congr 1
  ring
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
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

structure RegularizedProfileData (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (N B : ℕ) (s lam : ℝ) (m : ℝ → ℝ) : Prop where
  probability : IsProbabilityMeasure ν
  continuous : Continuous m
  zero : m 0 = 0
  slope : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ N →
    0 ≤ m v-m u ∧ m v-m u ≤ d*(v-u)/(N:ℝ)
  affine : ∀ i < N/B+1, ∃ a b : ℝ, ∀ u : ℝ,
    (blockDepth N B (i+1):ℝ) ≤ u → u ≤ (blockDepth N B i:ℝ) → m u = a*u+b
  cells : ∀ n ≤ N, ∀ P : CellPath d, P.length = n → 0 < ν (treeCell P) →
    ((2:ℝ)^N)^(-(d+1:ℝ)*lam)*((2:ℝ)^N)^(-m n) ≤ (ν (treeCell P)).toReal ∧
    (ν (treeCell P)).toReal ≤ ((2:ℝ)^N)^((d+1:ℝ)*lam)*((2:ℝ)^N)^(-m n)
  envelope : ∀ n ≤ N, s*(n:ℝ)/(N:ℝ)-(d+3:ℝ)*lam ≤ m n ∧ m n ≤ d*(n:ℝ)/(N:ℝ)
  adjusted : ∀ u v : ℝ, 0 ≤ u → u ≤ N → 0 ≤ v → v ≤ N →
    |(m v-(d:ℝ)/2*v/(N:ℝ))-(m u-(d:ℝ)/2*u/(N:ℝ))| ≤ (d:ℝ)/2*|v-u|/(N:ℝ)
  packing : ∀ g p : ℕ, g ≤ p → p ≤ N → ∀ x : EuclideanSpace ℝ (Fin d), ∀ C₀ : ℝ, 0 ≤ C₀ →
    ((occupiedCenterCells ν p x (C₀/(2:ℝ)^g)).card:ℝ) ≤
      (2*C₀+2*(d:ℝ)+7)^d*((2:ℝ)^N)^(m p-m g+2*(d+1:ℝ)*lam)

theorem actual_profile_regularization (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] (hcarry : μ (treeCell [])ᶜ = 0)
    {s C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam)
    (hball : ∀ x : EuclideanSpace ℝ (Fin d), ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^s)) :
    ∃ H N₀ : ℕ, 0 < H ∧ (H:ℝ) ≤ 1/lam+2 ∧ ∀ N ≥ N₀,
      let B := N/H
      let t := ENNReal.ofReal (((2:ℝ)^N)^(-lam))
      let L := regularizationLeaves μ N
      let F := regularizationLabel μ N B
      0 < N ∧ 0 < B ∧
      (retainedClassLabels μ N B t).card ≤ ((d+2)*N+1)^(2*H+1) ∧
      μ (retainedClassUnion μ N B t)ᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
        ((((d+2)*N+1)^(2*H+1):ℕ):ENNReal)*t ∧
      ∀ T ∈ retainedClassLabels μ N B t,
        t ≤ classMeasure μ L F T univ ∧
        ∃ m : ℝ → ℝ, RegularizedProfileData (normalizedClass μ L F T) N B s lam m := by
  classical
  obtain ⟨H,N₁,hH,hHbound,hscales⟩ := exists_bounded_regularization_control hlam
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed hlam (C*(d+2:ℝ)^s)
  refine ⟨H,max H (max N₁ N₂),hH,hHbound,?_⟩
  intro N hN
  dsimp only
  have hNH : H ≤ N := (le_max_left _ _).trans hN
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hs := hscales N hN₁
  have hc : (d*N+1)^(N/(N/H)+1)*((d+2)*N+1) ≤ ((d+2)*N+1)^(2*H+1) := by
    rw [pow_succ ((d+2)*N+1) (2*H)]
    apply Nat.mul_le_mul_right
    exact (Nat.pow_le_pow_left (by nlinarith) _).trans (Nat.pow_le_pow_right (by omega) hs.2.2.1)
  refine ⟨hs.1,hs.2.1,(retainedClassLabels_count μ N (N/H) _).trans hc,?_,?_⟩
  · have hh := retainedClass_discard_mass μ hcarry N (N/H)
      (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
    rw [thin_leaf_loss_identity] at hh
    apply hh.trans
    apply add_le_add_right
    apply mul_le_mul_left
    exact_mod_cast hc
  · intro T hT
    refine ⟨retainedClass_mass_lower μ hT,?_⟩
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hT).1
    subst T
    refine ⟨sourceProfile μ N (N/H) p,?_⟩
    refine ⟨sourceClass_probability μ N (N/H) hp,
      regularizedProfile_continuous _ _ _ _ _ _,regularizedProfile_zero _ _ _ _ _ _,
      ?_,?_,?_,?_,?_,?_⟩
    · intro u v hu huv hv
      exact regularizedProfile_increment hs.1
        (show regularizationLeaves μ N ⊆ dyadicPaths N from Finset.filter_subset _ _)
        (regularizationLabel μ N (N/H)) hs.2.1 p hu huv hv
    · exact fun i hi => sourceProfile_affine_on_blocks μ N (N/H) p hi
    · intro n hn P hP hpos
      exact sourceClass_occupied_comparison μ hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2 hp hn hP hpos
    · intro n hn
      refine ⟨?_,sourceProfile_upper μ hs.1 hs.2.1 p (Nat.cast_nonneg n) (Nat.cast_le.mpr hn)⟩
      apply sourceProfile_frostman_lower μ hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2 hp
        (retained_label_real_mass_lower μ hT) _ hn
      intro k hk P hP
      have hh := dyadic_cell_frostman_profile_bound μ hC hball hs.1 P
      rw [hP] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (hconst N hN₂) (by positivity))
    · exact fun u v hu huN hv hvN => sourceProfile_adjusted_lipschitz μ hs.1 hs.2.1 p hu huN hv hvN
    · exact fun g p' hgp hpN x C₀ hC₀ =>
        sourceClass_local_count μ hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2 hp hgp hpN x hC₀
end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
