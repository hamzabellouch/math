import OAI.Combinatorics.EuclideanRamsey.LatticeMoments

namespace OAI

universe uDomain uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct

open MeasureTheory
open scoped BigOperators
namespace EuclideanRamsey

lemma compact_taylor_bound {E : Type uDomain} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x h : E,
      |f (x+h)-f x-fderiv ℝ f x h-
        (1/2:ℝ)*iteratedFDeriv ℝ 2 f x ![h,h]| ≤ K*‖h‖^3 := by
  obtain ⟨K,hK⟩ := (hf.continuous_iteratedFDeriv (m := 3) (by norm_cast)).bounded_above_of_compact_support
    (hfc.iteratedFDeriv 3)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  refine ⟨K,hK0,?_⟩
  intro x h
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n := 2) (f := f) (x := x) (y := h)
    (fun t ht => (hf.of_le (by norm_cast)).contDiffAt)
  have he : f (x+h)-f x-fderiv ℝ f x h-(1/2:ℝ)*iteratedFDeriv ℝ 2 f x ![h,h] =
      (1/2:ℝ)*∫ t in (0:ℝ)..1, (1-t)^2 * iteratedFDeriv ℝ 3 f (x+t • h) (fun _ => h) := by
    have hvec : (fun _ : Fin 2 => h) = ![h,h] := by ext i; fin_cases i <;> rfl
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.factorial,
      Nat.cast_one,Nat.cast_mul,inv_one,
      iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,smul_eq_mul,hvec] at ht
    linarith
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  have hi : |∫ t in (0:ℝ)..1, (1-t)^2 * iteratedFDeriv ℝ 3 f (x+t • h) (fun _ => h)| ≤
      K*‖h‖^3 := by
    have ht (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
        ‖(1-t)^2 * iteratedFDeriv ℝ 3 f (x+t • h) (fun _ => h)‖ ≤ K*‖h‖^3 := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hm := (iteratedFDeriv ℝ 3 f (x+t • h)).le_opNorm (fun _ => h)
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hm
      have hd : ‖iteratedFDeriv ℝ 3 f (x+t • h) (fun _ => h)‖ ≤ K*‖h‖^3 :=
        hm.trans (mul_le_mul_of_nonneg_right (hK _) (by positivity))
      have ht2 : (1-t)^2 ≤ 1 := by nlinarith [ht.1,ht.2]
      calc
        _ ≤ 1 * (K*‖h‖^3) := mul_le_mul ht2 hd (norm_nonneg _) (by norm_num)
        _ = _ := one_mul _
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (C := K*‖h‖^3) (fun t ht' => ht t ⟨(by simpa using ht'.1 : 0 < t).le,by simpa using ht'.2⟩)
    simpa using hh
  nlinarith [mul_nonneg hK0 (pow_nonneg (norm_nonneg h) 3)]

end EuclideanRamsey

open scoped BigOperators
namespace EuclideanRamsey

lemma linear_moment_contract {ι : Type uIndex} {k : ℕ}
    (S : Finset ι) (q : ι → ℝ) (v : ι → (Fin k → ℝ))
    (L : (Fin k → ℝ) →L[ℝ] ℝ) :
    ∑ γ ∈ S,q γ*L (v γ) = ∑ j,(∑ γ ∈ S,q γ*v γ j)*L (Pi.single j 1) := by
  have hv (γ : ι) : v γ = ∑ j, v γ j • Pi.single j (1:ℝ) := by
    ext l
    simp [Pi.single_apply]
  conv_lhs => arg 2; intro γ; rw [hv γ]
  simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro γ hγ
  ring

lemma bilinear_moment_contract {ι : Type uIndex} {k : ℕ}
    (S : Finset ι) (q : ι → ℝ) (v : ι → (Fin k → ℝ))
    (L : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ) :
    ∑ γ ∈ S,q γ*L (v γ) (v γ) =
      ∑ j,∑ l,(∑ γ ∈ S,q γ*v γ j*v γ l)*L (Pi.single j 1) (Pi.single l 1) := by
  have hv (γ : ι) : v γ = ∑ j, v γ j • Pi.single j (1:ℝ) := by
    ext l
    simp [Pi.single_apply]
  have he (γ : ι) : q γ*L (v γ) (v γ) =
      ∑ j,∑ l,q γ*v γ j*v γ l*L (Pi.single j 1) (Pi.single l 1) := by
    have hfirst := congrArg (fun a => L a (v γ)) (hv γ)
    rw [hfirst]
    simp only [map_sum,map_smul,_root_.sum_apply,
      _root_.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hsecond := congrArg (fun a => L (Pi.single j 1) a) (hv γ)
    rw [hsecond]
    simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  simp only [he,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]

end EuclideanRamsey

open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
namespace EuclideanRamsey

abbrev realLattice (k : ℕ) := Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k)))
def latticeSample {k : ℕ} (n : ℕ) (γ : Fin k → ℤ) : Fin k → ℝ := fun j => (γ j : ℝ)/n

lemma latticeSample_injective {k n : ℕ} (hn : n ≠ 0) :
    Function.Injective (@latticeSample k n) := by
  intro γ δ h
  funext j
  have he := congr_fun h j
  dsimp [latticeSample] at he
  exact_mod_cast (div_left_inj' (show (n:ℝ) ≠ 0 by exact_mod_cast hn)).mp he

lemma latticeSample_mem_grid {k n : ℕ} (hn : n ≠ 0) (γ : Fin k → ℤ) :
    latticeSample n γ ∈ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ)) := by
  let : NeZero n := ⟨hn⟩
  rw [← Submodule.coe_pointwise_smul]
  apply BoxIntegral.unitPartition.mem_smul_span_iff.mpr
  intro j
  refine ⟨γ j,?_⟩
  change (γ j : ℝ) = (n:ℝ)*((γ j : ℝ)/n)
  field_simp

lemma grid_surjective {k n : ℕ} (hn : n ≠ 0) {x : Fin k → ℝ}
    (hx : x ∈ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ))) : ∃ γ, latticeSample n γ = x := by
  let : NeZero n := ⟨hn⟩
  rw [← Submodule.coe_pointwise_smul] at hx
  have h := BoxIntegral.unitPartition.mem_smul_span_iff.mp hx
  choose γ hγ using h
  refine ⟨γ,?_⟩
  funext j
  simp only [latticeSample]
  have he : (γ j : ℝ) = (n:ℝ)*x j := hγ j
  rw [he]
  exact mul_div_cancel_left₀ (x j) (by exact_mod_cast hn)

lemma lattice_tsum_eq_grid {k n : ℕ} (hn : n ≠ 0) (s : Set (Fin k → ℝ))
    (f : (Fin k → ℝ) → ℝ) (hf : Function.support f ⊆ s) :
    (∑' γ : Fin k → ℤ, f (latticeSample n γ)) =
      ∑' x : ↑(s ∩ (n:ℝ)⁻¹ • realLattice k), f x := by
  let e : {γ : Fin k → ℤ // latticeSample n γ ∈ s} ≃
      ↑(s ∩ (n:ℝ)⁻¹ • realLattice k) := Equiv.ofBijective
    (fun γ => ⟨latticeSample n γ,γ.property,latticeSample_mem_grid hn γ.val⟩) (by
      constructor
      · intro x y h
        apply Subtype.ext
        exact latticeSample_injective hn (congr_arg Subtype.val h)
      · intro x
        obtain ⟨γ,hγ⟩ := grid_surjective hn x.property.2
        exact ⟨⟨γ,by simpa [hγ] using x.property.1⟩,Subtype.ext hγ⟩)
  rw [← tsum_subtype_eq_of_support_subset (s := {γ | latticeSample n γ ∈ s})
    (f := fun γ => f (latticeSample n γ)) (fun γ hγ => hf hγ)]
  exact e.tsum_eq (fun x => f x)

theorem lattice_riemann {k : ℕ} {f : (Fin k → ℝ) → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun n : ℕ => (∑' γ : Fin k → ℤ, f (latticeSample n γ))/(n:ℝ)^k)
      atTop (𝓝 (∫ x, f x)) := by
  obtain ⟨R,hR,hfR⟩ := hfc.exists_pos_le_norm
  let s := Metric.closedBall (0 : Fin k → ℝ) R
  have hs : Function.support f ⊆ s := by
    intro x hx
    rw [show s = Metric.closedBall 0 R from rfl, Metric.mem_closedBall,dist_zero_right]
    exact le_of_lt (lt_of_not_ge (fun h => hx (hfR x h)))
  have hfront : volume (frontier s) = 0 :=
    measure_mono_null Metric.frontier_closedBall_subset_sphere
      (volume.addHaar_sphere_of_ne_zero 0 hR.ne')
  have h := tendsto_tsum_div_pow_atTop_integral s f hf Metric.isBounded_closedBall
    measurableSet_closedBall hfront
  have hi : (∫ x in s,f x) = ∫ x,f x := by
    rw [← integral_indicator measurableSet_closedBall, Set.indicator_eq_self.mpr hs]
  simp only [Fintype.card_fin,hi] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [lattice_tsum_eq_grid (by omega) s f hs]

lemma latticeSample_finite_support {k n : ℕ} (hn : n ≠ 0)
    {f : (Fin k → ℝ) → ℝ} (hf : HasCompactSupport f) :
    Function.HasFiniteSupport (fun γ : Fin k → ℤ => f (latticeSample n γ)) := by
  let b := Pi.basisFun ℝ (Fin k)
  have hb : Bornology.IsBounded ((n:ℝ) • tsupport f) :=
    (hf.isCompact.image (show Continuous (fun x : Fin k → ℝ => (n:ℝ) • x) by fun_prop)).isBounded
  have hfinite := ZSpan.setFinite_inter b hb
  let cast : (Fin k → ℤ) → (Fin k → ℝ) := fun γ j => γ j
  have hinj : Function.Injective cast := by
    intro x y h
    ext j
    have he : (x j : ℝ) = (y j : ℝ) := congr_fun h j
    exact_mod_cast he
  apply ((hfinite.preimage hinj.injOn).subset ?_)
  intro γ hγ
  have hs : latticeSample n γ ∈ tsupport f := subset_closure hγ
  constructor
  · refine ⟨latticeSample n γ,hs,?_⟩
    ext j
    change (n:ℝ)*((γ j : ℝ)/n) = (γ j : ℝ)
    field_simp
  · change cast γ ∈ Submodule.span ℤ (Set.range b)
    rw [b.mem_span_iff_repr_mem ℤ]
    intro j
    exact ⟨γ j,by simp [b,cast]⟩

end EuclideanRamsey

end

end OAI
