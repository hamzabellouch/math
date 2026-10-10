import OAI.Combinatorics.EuclideanRamsey.Discretization

namespace OAI

universe uGroup uIndex

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
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter

namespace EuclideanRamsey
open MeasureTheory Filter
open scoped BigOperators Pointwise Topology

lemma bounded_grid_finite {k n : ℕ} (hn : n ≠ 0) {s : Set (Fin k → ℝ)}
    (hs : Bornology.IsBounded s) :
    (s ∩ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ))).Finite := by
  rw [← Submodule.coe_pointwise_smul, ZSpan.smul _ (inv_ne_zero (by exact_mod_cast hn))]
  exact ZSpan.setFinite_inter _ hs

lemma lattice_sum_perturb_bound {k n : ℕ} (hn : n ≠ 0) {s : Set (Fin k → ℝ)}
    (hs : Bornology.IsBounded s) (f g : (Fin k → ℝ) → ℝ)
    (hf : Function.support f ⊆ s) (hg : Function.support g ⊆ s)
    (ε : ℝ) (hb : ∀ x, |f x-g x| ≤ ε) :
    |((∑' γ : Fin k → ℤ, f (latticeSample n γ))/(n:ℝ)^k)-
      ((∑' γ : Fin k → ℤ, g (latticeSample n γ))/(n:ℝ)^k)| ≤
      ε * ((Nat.card ↑(s ∩ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ))) : ℝ)/(n:ℝ)^k) := by
  let G := ↑(s ∩ (n:ℝ)⁻¹ • (realLattice k : Set (Fin k → ℝ)))
  let : Fintype G := (bounded_grid_finite hn hs).fintype
  rw [lattice_tsum_eq_grid hn s f hf,lattice_tsum_eq_grid hn s g hg,
    ← sub_div,abs_div,abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)^k)]
  have hsum : |(∑' x : G,f x)-(∑' x : G,g x)| ≤ (Nat.card G : ℝ)*ε := by
    rw [tsum_fintype,tsum_fintype,← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ x : G, |f x-g x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : G, ε := Finset.sum_le_sum (fun x hx => hb x)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  calc
    _ ≤ ((Nat.card G : ℝ)*ε)/(n:ℝ)^k := div_le_div_of_nonneg_right hsum (by positivity)
    _ = _ := by ring

theorem lattice_riemann_perturb {k : ℕ} (f : (Fin k → ℝ) → ℝ)
    (g : ℕ → (Fin k → ℝ) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {R : ℝ} (hR : 0 < R)
    (hfs : Function.support f ⊆ Metric.closedBall 0 R)
    (hgs : ∀ n, Function.support (g n) ⊆ Metric.closedBall 0 R)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, 1 ≤ n → ∀ x, |g n x-f x| ≤ ε n) :
    Tendsto (fun n : ℕ => (∑' γ : Fin k → ℤ, g n (latticeSample n γ))/(n:ℝ)^k)
      atTop (𝓝 (∫ x, f x)) := by
  let s := Metric.closedBall (0 : Fin k → ℝ) R
  have hfront : volume (frontier s) = 0 :=
    measure_mono_null Metric.frontier_closedBall_subset_sphere
      (volume.addHaar_sphere_of_ne_zero 0 hR.ne')
  have hc := tendsto_card_div_pow_atTop_volume s Metric.isBounded_closedBall
    measurableSet_closedBall hfront
  have hlim := hε.mul hc
  rw [zero_mul] at hlim
  have hdiff : Tendsto (fun n : ℕ =>
      (∑' γ : Fin k → ℤ, g n (latticeSample n γ))/(n:ℝ)^k-
      (∑' γ : Fin k → ℤ, f (latticeSample n γ))/(n:ℝ)^k) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa only [Real.norm_eq_abs,Fintype.card_fin] using
      lattice_sum_perturb_bound (by omega : n ≠ 0) Metric.isBounded_closedBall
        (g n) f (hgs n) hfs (ε n) (hbound n hn)
  convert hdiff.add (lattice_riemann hf hfc) using 1
  · ext n; ring
  · simp

end EuclideanRamsey

open scoped BigOperators Pointwise
namespace EuclideanRamsey

lemma convolution_support {G : Type uGroup} [AddCommGroup G] (S : Finset G) (q : G → ℝ)
    {d : G → ℝ} (hd : Function.HasFiniteSupport d) :
    Function.HasFiniteSupport (fun δ => ∑ γ ∈ S,q γ*d (δ-γ)) := by
  classical
  apply (S.finite_toSet.add hd).subset
  intro δ hδ
  obtain ⟨γ,hγ,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hδ
  have hd' : δ-γ ∈ Function.support d := by
    intro hz
    exact hn (by rw [hz,mul_zero])
  exact ⟨γ,hγ,δ-γ,hd',(add_comm _ _).trans (sub_add_cancel _ _)⟩

lemma rational_convolution_coeff {G : Type uGroup} [AddCommGroup G] [DecidableEq G]
    (ν d : AddMonoidAlgebra ℚ G) (δ : G) :
    (ν*d).coeff δ = ∑ γ ∈ ν.coeff.support,ν.coeff γ*d.coeff (δ-γ) := by
  rw [AddMonoidAlgebra.coeff_mul]
  apply Finset.sum_congr rfl
  intro γ hγ
  change (∑ β ∈ d.coeff.support,if γ+β=δ then ν.coeff γ*d.coeff β else 0) = _
  have he (β : G) : γ+β=δ ↔ β=δ-γ := by
    constructor
    · intro h; apply eq_sub_iff_add_eq.mpr; simpa [add_comm] using h
    · intro h; rw [h]; abel
  simp only [he,Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp [Finsupp.notMem_support_iff.mp h]

end EuclideanRamsey

open scoped BigOperators Topology
namespace EuclideanRamsey

lemma rational_vector_strict {ι : Type uIndex} [Fintype ι]
    (ζ N : (ι → ℝ) → ℝ) (hζ : Continuous ζ) (hN : Continuous N)
    (η : ℝ) (d : ι → ℝ) (hp : 0 < ζ d) (hn : N d < η*ζ d) :
    ∃ q : ι → ℚ, 0 < ζ (fun i => q i) ∧ N (fun i => q i) < η*ζ (fun i => q i) := by
  have hDense : DenseRange (fun q : ι → ℚ => fun i => (q i : ℝ)) := by
    exact DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hopen : IsOpen {d : ι → ℝ | 0 < ζ d ∧ N d < η*ζ d} :=
    (isOpen_lt continuous_const hζ).inter (isOpen_lt hN (continuous_const.mul hζ))
  exact hDense.exists_mem_open hopen ⟨d,hp,hn⟩
end EuclideanRamsey

namespace EuclideanRamsey
open scoped BigOperators Pointwise

lemma rationalize_convolution {G : Type uGroup} [AddCommGroup G] [DecidableEq G]
    (ν : AddMonoidAlgebra ℚ G) (w : G → ℝ) (t η : ℝ)
    {a : G → ℝ} (ha : Function.HasFiniteSupport a)
    (hp : 0 < (∑' γ,a γ)/t)
    (hn : (∑' δ,max (-(∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*a (δ-γ))) 0*w δ) <
      η*((∑' γ,a γ)/t)) :
    ∃ b : AddMonoidAlgebra ℚ G,
      0 < ((b.coeff.sum fun _ q => q : ℚ):ℝ)/t ∧
      (∑' δ,max (-((ν*b).coeff δ:ℝ)) 0*w δ) <
        η*(((b.coeff.sum fun _ q => q : ℚ):ℝ)/t) := by
  classical
  let E := ha.toFinset
  let : Fintype E := inferInstance
  let K := ν.coeff.support+E
  let ext (d : E → ℝ) (γ : G) := if h : γ ∈ E then d ⟨γ,h⟩ else 0
  let ζ (d : E → ℝ) := (∑ γ : E,d γ)/t
  let N (d : E → ℝ) := ∑ δ ∈ K,max (-(∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext d (δ-γ))) 0*w δ
  have hζ : Continuous ζ := by unfold ζ; fun_prop
  have hExt (γ : G) : Continuous (fun d : E → ℝ => ext d γ) := by
    dsimp [ext]
    split_ifs <;> fun_prop
  have hN : Continuous N := by unfold N; fun_prop
  have hsum (d : E → ℝ) : ∑' γ,ext d γ = ∑ γ : E,d γ := by
    rw [tsum_eq_sum (s := E)]
    · rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro γ hγ
      simp only [ext,dite_eq_left γ.property]
    · intro γ hγ
      simp [ext,hγ]
  have hNeg (d : E → ℝ) : (∑' δ,max (-(∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext d (δ-γ))) 0*w δ) = N d := by
    apply tsum_eq_sum
    intro δ hδ
    have hz : ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext d (δ-γ) = 0 := by
      apply Finset.sum_eq_zero
      intro γ hγ
      have hE : δ-γ ∉ E := by
        intro h
        exact hδ (Finset.mem_add.mpr ⟨γ,hγ,δ-γ,h,by abel⟩)
      simp [ext,hE]
    simp [hz]
  let aE : E → ℝ := fun γ => a γ
  have haE : ext aE = a := by
    funext γ
    dsimp [ext,aE]
    split_ifs with h
    · rfl
    · have hγ : γ ∉ Function.support a := by
        intro hh
        exact h (ha.mem_toFinset.mpr hh)
      exact (not_not.mp hγ).symm
  have hpE : 0 < ζ aE := by
    change 0 < (∑ γ : E,aE γ)/t
    rw [← hsum aE,haE]
    exact hp
  have hnE : N aE < η*ζ aE := by
    rw [← hNeg,haE]
    change _ < η*((∑ γ : E,aE γ)/t)
    rw [← hsum aE,haE]
    exact hn
  obtain ⟨q,hq0,hqN⟩ := rational_vector_strict ζ N hζ hN η aE hpE hnE
  let b : AddMonoidAlgebra ℚ G := ∑ γ : E,AddMonoidAlgebra.single γ.val (q γ)
  have hb (γ : G) : (b.coeff γ : ℝ) = ext (fun i => (q i:ℝ)) γ := by
    simp only [b,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,Rat.cast_sum]
    by_cases h : γ ∈ E
    · rw [Finset.sum_eq_single ⟨γ,h⟩]
      · simp [ext,h]
      · intro β hβ hne
        have hne' : β.val ≠ γ := fun he => hne (Subtype.ext he)
        simp [hne']
      · simp
    · have hz (β : E) : β.val ≠ γ := fun hb => h (hb ▸ β.property)
      simp [ext,h,hz]
  have hbMass : ((b.coeff.sum fun _ q => q : ℚ):ℝ) = ∑ γ : E,(q γ:ℝ) := by
    have ht : ∑' γ,(b.coeff γ:ℝ) = ((b.coeff.sum fun _ q => q : ℚ):ℝ) := by
      rw [tsum_eq_sum (s := b.coeff.support)]
      · simp [Finsupp.sum]
      · intro γ hγ; simp [Finsupp.notMem_support_iff.mp hγ]
    rw [← ht]
    simp only [hb]
    exact hsum (fun i => (q i:ℝ))
  refine ⟨b,?_,?_⟩
  · simpa only [hbMass,ζ] using hq0
  · have hc (δ : G) : ((ν*b).coeff δ:ℝ) = ∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*ext (fun i => (q i:ℝ)) (δ-γ) := by
      rw [rational_convolution_coeff]
      simp only [Rat.cast_sum,Rat.cast_mul,hb]
    simp only [hc,hNeg,hbMass]
    exact hqN

end EuclideanRamsey

end

end OAI
