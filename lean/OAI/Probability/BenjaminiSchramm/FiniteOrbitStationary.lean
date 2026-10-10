import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Classical Topology BigOperators

namespace Percolation.BenjaminiSchramm
variable {ι : Type*} [Fintype ι]

def orbitChainStep (K : ι → ι → ℝ) (μ : ι → ℝ) (y : ι) : ℝ := ∑ x, μ x * K x y

lemma orbitChainStep_nonneg (K : ι → ι → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (μ : ι → ℝ) (hμ : ∀ x, 0 ≤ μ x) (y : ι) : 0 ≤ orbitChainStep K μ y :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hμ x) (hK x y)

lemma orbitChainStep_mass (K : ι → ι → ℝ) (hK : ∀ x, ∑ y, K x y = 1) (μ : ι → ℝ) :
    ∑ y, orbitChainStep K μ y = ∑ y, μ y := by
  unfold orbitChainStep
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,hK,mul_one]

theorem finite_orbit_stationary [Nonempty ι] (K : ι → ι → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, ∑ y, K x y = 1) :
    ∃ μ : ι → ℝ, (∀ x, 0 ≤ μ x) ∧ (∑ x, μ x = 1) ∧ orbitChainStep K μ = μ := by
  let i₀ := Classical.arbitrary ι
  let d₀ : ι → ℝ := fun i => if i = i₀ then 1 else 0
  let d : ℕ → ι → ℝ := fun n => (orbitChainStep K)^[n] d₀
  have hdnext (n : ℕ) : d (n+1) = orbitChainStep K (d n) :=
    Function.iterate_succ_apply' (orbitChainStep K) n d₀
  have hd (n : ℕ) : (∀ i, 0 ≤ d n i) ∧ ∑ i, d n i = 1 := by
    induction n with
    | zero =>
      change (∀ i, 0 ≤ d₀ i) ∧ ∑ i, d₀ i = 1
      constructor
      · intro i
        dsimp [d₀]
        split_ifs <;> norm_num
      · simp [d₀]
    | succ n ih =>
      rw [hdnext]
      exact ⟨orbitChainStep_nonneg K hK _ ih.1,by rw [orbitChainStep_mass K hrow,ih.2]⟩
  have hdle (n : ℕ) (i : ι) : d n i ≤ 1 := by
    rw [← (hd n).2]
    exact Finset.single_le_sum (fun j _ => (hd n).1 j) (Finset.mem_univ i)
  let av : ℕ → ι → ℝ := fun n i => ((n : ℝ)+1)⁻¹ * ∑ k ∈ Finset.range (n+1), d k i
  have havnonneg (n : ℕ) (i : ι) : 0 ≤ av n i := by
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => (hd k).1 i)
  have havmass (n : ℕ) : ∑ i, av n i = 1 := by
    simp only [av,← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [(hd _).2,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one,Nat.cast_add,Nat.cast_one]
    exact inv_mul_cancel₀ (by positivity)
  have havcube (n : ℕ) : av n ∈ Set.Icc (0 : ι → ℝ) 1 := by
    refine ⟨havnonneg n,fun i => ?_⟩
    change av n i ≤ (1 : ℝ)
    rw [← havmass n]
    exact Finset.single_le_sum (fun j _ => havnonneg n j) (Finset.mem_univ i)
  obtain ⟨μ,hμcube,φ,hφ,hlim⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ι → ℝ) 1)).tendsto_subseq
    (x := av) havcube
  have hμmass : ∑ i, μ i = 1 := by
    have hs := tendsto_finsetSum Finset.univ (fun i _ => (continuous_apply i).tendsto μ |>.comp hlim)
    change Tendsto (fun n => ∑ i, av (φ n) i) atTop (𝓝 (∑ i, μ i)) at hs
    have he : (fun n => ∑ i, av (φ n) i) = fun _ : ℕ => (1 : ℝ) := by funext n; exact havmass _
    rw [he] at hs
    exact tendsto_nhds_unique hs tendsto_const_nhds
  refine ⟨μ,hμcube.1,hμmass,?_⟩
  have havstep (n : ℕ) (i : ι) : orbitChainStep K (av n) i - av n i =
      ((n : ℝ)+1)⁻¹ * (d (n+1) i-d 0 i) := by
    have hsum : ∑ x, (∑ k ∈ Finset.range (n+1), d k x) * K x i =
        ∑ k ∈ Finset.range (n+1), d (k+1) i := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [hdnext]
      rfl
    simp only [orbitChainStep,av,mul_assoc,← Finset.mul_sum,hsum,← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_range_sub (fun k => d k i) (n+1)
  have hsmall : Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  funext i
  have hz : Tendsto (fun n => orbitChainStep K (av n) i-av n i) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hsmall
    rw [havstep,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity)]
    apply mul_le_of_le_one_right (by positivity)
    rw [abs_le]
    constructor <;> linarith [(hd (n+1)).1 i,(hd 0).1 i,hdle (n+1) i,hdle 0 i]
  have hstep : Continuous (fun v : ι → ℝ => orbitChainStep K v i) :=
    continuous_finsetSum Finset.univ fun j _ => (continuous_apply j).mul continuous_const
  have ht := (hstep.tendsto μ |>.comp hlim).sub ((continuous_apply i).tendsto μ |>.comp hlim)
  exact sub_eq_zero.mp (tendsto_nhds_unique ht (hz.comp hφ.tendsto_atTop))

theorem finite_orbit_stationary_positive [Nonempty ι] (K : ι → ι → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, ∑ y, K x y = 1)
    (hconn : ∀ x y, Relation.ReflTransGen (fun i j => 0 < K i j) x y) :
    ∃ μ : ι → ℝ, (∀ x, 0 < μ x) ∧ (∑ x, μ x = 1) ∧ orbitChainStep K μ = μ := by
  obtain ⟨μ,hμ,hmass,hstat⟩ := finite_orbit_stationary K hK hrow
  have hpossum : 0 < ∑ x, μ x := by rw [hmass]; norm_num
  obtain ⟨x,_,hx⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hμ i)).mp hpossum
  refine ⟨μ,fun y => ?_,hmass,hstat⟩
  have hpath := hconn x y
  induction hpath with
  | refl => exact hx
  | @tail z y _ hzy ih =>
    have hle : μ z * K z y ≤ μ y := by
      rw [← congrFun hstat y]
      exact Finset.single_le_sum (fun i _ => mul_nonneg (hμ i) (hK i y)) (Finset.mem_univ z)
    exact (mul_pos ih hzy).trans_le hle

end Percolation.BenjaminiSchramm

end

end OAI
