import OAI.Probability.DilutedSpin.FiniteLogExpansion
import OAI.Probability.DilutedSpin.MixedPatterns
import OAI.Probability.DilutedSpin.PatternComparison
import OAI.Probability.DilutedSpin.ProductPatterns

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory PrescribedTree Pattern
open scoped BigOperators
noncomputable local instance rootPatternComparisonDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (S : PrescribedTree L) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (V : FinitePath Ω L → Fin N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

noncomputable def rootPatternMass (e : S.Leaf → Spin) : ℝ :=
  ∫ z, rootTreeMean S T Q m base old (fun x => empirical (fun i a => V (x a) i) e) z ∂μ

include hb in
lemma root_pattern_replacement (hN : 0<N) (a : ℕ)
    (f : (Fin a → S.Leaf → Spin) → ℝ) (hf : ∀ x, |f x|≤1) :
    |(∫ z, rootTreeMean S T Q m base old
        (fun y => ∑ x, (∏ i, empirical (fun v b => V (y b) v) (x i))*f x) z ∂μ)-
      (∑ x, (∏ i, rootPatternMass μ S T Q m base old V (x i))*f x)| ≤
      (a:ℝ)*shapeDeviation μ
        (rootAlphabet (Ω := Ω) (A := A)) S (rootTower T Q m base old)
        (rootVector (fun y i => spin (V y i))) := by
  let α := rootAlphabet (Ω := Ω) (A := A) (Y := Y) (X := X) (M := M)
  let K := rootTower T Q m base old
  let P := fun z => sampleLaw S (K z)
  let mass := fun z (w : Sample (α z) S) =>
    empirical (fun i b => V (physical (rootArray z.2.2.1 z.2.2.2) L (S.pathAt b w)) i)
  have hm (e : S.Leaf → Spin) : Measurable (fun z => (P z).expect (fun w => mass z w e)) :=
    measurable_rootTreeMean S T Q m base old (fun x => empirical (fun i b => V (x b) i) e) hb
  have he := mixed_pattern_replacement μ (fun z => Sample (α z) S) P mass
    (fun z w => empirical_nonneg _) (fun z w => empirical_total hN _) hm a f hf
    (measurable_rootTreeMean S T Q m base old
      (fun y => ∑ x, (∏ i, empirical (fun v b => V (y b) v) (x i))*f x) hb)
    (fun B => measurable_rootTreeMean S T Q m base old
      (fun y => |moment (empirical (fun i b => V (y b) i)) B -
        moment (mixedMass μ (fun z => Sample (α z) S) P mass) B|) hb)
  change |(∫ z, (P z).expect (fun w => ∑ x, (∏ i, mass z w (x i))*f x) ∂μ)-
    (∑ x, (∏ i, mixedMass μ (fun z => Sample (α z) S) P mass (x i))*f x)|≤_ 
  apply he.trans_eq
  congr 1
  have hmom (B : Finset S.Leaf) (z : FullRootState Y X I M) (w : Sample (α z) S) :
      moment (mass z w) B = subsetOverlap S B
        (rootVector (fun y i => spin (V y i)) z) w := by
    rw [empirical_moment]
    rfl
  simp_rw [hmom]
  change (∑ B∈(Finset.univ : Finset (Finset S.Leaf)).erase ∅,
    subsetDeviation μ α S B K (rootVector (fun y i => spin (V y i)))) = _
  unfold shapeDeviation
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ ∅)]
  have hempty (z : FullRootState Y X I M) :
      subsetOverlap S ∅ (rootVector (fun y i => spin (V y i)) z) = (fun _ : Sample (α z) S => (N:ℝ)/N) := by
    funext w
    simp [subsetOverlap]
  have hz : subsetDeviation μ α S ∅ K (rootVector (fun y i => spin (V y i)))=0 := by
    simp only [subsetDeviation,hempty,FiniteLaw.mixedDeviation,
      FiniteLaw.expect_const,integral_const,probReal_univ,smul_eq_mul,one_mul,sub_self,abs_zero]
  have hh : (∑ B : Finset S.Leaf,
    if B.Nonempty then subsetDeviation μ α S B K (rootVector (fun y i => spin (V y i))) else 0) =
      ∑ B : Finset S.Leaf, subsetDeviation μ α S B K (rootVector (fun y i => spin (V y i))) := by
    apply Finset.sum_congr rfl
    intro B _
    by_cases h : B.Nonempty
    · rw [ite_eq_left h]
    · rw [ite_eq_right h,Finset.not_nonempty_iff_eq_empty.mp h,hz]
  rw [hh,hz,sub_zero]

end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass
open scoped BigOperators
namespace Pattern
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} [NeZero N]

omit [DecidableEq ι] in
lemma empirical_eq_uniform (σ : Fin N → ι → Spin) (e : ι → Spin) :
    empirical σ e = (FiniteLaw.uniform : FiniteLaw (Fin N)).expect
      (fun i => if σ i=e then 1 else 0) := by
  classical
  rw [FiniteLaw.expect_uniform,Fintype.card_fin]
  rfl

lemma uniform_patterns (σ : Fin N → ι → Spin) (a : ℕ)
    (f : (Fin a → ι → Spin) → ℝ) :
    (FiniteLaw.uniform : FiniteLaw (Fin a → Fin N)).expect (fun x => f (fun i => σ (x i))) =
      ∑ e, (∏ i, empirical σ (e i))*f e := by
  classical
  rw [← FiniteLaw.pi_uniform,FiniteLaw.expect_pi_map (fun _ : Fin a => (FiniteLaw.uniform : FiniteLaw (Fin N)))
    (fun _ => σ) f]
  change (∑ e, (∏ i, (FiniteLaw.map FiniteLaw.uniform σ).weight (e i))*f e)=_
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [empirical_eq_uniform]
  dsimp only [FiniteLaw.map]
  apply FiniteLaw.expect_congr
  intro v
  split_ifs <;> rfl

end Pattern

namespace PrescribedTree
variable {Ω : Type} [Fintype Ω] {N n : ℕ} [NeZero N]
lemma treeMean_uniform_patterns (S : PrescribedTree n) (T : KernelTower Ω n)
    (V : FinitePath Ω n → Fin N → Spin) (a : ℕ) (f : (Fin a → Spin) → ℝ) :
    (FiniteLaw.uniform : FiniteLaw (Fin a → Fin N)).expect (fun i =>
      treeMean S T (fun y => f (fun j => V y (i j)))) =
      (sampleLaw S T).expect (fun w => ∑ e : Fin a → S.Leaf → Spin,
        (∏ j, Pattern.empirical (fun i b => V (S.pathAt b w) i) (e j))*(∏ b, f (fun j => e j b))) := by
  simp_rw [treeMean_eq_expect]
  rw [FiniteLaw.expect_comm]
  apply FiniteLaw.expect_congr
  intro w
  simp_rw [leafProduct_eq_prod]
  exact Pattern.uniform_patterns (fun i b => V (S.pathAt b w) i) a (fun e => ∏ b, f (fun j => e j b))

end PrescribedTree
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z]

lemma integral_logInsertion_tail {n : ℕ} (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (T : (z : Z) → KernelTower (Ω z) n)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hnz : ∀ j : Fin n, m j.succ≠0) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (D : (z : Z) → FinitePath (Ω z) n → ℝ) (hD : ∀ z y, |D z y|≤1)
    {t : ℝ} (ht : |t|<1)
    (hI : Measurable (fun z => logInsertion (T z) m (D z) t))
    (hQ : ∀ k, Measurable (fun z => qMoment m (T z) (D z) k (single n))) (K : ℕ) :
    |(∫ z, logInsertion (T z) m (D z) t ∂μ)-∑ k∈Finset.range K,
      (-1:ℝ)^k/(k+1)*(∫ z, qMoment m (T z) (D z) k (single n) ∂μ)*t^(k+1)| ≤
      ∑' k : ℕ, |t|^(k+K+1)/(k+K+1) := by
  let b := ∑' k : ℕ, |t|^(k+1)/(k+1)
  have hIb (z : Z) : |logInsertion (T z) m (D z) t|≤b := by
    simpa only [Finset.range_zero,Finset.sum_empty,sub_zero,Nat.add_zero,Nat.cast_zero,add_zero,b] using
      logInsertion_tail_bound (T z) m hm hpos hnz hroot hend (D z) (hD z) ht 0
  have hIi : Integrable (fun z => logInsertion (T z) m (D z) t) μ :=
    (bounded_memLp hI hIb 1).integrable le_rfl
  have hQi (k : ℕ) : Integrable (fun z => qMoment m (T z) (D z) k (single n)) μ :=
    (bounded_memLp (hQ k) (fun z => abs_qMoment_le_one m hm hpos hroot hend (T z) (D z) (hD z) k (single n)) 1).integrable le_rfl
  have hi (k : ℕ) : Integrable (fun z => (-1:ℝ)^k/(k+1)*qMoment m (T z) (D z) k (single n)*t^(k+1)) μ :=
    ((hQi k).const_mul _).mul_const _
  have he : (∑ k∈Finset.range K, (-1:ℝ)^k/(k+1)*(∫ z, qMoment m (T z) (D z) k (single n) ∂μ)*t^(k+1)) =
      ∫ z, ∑ k∈Finset.range K, (-1:ℝ)^k/(k+1)*qMoment m (T z) (D z) k (single n)*t^(k+1) ∂μ := by
    rw [integral_finsetSum _ (fun k _ => hi k)]
    simp only [integral_mul_const,integral_const_mul]
  rw [he,← integral_sub hIi (integrable_finsetSum _ (fun k _ => hi k))]
  exact abs_integral_le_bound (fun z => logInsertion_tail_bound (T z) m hm hpos hnz hroot hend (D z) (hD z) ht K)

/-- Comparing two integrated finite expansions only requires finitely many
 coefficient errors, with the same uniform geometric remainder. -/
lemma logExpansion_comparison {A B : ℝ} {a b : ℕ → ℝ} (K : ℕ) {t R : ℝ}
    (hA : |A-∑ k∈Finset.range K,(-1:ℝ)^k/(k+1)*a k*t^(k+1)|≤R)
    (hB : |B-∑ k∈Finset.range K,(-1:ℝ)^k/(k+1)*b k*t^(k+1)|≤R) :
    |A-B|≤2*R+∑ k∈Finset.range K, |t|^(k+1)/(k+1)*|a k-b k| := by
  let U := ∑ k∈Finset.range K,(-1:ℝ)^k/(k+1)*a k*t^(k+1)
  let V := ∑ k∈Finset.range K,(-1:ℝ)^k/(k+1)*b k*t^(k+1)
  have hUV : |U-V|≤∑ k∈Finset.range K, |t|^(k+1)/(k+1)*|a k-b k| := by
    dsimp only [U,V]
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro k _
    have he : (-1:ℝ)^k/(k+1)*a k*t^(k+1)-(-1:ℝ)^k/(k+1)*b k*t^(k+1)=
        ((-1:ℝ)^k*t^(k+1)/(k+1))*(a k-b k) := by ring
    rw [he,abs_mul,abs_div,abs_mul,abs_pow,abs_pow,abs_neg,abs_one,one_pow,one_mul,
      abs_of_pos (show (0:ℝ)<k+1 by positivity)]
  have h1 := abs_sub_le A U B
  have h2 := abs_sub_le U V B
  rw [abs_sub_comm V B] at h2
  dsimp only [U,V] at h1 h2 hUV
  linarith

end DilutedSpinGlass.PrescribedTree

end

end OAI
