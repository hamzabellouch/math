import OAI.Analysis.CircleDomains.Topology.CountableBallSynthesis
import OAI.Analysis.CircleDomains.Rigidity.TraceBalloonPacking

namespace OAI

/-! The actual trace balloon density is square integrable. Positive
source disks pay for one sublist; reserved pieces pay for the zero-radius
sublist. The two sublists may overlap each other. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] Classical.propDecidable

 theorem exists_trace_balloon_density (hmax : PlanarMaximalL2)
    (c : ℕ → ℂ) (r d a : ℕ → ℝ)
    (hr : ∀ j, 0 ≤ r j) (hd : ∀ j, 0 < d j) (ha : ∀ j, 0 ≤ a j)
    (hrd : ∀ j, r j ≤ d j) (hdr : ∀ j, 0 < r j → d j ≤ 2*r j)
    (hdisj : Pairwise (Disjoint on fun j => ball (c j) (r j)))
    (ha2 : Summable (fun j => a j^2)) (hd2 : Summable (fun j => d j^2))
    (htail : ∀ j, r j = 0 →
      (∑' k : ℕ, (if r (k+j+1) = 0 then d (k+j+1) else 0)^2) ≤ d j^2/2) :
    ∃ P : ℂ → ℝ, Measurable P ∧ (∀ z, 0 ≤ P z) ∧ MemLp P 2 volume ∧
      ∀ᵐ z ∂volume, ∀ n, finiteBallDensity (Finset.range n) c d a z ≤ P z := by
  let ap := fun j => if 0 < r j then a j else 0
  let az := fun j => if 0 < r j then 0 else a j
  let dz := fun j => if r j = 0 then d j else 0
  let Ep := fun j => ball (c j) (r j)
  let Ez := reservedBalloon (fun j => ball (c j) (dz j))
  have hap (j : ℕ) : 0 ≤ ap j := by dsimp [ap]; split_ifs; exact ha j; exact le_rfl
  have haz (j : ℕ) : 0 ≤ az j := by dsimp [az]; split_ifs; exact le_rfl; exact ha j
  have hdzn (j : ℕ) : 0 ≤ dz j := by dsimp [dz]; split_ifs; exact (hd j).le; exact le_rfl
  have hdz2 : Summable (fun j => dz j^2) := by
    apply hd2.of_nonneg_of_le (fun _ => sq_nonneg _)
    intro j
    dsimp only [dz]
    split_ifs <;> simp [sq_nonneg]
  have hap2 : Summable (fun j => ap j^2) := by
    apply ha2.of_nonneg_of_le (fun _ => sq_nonneg _)
    intro j
    dsimp only [ap]
    split_ifs <;> simp [sq_nonneg]
  have haz2 : Summable (fun j => az j^2) := by
    apply ha2.of_nonneg_of_le (fun _ => sq_nonneg _)
    intro j
    dsimp only [az]
    split_ifs <;> simp [sq_nonneg]
  obtain ⟨C,_,hC⟩ := exists_countable_ball_synthesis_constant hmax
    (show 0 < Real.pi/4 by positivity)
  have hpsize (j : ℕ) (hj : ap j ≠ 0) : Real.pi/4*d j^2 ≤ volume.real (Ep j) := by
    have hrp : 0 < r j := by
      by_contra h
      exact hj (by simp [ap,h])
    have hs : d j^2 ≤ (2*r j)^2 := pow_le_pow_left₀ (hd j).le (hdr j hrp) 2
    change Real.pi/4*d j^2 ≤ volume.real (ball (c j) (r j))
    rw [show volume.real (ball (c j) (r j)) = Real.pi*r j^2 from real_volume_ball _ (hr j)]
    nlinarith [mul_le_mul_of_nonneg_left hs Real.pi_pos.le]
  have hezsub (j : ℕ) : Ez j ⊆ ball (c j) (d j) := by
    intro z hz
    exact (ball_subset_ball (by dsimp only [dz]; split_ifs; exact le_rfl; exact (hd j).le : dz j ≤ d j)) hz.1
  have hzsize (j : ℕ) (hj : az j ≠ 0) : Real.pi/4*d j^2 ≤ volume.real (Ez j) := by
    have hrz : r j = 0 := by
      have hn : ¬0 < r j := by intro h; exact hj (by simp [az,h])
      exact le_antisymm (le_of_not_gt hn) (hr j)
    have hb := reservedBalloon_area_lower (c := c) hdzn hdz2 j (by
      simpa only [dz,hrz,ite_true] using htail j hrz)
    have he : dz j = d j := by simp [dz,hrz]
    rw [he] at hb
    change Real.pi/4*d j^2 ≤ volume.real (reservedBalloon (fun i => ball (c i) (dz i)) j)
    nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg (d j))]
  obtain ⟨hP,_,hPbound⟩ := hC c d ap Ep hd hap hap2 (fun _ => measurableSet_ball)
    hdisj (fun j => ball_subset_ball (hrd j)) hpsize
  obtain ⟨hZ,_,hZbound⟩ := hC c d az Ez hd haz haz2
    (reservedBalloon_measurable (fun _ => measurableSet_ball))
    (reservedBalloon_pairwise _) hezsub hzsize
  let S := fun z => countableBallDensity c d ap z+countableBallDensity c d az z
  have hS : MemLp S 2 volume := hP.add hZ
  have hS0 (z : ℂ) : 0 ≤ S z := by
    apply add_nonneg <;> apply tsum_nonneg <;> intro j
    · exact indicator_nonneg (fun _ _ => div_nonneg (hap j) (hd j).le) z
    · exact indicator_nonneg (fun _ _ => div_nonneg (haz j) (hd j).le) z
  let P := fun z => max (hS.aestronglyMeasurable.mk S z) 0
  have hPeq : P =ᵐ[volume] S := by
    filter_upwards [hS.aestronglyMeasurable.ae_eq_mk] with z hz
    change max (hS.aestronglyMeasurable.mk S z) 0 = S z
    rw [← hz,max_eq_left (hS0 z)]
  refine ⟨P,hS.aestronglyMeasurable.stronglyMeasurable_mk.measurable.max measurable_const,
    (fun _ => le_max_right _ _),hS.ae_eq hPeq.symm,?_⟩
  filter_upwards [hPeq,hPbound,hZbound] with z hz hp hz'
  intro n
  rw [hz]
  have he : finiteBallDensity (Finset.range n) c d a z =
      finiteBallDensity (Finset.range n) c d ap z+finiteBallDensity (Finset.range n) c d az z := by
    simp only [finiteBallDensity,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [ap,az]
    split_ifs <;> simp
  rw [he]
  exact add_le_add (hp n) (hz' n)

end CircleDomainRigidity

end

end OAI
