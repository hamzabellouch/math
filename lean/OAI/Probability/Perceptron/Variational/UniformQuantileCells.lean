import Mathlib
import OAI.Probability.Perceptron.Variational.FiniteFieldModel

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def uniformQuantileGrid (n : ℕ) (i : Fin (n+2)) : Time :=
  ⟨(i:ℝ)/(n+1),div_nonneg (Nat.cast_nonneg _) (by positivity),
    (div_le_one (by positivity : (0:ℝ)<n+1)).mpr (by exact_mod_cast (Nat.le_of_lt_succ i.isLt))⟩

lemma uniformQuantileGrid_strict (n : ℕ) : StrictMono (uniformQuantileGrid n) := by
  intro i j hij
  change (i:ℝ)/(n+1)<(j:ℝ)/(n+1)
  exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by positivity)

lemma uniformQuantileGrid_zero (n : ℕ) : uniformQuantileGrid n 0=0 := by
  apply Subtype.ext
  norm_num [uniformQuantileGrid]

lemma uniformQuantileGrid_last (n : ℕ) : uniformQuantileGrid n (Fin.last (n+1))=1 := by
  apply Subtype.ext
  change ((n+1:ℕ):ℝ)/(n+1)=1
  push_cast
  exact div_self (by positivity)

def uniformQuantileCell (n : ℕ) (u : Time) : Fin (n+1) :=
  ⟨min ⌊(n+1:ℝ)*(u:ℝ)⌋₊ n, Nat.lt_succ_of_le (min_le_right _ _)⟩

lemma uniformQuantileCell_mono (n : ℕ) : Monotone (uniformQuantileCell n) := by
  intro u v huv
  change min ⌊(n+1:ℝ)*(u:ℝ)⌋₊ n ≤ min ⌊(n+1:ℝ)*(v:ℝ)⌋₊ n
  exact min_le_min_right _ (Nat.floor_mono (mul_le_mul_of_nonneg_left (show (u:ℝ)≤v from huv) (by positivity)))

lemma uniformQuantileCell_measurable (n : ℕ) : Measurable (uniformQuantileCell n) :=
  (uniformQuantileCell_mono n).measurable

lemma uniformQuantileCell_floor {n : ℕ} {u : Time} (hu : (u:ℝ)<1) :
    (uniformQuantileCell n u).val=⌊(n+1:ℝ)*(u:ℝ)⌋₊ := by
  change min _ n=_
  apply min_eq_left
  have hf : ⌊(n+1:ℝ)*(u:ℝ)⌋₊<n+1 := by
    rw [Nat.floor_lt (mul_nonneg (by positivity) u.2.1)]
    push_cast
    nlinarith
  omega

lemma uniformQuantileCell_bounds (n : ℕ) (u : Time) :
    uniformQuantileGrid n (uniformQuantileCell n u).castSucc≤u ∧
      u≤uniformQuantileGrid n (uniformQuantileCell n u).succ := by
  by_cases hu : (u:ℝ)<1
  · have he := uniformQuantileCell_floor (n:=n) hu
    constructor
    · change ((uniformQuantileCell n u).val:ℝ)/(n+1)≤u
      rw [he,div_le_iff₀ (by positivity)]
      simpa only [mul_comm] using Nat.floor_le (mul_nonneg (show (0:ℝ)≤(n:ℝ)+1 by positivity) u.2.1)
    · change (u:ℝ)≤((_ : ℕ):ℝ)/(n+1)
      rw [Fin.val_succ,he,le_div_iff₀ (by positivity)]
      push_cast
      simpa only [mul_comm] using (Nat.lt_floor_add_one ((n+1:ℝ)*(u:ℝ))).le
  · have he : u=1 := Subtype.ext (le_antisymm u.2.2 (le_of_not_gt hu))
    subst u
    have hcell : uniformQuantileCell n 1=Fin.last n := by
      apply Fin.ext
      change min ⌊(n+1:ℝ)*1⌋₊ n=n
      rw [mul_one,show (n:ℝ)+1=((n+1:ℕ):ℝ) by push_cast; rfl,Nat.floor_natCast]
      omega
    rw [hcell,Fin.succ_last,uniformQuantileGrid_last]
    exact ⟨le_top,le_rfl⟩

lemma uniformQuantileCell_atom {n : ℕ} {u : Time} (hu : (u:ℝ)<1) (i : Fin (n+1)) :
    uniformQuantileCell n u=i ↔
      u∈Ico (uniformQuantileGrid n i.castSucc) (uniformQuantileGrid n i.succ) := by
  rw [Fin.ext_iff,uniformQuantileCell_floor hu]
  rw [Nat.floor_eq_iff (mul_nonneg (by positivity) u.2.1)]
  change ((i:ℝ)≤(n+1:ℝ)*(u:ℝ) ∧ (n+1:ℝ)*(u:ℝ)<(i:ℝ)+1) ↔
    ((i:ℝ)/(n+1)≤(u:ℝ) ∧ (u:ℝ)<((i.val+1:ℕ):ℝ)/(n+1))
  rw [div_le_iff₀ (by positivity),lt_div_iff₀ (by positivity)]
  push_cast
  ring_nf

lemma uniformQuantileCell_weight (n : ℕ) (i : Fin (n+1)) :
    timeLaw.real ((uniformQuantileCell n) ⁻¹' {i})=1/(n+1:ℝ) := by
  have hae : ((uniformQuantileCell n) ⁻¹' {i})=ᵐ[timeLaw]
      Ico (uniformQuantileGrid n i.castSucc) (uniformQuantileGrid n i.succ) := by
    have hnot : ∀ᵐ u ∂timeLaw, u≠1 := by exact ae_iff.mpr (by simp)
    filter_upwards [hnot] with u hu
    exact propext (uniformQuantileCell_atom (lt_of_le_of_ne u.2.2 (fun he => hu (Subtype.ext he))) i)
  rw [measureReal_congr hae]
  simp only [Measure.real,timeLaw_eq_volume,unitInterval.volume_Ico]
  rw [ENNReal.toReal_ofReal]
  · dsimp [uniformQuantileGrid]
    push_cast
    ring
  · exact sub_nonneg.mpr ((uniformQuantileGrid_strict n).monotone (Fin.castSucc_le_succ i))

lemma uniformQuantileCell_integral (n : ℕ) (F : Fin (n+1)→ℝ) :
    (∫ u, F (uniformQuantileCell n u) ∂timeLaw)=∑ i, (1/(n+1:ℝ))*F i := by
  rw [integral_finite_label _ (uniformQuantileCell_measurable n)]
  simp_rw [uniformQuantileCell_weight]

lemma uniformQuantileCell_upper {n : ℕ} (k : Fin (n+1)) (u : Time) :
    k ≤ uniformQuantileCell n u ↔ uniformQuantileGrid n k.castSucc≤u := by
  change k.val ≤ min ⌊(n+1:ℝ)*(u:ℝ)⌋₊ n ↔ (k:ℝ)/(n+1)≤u
  rw [le_min_iff,and_iff_left (Nat.le_of_lt_succ k.isLt),Nat.le_floor_iff (mul_nonneg (by positivity) u.2.1),
    div_le_iff₀ (by positivity)]
  rw [mul_comm (u:ℝ)]

lemma uniformQuantileCell_tail_integral (n : ℕ) (F : Fin (n+1)→ℝ) (k : Fin (n+1)) :
    (∫ u in Ici (uniformQuantileGrid n k.castSucc), F (uniformQuantileCell n u) ∂timeLaw)=
      ∑ i, if k ≤ i then (1/(n+1:ℝ))*F i else 0 := by
  rw [← integral_indicator measurableSet_Ici]
  have he (u : Time) : (Ici (uniformQuantileGrid n k.castSucc)).indicator
      (fun u => F (uniformQuantileCell n u)) u=
      (if k ≤ uniformQuantileCell n u then F (uniformQuantileCell n u) else 0) := by
    simp only [Set.indicator_apply,mem_Ici,← uniformQuantileCell_upper]
  simp_rw [he]
  rw [uniformQuantileCell_integral n (fun i => if k ≤ i then F i else 0)]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

def compactSpinTime (x : CompactOverlap) : Time :=
  ⟨(x.val+1)/2,by linarith [x.2.1],by linarith [x.2.2]⟩

lemma compactSpinTime_continuous : Continuous compactSpinTime := by
  unfold compactSpinTime
  fun_prop

lemma compactSpinTime_mono : Monotone compactSpinTime := by
  intro x y hxy
  change (x.val+1)/2 ≤ (y.val+1)/2
  have : x.val ≤ y.val := hxy
  linarith

def compactSpinCode (n : ℕ) (x : CompactJointOverlap) : Fin (n+1) :=
  uniformQuantileCell n (compactSpinTime x.1)

lemma compactSpinCode_measurable (n : ℕ) : Measurable (compactSpinCode n) :=
  (uniformQuantileCell_measurable n).comp (compactSpinTime_continuous.measurable.comp measurable_fst)

lemma compactSpinCode_mono (n : ℕ) {x y : CompactJointOverlap} (h : x.1.val ≤ y.1.val) :
    compactSpinCode n x ≤ compactSpinCode n y :=
  uniformQuantileCell_mono n (compactSpinTime_mono h)

def compactSpinDecode (n : ℕ) (i : Fin (n+1)) : ℝ :=
  2*(uniformQuantileGrid n i.castSucc:ℝ)-1

lemma compactSpinDecode_error (n : ℕ) (x : CompactJointOverlap) :
    |compactSpinDecode n (compactSpinCode n x)-x.1.val| ≤ 2/(n+1:ℝ) := by
  obtain ⟨hlo,hhi⟩ := uniformQuantileCell_bounds n (compactSpinTime x.1)
  have hlo' : (uniformQuantileGrid n (compactSpinCode n x).castSucc:ℝ) ≤ (x.1.val+1)/2 := hlo
  have hhi' : (x.1.val+1)/2 ≤ (uniformQuantileGrid n (compactSpinCode n x).succ:ℝ) := hhi
  have hgap : (uniformQuantileGrid n (compactSpinCode n x).succ:ℝ)-
      (uniformQuantileGrid n (compactSpinCode n x).castSucc:ℝ)=1/(n+1:ℝ) := by
    simp only [uniformQuantileGrid,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
    ring
  dsimp only [compactSpinDecode]
  rw [abs_of_nonpos (by linarith)]
  simp only [div_eq_mul_inv,one_mul] at hgap ⊢
  linarith

lemma compactSpinDecode_tendsto (x : CompactJointOverlap) :
    Tendsto (fun n => compactSpinDecode n (compactSpinCode n x)) atTop (𝓝 x.1.val) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun n : ℕ => x.1.val-2*(1/(n+1:ℝ))) (h := fun n : ℕ => x.1.val+2*(1/(n+1:ℝ)))
  · simpa using tendsto_const_nhds.sub ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul 2)
  · simpa using tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul 2)
  · intro n
    have h := (abs_le.mp (compactSpinDecode_error n x)).1
    simp only [div_eq_mul_inv,one_mul] at h ⊢
    linarith
  · intro n
    have h := (abs_le.mp (compactSpinDecode_error n x)).2
    simp only [div_eq_mul_inv,one_mul] at h ⊢
    linarith

end SphericalPerceptronFreeEnergy

end

end OAI
