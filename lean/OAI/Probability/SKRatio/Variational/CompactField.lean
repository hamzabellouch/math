import Mathlib
import OAI.Probability.SKRatio.Calculus.PlusSpin
import OAI.Probability.SKRatio.Variational.ScalarKernel

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open Scalar Calculus

abbrev FieldWeight := Set.Icc (0:ℝ) 2

instance : CompactSpace FieldWeight := inferInstanceAs (CompactSpace (Set.Icc (0:ℝ) 2))

def compactWeight (h : ℝ) : FieldWeight :=
  ⟨w h, (w_pos h).le, by unfold w; linarith [(m_bounds h).1]⟩

lemma compactWeight_lipschitz : LipschitzWith 1 compactWeight := by
  apply LipschitzWith.of_dist_le_mul
  intro h t
  change |w h-w t| ≤ (1:ℝ)*|h-t|
  simpa only [w,m,sub_sub_sub_cancel_left,abs_sub_comm,one_mul] using tanh_lipschitz_abs h t

@[simp] lemma compactWeight_coe (h : ℝ) : (compactWeight h : ℝ) = w h := rfl

def compactV (a : FieldWeight) : ℝ := (a:ℝ)*(2-a)

def compactF (p : FieldWeight × FieldWeight) : ℝ :=
  (p.2:ℝ)^2*(2-p.2)^2/((p.1:ℝ)+p.2)
def compactK (p : FieldWeight × FieldWeight) : ℝ :=
  compactV p.1*compactV p.2/((p.1:ℝ)+p.2)

lemma compactV_nonneg (a : FieldWeight) : 0≤compactV a :=
  mul_nonneg a.2.1 (sub_nonneg.mpr a.2.2)
lemma compactV_le_one (a : FieldWeight) : compactV a≤1 := by
  dsimp [compactV]
  nlinarith [sq_nonneg ((a:ℝ)-1)]
lemma compactV_le (a : FieldWeight) : compactV a≤2*a := by
  dsimp [compactV]
  nlinarith [sq_nonneg (a:ℝ)]
lemma compactF_nonneg (p : FieldWeight × FieldWeight) : 0≤compactF p := by
  unfold compactF
  exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (add_nonneg p.1.2.1 p.2.2.1)
lemma compactK_nonneg (p : FieldWeight × FieldWeight) : 0≤compactK p := by
  unfold compactK
  exact div_nonneg (mul_nonneg (compactV_nonneg _) (compactV_nonneg _)) (add_nonneg p.1.2.1 p.2.2.1)

lemma compactF_bound (p : FieldWeight × FieldWeight) : compactF p ≤ 4*(p.2:ℝ) := by
  by_cases hz : (p.1:ℝ)+(p.2:ℝ)=0
  · simp only [compactF,hz,div_zero]
    exact mul_nonneg (by norm_num) p.2.2.1
  have hd : 0<(p.1:ℝ)+(p.2:ℝ) := lt_of_le_of_ne (add_nonneg p.1.2.1 p.2.2.1) (Ne.symm hz)
  apply (div_le_iff₀ hd).mpr
  have hs : (2-(p.2:ℝ))^2≤4 := by nlinarith [p.2.2.1,p.2.2.2]
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (p.2:ℝ))
  nlinarith only [hm,mul_nonneg p.1.2.1 p.2.2.1]

lemma compactK_bound (p : FieldWeight × FieldWeight) : compactK p ≤ 4*(p.2:ℝ) := by
  by_cases hz : (p.1:ℝ)+(p.2:ℝ)=0
  · simp only [compactK,hz,div_zero]
    exact mul_nonneg (by norm_num) p.2.2.1
  have hd : 0<(p.1:ℝ)+(p.2:ℝ) := lt_of_le_of_ne (add_nonneg p.1.2.1 p.2.2.1) (Ne.symm hz)
  apply (div_le_iff₀ hd).mpr
  have hm := mul_le_mul (compactV_le p.1) (compactV_le p.2)
    (compactV_nonneg p.2) (mul_nonneg (by norm_num : (0:ℝ)≤2) p.1.2.1)
  nlinarith only [hm,sq_nonneg (p.2:ℝ)]

lemma continuous_compactV : Continuous compactV := by unfold compactV; fun_prop

lemma continuous_compact_div {f : FieldWeight × FieldWeight → ℝ}
    (hnonneg : ∀ p, 0≤f p) (hbound : ∀ p, f p≤4*(p.2:ℝ))
    (hoff : ∀ p, (p.1:ℝ)+(p.2:ℝ)≠0 → ContinuousAt f p) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hz : (p.1:ℝ)+(p.2:ℝ)=0
  · have h2 : (p.2:ℝ)=0 := by linarith [p.1.2.1,p.2.2.1]
    have hp : f p=0 := le_antisymm (by simpa [h2] using hbound p) (hnonneg p)
    rw [ContinuousAt,hp]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h := fun q : FieldWeight × FieldWeight => 4*(q.2:ℝ))
      (by simpa only [ContinuousAt,h2,mul_zero] using
        (show Continuous (fun q : FieldWeight × FieldWeight => 4*(q.2:ℝ)) by fun_prop).continuousAt (x := p))
      hnonneg hbound
  · exact hoff p hz

lemma continuous_compactF : Continuous compactF := by
  apply continuous_compact_div compactF_nonneg compactF_bound
  intro p hp
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hp

lemma continuous_compactK : Continuous compactK := by
  apply continuous_compact_div compactK_nonneg compactK_bound
  intro p hp
  exact ContinuousAt.div
    ((continuous_compactV.comp continuous_fst).mul (continuous_compactV.comp continuous_snd)).continuousAt
    (by fun_prop) hp

lemma compactV_weight (h : ℝ) : compactV (compactWeight h) = v h := by
  unfold compactV compactWeight w v
  dsimp
  ring

lemma compactF_weight (h t : ℝ) : compactF (compactWeight h,compactWeight t) =
    v t^2/(w h+w t) := by
  unfold compactF
  simp only [compactWeight_coe,←mul_pow]
  rw [show w t*(2-w t)=v t from compactV_weight t]

lemma compactK_weight (h t : ℝ) : compactK (compactWeight h,compactWeight t) =
    kernel h t := by
  unfold compactK kernel
  rw [compactV_weight,compactV_weight]
  rfl

end SKRatio.Planted

end
end

end OAI
