import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FlagGerms

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TentMatrixPositivity
open Classical MeasureTheory

theorem integral_posSemidef {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Ω → Matrix ι ι ℝ) (hA : ∀ᵐ ω∂μ,(A ω).PosSemidef)
    (hi : ∀i j,Integrable (fun ω => A ω i j) μ) :
    Matrix.PosSemidef (fun i j => ∫ω,A ω i j ∂μ) := by
  refine ⟨?_,fun x => ?_⟩
  · ext i j
    change star (∫ω,A ω j i ∂μ)=∫ω,A ω i j ∂μ
    simp only [star_trivial]
    apply integral_congr_ae
    filter_upwards [hA] with ω hω
    have he := congrFun (congrFun hω.isHermitian i) j
    simpa using he
  · have hi' (i j : ι) : Integrable (fun ω => x i*A ω i j*x j) μ :=
      ((hi i j).const_mul _).mul_const _
    have he : (∫ω,x.sum (fun i xi => x.sum (fun j xj => star xi*A ω i j*xj)) ∂μ)=
        x.sum (fun i xi => x.sum (fun j xj => star xi*(∫ω,A ω i j ∂μ)*xj)) := by
      simp only [star_trivial,Finsupp.sum]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi' i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hi' i j)]
      simp only [integral_mul_const,integral_const_mul]
    rw [← he]
    apply integral_nonneg_of_ae
    filter_upwards [hA] with ω hω
    exact hω.2 x

noncomputable def intervalMark (x t : ℝ) : ℝ :=
  (Set.Icc x (x+1)).indicator (fun _ => 1) t

theorem intervalMark_mul (x y : ℝ) :
    (fun t => intervalMark x t*intervalMark y t)=
      (Set.Icc (max x y) (min (x+1) (y+1))).indicator (fun _ => (1:ℝ)) := by
  funext t
  have hm : t∈Set.Icc (max x y) (min (x+1) (y+1)) ↔
      t∈Set.Icc x (x+1) ∧ t∈Set.Icc y (y+1) := by
    simp only [Set.mem_Icc,max_le_iff,le_min_iff]
    tauto
  by_cases hx : t∈Set.Icc x (x+1) <;> by_cases hy : t∈Set.Icc y (y+1) <;>
    simp [intervalMark,Set.indicator,hm,hx,hy]

theorem intervalMark_mul_integrable (x y : ℝ) :
    Integrable (fun t => intervalMark x t*intervalMark y t) := by
  rw [intervalMark_mul]
  exact (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))

theorem tent_eq_intervalMark_integral (x y : ℝ) :
    max (1-|x-y|) 0=∫t,intervalMark x t*intervalMark y t := by
  rw [intervalMark_mul,integral_indicator_const 1 measurableSet_Icc]
  simp only [smul_eq_mul,mul_one,Real.volume_real_Icc]
  congr 1
  rcases le_total x y with h|h
  · rw [max_eq_right h,min_eq_left (by linarith),abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h,min_eq_right (by linarith),abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem real_rankOne_posSemidef {ι : Type*} (a : ι → ℝ) :
    Matrix.PosSemidef (fun i j => a i*a j) := by
  refine ⟨?_,fun x => ?_⟩
  · ext i j
    change a j*a i=a i*a j
    exact mul_comm _ _
  · calc
      0≤(x.sum (fun i xi => xi*a i))^2 := sq_nonneg _
      _=x.sum (fun i xi => x.sum (fun j xj => star xi*(a i*a j)*xj)) := by
        simp only [pow_two,Finsupp.sum,Finset.sum_mul,Finset.mul_sum,star_trivial]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring

theorem tentMatrix_posSemidef {ι : Type*} (x : ι → ℝ) :
    Matrix.PosSemidef (fun i j => max (1-|x i-x j|) 0) := by
  have hp (t : ℝ) : Matrix.PosSemidef (fun i j => intervalMark (x i) t*intervalMark (x j) t) :=
    real_rankOne_posSemidef _
  have h := integral_posSemidef volume
    (fun t i j => intervalMark (x i) t*intervalMark (x j) t)
    (Filter.Eventually.of_forall hp) (fun i j => intervalMark_mul_integrable (x i) (x j))
  simpa only [← tent_eq_intervalMark_integral] using h

theorem planeTentMatrix_posSemidef {ι : Type*} (x : ι → ℝ×ℝ) (s : ℝ) :
    Matrix.PosSemidef (fun i j => max (1-|(x i).1/s-(x j).1/s|) 0 *
      max (1-|(x i).2/s-(x j).2/s|) 0) := by
  exact (tentMatrix_posSemidef (fun i => (x i).1/s)).hadamard
    (tentMatrix_posSemidef (fun i => (x i).2/s))

end TentMatrixPositivity

section FlagSeparatorMatrices
open Classical MeasureTheory

noncomputable def flagChamber {a : ℕ} {v : ℝ×ℝ} (t : Fin 4 → ℝ)
    (z : SquareFlag a v) : (Fin 4 × CutRing) → Bool := fun l =>
  if |conjugate l.2|≤t l.1 then
    decide (flagMem ⟨halfPlane a l.1 l.2,halfPlane_mem a l.1 l.2⟩ z) else false

theorem flagChamber_eq_iff {a : ℕ} {v : ℝ×ℝ} (t : Fin 4 → ℝ)
    (z w : SquareFlag a v) : flagChamber t z=flagChamber t w ↔
    ∀j c,|conjugate c|≤t j →
      (flagMem ⟨halfPlane a j c,halfPlane_mem a j c⟩ z ↔
       flagMem ⟨halfPlane a j c,halfPlane_mem a j c⟩ w) := by
  constructor
  · intro he j c hc
    have h := congrFun he (j,c)
    simpa only [flagChamber,hc,ite_true,decide_eq_decide] using h
  · intro h
    funext l
    simp only [flagChamber]
    split_ifs with hl
    · exact propext (h l.1 l.2 hl) ▸ rfl
    · rfl

theorem measurableSet_flagChamber_eq {a : ℕ} {v : ℝ×ℝ} (z w : SquareFlag a v) :
    MeasurableSet {t : Fin 4 → ℝ | flagChamber t z=flagChamber t w} := by
  have he : {t : Fin 4 → ℝ | flagChamber t z=flagChamber t w}=
      ⋂l : Fin 4 × CutRing, {t | flagChamber t z l=flagChamber t w l} := by
    ext t
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    exact funext_iff
  rw [he]
  apply MeasurableSet.iInter
  intro l
  by_cases hz : flagMem ⟨halfPlane a l.1 l.2,halfPlane_mem a l.1 l.2⟩ z <;>
    by_cases hw : flagMem ⟨halfPlane a l.1 l.2,halfPlane_mem a l.1 l.2⟩ w
  · simp only [flagChamber,hz,hw,decide_true,Set.ofPred_true]
    exact MeasurableSet.univ
  · simpa [flagChamber,hz,hw] using
      (measurableSet_lt (measurable_pi_apply l.1) (measurable_const (a := |conjugate l.2|)) :
        MeasurableSet {t : Fin 4 → ℝ | t l.1 < |conjugate l.2|})
  · simpa [flagChamber,hz,hw] using
      (measurableSet_lt (measurable_pi_apply l.1) (measurable_const (a := |conjugate l.2|)) :
        MeasurableSet {t : Fin 4 → ℝ | t l.1 < |conjugate l.2|})
  · simp only [flagChamber,hz,hw,decide_false,ite_self,Set.ofPred_true]
    exact MeasurableSet.univ

theorem equalityMatrix_posSemidef {ι κ : Type*} (f : ι → κ) :
    Matrix.PosSemidef (fun i j => if f i=f j then (1:ℝ) else 0) := by
  have h := (Matrix.PosSemidef.one (n := κ) (R := ℝ)).submatrix f
  have he : (1 : Matrix κ κ ℝ).submatrix f f=(fun i j => if f i=f j then 1 else 0) := by
    funext i j
    exact Matrix.one_apply (α := ℝ) (n := κ) (i := f i) (j := f j)
  rw [he] at h
  exact h

noncomputable def separatorMatrix {a : ℕ} {v : ℝ×ℝ}
    (μ : Measure (Fin 4 → ℝ)) (z w : SquareFlag a v) : ℝ :=
  ∫t,if flagChamber t z=flagChamber t w then 1 else 0 ∂μ

theorem separatorMatrix_integrand_integrable {a : ℕ} {v : ℝ×ℝ}
    (μ : Measure (Fin 4 → ℝ)) [IsFiniteMeasure μ] (z w : SquareFlag a v) :
    Integrable (fun t => if flagChamber t z=flagChamber t w then (1:ℝ) else 0) μ := by
  exact (integrable_indicator_iff (measurableSet_flagChamber_eq z w)).mpr integrableOn_const

theorem separatorMatrix_eq_measure {a : ℕ} {v : ℝ×ℝ}
    (μ : Measure (Fin 4 → ℝ)) (z w : SquareFlag a v) :
    separatorMatrix μ z w=μ.real {t|flagChamber t z=flagChamber t w} :=
  integral_indicator_one (measurableSet_flagChamber_eq z w)

theorem separatorMatrix_posSemidef {a : ℕ} {v : ℝ×ℝ}
    (μ : Measure (Fin 4 → ℝ)) [IsFiniteMeasure μ] :
    Matrix.PosSemidef (separatorMatrix (a:=a) (v:=v) μ) := by
  apply integral_posSemidef
  · exact Filter.Eventually.of_forall fun t => equalityMatrix_posSemidef (flagChamber t)
  · exact separatorMatrix_integrand_integrable μ

noncomputable def thresholdLaw (s κ : ℝ) : Measure (Fin 4 → ℝ) :=
  Measure.pi fun _ => ProbabilityTheory.cond volume (Set.Icc (κ/s) (2*κ/s))

theorem thresholdLaw_isProbability {s κ : ℝ} (hs : 0<s) (hκ : 0<κ) :
    IsProbabilityMeasure (thresholdLaw s κ) := by
  have hlt : κ/s<2*κ/s := by exact (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have : IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Icc (κ/s) (2*κ/s))) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hlt))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  unfold thresholdLaw
  infer_instance

theorem separatorMatrix_self {a : ℕ} {v : ℝ×ℝ}
    (μ : Measure (Fin 4 → ℝ)) [IsProbabilityMeasure μ] (z : SquareFlag a v) :
    separatorMatrix μ z z=1 := by simp [separatorMatrix]

theorem separatorMatrix_bounds {a : ℕ} {v : ℝ×ℝ}
    (μ : Measure (Fin 4 → ℝ)) [IsProbabilityMeasure μ] (z w : SquareFlag a v) :
    0 ≤ separatorMatrix μ z w ∧ separatorMatrix μ z w≤1 := by
  rw [separatorMatrix_eq_measure]
  exact ⟨ENNReal.toReal_nonneg,measureReal_le_one⟩

end FlagSeparatorMatrices

end SimpleAmenable
end
end

end OAI
