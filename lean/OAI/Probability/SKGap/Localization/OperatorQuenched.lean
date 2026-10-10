import Mathlib
import OAI.Probability.SKGap.Localization.PlantedMarginalLaw

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
local instance (n : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := borel _
local instance (n : ℕ) : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

lemma coupling_goeEdges {n : ℕ} (r : ℝ) (g : MatrixCoordinates (Fin n)→ℝ) :
    coupling (goeEdges r g)=eraseDiagonal (goeMatrix r g) := by
  ext i k
  by_cases hik : i < k
  · simp [coupling,hik,goeEdges,eraseDiagonal,ne_of_lt hik]
  · by_cases hki : k < i
    · simp [coupling,hik,hki,goeEdges,eraseDiagonal,
        (ne_of_lt hki).symm,goeMatrix,add_comm]
    · have he : i=k := le_antisymm (le_of_not_gt hki) (le_of_not_gt hik)
      subst k
      simp [coupling,eraseDiagonal]

lemma operatorBound_of_opNorm {n : ℕ} {K : ℝ} {J : Matrix (Fin n) (Fin n) ℝ}
    (hJ : opNorm J ≤ K) : operatorBound K J := by
  intro z
  have hh := J.toEuclideanLin.toContinuousLinearMap.le_opNorm
    (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))
  exact hh.trans (mul_le_mul_of_nonneg_right hJ (vectorNorm_nonneg z))

lemma zero_diagonal_operator_tail {j d : ℝ} (hj : 0<j) (hd : 0<d)
    {n : ℕ} (hn : 0 < n) :
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | ¬operatorBound (2*sqrt j+2*d) (eraseDiagonal (goeMatrix (j/(n:ℝ)) g))} ≤
      2*exp (-(d^2/(π^2*j))*(n:ℝ))+2*(n:ℝ)*exp (-(d^2/(8*j))*(n:ℝ)) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let μ := gaussianCoordinates (MatrixCoordinates (Fin n))
  let r := j/(n:ℝ)
  let E := {g : MatrixCoordinates (Fin n)→ℝ | 2*sqrt j+d<opNorm (goeMatrix r g)}
  let V := {g : MatrixCoordinates (Fin n)→ℝ | ∃ i,d < |goeMatrix r g i i|}
  have hr : 0<r := div_pos hj (Nat.cast_pos.mpr hn)
  have hs : {g | ¬operatorBound (2*sqrt j+2*d) (eraseDiagonal (goeMatrix r g))}⊆E∪V := by
    intro g hg
    by_contra hh
    have hh' : ¬2*sqrt j+d<opNorm (goeMatrix r g) ∧ ¬∃ i,d < |goeMatrix r g i i| := by
      simpa only [Set.mem_union,E,V,Set.mem_ofPred_eq,not_or] using hh
    apply hg
    apply operatorBound_of_opNorm
    have hdg := opNorm_diagonal_le hd.le (fun i=>le_of_not_gt (fun hi=>hh'.2 ⟨i,hi⟩))
    calc
      _ ≤ opNorm (goeMatrix r g)+opNorm (diagonal (fun i=>goeMatrix r g i i)) := opNorm_sub _ _
      _ ≤ (2*sqrt j+d)+d := add_le_add (le_of_not_gt hh'.1) hdg
      _ = _ := by ring
  have he : μ.real E ≤ 2*exp (-(d^2/(π^2*j))*(n:ℝ)) := by
    have hh := goe_norm_tail (ι:=Fin n) hj hd.le
    have heq : -(d^2/(π^2*j))*(n:ℝ) = -d^2*(n:ℝ)/(π^2*j) := by ring
    rw [heq]
    simpa only [Fintype.card_fin,matrixOperator,opNorm,μ,E,r] using hh
  have hv : μ.real V ≤ 2*(n:ℝ)*exp (-(d^2/(8*j))*(n:ℝ)) := by
    have hh := goe_diagonal_tail (ι:=Fin n) hr hd.le
    apply hh.trans_eq
    simp only [Fintype.card_fin]
    congr 2
    dsimp [r]
    field_simp
  exact (measureReal_mono hs).trans ((measureReal_union_le E V).trans (add_le_add he hv))

lemma disorder_operator_tail {β d : ℝ} (hβ : 0<β) (hd : 0<d)
    {n : ℕ} (hn : 0 < n) :
    (disorderLaw β n).real {J | ¬operatorBound (2*β+2*d) (coupling J)} ≤
      2*exp (-(d^2/(π^2*β^2))*(n:ℝ))+2*(n:ℝ)*exp (-(d^2/(8*β^2))*(n:ℝ)) := by
  let E : Set (Disorder n) := {J | ¬operatorBound (2*β+2*d) (coupling J)}
  have hE : MeasurableSet E := by
    have hc : Continuous (coupling : Disorder n→Matrix (Fin n) (Fin n) ℝ) := continuous_coupling
    exact ((isClosed_operatorBound _).preimage hc).measurableSet.compl
  have hm := (measurePreserving_goeEdges (n:=n) (r:=β^2/(n:ℝ)) (by positivity)).measure_preimage hE.nullMeasurableSet
  have he : (disorderLaw β n).real E =
      (gaussianCoordinates (MatrixCoordinates (Fin n))).real
        {g | ¬operatorBound (2*sqrt (β^2)+2*d) (eraseDiagonal (goeMatrix (β^2/(n:ℝ)) g))} := by
    have hm' := congrArg ENNReal.toReal hm
    rw [sqrt_sq hβ.le]
    simpa only [Measure.real,E,Set.preimage_ofPred_eq,coupling_goeEdges,disorderLaw] using hm'.symm
  rw [he]
  exact zero_diagonal_operator_tail (sq_pos_of_pos hβ) hd hn

lemma exp_dimension_tendsto_zero {a : ℝ} (ha : 0<a) :
    Tendsto (fun n : ℕ=>exp (-a*(n:ℝ))) atTop (𝓝 0) := by
  have hh : Tendsto (fun n : ℕ=>a*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  simpa only [Function.comp_def,neg_mul] using tendsto_exp_neg_atTop_nhds_zero.comp hh

theorem quenched_operator_bound {β K : ℝ} (hβ : 0<β) (hK : 2*β<K) :
    Tendsto (fun n=>(disorderLaw β n).real {J | ¬operatorBound K (coupling J)}) atTop (𝓝 0) := by
  let d := (K-2*β)/2
  have hd : 0<d := by dsimp [d]; linarith
  let a := d^2/(π^2*β^2)
  let b := d^2/(8*β^2)
  have ha : 0<a := by dsimp [a]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  obtain ⟨N,hN⟩ := absorb_linear_exponential hb
  have hbound : ∀ᶠ n : ℕ in atTop,(disorderLaw β n).real {J | ¬operatorBound K (coupling J)} ≤
      2*exp (-a*(n:ℝ))+exp (-(b/2)*(n:ℝ)) := by
    filter_upwards [eventually_ge_atTop N,eventually_gt_atTop 0] with n hn hn0
    have he : 2*β+2*d=K := by dsimp [d];ring
    have hh := disorder_operator_tail hβ hd hn0
    rw [he] at hh
    exact hh.trans (add_le_add le_rfl (hN n hn))
  have ht := ((exp_dimension_tendsto_zero ha).const_mul 2).add
    (exp_dimension_tendsto_zero (half_pos hb))
  simp only [mul_zero,add_zero] at ht
  exact squeeze_zero' (Eventually.of_forall (fun _=>measureReal_nonneg)) hbound ht
end SKGap.ObservationBridge

end
end

end OAI
