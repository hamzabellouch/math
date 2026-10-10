import Mathlib
import OAI.Probability.Subsphere.Geometry.Affine

namespace OAI

noncomputable section

namespace SubsphereCurrent.Fixed
section
open scoped ENNReal NNReal

def boundConstant : ℝ := Real.exp 2048
lemma boundConstant_pos : 0 < boundConstant := Real.exp_pos _
lemma two_le_boundConstant : 2 ≤ boundConstant := by
  have h := Real.add_one_le_exp (2048 : ℝ)
  unfold boundConstant
  linarith

lemma parameters {d j m : ℕ} (hd : 64 ≤ d) (hm : (d : ℝ)/2 + 2*j ≤ m) :
    let q := (m-1)/4
    2 ≤ q ∧ d ≤ 16*q ∧ d/32 ≤ q ∧ (d : ℝ)/32 ≤ 2*q ∧
      j*(d/32)/q+1 ≤ j+1 := by
  have hdm : d ≤ 2*m := by
    have : (d : ℝ) ≤ 2*m := by nlinarith [Nat.cast_nonneg j (α := ℝ)]
    exact_mod_cast this
  dsimp
  have hq : 2 ≤ (m-1)/4 := by omega
  have hq32 : d/32 ≤ (m-1)/4 := by omega
  refine ⟨hq, by omega, hq32, ?_, ?_⟩
  · have hn : d ≤ 64*((m-1)/4) := by omega
    have hr : (d : ℝ) ≤ 64*((m-1)/4 : ℕ) := by exact_mod_cast hn
    linarith
  · have hmul : j*(d/32) ≤ j*((m-1)/4) := Nat.mul_le_mul_left j hq32
    have hdiv : j*(d/32)/((m-1)/4) ≤ j := by
      exact Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hmul)
    omega

lemma raw_bound_le {d j m : ℕ} {η : ℝ}
    (hd : 64 ≤ d) (hm : (d : ℝ)/2 + 2*j ≤ m) (hmd : m ≤ d)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ((3 : ℝ)*4^m * η^(2*((m-1)/4))) *
      ((32768 : ℝ)^m * ((2 : ℝ)^(d^2))^(1/(((m-1)/4 : ℕ) : ℝ)))^
        (j*(d/32)/((m-1)/4)+1) ≤
      (boundConstant^(j+1)*η)^((d : ℝ)/32) := by
  let q := (m-1)/4
  let b := j*(d/32)/q+1
  obtain ⟨hq,hdq,_,ha,hb⟩ := parameters hd hm
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hdp : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hmp : (m : ℝ) ≤ d := by exact_mod_cast hmd
  have hdqp : (d : ℝ) ≤ 16*q := by exact_mod_cast hdq
  have hbp : (b : ℝ) ≤ j+1 := by exact_mod_cast hb
  have hapse : (d : ℝ)/32 ≤ (2*q : ℕ) := by simpa [q] using ha
  have hMq : (d : ℝ)^2/q ≤ 16*d := by
    apply (div_le_iff₀ hqpos).2
    nlinarith [mul_le_mul_of_nonneg_left hdqp (Nat.cast_nonneg d)]
  have hlogη : Real.log η ≤ 0 := Real.log_nonpos hη.le hη1
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hlog3 : Real.log (3 : ℝ) ≤ 3 := Real.log_le_self (by norm_num)
  have hlog4 : Real.log (4 : ℝ) ≤ 4 := Real.log_le_self (by norm_num)
  have hlog32 : Real.log (32768 : ℝ) ≤ 15 := by
    have he : (32768 : ℝ) = 2^(15 : ℕ) := by norm_num
    rw [he,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith
  have hinside : (m : ℝ)*Real.log 32768 + (d : ℝ)^2/q*Real.log 2 ≤ 31*d := by
    have h1 := mul_le_mul_of_nonneg_left hlog32 (Nat.cast_nonneg m)
    have h2 := mul_le_mul_of_nonneg_left hlog2 (by positivity : 0 ≤ (d : ℝ)^2/q)
    nlinarith
  have hfull : (b : ℝ)*((m : ℝ)*Real.log 32768 + (d : ℝ)^2/q*Real.log 2)
      ≤ 31*d*(j+1) := by
    calc
      _ ≤ (b : ℝ)*(31*d) := mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg b)
      _ ≤ ((j : ℝ)+1)*(31*d) := mul_le_mul_of_nonneg_right hbp (by positivity)
      _ = _ := by ring
  have hεpow := mul_le_mul_of_nonpos_right hapse hlogη
  have hrawpos : 0 < ((3 : ℝ)*4^m * η^(2*q)) *
      ((32768 : ℝ)^m * ((2 : ℝ)^(d^2))^(1/(q : ℝ)))^b := by positivity
  have htargpos : 0 < (boundConstant^(j+1)*η)^((d : ℝ)/32) := by
    exact Real.rpow_pos_of_pos (mul_pos (pow_pos boundConstant_pos _) hη) _
  apply (Real.log_le_log_iff hrawpos htargpos).1
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow,Real.log_pow,
    Real.log_mul (by positivity) (by positivity),Real.log_pow,
    Real.log_rpow (by positivity),Real.log_pow,
    Real.log_rpow (mul_pos (pow_pos boundConstant_pos _) hη),
    Real.log_mul (pow_ne_zero _ boundConstant_pos.ne') hη.ne',Real.log_pow]
  have he : (1/(q : ℝ))*((d^2 : ℕ)*Real.log 2) = (d : ℝ)^2/q*Real.log 2 := by
    push_cast; ring
  rw [he]
  simp only [boundConstant, Real.log_exp]
  have h4 := mul_le_mul_of_nonneg_left hlog4 (Nat.cast_nonneg m)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  push_cast at hεpow ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hdp) (show (0 : ℝ) ≤ (j:ℝ)+1 by positivity)]

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
universe u

lemma dimension_bound_one_seed {d j m : ℕ} (hd : 64 ≤ d)
    (hm : (d : ℝ)/2 + 2*j ≤ m) (hmd : m ≤ d)
    (L : Stream (Vector m) (Fin (2^(d^2))) (j*(d/32))) (hL : L.BorelRules)
    {η : ℝ} (hη : 0 < η) :
    (∫⁻ z : Sphere (Vector m) × (Fin (j*(d/32)) → Vector m),
      L.euclideanSuccess η z.1.val z.2
        ∂(sphereLaw (Vector m)).prod (rowsLaw (Vector m) (j*(d/32)))) ≤
      ENNReal.ofReal ((boundConstant^(j+1)*η)^((d : ℝ)/32)) := by
  have hmpos : 0 < m := by
    have hdp : (64 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) < m := by nlinarith [Nat.cast_nonneg j (α := ℝ)]
    exact_mod_cast this
  let : NeZero m := ⟨by omega⟩
  let q := (m-1)/4
  let a := 2*q
  have hq : 2 ≤ q := (parameters hd hm).1
  have ha : 2*a ≤ Module.finrank ℝ (Vector m)-1 := by
    simp only [Vector,finrank_euclideanSpace_fin]
    dsimp [a,q]
    omega
  have hcpos : 0 < boundConstant := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) two_le_boundConstant
  have hP1 := L.average_euclideanSuccess_le_one η
  by_cases hη1 : η ≤ 1
  · have hb := L.average_euclideanSuccess_bound hL hη ha hq (le_refl a)
    have ht : (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ (Vector m)) * ENNReal.ofReal (η^a)) *
        SubsphereRegression.streamFactor (E := Vector m) (J := Fin (2^(d^2))) q ^
          (j*(d/32)/q+1) ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top (SubsphereRegression.streamFactor_ne_top q))
    have hr := ENNReal.toReal_mono ht hb
    have hr' : (∫⁻ z : Sphere (Vector m) × (Fin (j*(d/32)) → Vector m),
        L.euclideanSuccess η z.1.val z.2
          ∂(sphereLaw (Vector m)).prod (rowsLaw (Vector m) (j*(d/32)))).toReal ≤
        ((3 : ℝ)*4^m * η^(2*((m-1)/4))) *
          ((32768 : ℝ)^m * ((2 : ℝ)^(d^2))^(1/(((m-1)/4 : ℕ) : ℝ)))^
            (j*(d/32)/((m-1)/4)+1) := by
      simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 3*4^m),
        ENNReal.toReal_ofReal (by positivity : 0 ≤ η^a), SubsphereRegression.streamFactor,
        ENNReal.toReal_pow, ← ENNReal.toReal_rpow, finrank_euclideanSpace_fin,
        Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Vector,a,q] using hr
    apply (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top (by simp) hP1) ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (by positivity) _)]
    exact hr'.trans (raw_bound_le hd hm hmd hη hη1)
  · apply hP1.trans
    apply ENNReal.one_le_ofReal.2
    apply Real.one_le_rpow _ (by positivity)
    have hc : 1 ≤ boundConstant^(j+1) := one_le_pow₀ (by linarith [two_le_boundConstant])
    nlinarith

theorem dimension_estimate : DimensionEstimate.{u} := by
  refine ⟨boundConstant,two_le_boundConstant,64,?_⟩
  intro d hd j m hm hmd η hη Ω _ ρ hρ L hL hmexp
  let : IsProbabilityMeasure ρ := hρ
  have hmpos : 0 < m := by
    have hdp : (64 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) < m := by nlinarith [Nat.cast_nonneg j (α := ℝ)]
    exact_mod_cast this
  let : NeZero m := ⟨by omega⟩
  let : IsProbabilityMeasure (rowsLaw (Vector m) (j*(d/32))) := rowsLaw_probability _
  let : IsFiniteMeasure (rowsLaw (Vector m) (j*(d/32))) := inferInstance
  let : SFinite (rowsLaw (Vector m) (j*(d/32))) := by
    let : SigmaFinite (rowsLaw (Vector m) (j*(d/32))) := IsFiniteMeasure.toSigmaFinite _
    infer_instance
  let e := swapFirstTwo Ω (Sphere (Vector m)) (Fin (j*(d/32)) → Vector m)
  have hp := measurePreserving_swapFirstTwo ρ (sphereLaw (Vector m)) (rowsLaw (Vector m) (j*(d/32)))
  have hm' := hmexp.comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  have he := hp.lintegral_comp_emb e.measurableEmbedding
    (fun z : Sphere (Vector m) × (Ω × (Fin (j*(d/32)) → Vector m)) =>
      (L z.2.1).euclideanSuccess η z.1.val z.2.2)
  dsimp only [Function.comp_def] at hm'
  rw [← he,lintegral_prod _ hm']
  calc
    _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal ((boundConstant^(j+1)*η)^((d : ℝ)/32)) ∂ρ := by
      apply lintegral_mono_ae
      filter_upwards [hL] with ω hω
      exact dimension_bound_one_seed hd hm hmd (L ω) hω hη
    _ = _ := by simp

end SubsphereCurrent.Fixed

end

end OAI
