import OAI.Dynamics.StandardMap.RealScarcityCover

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma CommonGood.scale_ge_one {k q a : ℝ} {jm jp : ℕ}
    (hg : CommonGood k q a jm jp) (hM : 1 < growthBase k) :
    1 ≤ matchedScale k q a jm jp := by
  obtain ⟨b,hm,hp⟩:=hg
  have hh:=hm.t_earlier hM 1 le_rfl (by have :=hm.1; omega)
  have ht : tSolution (orbitCoefficient k q a) 1=1 := linearSolution_one _ _ _
  rw [ht,abs_one,Nat.cast_one] at hh
  have hr : growthBase k ^ (-goodExponent*((jm:ℝ)-1)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hM.le
    have hj : (2:ℝ) ≤ jm := by exact_mod_cast hm.1
    nlinarith [goodExponent_pos]
  have hpos := abs_nonneg (tSolution (orbitCoefficient k q a) jm)
  exact (hh.trans (by nlinarith)).trans (le_max_left _ _)
lemma CommonGood.scale_mono_factor {k q a : ℝ} {jm jp lm lp : ℕ}
    (hg : CommonGood k q a jm jp) (hl : CommonGood k q a lm lp)
    (hmj : jm < lm) (hpj : jp < lp) (hM : 1 < growthBase k) :
    matchedScale k q a jm jp ≤ matchedScale k q a lm lp * growthBase k ^ (-goodExponent) := by
  obtain ⟨b,hm,hp⟩:=hg
  obtain ⟨d,hlm,hlp⟩:=hl
  have hbase := lt_trans zero_lt_one hM
  have hpow (j l : ℕ) (hjl : j < l) :
      growthBase k ^ (-goodExponent*((l:ℝ)-(j:ℝ))) ≤ growthBase k ^ (-goodExponent) := by
    apply Real.rpow_le_rpow_of_exponent_le hM.le
    have hh : (j:ℝ)+1 ≤ l := by exact_mod_cast hjl
    nlinarith [goodExponent_pos]
  apply max_le
  · calc
      _ ≤ |tSolution (orbitCoefficient k q a) lm| *growthBase k ^ (-goodExponent*((lm:ℝ)-(jm:ℝ))) :=
        hlm.t_earlier hM jm (by have :=hm.1; omega) hmj
      _ ≤ matchedScale k q a lm lp*growthBase k ^ (-goodExponent) := by
        exact mul_le_mul (le_max_left _ _) (hpow jm lm hmj) (Real.rpow_nonneg hbase.le _) ((abs_nonneg _).trans (le_max_left _ _))
  · calc
      _ ≤ |tSolution (orbitCoefficient k q (phi k q-a)) lp| *growthBase k ^ (-goodExponent*((lp:ℝ)-(jp:ℝ))) :=
        hlp.t_earlier hM jp (by have :=hp.1; omega) hpj
      _ ≤ matchedScale k q a lm lp*growthBase k ^ (-goodExponent) := by
        exact mul_le_mul (le_max_right _ _) (hpow jp lp hpj) (Real.rpow_nonneg hbase.le _) ((abs_nonneg _).trans (le_max_left _ _))

lemma pattern_decay (k q η η' : ℝ) (jm jp : ℕ → ℕ) (r : ℕ) (F : Set ℝ)
    (hr : 1 ≤ r) (hM : 1 < growthBase k) (hη : 0 ≤ η)
    (hsmall : growthBase k ^ (-goodExponent)/5 < η')
    (hF : F ⊆ Icc 0 1)
    (hgood : ∀ a ∈ F, ∀ i, i < r → CommonGood k q a (jm i) (jp i))
    (hmono : ∀ i, i+1 < r → jm i < jm (i+1) ∧ jp i < jp (i+1))
    (hscarce : ∀ i, i < r → ∀ b ∈ F,
      volume {x : ℝ | ∃ y ∈ localSuccessfulSet k q b (jm i) (jp i), dist x y < η'} ≤ ENNReal.ofReal η) :
    volume F ≤ ENNReal.ofReal (5*η)^(r-1)*3 := by
  let L := fun i a => matchedScale k q a (jm i) (jp i)
  let radius := fun i a => 1/(10*L i a)
  let V := fun i => ⋃ a ∈ F, ball a (radius i a)
  have hL (i : ℕ) (hi : i < r) (a : ℝ) (ha : a ∈ F) : 1 ≤ L i a :=
    (hgood a ha i hi).scale_ge_one hM
  have hrad (i : ℕ) (hi : i < r) (a : ℝ) (ha : a ∈ F) : 0 < radius i a ∧ radius i a ≤ 1/10 := by
    have hh:=hL i hi a ha
    dsimp [radius]
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < 10*L i a)).mpr
      linarith
  have hVF (i : ℕ) (hi : i < r) : F ⊆ V i := by
    intro a ha
    exact mem_iUnion₂.mpr ⟨a,ha,mem_ball_self (hrad i hi a ha).1⟩
  have hstep (i : ℕ) (hi : i+1 < r) : volume (V (i+1)) ≤ ENNReal.ofReal (5*η)*volume (V i) := by
    apply covering_contraction_of_distance volume F (radius i) (radius (i+1)) (1/10)
      (ENNReal.ofReal (5*η)) (hrad i (by omega))
    have hrec (a : ℝ) (ha : a ∈ F) : radius (i+1) a ≤ growthBase k ^ (-goodExponent)/(10*L i a) := by
      have hh := (hgood a ha i (by omega)).scale_mono_factor (hgood a ha (i+1) hi)
        (hmono i hi).1 (hmono i hi).2 hM
      have hpos : 0 < L i a := lt_of_lt_of_le zero_lt_one (hL i (by omega) a ha)
      have hpos' : 0 < L (i+1) a := lt_of_lt_of_le zero_lt_one (hL (i+1) hi a ha)
      dsimp [radius]
      apply (div_le_div_iff₀ (by positivity : 0 < 10*L (i+1) a) (by positivity : 0 < 10*L i a)).mpr
      dsimp [L] at *
      nlinarith
    have hh:=local_group_scarcity k q (jm i) (jp i) F (radius (i+1)) η η'
      (growthBase k ^ (-goodExponent)) hM hη (Real.rpow_nonneg (by linarith : 0 ≤ growthBase k) _) hsmall
      (fun a ha => hgood a ha i (by omega)) hrec (hscarce i (by omega))
    simpa only [radius,L,mul_one_div] using hh
  have hV0 : volume (V 0) ≤ 3 := by
    calc
      _ ≤ volume (Ioo (-1:ℝ) 2) := measure_mono (by
        intro x hx
        obtain ⟨a,ha,hx⟩:=mem_iUnion₂.mp hx
        have hh:=mem_ball.mp hx
        rw [Real.dist_eq] at hh
        have ha':=hF ha
        change 0 ≤ a ∧ a ≤ 1 at ha'
        have hh':=abs_lt.mp (hh.trans_le (hrad 0 (by omega) a ha).2)
        exact ⟨by linarith,by linarith⟩)
      _ = 3 := by norm_num
  have hbound (i : ℕ) (hi : i < r) : volume (V i) ≤ ENNReal.ofReal (5*η)^i*3 := by
    induction i with
    | zero => simpa using hV0
    | succ i ih =>
      calc
        _ ≤ ENNReal.ofReal (5*η)*volume (V i) := hstep i hi
        _ ≤ ENNReal.ofReal (5*η)*(ENNReal.ofReal (5*η)^i*3) := by gcongr; exact ih (by omega)
        _ = _ := by rw [pow_succ]; ring
  exact (measure_mono (hVF (r-1) (by omega))).trans (hbound (r-1) (by omega))
end StandardMapEntropy

end OAI
