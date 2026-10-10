import Mathlib
import OAI.Probability.BinarySweep.Representations.FiniteUnitaryAverage

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma realAverage_uniform_commute (ρ : Representation ℂ G V) {p : G → ℝ}
    (hp : IsProbability p) (v : V) :
    complexAverage ρ (fun g => (p g:ℂ))
        (complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v)=
      complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v ∧
    complexAverage ρ (fun g => (uniformLaw G g:ℂ))
        (complexAverage ρ (fun g => (p g:ℂ)) v)=
      complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v := by
  constructor
  · rw [complexAverage_apply]
    simp only [complexAverage_uniform_left,←Finset.sum_smul,←Complex.ofReal_sum,hp.2,
      Complex.ofReal_one,one_smul]
  · rw [complexAverage_apply ρ (fun g => (p g:ℂ)),map_sum]
    simp only [map_smul,complexAverage_uniform_right,←Finset.sum_smul,←Complex.ofReal_sum,
      hp.2,Complex.ofReal_one,one_smul]

lemma realAverage_TV_bound (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) (p q : G → ℝ) (v : V) :
    ‖complexAverage ρ (fun g => (p g:ℂ)) v-
      complexAverage ρ (fun g => (q g:ℂ)) v‖ ≤ 2*totalVariation p q*‖v‖ := by
  have he : ∑g, ‖((p g:ℂ)-(q g:ℂ))‖=2*totalVariation p q := by
    simp only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,totalVariation]
    ring
  simpa only [complexAverage_sub,sub_apply,he] using
    complexAverage_norm_apply ρ hρ (fun g => (p g:ℂ)-(q g:ℂ)) v

omit [FiniteDimensional ℂ V] in
lemma contraction_power_drift (B : V →L[ℂ] V) (hB : ∀v, ‖B v‖ ≤ ‖v‖) (n : ℕ) (v : V) :
    ‖v-(B^n) v‖ ≤ n*‖v-B v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : v-(B^(n+1)) v=(v-B v)+B (v-(B^n) v) := by
      rw [pow_succ',mul_apply_eq_comp,map_sub]
      abel
    rw [he,Nat.cast_add,Nat.cast_one,add_mul]
    calc
      _ ≤ ‖v-B v‖ + ‖B (v-(B^n) v)‖ := norm_add_le _ _
      _ ≤ ‖v-B v‖ + n*‖v-B v‖ := by linarith [hB (v-(B^n) v)]
      _ = _ := by ring

theorem finite_average_gap (ρ : Representation ℂ G V)
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) {p : G → ℝ} (hp : IsProbability p)
    (hp1 : 0 < p 1) {L : ℕ} (hL : 0<L)
    (hTV : totalVariation (convolutionPower p L) (uniformLaw G) ≤ 1/4)
    (v : V) (hv : complexAverage ρ (fun g => (uniformLaw G g:ℂ)) v=0) :
    ‖complexAverage ρ (fun g => (p g:ℂ)) v‖^2 ≤
      (1-p 1/(4*(L:ℝ)^2))*‖v‖^2 := by
  let B := complexAverage ρ (fun g => (p g:ℂ))
  have hLp : (0:ℝ)<L := by exact_mod_cast hL
  have hpow : ‖(B^L) v‖ ≤ ‖v‖/2 := by
    have ht := realAverage_TV_bound ρ hρ (convolutionPower p L) (uniformLaw G) v
    rw [complexAverage_power,hv,sub_zero] at ht
    calc _ ≤ 2*totalVariation (convolutionPower p L) (uniformLaw G)*‖v‖ := ht
         _ ≤ ‖v‖/2 := by nlinarith [mul_le_mul_of_nonneg_right hTV (norm_nonneg v)]
  have hd := contraction_power_drift B (realAverage_contraction ρ hρ hp) L v
  have hn : ‖v‖ ≤ ‖v-(B^L) v‖+‖(B^L) v‖ := by simpa only [add_comm] using norm_le_insert' v ((B^L) v)
  have hc : ‖v‖/2 ≤ (L:ℝ)*‖v-B v‖ := by linarith
  have hcs : ‖v‖^2 ≤ 4*(L:ℝ)^2*‖v-B v‖^2 := by
    have hs := mul_self_le_mul_self (by positivity : 0≤‖v‖/2) hc
    nlinarith
  have hdef := realAverage_identity_defect ρ hρ hp v
  change p 1*‖v-B v‖^2 ≤ ‖v‖^2-‖B v‖^2 at hdef
  have hscale : p 1/(4*(L:ℝ)^2)*‖v‖^2 ≤ p 1*‖v-B v‖^2 := by
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hcs hp1.le]
  change ‖B v‖^2 ≤ _
  nlinarith

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {G V : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem finite_average_disk {p : G → ℝ} (hp : IsProbability p)
    (hp1 : 0<p 1) {L : ℕ} (hL : 0<L)
    (hTV : totalVariation (convolutionPower p L) (uniformLaw G) ≤ 1/4) :
    ∃ R : ℝ, 1<R ∧ ∀ (V : Type*) [NormedAddCommGroup V]
      [InnerProductSpace ℂ V] [FiniteDimensional ℂ V], ∀ (ρ : Representation ℂ G V),
      (∀g v, ‖ρ g v‖=‖v‖) → ∀z : ℂ, ‖z‖ ≤ R →
      ‖complexAverage ρ (fun g => (uniformLaw G g:ℂ))+
        z • (complexAverage ρ (fun g => (p g:ℂ))-
          complexAverage ρ (fun g => (uniformLaw G g:ℂ)))‖ ≤ 1 := by
  let c : ℝ := p 1/(4*(L:ℝ)^2)
  have hLp : (0:ℝ)<L := by exact_mod_cast hL
  have hL1 : (1:ℝ)≤L := by exact_mod_cast hL
  have hp1le : p 1≤1 := by
    rw [←hp.2]
    exact Finset.single_le_sum (fun g _ => hp.1 g) (Finset.mem_univ 1)
  have hc : 0<c := by dsimp [c]; positivity
  have hc1 : c≤1 := by
    dsimp [c]
    rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg ((L:ℝ)-1)]
  let R : ℝ := 1+c/4
  have hR : 1<R := by dsimp [R]; linarith
  have hRq : R^2*(1-c) ≤ 1 := by
    dsimp [R]
    nlinarith [sq_nonneg c,mul_nonneg hc.le (sq_nonneg c)]
  refine ⟨R,hR,?_⟩
  intro V _ _ _ ρ hρ z hz
  let P := complexAverage ρ (fun g => (uniformLaw G g:ℂ))
  let B := complexAverage ρ (fun g => (p g:ℂ))
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [one_mul]
  let u := P v
  let w := v-u
  have hPw : P w=0 := by
    change P (v-P v)=0
    rw [map_sub,complexAverage_uniform_idem,sub_self]
  have hPBw : P (B w)=0 := by
    rw [(realAverage_uniform_commute ρ hp w).2,hPw]
  have hiw : inner ℂ u w=0 := by
    change inner ℂ (P v) w=0
    rw [complexAverage_uniform_inner ρ hρ,hPw,inner_zero_right]
  have hiB : inner ℂ u (B w)=0 := by
    change inner ℂ (P v) (B w)=0
    rw [complexAverage_uniform_inner ρ hρ,hPBw,inner_zero_right]
  have hvsplit : v=u+w := by dsimp [w]; abel
  have hvsq : ‖v‖^2=‖u‖^2+‖w‖^2 := by
    calc ‖v‖^2=‖u+w‖^2 := congrArg (fun x : V => ‖x‖^2) hvsplit
         _ = _ := by simpa only [pow_two] using
           norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u w hiw
  have hB : ‖B w‖^2 ≤ (1-c)*‖w‖^2 := finite_average_gap ρ hρ hp hp1 hL hTV w hPw
  have he : (P+z • (B-P)) v=u+z • B w := by
    simp only [add_apply,smul_apply,sub_apply]
    have hu : B u=u := (realAverage_uniform_commute ρ hp v).1
    have hb : B v=B u+B w := by rw [←map_add,←hvsplit]
    rw [hb,hu,show P v=u from rfl]
    abel_nf
  change ‖(P+z • (B-P)) v‖ ≤ ‖v‖
  rw [he]
  have hs : ‖u+z • B w‖^2=‖u‖^2+‖z‖^2*‖B w‖^2 := by
    have hi : inner ℂ u (z • B w)=0 := by rw [inner_smul_right,hiB,mul_zero]
    have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u (z • B w) hi
    simpa only [←pow_two,norm_smul,mul_pow] using hh
  have hzq : ‖z‖^2 ≤ R^2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have htot : ‖z‖^2*‖B w‖^2 ≤ ‖w‖^2 := by
    calc _ ≤ R^2*‖B w‖^2 := mul_le_mul_of_nonneg_right hzq (sq_nonneg _)
         _ ≤ R^2*((1-c)*‖w‖^2) := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
         _ ≤ ‖w‖^2 := by nlinarith [mul_le_mul_of_nonneg_right hRq (sq_nonneg ‖w‖)]
  nlinarith [norm_nonneg (u+z • B w),norm_nonneg v]

end BinaryCoordinateSweeps

end

end OAI
