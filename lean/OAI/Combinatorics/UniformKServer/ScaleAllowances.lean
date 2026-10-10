import Mathlib
import OAI.Combinatorics.UniformKServer.PartitionScales
import OAI.Combinatorics.UniformKServer.LevelAllowances

namespace OAI

noncomputable section

/-! Height-free sum of the designated-mover auxiliary errors. -/
namespace UniformKServer.PartitionScales.Input
open Finset GeometricMass
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N J : ℕ}

def editCoefficient (I : Input X N J) : ℝ :=
  198/I.P.gammaH+1/Real.log (1+I.P.deltaH)+(8*I.C+24)

theorem small_sum (I : Input X N J) (n : Fin N) (p : X) :
    (∑ j∈range J,(I.level j).smallError n p)≤(2/I.P.gammaH)*dist (I.center n) p := by
  let d := dist (I.center n) p
  have hd : 0≤ d := dist_nonneg
  have hγ := I.P.gammaH_pos
  have hc := SmallScales.small (I.R*I.q) I.q (d/I.P.gammaH) (mul_pos I.R_pos I.q_pos).le I.q_pos.le
    (by linarith [I.q_small]) (div_nonneg hd hγ.le) J
  have he (j : ℕ) : (I.level j).r=(I.R*I.q)*I.q^j := by dsimp [level,radius]; rw [pow_succ]; ring
  have hbound (j : ℕ) : (I.level j).smallError n p≤
      (if (I.R*I.q)*I.q^j≤d/I.P.gammaH then (I.R*I.q)*I.q^j else 0) := by
    unfold PartitionLevel.Input.smallError
    change (if I.P.gammaH*(I.level j).r<d then (I.level j).r else 0)≤_
    rw [he]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exfalso
      apply h2
      exact (le_div_iff₀ hγ).mpr (by linarith only [h1])
    · exact (mul_nonneg (mul_pos I.R_pos I.q_pos).le (pow_nonneg I.q_pos.le _))
    · exact le_rfl
  calc
    _≤∑ j∈range J,if (I.R*I.q)*I.q^j≤d/I.P.gammaH then (I.R*I.q)*I.q^j else 0 := sum_le_sum (fun j _=>hbound j)
    _≤(d/I.P.gammaH)/(1-I.q) := hc
    _≤(2/I.P.gammaH)*d := by
      apply (div_le_iff₀ (by linarith [I.q_small] : 0<1-I.q)).mpr
      have hz : 0≤d/I.P.gammaH := div_nonneg hd hγ.le
      have heq : (2/I.P.gammaH)*d*(1-I.q)=2*(d/I.P.gammaH)*(1-I.q) := by ring
      rw [heq]
      nlinarith [I.q_small]

theorem nonheavy_motion_sum (I : Input X N J) (n : Fin N) (p : X) :
    (∑ j∈range J,(I.level j).nonheavyMotion n p)≤
      (Real.log I.k/Real.log (1+I.P.deltaH))*dist (I.center n) p := by
  have he (j : ℕ) : (I.level j).nonheavyMotion n p=
      (if I.isNonheavy n j then (1:ℝ) else 0)*dist (I.center n) p := by
    unfold PartitionLevel.Input.nonheavyMotion
    by_cases hh : (I.level j).data.heavy n
    · simp only [hh,ite_true,ite_eq_right (fun hn=>((I.not_heavy n j).mp hn) hh),zero_mul]
    · rw [ite_eq_right hh,ite_eq_left ((I.not_heavy n j).mpr hh),one_mul]
      rfl
  simp_rw [he]
  rw [←sum_mul,←sum_filter]
  simp only [sum_const,nsmul_eq_mul,mul_one]
  exact mul_le_mul_of_nonneg_right (I.nonheavy_count n) dist_nonneg

theorem mover_allowance_sum (I : Input X N J) (n : Fin N) (p : X) :
    (∑ j∈range J,(I.level j).data.moverAllowance (I.level j).order I.P.gammaH n p)≤
      49*(∑ j∈range J,(I.level j).charges n)+I.editCoefficient*(1+Real.log I.k)*dist (I.center n) p := by
  have hb := sum_le_sum (s:=range J) (fun j _=>(I.level j).mover_allowance n p)
  have he : (∑ j∈range J,(49*(I.level j).charges n+99*(I.level j).smallError n p+
      (I.level j).nonheavyMotion n p+(8*(I.level j).C+24)*(I.level j).localLog n*dist ((I.level j).center n) p))=
      49*(∑ j∈range J,(I.level j).charges n)+99*(∑ j∈range J,(I.level j).smallError n p)+
      (∑ j∈range J,(I.level j).nonheavyMotion n p)+(8*I.C+24)*(∑ j∈range J,(I.level j).localLog n)*dist (I.center n) p := by
    simp only [sum_add_distrib,←mul_sum,←sum_mul,level]
  rw [he] at hb
  have hs := mul_le_mul_of_nonneg_left (I.small_sum n p) (by norm_num : (0:ℝ)≤99)
  have hn := I.nonheavy_motion_sum n p
  have hl := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (I.log_sum n)
    (show 0≤8*I.C+24 by linarith [I.C_one])) (dist_nonneg (x:=I.center n) (y:=p))
  have hlog : 0≤Real.log I.k := Real.log_nonneg (by exact_mod_cast (show 1≤I.k by have := I.two; omega))
  have hdelta : 0<Real.log (1+I.P.deltaH) := Real.log_pos (by linarith [I.P.deltaH_pos])
  have hγ := I.P.gammaH_pos
  have hd : 0≤dist (I.center n) p := dist_nonneg
  have hC : 0≤8*I.C+24 := by linarith [I.C_one]
  have hec : (198/I.P.gammaH+1/Real.log (1+I.P.deltaH)+(8*I.C+24))*(1+Real.log I.k)*dist (I.center n) p-
      (99*((2/I.P.gammaH)*dist (I.center n) p)+(Real.log I.k/Real.log (1+I.P.deltaH))*dist (I.center n) p+
      (8*I.C+24)*Real.log I.k*dist (I.center n) p)=
      ((198/I.P.gammaH)*Real.log I.k+1/Real.log (1+I.P.deltaH)+(8*I.C+24))*dist (I.center n) p := by ring
  have hp : 0≤((198/I.P.gammaH)*Real.log I.k+1/Real.log (1+I.P.deltaH)+(8*I.C+24))*dist (I.center n) p := by positivity
  change (∑ j∈range J,(I.level j).data.moverAllowance (I.level j).order I.P.gammaH n p)≤_ at hb
  unfold editCoefficient
  linarith only [hb,hs,hn,hl,hec,hp]

end UniformKServer.PartitionScales.Input

end

end OAI
