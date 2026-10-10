import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.NaturalPolynomial
import OAI.Analysis.MatrixSigning.Optimization.Transition
import OAI.Analysis.MatrixSigning.Optimization.UpperIndex
import OAI.Analysis.MatrixSigning.Potential.PenaltyParameter

namespace OAI

namespace CurrentKS.Schedule

section
open KS.W23
open scoped BigOperators

def X : NaturalPolynomial := .variable

def coarseP : NaturalPolynomial :=
  200+(X+1)+1+200*X^4*(X+1)+200*(X+1)+((X+1)+X)+
    384*X*(1+800*(40000*X^2)^3)
def jacobianP : NaturalPolynomial := 10^18*(X+1)*(1+X^4)^4
def derivativeP : NaturalPolynomial := 300*coarseP^5
def secondP : NaturalPolynomial := (1+2*(X+1))*(jacobianP*derivativeP*(1+jacobianP*derivativeP)^2)
def thirdP : NaturalPolynomial := (1+2*(X+1))*(jacobianP*derivativeP*
    ((1+jacobianP*derivativeP)^3+3*(1+jacobianP*derivativeP)*(jacobianP*derivativeP*(1+jacobianP*derivativeP)^2)))
def curvatureP : NaturalPolynomial :=
  1+secondP+thirdP+X*(1+800*(40000*X^2)^3)
def movementP : NaturalPolynomial :=
  1+48*(2*(1+(3*X)^2*(40000*X^4))^2*(1+3*X)^2)+4*(1+9*X^2)
def thresholdInvP : NaturalPolynomial := 512*movementP^2*(200*X^4)
def stepInvP : NaturalPolynomial := 4*(40000*X^2)+4*curvatureP*thresholdInvP+4
def dropInvP : NaturalPolynomial := 1+thresholdInvP*stepInvP^2
def iterationP : NaturalPolynomial := 100*dropInvP+1

lemma coarseBudget_polynomial {d n B : ℕ} (hd : d≤B) (hn : n≤B)
    {ε σ : ℚ} (hε : 0<ε) (hε1 : ε≤1) (hσ : 0<σ)
    (hei : ε⁻¹≤(B:ℚ)^4) (hsi : σ⁻¹≤40000*(B:ℚ)^2) :
    coarseBudgetQ d n ε σ ≤ (coarseP.eval B:ℚ) := by
  have hd' : (d:ℚ)≤B := by exact_mod_cast hd
  have hn' : (n:ℚ)≤B := by exact_mod_cast hn
  unfold coarseBudgetQ coarseP X
  simp only [NaturalPolynomial.eval_power,NaturalPolynomial.eval,
    Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,abs_of_pos hε,
    div_eq_mul_inv,←inv_pow]
  gcongr

lemma jacobian_polynomial {d B : ℕ} (hd : d≤B) {ε : ℚ} (hε : 0<ε)
    (hei : ε⁻¹≤(B:ℚ)^4) :
    10^18*((d:ℚ)+1)*(1+ε⁻¹)^4 ≤ (jacobianP.eval B:ℚ) := by
  have hd' : (d:ℚ)≤B := by exact_mod_cast hd
  unfold jacobianP X
  simp only [NaturalPolynomial.eval_power,NaturalPolynomial.eval,
    Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  gcongr

lemma derivative_polynomial {d n B : ℕ} (hd : d≤B) (hn : n≤B)
    {ε σ : ℚ} (hε : 0<ε) (hε1 : ε≤1) (hσ : 0<σ)
    (hei : ε⁻¹≤(B:ℚ)^4) (hsi : σ⁻¹≤40000*(B:ℚ)^2) :
    300*coarseBudgetQ d n ε σ^5 ≤ (derivativeP.eval B:ℚ) := by
  have hc := coarseBudget_polynomial hd hn hε hε1 hσ hei hsi
  have hc0 : 0≤coarseBudgetQ d n ε σ := by unfold coarseBudgetQ;positivity
  change 300*coarseBudgetQ d n ε σ^5 ≤ ((300*(coarseP.eval B)^5:ℕ):ℚ)
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  gcongr

lemma secondP_eval (B:ℕ) : (secondP.eval B:ℚ)=
    (1+2*((B:ℚ)+1))*((jacobianP.eval B:ℚ)*(derivativeP.eval B:ℚ)*
       (1+(jacobianP.eval B:ℚ)*(derivativeP.eval B:ℚ))^2) := by
  change (((1+2*(B+1))*(jacobianP.eval B*derivativeP.eval B*
       (1+jacobianP.eval B*derivativeP.eval B)^2):ℕ):ℚ)=_
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat]

lemma thirdP_eval (B:ℕ) : (thirdP.eval B:ℚ)=
    (1+2*((B:ℚ)+1))*((jacobianP.eval B:ℚ)*(derivativeP.eval B:ℚ)*
       ((1+(jacobianP.eval B:ℚ)*(derivativeP.eval B:ℚ))^3+
         3*(1+(jacobianP.eval B:ℚ)*(derivativeP.eval B:ℚ))*
         ((jacobianP.eval B:ℚ)*(derivativeP.eval B:ℚ)*
          (1+(jacobianP.eval B:ℚ)*(derivativeP.eval B:ℚ))^2))) := by
  change (((1+2*(B+1))*(jacobianP.eval B*derivativeP.eval B*
       ((1+jacobianP.eval B*derivativeP.eval B)^3+
         3*(1+jacobianP.eval B*derivativeP.eval B)*
         (jacobianP.eval B*derivativeP.eval B*
          (1+jacobianP.eval B*derivativeP.eval B)^2))):ℕ):ℚ)=_
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat]

lemma outer_polynomial {d B:ℕ} (hd:d≤B) {ε:ℚ} (hε:0<ε) (hε1:ε≤1):
    1+|ε| *(2*((d:ℚ)+1)) ≤ 1+2*((B:ℚ)+1) := by
  have hd' : (d:ℚ)≤B := by exact_mod_cast hd
  rw [abs_of_pos hε]
  have hh := mul_le_mul_of_nonneg_right hε1 (show (0:ℚ)≤2*((d:ℚ)+1) by positivity)
  nlinarith

private lemma curve2_mono {o O j J q Q : ℚ}
    (ho: o≤O) (hj:j≤J) (hq:q≤Q) (ho0:0≤o) (hj0:0≤j) (hq0:0≤q) :
    o*(j*q*(1+j*q)^2) ≤ O*(J*Q*(1+J*Q)^2) := by
  have hO : 0≤O := ho0.trans ho
  have hJ : 0≤J := hj0.trans hj
  have hQ : 0≤Q := hq0.trans hq
  gcongr

private lemma curve3_mono {o O j J q Q : ℚ}
    (ho: o≤O) (hj:j≤J) (hq:q≤Q) (ho0:0≤o) (hj0:0≤j) (hq0:0≤q) :
    o*(j*q*((1+j*q)^3+3*(1+j*q)*(j*q*(1+j*q)^2))) ≤
    O*(J*Q*((1+J*Q)^3+3*(1+J*Q)*(J*Q*(1+J*Q)^2))) := by
  have hO : 0≤O := ho0.trans ho
  have hJ : 0≤J := hj0.trans hj
  have hQ : 0≤Q := hq0.trans hq
  gcongr

lemma valueCurve2_polynomial {d n B : ℕ} (hd : d≤B) (hn : n≤B)
    {ε σ : ℚ} (hε : 0<ε) (hε1 : ε≤1) (hσ : 0<σ)
    (hei : ε⁻¹≤(B:ℚ)^4) (hsi : σ⁻¹≤40000*(B:ℚ)^2) :
    valueCurve2Q d n ε σ ≤ (secondP.eval B:ℚ) := by
  have hj := jacobian_polynomial hd hε hei
  have hD := derivative_polynomial hd hn hε hε1 hσ hei hsi
  have hc0 : 0≤coarseBudgetQ d n ε σ := by unfold coarseBudgetQ;positivity
  have houter := outer_polynomial hd hε hε1
  rw [secondP_eval]
  unfold valueCurve2Q
  dsimp only
  exact curve2_mono houter hj hD (by positivity) (by positivity) (by positivity)

lemma valueCurve3_polynomial {d n B : ℕ} (hd : d≤B) (hn : n≤B)
    {ε σ : ℚ} (hε : 0<ε) (hε1 : ε≤1) (hσ : 0<σ)
    (hei : ε⁻¹≤(B:ℚ)^4) (hsi : σ⁻¹≤40000*(B:ℚ)^2) :
    valueCurve3Q d n ε σ ≤ (thirdP.eval B:ℚ) := by
  have hj := jacobian_polynomial hd hε hei
  have hD := derivative_polynomial hd hn hε hε1 hσ hei hsi
  have hc0 : 0≤coarseBudgetQ d n ε σ := by unfold coarseBudgetQ;positivity
  have houter := outer_polynomial hd hε hε1
  rw [thirdP_eval]
  unfold valueCurve3Q
  dsimp only
  exact curve3_mono houter hj hD (by positivity) (by positivity) (by positivity)

lemma curvatureP_eval (B : ℕ) : (curvatureP.eval B:ℚ) =
    1+(secondP.eval B:ℚ)+(thirdP.eval B:ℚ)+(B:ℚ)*(1+800*(40000*(B:ℚ)^2)^3) := by
  change (((1+secondP.eval B+thirdP.eval B+B*(1+800*(40000*B^2)^3)):ℕ):ℚ)=_
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat]

lemma curveBudget_polynomial {d n B : ℕ} (hd : d≤B) (hn : n≤B)
    {ε σ lam : ℚ} (hε : 0<ε) (hε1 : ε≤1) (hσ : 0<σ)
    (hlam : 0<lam) (hlam1 : lam≤1)
    (hei : ε⁻¹≤(B:ℚ)^4) (hsi : σ⁻¹≤40000*(B:ℚ)^2) :
    curveBudget d n ε σ lam ≤ (curvatureP.eval B:ℚ) := by
  have hn' : (n:ℚ)≤B := by exact_mod_cast hn
  have hpen : |lam| *(n:ℚ)*(1+800/σ^3) ≤ (B:ℚ)*(1+800*(40000*(B:ℚ)^2)^3) := by
    rw [abs_of_pos hlam]
    simp only [div_eq_mul_inv,←inv_pow]
    calc
      _ ≤ 1*(B:ℚ)*(1+800*(40000*(B:ℚ)^2)^3) := by gcongr
      _ = _ := by rw [one_mul]
  have h2 := valueCurve2_polynomial hd hn hε hε1 hσ hei hsi
  have h3 := valueCurve3_polynomial hd hn hε hε1 hσ hei hsi
  rw [curvatureP_eval]
  unfold curveBudget
  exact add_le_add (add_le_add (add_le_add le_rfl h2) h3) hpen

lemma movementBudget_polynomial {n B : ℕ} (hn : n≤B)
    {ε : ℚ} (hε : 0<ε) (hei : ε⁻¹≤(B:ℚ)^4) :
    movementBudget n ε ≤ (movementP.eval B:ℚ) := by
  have hn' : (n:ℚ)≤B := by exact_mod_cast hn
  have hj : 1+(3*(n:ℚ))^2/(ε/40000) ≤ 1+(3*(B:ℚ))^2*(40000*(B:ℚ)^4) := by
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    gcongr
  have he : 2*(1+(3*(n:ℚ))^2/(ε/40000))^2*(1+3*(n:ℚ))^2 ≤
      2*(1+(3*(B:ℚ))^2*(40000*(B:ℚ)^4))^2*(1+3*(B:ℚ))^2 := by gcongr
  unfold movementBudget
  dsimp only
  have he0 : 0 ≤ 2*(1+(3*(n:ℚ))^2/(ε/40000))^2*(1+3*(n:ℚ))^2 := by positivity
  have hq : 4*(1+9*(n:ℚ)^2) ≤ 4*(1+9*(B:ℚ)^2) := by gcongr
  unfold movementP X
  simp only [NaturalPolynomial.eval_power,NaturalPolynomial.eval,
    Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  apply max_le
  · have hp : (0:ℚ) ≤ 48*(2*(1+(3*(B:ℚ))^2*(40000*(B:ℚ)^4))^2*(1+3*(B:ℚ))^2) := by positivity
    have hq0 : (0:ℚ) ≤ 4*(1+9*(B:ℚ)^2) := by positivity
    linarith
  · apply max_le
    · have hdiv := div_le_self (mul_nonneg (by norm_num : (0:ℚ)≤48) he0) (by norm_num : (1:ℚ)≤23)
      have hm := mul_le_mul_of_nonneg_left he (by norm_num : (0:ℚ)≤48)
      have hq0 : (0:ℚ) ≤ 4*(1+9*(B:ℚ)^2) := by positivity
      linarith
    · have he' : (0:ℚ)≤48*(2*(1+(3*(B:ℚ))^2*(40000*(B:ℚ)^4))^2*(1+3*(B:ℚ))^2) := by positivity
      linarith

end

open KS.W23

lemma thresholdInvP_eval (B : ℕ) : (thresholdInvP.eval B:ℚ)=
    512*(movementP.eval B:ℚ)^2*(200*(B:ℚ)^4) := by
  change ((512*(movementP.eval B)^2*(200*B^4):ℕ):ℚ)=_
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]

lemma threshold_inv_polynomial {n B:ℕ} (hn:n≤B) {ε lam:ℚ}
    (hε:0<ε) (hlam:0<lam) (hei:ε⁻¹≤(B:ℚ)^4) (hli:lam⁻¹≤200*(B:ℚ)^4) :
    (threshold n ε lam)⁻¹ ≤ (thresholdInvP.eval B:ℚ) := by
  have hb := movementBudget_polynomial hn hε hei
  have hp := (movementBudget_pos n ε).le
  rw [threshold,inv_div,div_eq_mul_inv,thresholdInvP_eval]
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hb 2) (by norm_num)
  · exact hli
  · exact (inv_pos.mpr hlam).le
  · positivity

lemma inv_min_le_sum {a b:ℚ} (ha:0<a) (hb:0<b) :
    (min a b)⁻¹ ≤ a⁻¹+b⁻¹ := by
  rcases le_total a b with h|h
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hb.le)
  · rw [min_eq_right h]
    exact le_add_of_nonneg_left (inv_nonneg.mpr ha.le)

lemma stepSize_inv_bound {a M σ:ℚ} (ha:0<a) (hM:0<M) (hσ:0<σ) :
    (stepSize a M σ)⁻¹ ≤ 4*σ⁻¹+4*M*a⁻¹+4 := by
  have h1 := inv_min_le_sum (div_pos hσ (by norm_num : (0:ℚ)<4))
    (lt_min (div_pos ha (mul_pos (by norm_num : (0:ℚ)<4) hM)) (by norm_num : (0:ℚ)<1/4))
  have h2 := inv_min_le_sum (div_pos ha (mul_pos (by norm_num : (0:ℚ)<4) hM)) (by norm_num : (0:ℚ)<1/4)
  have hh := h1.trans (add_le_add le_rfl h2)
  unfold stepSize
  convert hh using 1
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

lemma stepInvP_eval (B:ℕ) : (stepInvP.eval B:ℚ)=
    4*(40000*(B:ℚ)^2)+4*(curvatureP.eval B:ℚ)*(thresholdInvP.eval B:ℚ)+4 := by
  change ((4*(40000*B^2)+4*curvatureP.eval B*thresholdInvP.eval B+4:ℕ):ℚ)=_
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]

lemma dropInvP_eval (B:ℕ) : (dropInvP.eval B:ℚ)=
    1+(thresholdInvP.eval B:ℚ)*(stepInvP.eval B:ℚ)^2 := by
  change ((1+thresholdInvP.eval B*(stepInvP.eval B)^2:ℕ):ℚ)=_
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one]

lemma dropInvP_one (B:ℕ) : (1:ℚ)≤(dropInvP.eval B:ℚ) := by
  rw [dropInvP_eval]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

lemma step_inv_polynomial {d n B:ℕ} (hd:d≤B) (hn:n≤B)
    {ε σ lam:ℚ} (hε:0<ε) (hε1:ε≤1) (hσ:0<σ) (hlam:0<lam) (hlam1:lam≤1)
    (hei:ε⁻¹≤(B:ℚ)^4) (hsi:σ⁻¹≤40000*(B:ℚ)^2) (hli:lam⁻¹≤200*(B:ℚ)^4) :
    (stepSize (threshold n ε lam) (curveBudget d n ε σ lam) σ)⁻¹ ≤ (stepInvP.eval B:ℚ) := by
  have ha := threshold_pos n ε hlam
  have hM := (show (0:ℚ)<1 by norm_num).trans_le (curveBudget_one_le d n hε hσ lam)
  have hh := stepSize_inv_bound ha hM hσ
  have hm := curveBudget_polynomial hd hn hε hε1 hσ hlam hlam1 hei hsi
  have ht := threshold_inv_polynomial hn hε hlam hei hli
  rw [stepInvP_eval]
  apply hh.trans
  apply add_le_add _ le_rfl
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left hsi (by norm_num)
  · exact mul_le_mul (mul_le_mul_of_nonneg_left hm (by norm_num)) ht
      (inv_nonneg.mpr ha.le) (by positivity)

lemma drop_inv_polynomial {d n B:ℕ} (hd:d≤B) (hn:n≤B)
    {ε σ lam:ℚ} (hε:0<ε) (hε1:ε≤1) (hσ:0<σ) (hlam:0<lam) (hlam1:lam≤1)
    (hei:ε⁻¹≤(B:ℚ)^4) (hsi:σ⁻¹≤40000*(B:ℚ)^2) (hli:lam⁻¹≤200*(B:ℚ)^4) :
    (threshold n ε lam*(stepSize (threshold n ε lam) (curveBudget d n ε σ lam) σ)^2)⁻¹ ≤
      (dropInvP.eval B:ℚ) := by
  have ht := threshold_inv_polynomial hn hε hlam hei hli
  have hs := step_inv_polynomial hd hn hε hε1 hσ hlam hlam1 hei hsi hli
  have ha := threshold_pos n ε hlam
  have hM := (show (0:ℚ)<1 by norm_num).trans_le (curveBudget_one_le d n hε hσ lam)
  have hsp := (stepSize_spec ha hM hσ).1
  rw [mul_inv_rev,←inv_pow,mul_comm,dropInvP_eval]
  apply le_trans _ (le_add_of_nonneg_left (by norm_num : (0:ℚ)≤1))
  exact mul_le_mul ht (pow_le_pow_left₀ (inv_nonneg.mpr hsp.le) hs 2)
    (sq_nonneg _) (Nat.cast_nonneg _)

end CurrentKS.Schedule

namespace CurrentKS.Descent
lemma minList_inv_le {K:ℚ} (hK:1≤K) (l:List ℚ) (hl:∀a∈l,a⁻¹≤K) :
    (minList l)⁻¹≤K := by
  induction l with
  | nil => simpa only [minList,inv_one] using hK
  | cons a l ih =>
    rw [minList]
    rcases le_total a (minList l) with h|h
    · rw [min_eq_left h]
      exact hl a (by simp)
    · rw [min_eq_right h]
      exact ih (fun a ha => hl a (by simp [ha]))
end CurrentKS.Descent

namespace CurrentKS.Schedule
noncomputable section
open CurrentKS.RationalSDP CurrentKS.Hermitian CurrentKS.State
open scoped BigOperators

variable {d N : ℕ}

theorem normalized_parameter_bounds [NeZero d] [NeZero N]
    (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1) :
    let ν := varianceQuery coords
    let lam := penaltyParameter N ν
    ν⁻¹ ≤ (N:ℚ)*d^2 ∧ (ν/(d:ℚ))⁻¹ ≤ (N:ℚ)*d^3 ∧
      lam⁻¹ ≤ 200*(N:ℚ)^2*d^2 ∧ (lam^2/ν)⁻¹ ≤ 40000*(N:ℚ)^2 := by
  let ν := varianceQuery coords
  let lam := penaltyParameter N ν
  have hν := varianceQuery_spec coords hA hrank htr
  have hd : (0:ℚ) < d := by exact_mod_cast NeZero.pos d
  have hN : (0:ℚ) < N := by exact_mod_cast NeZero.pos N
  have hlo := variance_lower_paper (rationalAtoms coords) hA hrank htr
  have hlo' : 1/((N:ℚ)*d^2) ≤ ν := by
    apply (Rat.cast_le (K:=ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_natCast,Rat.cast_pow]
      using hlo.trans hν.2.2.1
  have hvi : ν⁻¹ ≤ (N:ℚ)*d^2 := by
    apply (inv_le_comm₀ hν.1 (by positivity)).mpr
    simpa only [inv_eq_one_div] using hlo'
  have hei : (ν/(d:ℚ))⁻¹ ≤ (N:ℚ)*d^3 := by
    rw [inv_div]
    calc
      (d:ℚ)/ν = (d:ℚ)*ν⁻¹ := div_eq_mul_inv _ _
      _ ≤ (d:ℚ)*((N:ℚ)*d^2) := mul_le_mul_of_nonneg_left hvi hd.le
      _ = (N:ℚ)*d^3 := by ring
  have hp := penaltyParameter_pos_le (NeZero.pos N) hν.1 hν.2.1
  have hi := penaltyParameter_interval (NeZero.pos N) hν.1 hν.2.1
  have hνsqrt : (ν:ℝ) ≤ Real.sqrt (ν:ℝ) :=
    Real.le_sqrt_of_sq_le (by
      have ha : (0:ℝ) ≤ ν := by exact_mod_cast hν.1.le
      have hb : (ν:ℝ) ≤ 1 := by exact_mod_cast hν.2.1
      nlinarith)
  have hlamlo : ν/(200*(N:ℚ)) ≤ lam := by
    apply (Rat.cast_le (K:=ℝ)).mp
    have hN' : (0:ℝ) < N := by exact_mod_cast NeZero.pos N
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast] using
      (div_le_div_of_nonneg_right hνsqrt (by positivity : (0:ℝ)≤200*N)).trans hi.1
  have hli : lam⁻¹ ≤ 200*(N:ℚ)^2*d^2 := by
    calc
      lam⁻¹ ≤ (ν/(200*(N:ℚ)))⁻¹ := inv_anti₀ (div_pos hν.1 (mul_pos (by norm_num) hN)) hlamlo
      _ = 200*(N:ℚ)*ν⁻¹ := by rw [inv_div,div_eq_mul_inv]
      _ ≤ 200*(N:ℚ)*((N:ℚ)*d^2) := mul_le_mul_of_nonneg_left hvi (by positivity)
      _ = 200*(N:ℚ)^2*d^2 := by ring
  have hstrip := (penaltyParameter_strip (NeZero.pos N) hν.1 hν.2.1).1
  have hsi : (lam^2/ν)⁻¹ ≤ 40000*(N:ℚ)^2 := by
    calc
      (lam^2/ν)⁻¹ ≤ (1/(40000*(N:ℚ)^2))⁻¹ := inv_anti₀ (by positivity) hstrip
      _ = 40000*(N:ℚ)^2 := by rw [one_div,inv_inv]
  exact ⟨hvi,hei,hli,hsi⟩

end
end CurrentKS.Schedule

namespace CurrentKS.RationalFace
open CurrentKS.Schedule CurrentKS.Descent CurrentKS.RationalSDP
open CurrentKS.Hermitian CurrentKS.State KS.W23
open scoped BigOperators

variable {d N : ℕ}

lemma uniformDrop_inv_polynomial {B : ℕ} (hd : d≤B) (hN : N≤B)
    {ν lam : ℚ} (hε : 0<ν/(d:ℚ)) (hε1 : ν/(d:ℚ)≤1)
    (hσ : 0<lam^2/ν) (hlam : 0<lam) (hlam1 : lam≤1)
    (hei : (ν/(d:ℚ))⁻¹≤(B:ℚ)^4) (hsi : (lam^2/ν)⁻¹≤40000*(B:ℚ)^2)
    (hli : lam⁻¹≤200*(B:ℚ)^4) :
    (uniformDrop d N ν lam)⁻¹≤(dropInvP.eval B:ℚ) := by
  apply minList_inv_le (dropInvP_one B)
  intro q hq
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hq
  have hnN : n≤N := by have := List.mem_range.mp hn; omega
  exact drop_inv_polynomial hd (hnN.trans hN) hε hε1 hσ hlam hlam1 hei hsi hli

lemma fuel_polynomial {B:ℕ} {r:ℚ} (hr : r⁻¹≤(dropInvP.eval B:ℚ)) :
    fuel r ≤ iterationP.eval B := by
  change ⌈100/r⌉₊+1≤100*dropInvP.eval B+1
  apply Nat.add_le_add_right
  apply Nat.ceil_le.mpr
  rw [div_eq_mul_inv]
  exact_mod_cast mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℚ)≤100)

theorem normalized_fuel_polynomial [NeZero d] [NeZero N]
    (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank≤1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1) :
    fuel (uniformDrop d N (varianceQuery coords) (penaltyParameter N (varianceQuery coords))) ≤
      iterationP.eval (d+N) := by
  let ν := varianceQuery coords
  let lam := penaltyParameter N ν
  have hν := varianceQuery_spec coords hA hrank htr
  have hl := penaltyParameter_pos_le (NeZero.pos N) hν.1 hν.2.1
  have b := normalized_parameter_bounds coords hA hrank htr
  have hd : (0:ℚ)<d := by exact_mod_cast NeZero.pos d
  have hd1 : (1:ℚ)≤d := by exact_mod_cast NeZero.pos d
  have hdB : (d:ℚ)≤(d+N:ℕ) := by exact_mod_cast Nat.le_add_right d N
  have hNB : (N:ℚ)≤(d+N:ℕ) := by exact_mod_cast Nat.le_add_left N d
  have hε : 0<ν/(d:ℚ) := div_pos hν.1 hd
  have hε1 : ν/(d:ℚ)≤1 := (div_le_one hd).mpr (hν.2.1.trans hd1)
  have hσ : 0<lam^2/ν := div_pos (sq_pos_of_pos hl.1) hν.1
  have hei : (ν/(d:ℚ))⁻¹≤((d+N:ℕ):ℚ)^4 := by
    apply b.2.1.trans
    calc
      (N:ℚ)*d^3 ≤ ((d+N:ℕ):ℚ)*((d+N:ℕ):ℚ)^3 := by gcongr
      _ = ((d+N:ℕ):ℚ)^4 := by ring
  have hli : lam⁻¹≤200*((d+N:ℕ):ℚ)^4 := by
    apply b.2.2.1.trans
    calc
      200*(N:ℚ)^2*d^2 ≤ 200*((d+N:ℕ):ℚ)^2*((d+N:ℕ):ℚ)^2 := by gcongr
      _ = 200*((d+N:ℕ):ℚ)^4 := by ring
  have hsi : (lam^2/ν)⁻¹≤40000*((d+N:ℕ):ℚ)^2 := by
    apply b.2.2.2.trans
    gcongr
  exact fuel_polynomial (uniformDrop_inv_polynomial (Nat.le_add_right d N)
    (Nat.le_add_left N d) hε hε1 hσ hl.1 hl.2 hei hsi hli)

end CurrentKS.RationalFace

namespace CurrentKS.RationalSDP
variable {n d : ℕ}

lemma searchFuel_le {r R : ℚ} (hr : 0<r) (hR : 0≤R) {R₀ r₀ : ℕ}
    (hRb : R≤R₀) (hrb : r⁻¹≤r₀) :
    searchFuel n r R ≤ 4*R₀^2*(r₀*(n+1))^2+1 := by
  unfold searchFuel
  apply Nat.add_le_add_right
  apply Nat.ceil_le.mpr
  have hi : (searchStep n r)⁻¹ = r⁻¹*((n:ℚ)+1) := by
    simp only [searchStep,div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  rw [div_eq_mul_inv,←inv_pow,hi]
  push_cast
  gcongr

lemma optimizeFuel_le {δ : ℚ} {D : ℕ} (hδ : δ⁻¹≤D) :
    optimizeFuel δ 100 ≤ 200*D+3 := by
  unfold optimizeFuel
  apply Nat.add_le_add_right
  apply Nat.ceil_le.mpr
  rw [div_eq_mul_inv]
  push_cast
  nlinarith

def queryDimensionBound (B : ℕ) : ℕ := 1+2*B^2
def queryOuterBound (B : ℕ) : ℕ := (queryDimensionBound B+1)*(100+400*B*(B+1))
def queryLipschitzBound (B : ℕ) : ℕ := (queryDimensionBound B+1)*(1+2*B)
def queryInnerInvBound (B : ℕ) : ℕ := 4000*(B^2+1)
def queryNearInvBound (B : ℕ) : ℕ :=
  queryLipschitzBound B*(2*queryOuterBound B+1)*B*queryInnerInvBound B
def querySearchBound (B : ℕ) : ℕ :=
  4*(queryOuterBound B)^2*(queryNearInvBound B*(queryDimensionBound B+1))^2+1

def queryScanBound (B : ℕ) : ℕ := (200*B+4)*querySearchBound B

lemma valueDimension_le {B : ℕ} (hd : d≤B) : valueDimension d ≤ queryDimensionBound B := by
  unfold valueDimension queryDimensionBound
  have hh := Nat.mul_le_mul hd hd
  nlinarith

lemma valueOuterRadius_le_bound {B : ℕ} (hd : d≤B) {ε : ℚ} (he : 0<ε) (hei : ε⁻¹≤B) :
    valueOuterRadius d ε ≤ queryOuterBound B := by
  have hn : (valueDimension d:ℚ)≤queryDimensionBound B := by exact_mod_cast valueDimension_le hd
  have hd' : (d:ℚ)≤B := by exact_mod_cast hd
  unfold valueOuterRadius queryOuterBound
  push_cast
  simp only [div_eq_mul_inv]
  gcongr

lemma valueLipschitz_le_bound {B : ℕ} (hd : d≤B) {ε : ℚ} (he : 0≤ε) (he1 : ε≤1) :
    valueLipschitz d ε ≤ queryLipschitzBound B := by
  have hn : (valueDimension d:ℚ)≤queryDimensionBound B := by exact_mod_cast valueDimension_le hd
  have hd' : (d:ℚ)≤B := by exact_mod_cast hd
  unfold valueLipschitz queryLipschitzBound
  push_cast
  calc
    ((valueDimension d:ℚ)+1)*(1+2*ε*d) ≤
        ((queryDimensionBound B:ℚ)+1)*(1+2*1*B) := by gcongr
    _ = _ := by ring

lemma valueInnerRadius_inv_le_bound {B : ℕ} (hd : d≤B) :
    (valueInnerRadius d)⁻¹ ≤ queryInnerInvBound B := by
  have hd' : (d:ℚ)≤B := by exact_mod_cast hd
  unfold valueInnerRadius queryInnerInvBound
  simp only [one_div,inv_inv,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_pow,Nat.cast_one]
  gcongr

lemma valueNearRadius_inv_le_bound {B : ℕ} (hd : d≤B) {ε δ : ℚ}
    (he : 0<ε) (he1 : ε≤1) (hei : ε⁻¹≤B) (hδ : 0<δ) (hδi : δ⁻¹≤B) :
    (nearRadius δ (valueLipschitz d ε) (valueOuterRadius d ε) (valueInnerRadius d))⁻¹ ≤
      queryNearInvBound B := by
  have hL := valueLipschitz_le_bound hd he.le he1
  have hR := valueOuterRadius_le_bound hd he hei
  have hr := valueInnerRadius_inv_le_bound hd
  have hr1 := valueInnerRadius_le (d:=d)
  have hL0 := (valueLipschitz_pos (d:=d) he.le).le
  have hR0 := valueOuterRadius_nonneg (d:=d) he
  have hr0 := (valueInnerRadius_pos (d:=d)).le
  unfold nearRadius queryNearInvBound
  rw [mul_inv_rev,inv_div]
  simp only [div_eq_mul_inv]
  push_cast
  calc
    (valueInnerRadius d)⁻¹*(valueLipschitz d ε*(2*valueOuterRadius d ε+valueInnerRadius d)*δ⁻¹) ≤
      (queryInnerInvBound B:ℚ)*(queryLipschitzBound B*(2*queryOuterBound B+1)*B) := by gcongr
    _ = _ := by ring

theorem valueSearchFuel_le {B : ℕ} (hd : d≤B) {ε δ : ℚ}
    (he : 0<ε) (he1 : ε≤1) (hei : ε⁻¹≤B) (hδ : 0<δ) (hδi : δ⁻¹≤B) :
    searchFuel (valueDimension d)
      (nearRadius δ (valueLipschitz d ε) (valueOuterRadius d ε) (valueInnerRadius d))
      (valueOuterRadius d ε) ≤ querySearchBound B := by
  have hr := nearRadius_pos hδ (valueLipschitz_pos (d:=d) he.le)
    (valueOuterRadius_nonneg (d:=d) he) (valueInnerRadius_pos (d:=d))
  have h := searchFuel_le (n:=valueDimension d) hr (valueOuterRadius_nonneg (d:=d) he)
    (valueOuterRadius_le_bound hd he hei) (valueNearRadius_inv_le_bound hd he he1 hei hδ hδi)
  apply h.trans
  unfold querySearchBound
  gcongr
  exact valueDimension_le hd

theorem valueScanIterations_le {B : ℕ} (hd : d≤B) {ε δ : ℚ}
    (he : 0<ε) (he1 : ε≤1) (hei : ε⁻¹≤B) (hδ : 0<δ) (hδi : δ⁻¹≤B) :
    (optimizeFuel δ 100+1)*searchFuel (valueDimension d)
      (nearRadius δ (valueLipschitz d ε) (valueOuterRadius d ε) (valueInnerRadius d))
      (valueOuterRadius d ε) ≤ queryScanBound B := by
  have hf := optimizeFuel_le hδi
  have hs := valueSearchFuel_le hd he he1 hei hδ hδi
  apply (Nat.mul_le_mul (Nat.add_le_add_right hf 1) hs).trans
  unfold queryScanBound
  simp only [show 200*B+3+1=200*B+4 by omega, le_refl]
end CurrentKS.RationalSDP

namespace CurrentKS.Schedule
open KS.W23

def stencilInvP : NaturalPolynomial :=
  8*(40000*NaturalPolynomial.variable^2)+1+
    64*curvatureP*NaturalPolynomial.variable*thresholdInvP

def queryPrecisionP : NaturalPolynomial :=
  1+NaturalPolynomial.variable+NaturalPolynomial.variable^4+
    512*NaturalPolynomial.variable*thresholdInvP*stencilInvP^2+
    16*thresholdInvP*stepInvP^2

lemma stencilSize_inv_bound {n : ℕ} (hn : 0<n) {a M σ : ℚ}
    (ha : 0<a) (hM : 0<M) (hσ : 0<σ) :
    (stencilSize n a M σ)⁻¹ ≤ 8*σ⁻¹+1+64*M*n*a⁻¹ := by
  have hn' : (0:ℚ)<n := by exact_mod_cast hn
  have h1 := inv_min_le_sum (div_pos hσ (by norm_num : (0:ℚ)<8))
    (lt_min (by norm_num : (0:ℚ)<1) (by positivity : (0:ℚ)<a/(64*M*n)))
  have h2 := inv_min_le_sum (by norm_num : (0:ℚ)<1) (by positivity : (0:ℚ)<a/(64*M*n))
  have h := h1.trans (add_le_add le_rfl h2)
  unfold stencilSize
  convert h using 1
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,inv_one]
  ring

lemma stencilInvP_eval (B : ℕ) : (stencilInvP.eval B:ℚ) =
    8*(40000*(B:ℚ)^2)+1+64*(curvatureP.eval B:ℚ)*B*(thresholdInvP.eval B:ℚ) := by
  change ((8*(40000*B^2)+1+64*curvatureP.eval B*B*thresholdInvP.eval B:ℕ):ℚ)=_
  push_cast
  rfl

lemma stencil_inv_polynomial {d n B : ℕ} (hd : d≤B) (hn : n≤B) (hn0 : 0<n)
    {ε σ lam : ℚ} (hε : 0<ε) (hε1 : ε≤1) (hσ : 0<σ) (hlam : 0<lam) (hlam1 : lam≤1)
    (hei : ε⁻¹≤(B:ℚ)^4) (hsi : σ⁻¹≤40000*(B:ℚ)^2) (hli : lam⁻¹≤200*(B:ℚ)^4) :
    (stencilSize n (threshold n ε lam) (curveBudget d n ε σ lam) σ)⁻¹ ≤
      (stencilInvP.eval B:ℚ) := by
  have ha := threshold_pos n ε hlam
  have hM := (show (0:ℚ)<1 by norm_num).trans_le (curveBudget_one_le d n hε hσ lam)
  have hs := stencilSize_inv_bound hn0 ha hM hσ
  have ht := threshold_inv_polynomial hn hε hlam hei hli
  have hm := curveBudget_polynomial hd hn hε hε1 hσ hlam hlam1 hei hsi
  have hn' : (n:ℚ)≤B := by exact_mod_cast hn
  rw [stencilInvP_eval]
  apply hs.trans
  gcongr

lemma queryPrecisionP_eval (B : ℕ) : (queryPrecisionP.eval B:ℚ) =
    1+B+(B:ℚ)^4+512*B*(thresholdInvP.eval B:ℚ)*(stencilInvP.eval B:ℚ)^2+
      16*(thresholdInvP.eval B:ℚ)*(stepInvP.eval B:ℚ)^2 := by
  change ((1+B+B^4+512*B*thresholdInvP.eval B*(stencilInvP.eval B)^2+
    16*thresholdInvP.eval B*(stepInvP.eval B)^2:ℕ):ℚ)=_
  push_cast
  rfl

lemma queryPrecisionP_ge (B : ℕ) :
    B≤queryPrecisionP.eval B ∧ (B:ℚ)^4≤(queryPrecisionP.eval B:ℚ) := by
  constructor
  · change B≤1+B+B^4+512*B*thresholdInvP.eval B*(stencilInvP.eval B)^2+
      16*thresholdInvP.eval B*(stepInvP.eval B)^2
    omega
  · rw [queryPrecisionP_eval]
    have h1 : (0:ℚ)≤512*B*(thresholdInvP.eval B:ℚ)*(stencilInvP.eval B:ℚ)^2 := by positivity
    have h2 : (0:ℚ)≤16*(thresholdInvP.eval B:ℚ)*(stepInvP.eval B:ℚ)^2 := by positivity
    linarith [Nat.cast_nonneg (α:=ℚ) B]

lemma query_errors_inv_polynomial {d n B : ℕ} (hd : d≤B) (hn : n≤B) (hn0 : 0<n)
    {ν lam : ℚ} (hε : 0<ν/(d:ℚ)) (hε1 : ν/(d:ℚ)≤1) (hσ : 0<lam^2/ν)
    (hlam : 0<lam) (hlam1 : lam≤1)
    (hei : (ν/(d:ℚ))⁻¹≤(B:ℚ)^4) (hsi : (lam^2/ν)⁻¹≤40000*(B:ℚ)^2)
    (hli : lam⁻¹≤200*(B:ℚ)^4) :
    ((parameters d n ν lam).stencilError/4)⁻¹≤(queryPrecisionP.eval B:ℚ) ∧
      ((parameters d n ν lam).selectionError/4)⁻¹≤(queryPrecisionP.eval B:ℚ) := by
  have ha := threshold_pos n (ν/(d:ℚ)) hlam
  have hM := (show (0:ℚ)<1 by norm_num).trans_le
    (curveBudget_one_le d n hε hσ lam)
  have hhp := (stencilSize_spec hn0 ha hM hσ).1
  have hsp := (stepSize_spec ha hM hσ).1
  have ht := threshold_inv_polynomial hn hε hlam hei hli
  have hh := stencil_inv_polynomial hd hn hn0 hε hε1 hσ hlam hlam1 hei hsi hli
  have hs := step_inv_polynomial hd hn hε hε1 hσ hlam hlam1 hei hsi hli
  have hn' : (n:ℚ)≤B := by exact_mod_cast hn
  have h0 : (0:ℚ)≤1+B+(B:ℚ)^4 := by positivity
  have h1 : (0:ℚ)≤512*B*(thresholdInvP.eval B:ℚ)*(stencilInvP.eval B:ℚ)^2 := by positivity
  have h2 : (0:ℚ)≤16*(thresholdInvP.eval B:ℚ)*(stepInvP.eval B:ℚ)^2 := by positivity
  constructor
  · change ((threshold n (ν/(d:ℚ)) lam*(stencilSize n (threshold n (ν/(d:ℚ)) lam)
      (curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam) (lam^2/ν))^2/(128*n))/4)⁻¹≤_
    rw [queryPrecisionP_eval]
    have heq : ((threshold n (ν/(d:ℚ)) lam*(stencilSize n (threshold n (ν/(d:ℚ)) lam)
      (curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam) (lam^2/ν))^2/(128*n))/4)⁻¹=
        512*n*(threshold n (ν/(d:ℚ)) lam)⁻¹*
          ((stencilSize n (threshold n (ν/(d:ℚ)) lam)
          (curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam) (lam^2/ν))⁻¹)^2 := by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,←inv_pow]
      ring
    rw [heq]
    apply le_trans _ (le_add_of_nonneg_right h2)
    apply le_trans _ (le_add_of_nonneg_left h0)
    gcongr
  · change ((threshold n (ν/(d:ℚ)) lam*(stepSize (threshold n (ν/(d:ℚ)) lam)
      (curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam) (lam^2/ν))^2/4)/4)⁻¹≤_
    rw [queryPrecisionP_eval]
    have heq : ((threshold n (ν/(d:ℚ)) lam*(stepSize (threshold n (ν/(d:ℚ)) lam)
      (curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam) (lam^2/ν))^2/4)/4)⁻¹=
        16*(threshold n (ν/(d:ℚ)) lam)⁻¹*
          ((stepSize (threshold n (ν/(d:ℚ)) lam)
          (curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam) (lam^2/ν))⁻¹)^2 := by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,←inv_pow]
      ring
    rw [heq]
    apply le_trans _ (le_add_of_nonneg_left (add_nonneg h0 h1))
    gcongr
end CurrentKS.Schedule

namespace CurrentKS.RationalSDP
open KS.W23 CurrentKS.Schedule CurrentKS.Hermitian CurrentKS.State
open scoped BigOperators

variable {d N : ℕ}

def valueScanP (p : NaturalPolynomial) : NaturalPolynomial :=
  let dim := 1+2*p^2
  let R := (dim+1)*(100+400*p*(p+1))
  let L := (dim+1)*(1+2*p)
  let rInv := 4000*(p^2+1)
  let nearInv := L*(2*R+1)*p*rInv
  (200*p+4)*(4*R^2*(nearInv*(dim+1))^2+1)

lemma valueScanP_eval (p : NaturalPolynomial) (B : ℕ) :
    (valueScanP p).eval B = queryScanBound (p.eval B) := rfl

theorem normalized_query_precisions [NeZero d] [NeZero N]
    (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank≤1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {n : ℕ} (hn0 : 0<n) (hn : n≤N) :
    let ν := varianceQuery coords
    let lam := penaltyParameter N ν
    let p := parameters d n ν lam
    ((ν/(d:ℚ))⁻¹≤(queryPrecisionP.eval (d+N):ℚ)) ∧
      (p.stencilError/4)⁻¹≤(queryPrecisionP.eval (d+N):ℚ) ∧
      (p.selectionError/4)⁻¹≤(queryPrecisionP.eval (d+N):ℚ) := by
  let ν := varianceQuery coords
  let lam := penaltyParameter N ν
  have hν := varianceQuery_spec coords hA hrank htr
  have hl := penaltyParameter_pos_le (NeZero.pos N) hν.1 hν.2.1
  have b := normalized_parameter_bounds coords hA hrank htr
  have hd : (0:ℚ)<d := by exact_mod_cast NeZero.pos d
  have hd1 : (1:ℚ)≤d := by exact_mod_cast NeZero.pos d
  have hdB : (d:ℚ)≤(d+N:ℕ) := by exact_mod_cast Nat.le_add_right d N
  have hNB : (N:ℚ)≤(d+N:ℕ) := by exact_mod_cast Nat.le_add_left N d
  have hε : 0<ν/(d:ℚ) := div_pos hν.1 hd
  have hε1 : ν/(d:ℚ)≤1 := (div_le_one hd).mpr (hν.2.1.trans hd1)
  have hσ : 0<lam^2/ν := div_pos (sq_pos_of_pos hl.1) hν.1
  have hei : (ν/(d:ℚ))⁻¹≤((d+N:ℕ):ℚ)^4 := by
    apply b.2.1.trans
    calc
      (N:ℚ)*d^3 ≤ ((d+N:ℕ):ℚ)*((d+N:ℕ):ℚ)^3 := by gcongr
      _ = ((d+N:ℕ):ℚ)^4 := by ring
  have hli : lam⁻¹≤200*((d+N:ℕ):ℚ)^4 := by
    apply b.2.2.1.trans
    calc
      200*(N:ℚ)^2*d^2 ≤ 200*((d+N:ℕ):ℚ)^2*((d+N:ℕ):ℚ)^2 := by gcongr
      _ = 200*((d+N:ℕ):ℚ)^4 := by ring
  have hsi : (lam^2/ν)⁻¹≤40000*((d+N:ℕ):ℚ)^2 := by
    apply b.2.2.2.trans
    gcongr
  exact ⟨hei.trans (queryPrecisionP_ge (d+N)).2,
    query_errors_inv_polynomial (Nat.le_add_right d N) (hn.trans (Nat.le_add_left N d)) hn0
      hε hε1 hσ hl.1 hl.2 hei hsi hli⟩

theorem normalized_query_search_iterations [NeZero d] [NeZero N]
    (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank≤1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {n : ℕ} (hn0 : 0<n) (hn : n≤N) :
    let ν := varianceQuery coords
    let lam := penaltyParameter N ν
    let p := parameters d n ν lam
    ∀ δ∈[p.stencilError/4,p.selectionError/4],
      (optimizeFuel δ 100+1)*searchFuel (valueDimension d)
        (nearRadius δ (valueLipschitz d (ν/d)) (valueOuterRadius d (ν/d)) (valueInnerRadius d))
        (valueOuterRadius d (ν/d)) ≤ (valueScanP queryPrecisionP).eval (d+N) := by
  let ν := varianceQuery coords
  let lam := penaltyParameter N ν
  have hν := varianceQuery_spec coords hA hrank htr
  have hl := penaltyParameter_pos_le (NeZero.pos N) hν.1 hν.2.1
  have hp := parameters_valid (NeZero.pos d) hn0 hν.1 hν.2.1 hl.1 hl.2
  have hb := normalized_query_precisions coords hA hrank htr hn0 hn
  have hd : d≤queryPrecisionP.eval (d+N) :=
    (Nat.le_add_right d N).trans (queryPrecisionP_ge (d+N)).1
  dsimp only
  intro δ hδ
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hδ
  rcases hδ with rfl|rfl
  · exact valueScanIterations_le hd hp.epsilon_pos hp.epsilon_le hb.1
      (div_pos hp.stencilError_pos (by norm_num)) hb.2.1
  · exact valueScanIterations_le hd hp.epsilon_pos hp.epsilon_le hb.1
      (div_pos hp.selectionError_pos (by norm_num)) hb.2.2
end CurrentKS.RationalSDP

end OAI
