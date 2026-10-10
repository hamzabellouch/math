import OAI.NumberTheory.DirichletL.Moments.FirstMixedCommonRadius
import OAI.NumberTheory.DirichletL.Moments.AmplificationErrorEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedNormalization
open CenteredMomentDescentLedger CenteredMomentSectorLocalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
local notation "O" => ActualEisensteinCubic.O

theorem exceptional_reference_identity (Z V C D NE NR K Q w wo B j g ell:ℝ)
    (hZ:1<Z)(hV:0<V)(hC:0<C)(hD:0<D)(hE:0<NE)(hR:0<NR)(hK:0<K)(hQ:0<Q):
    let c:=Real.logb Z C;
    let d:=Real.logb Z D;
    let q:=Real.logb Z Q;
    let K0:=Real.logb Z (NE*NR*V^2/(K*C*D));
    let M:=Real.logb Z K+q-Real.logb Z NE-Real.logb Z NR;
    (V/C)*Z^(-wo)*(V/C/Z^w)^((1:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6)*Z^(-ell)/
      (Q*(V/C)^2*Z^B)=
      Z^(Real.logb Z V-5*M/6-firstSaving c (d+K0-j) w q wo B g ell):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hzlog:Real.log Z≠0:=ne_of_gt (Real.log_pos hZ)
  dsimp only
  apply Real.log_injOn_pos
  · simp only [Set.mem_Ioi];positivity
  · simp only [Set.mem_Ioi];positivity
  · simp (disch := positivity) only [Real.log_div,Real.log_mul,Real.log_rpow,Real.log_pow]
    unfold firstSaving Real.logb
    rw [Real.log_div,Real.log_mul,Real.log_mul,Real.log_pow,
      Real.log_mul,Real.log_mul] <;> try positivity
    field_simp
    ; ring

theorem actual_error_weight (p:O)(hp:p≠0)(Z:ℝ)(hZ:1<Z)(k:ℕ)
    (hk:k=1 ∨ k=6 ∨ k=7):
    localErrorCost p (k-1)≤Z^(-errorMoving p Z k):=by
  have hn:1≤normValue p:=normValue_ge_one p hp
  have hnpos:0<normValue p:=normValue_pos p hp
  have he:Z^(-(Real.logb Z (normValue p)))=(normValue p)⁻¹:=by
    rw [Real.rpow_neg (zero_lt_one.trans hZ).le,
      Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hnpos]
  rcases hk with rfl|rfl|rfl
  · simpa [localErrorCost,errorMoving,normValue] using he.ge
  · norm_num only [Nat.reduceSub,localErrorCost,errorMoving,ite_true,neg_zero,Real.rpow_zero]
    change (1-(normValue p)⁻¹)^2≤1
    have hi:0≤(normValue p)⁻¹:=inv_nonneg.mpr hnpos.le
    have hu:(normValue p)⁻¹≤1:=inv_le_one_of_one_le₀ hn
    nlinarith
  · simpa [localErrorCost,errorMoving,normValue] using he.ge

end SevenEighths.CenteredMomentFirstMixedNormalization

end

end OAI
