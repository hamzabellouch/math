import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.PowerSeriesSplitLeading
import OAI.Combinatorics.Chromatic.GradedAlgebra.NoncommSeriesCalculus
import OAI.Combinatorics.Chromatic.GradedAlgebra.NonpRegradeFaithful
import OAI.Combinatorics.Chromatic.GradedAlgebra.QuantumTorusAlgebra

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A] [Algebra ℚ A]
def logPolynomial (F : PowerSeries A) (N : ℕ) : PowerSeries A :=
  ∑k∈Finset.range N,((-1:ℚ)^k/(k+1:ℕ)) • (F-1)^(k+1)
lemma logPolynomial_coeff (F : PowerSeries A) (hf : constantCoeff F=1) (N n : ℕ) (hn : n≤N) :
    coeff n (logPolynomial F N)=coeff n (FormalLog.log F) := by
  simp only [logPolynomial,FormalLog.log,coeff_mk,map_sum,coeff_smul]
  symm
  apply Finset.sum_subset (Finset.range_mono hn)
  intro k hk hkn
  rw [coeff_power_vanish (F-1) (by simp [hf]) (k+1) n (by
    simp only [Finset.mem_range,not_lt] at hkn; omega),smul_zero]
end
end ElementaryPositivity.FormalLog
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ) (B : ℕ)
local instance regradeLogRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance regradeLogNonUnitalSemiring : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance regradeLogNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
local instance regradeLogAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance regradeLogAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance regradeLogAddCommGroup : AddCommGroup (Torus v Ω) := (Torus.instRing v Ω).toAddCommGroup
local instance regradeLogSub : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
lemma homogenize_smul (q : ℚ) (f : Torus v Ω) :
    homogenize v Ω δ (q • f)=q • homogenize v Ω δ f := by
  ext n m
  simp only [homogenize_coeff,coeff_smul,Finsupp.smul_apply]
  split_ifs <;> simp

def regradeLinear : PowerSeries (Torus v Ω) →ₗ[ℚ] PowerSeries (Torus v Ω) where
  toFun:=regrade v Ω δ B
  map_add' f g:=by
    apply PowerSeries.ext
    intro n
    ext m
    simp only [regrade_coeff,nonp_torus_eval_sum,homogenize_coeff,_root_.map_add,Finsupp.add_apply]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  map_smul' q f:=by
    apply PowerSeries.ext
    intro n
    simp only [regrade_coeff,coeff_smul,homogenize_smul,Finset.smul_sum,RingHom.id_apply]

omit [Algebra ℚ R] in
lemma RegradeBound.pow {f : PowerSeries (Torus v Ω)} (hf : RegradeBound v Ω δ B f) (k : ℕ) :
    RegradeBound v Ω δ B (f^k) := by
  induction k with
  | zero=>simpa using RegradeBound.one v Ω δ B
  | succ k ih=>exact ih.mul v Ω δ B hf

omit [Algebra ℚ R] in
lemma regrade_pow {F : PowerSeries (Torus v Ω)} (hf : RegradeBound v Ω δ B F) (k : ℕ) :
    regrade v Ω δ B (F^k)=(regrade v Ω δ B F)^k := by
  induction k with
  | zero=>simpa using regrade_one v Ω δ B
  | succ k ih=>rw [pow_succ,regrade_mul v Ω δ B (hf.pow v Ω δ B k) hf,ih,pow_succ]
lemma regrade_logPolynomial (F : PowerSeries (Torus v Ω)) (hf : RegradeBound v Ω δ B F) (N : ℕ) :
    regrade v Ω δ B (FormalLog.logPolynomial F N)=
      FormalLog.logPolynomial (regrade v Ω δ B F) N := by
  change regradeLinear v Ω δ B (FormalLog.logPolynomial F N)=_
  rw [FormalLog.logPolynomial,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul]
  congr 1
  change regrade v Ω δ B ((F-1)^(k+1))=_
  rw [regrade_pow v Ω δ B (by
    intro j m hm
    by_cases hF : coeff j F m=0
    · apply RegradeBound.one v Ω δ B j m
      intro h1
      apply hm
      rw [map_sub,sub_eq_add_neg]
      change coeff j F m+ -(coeff j (1 : PowerSeries (Torus v Ω)) m)=0
      rw [hF,h1,neg_zero,add_zero]
    · exact hf j m hF)]
  congr 1
  change regradeLinear v Ω δ B (F-1)=_
  rw [map_sub]
  change regrade v Ω δ B F-regrade v Ω δ B 1=_
  rw [regrade_one]
omit [Algebra ℚ R] in
lemma regrade_constant (F : PowerSeries (Torus v Ω)) (hf : constantCoeff F=1) :
    constantCoeff (regrade v Ω δ B F)=1 := by
  rw [←coeff_zero_eq_constantCoeff_apply,regrade_coeff]
  simp only [mul_zero,zero_add,Finset.sum_range_one,coeff_zero_eq_constantCoeff,hf,
    homogenize_one,constantCoeff_one]
omit [Algebra ℚ R] in
lemma regrade_coeff_congr (F G : PowerSeries (Torus v Ω)) (d : ℕ)
    (H : ∀n≤B*d,coeff n F=coeff n G) :
    coeff d (regrade v Ω δ B F)=coeff d (regrade v Ω δ B G) := by
  rw [regrade_coeff,regrade_coeff]
  apply Finset.sum_congr rfl
  intro n hn
  rw [H n (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hn)]
lemma regrade_log (F : PowerSeries (Torus v Ω))
    (hf : RegradeBound v Ω δ B F) (hc : constantCoeff F=1) :
    regrade v Ω δ B (FormalLog.log F)=FormalLog.log (regrade v Ω δ B F) := by
  apply PowerSeries.ext
  intro d
  let N:=max d (B*d)
  calc
    coeff d (regrade v Ω δ B (FormalLog.log F))=
        coeff d (regrade v Ω δ B (FormalLog.logPolynomial F N)) := by
      apply regrade_coeff_congr
      intro n hn
      exact (FormalLog.logPolynomial_coeff F hc N n (hn.trans (le_max_right _ _))).symm
    _ = coeff d (FormalLog.logPolynomial (regrade v Ω δ B F) N) := by
      rw [regrade_logPolynomial v Ω δ B F hf N]
    _ = coeff d (FormalLog.log (regrade v Ω δ B F)) :=
      FormalLog.logPolynomial_coeff _ (regrade_constant v Ω δ B F hc) N d (le_max_left _ _)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
