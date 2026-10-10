import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.SplitContinuity

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I → ℤ) →+ M) (l : Filter ι)
local instance : AddCommGroup (Torus v Ω) := (Torus.instRing v Ω).toAddCommGroup
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
attribute [local instance] Classical.propDecidable

lemma TorusConverges.neg {f : ι → Torus v Ω} {F : Torus v Ω}
    (hf : TorusConverges v Ω l f F) :
    TorusConverges v Ω l (fun i=> -f i) (-F) :=
  fun m=>(hf m).neg l

lemma SeriesGraded.mul {F G : PowerSeries (Torus v Ω)}
    (hF : SeriesGraded v Ω C F) (hG : SeriesGraded v Ω C G) :
    SeriesGraded v Ω C (F*G) := by
  intro n
  rw [coeff_mul]
  apply (rootGrade v Ω C n).sum_mem
  intro p hp
  have H := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [←H]
  exact rootGrade_mul v Ω C p.1 p.2 _ _ (hF p.1) (hG p.2)

lemma SeriesGraded.one : SeriesGraded v Ω C 1 := by
  intro n
  rw [coeff_one]
  split_ifs with h
  · subst n; exact rootGrade_one v Ω C
  · exact (rootGrade v Ω C n).zero_mem

lemma SeriesGraded.sub {F G : PowerSeries (Torus v Ω)}
    (hF : SeriesGraded v Ω C F) (hG : SeriesGraded v Ω C G) :
    SeriesGraded v Ω C (F-G) := fun n=> (rootGrade v Ω C n).sub_mem (hF n) (hG n)

lemma SeriesGraded.pow {F : PowerSeries (Torus v Ω)} (hF : SeriesGraded v Ω C F) (k : ℕ) :
    SeriesGraded v Ω C (F^k) := by
  induction k with
  | zero => simpa only [pow_zero] using SeriesGraded.one v Ω C
  | succ k ih => simpa only [pow_succ] using ih.mul v Ω C hF

lemma SeriesConverges.pow {f : ι → PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F)
    (hfg : ∀i,SeriesGraded v Ω C (f i)) (hF : SeriesGraded v Ω C F) (k : ℕ) :
    SeriesConverges v Ω l (fun i=>f i^k) (F^k) := by
  induction k with
  | zero => simpa only [pow_zero] using seriesConverges_const v Ω l 1
  | succ k ih =>
    simpa only [pow_succ] using ih.mul v Ω C l hf
      (fun i=>(hfg i).pow v Ω C k) hfg (hF.pow v Ω C k) hF

lemma coeff_inverse_one (F : PowerSeries (Torus v Ω)) (n : ℕ) :
    coeff n (PowerSeries.invOfUnit F 1) =
      if n=0 then 1 else -∑p∈Finset.HasAntidiagonal.antidiagonal n,
        if p.2<n then coeff p.1 F*coeff p.2 (PowerSeries.invOfUnit F 1) else 0 := by
  rw [coeff_invOfUnit]
  simp only [inv_one,Units.val_one,neg_mul,one_mul]
  congr 1

lemma SeriesGraded.inverse {F : PowerSeries (Torus v Ω)} (hF : SeriesGraded v Ω C F) :
    SeriesGraded v Ω C (PowerSeries.invOfUnit F 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [coeff_inverse_one]
    split_ifs with hn
    · subst n; exact rootGrade_one v Ω C
    · apply (rootGrade v Ω C n).neg_mem
      intro m hm
      rw [Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro p hp
      split_ifs with hp2
      · have H := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        rw [←H] at hm
        exact rootGrade_mul v Ω C p.1 p.2 _ _ (hF p.1) (ih p.2 hp2) m hm
      · rfl

theorem SeriesConverges.inverse {f : ι → PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F)
    (hfg : ∀i,SeriesGraded v Ω C (f i)) (hF : SeriesGraded v Ω C F) :
    SeriesConverges v Ω l (fun i=>PowerSeries.invOfUnit (f i) 1) (PowerSeries.invOfUnit F 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    change TorusConverges v Ω l (fun i=>coeff n (PowerSeries.invOfUnit (f i) 1)) _
    have he := fun i=>coeff_inverse_one v Ω (f i) n
    simp_rw [funext he]
    rw [coeff_inverse_one]
    by_cases hn : n=0
    · simp only [ite_eq_left hn]
      exact torusConverges_const v Ω l 1
    · simp only [ite_eq_right hn]
      apply TorusConverges.neg
      apply TorusConverges.sum
      intro p hp
      by_cases hp2 : p.2<n
      · simp only [ite_eq_left hp2]
        exact (hf p.1).mul_graded v Ω C l (ih p.2 hp2) p.1 p.2
          (fun i=>hfg i p.1) (fun i=>(hfg i).inverse v Ω C p.2)
          (hF p.1) (hF.inverse v Ω C p.2)
      · simp only [ite_eq_right hp2]
        exact torusConverges_const v Ω l 0

def completedInverse (F : CompletedPositive v Ω C) : CompletedPositive v Ω C :=
  ⟨PowerSeries.invOfUnit F.val 1, by simp,
    SeriesGraded.inverse v Ω C F.property.2⟩

lemma completedInverse_mul (F : CompletedPositive v Ω C) :
    (completedInverse v Ω C F).val*F.val=1 :=
  PowerSeries.invOfUnit_mul F.val 1 F.property.1
lemma mul_completedInverse (F : CompletedPositive v Ω C) :
    F.val*(completedInverse v Ω C F).val=1 :=
  PowerSeries.mul_invOfUnit F.val 1 F.property.1

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
def adjoint (F X : PowerSeries A) : PowerSeries A := F*X*invOfUnit F 1
@[simp] lemma constant_adjoint (F X : PowerSeries A) (hF : constantCoeff F=1) :
    constantCoeff (adjoint F X)=constantCoeff X := by simp [adjoint,hF]
lemma inverse_mul (F G : PowerSeries A) (hF : constantCoeff F=1) (hG : constantCoeff G=1) :
    invOfUnit (F*G) 1=invOfUnit G 1*invOfUnit F 1 := by
  have hh : F*G*(invOfUnit G 1*invOfUnit F 1)=1:=by
    calc
      _=F*(G*invOfUnit G 1)*invOfUnit F 1:=by simp only [mul_assoc]
      _=1:=by rw [mul_invOfUnit G 1 hG,mul_one,mul_invOfUnit F 1 hF]
  calc
    _=invOfUnit (F*G) 1*(F*G*(invOfUnit G 1*invOfUnit F 1)):=by rw [hh,mul_one]
    _=(invOfUnit (F*G) 1*(F*G))*(invOfUnit G 1*invOfUnit F 1):=by simp only [mul_assoc]
    _=invOfUnit G 1*invOfUnit F 1:=by rw [invOfUnit_mul _ 1 (by simp [hF,hG]),one_mul]
lemma adjoint_mul (F G X : PowerSeries A) (hF : constantCoeff F=1) (hG : constantCoeff G=1) :
    adjoint (F*G) X=adjoint F (adjoint G X) := by
  simp only [adjoint,inverse_mul F G hF hG,mul_assoc]
lemma inverse_coeff_congr (F G : PowerSeries A) (N : ℕ) (h : ∀n≤N,coeff n F=coeff n G) :
    ∀n≤N,coeff n (invOfUnit F 1)=coeff n (invOfUnit G 1) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [coeff_invOfUnit,coeff_invOfUnit]
    split_ifs with h0
    · rfl
    · congr 1
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs with hpn
      · rw [h p.1 (by have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp; omega),ih p.2 hpn (by omega)]
      · rfl
lemma adjoint_coeff_congr (F G X Y : PowerSeries A) (N : ℕ)
    (hFG : ∀n≤N,coeff n F=coeff n G) (hXY : ∀n≤N,coeff n X=coeff n Y) :
    coeff N (adjoint F X)=coeff N (adjoint G Y) := by
  apply FormalLog.mul_coeff_congr
  · intro j hj
    exact FormalLog.mul_coeff_congr F X G Y j (fun k hk=>hFG k (hk.trans hj)) (fun k hk=>hXY k (hk.trans hj))
  · exact inverse_coeff_congr F G N hFG
lemma coeff_mul_vanish_right (F U : PowerSeries A) (n : ℕ) (hU : ∀j<n,coeff j U=0) :
    coeff n (F*U)=constantCoeff F*coeff n U := by
  classical
  rw [coeff_mul,Finset.sum_eq_single (0,n)]
  · simp only [coeff_zero_eq_constantCoeff]
  · intro p hp hpn
    have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hx : p.2<n:=by
      by_contra hh
      have hp0 : p.1=0:=by omega
      have hp2 : p.2=n:=by omega
      exact hpn (Prod.ext hp0 hp2)
    rw [hU p.2 hx,mul_zero]
  · intro hn
    exact (hn (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp))).elim
lemma coeff_mul_vanish_left (U F : PowerSeries A) (n : ℕ) (hU : ∀j<n,coeff j U=0) :
    coeff n (U*F)=coeff n U*constantCoeff F := by
  classical
  rw [coeff_mul,Finset.sum_eq_single (n,0)]
  · simp only [coeff_zero_eq_constantCoeff]
  · intro p hp hpn
    have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hx : p.1<n:=by
      by_contra hh
      have hp0 : p.2=0:=by omega
      have hp1 : p.1=n:=by omega
      exact hpn (Prod.ext hp1 hp0)
    rw [hU p.1 hx,zero_mul]
  · intro hn
    exact (hn (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp))).elim
lemma adjoint_sub (F X Y : PowerSeries A) : adjoint F (X-Y)=adjoint F X-adjoint F Y := by
  simp only [adjoint,mul_sub,sub_mul]
lemma adjoint_leading (F X Y : PowerSeries A) (hF : constantCoeff F=1) (n : ℕ)
    (hXY : ∀j<n,coeff j X=coeff j Y) :
    coeff n (adjoint F X)-coeff n (adjoint F Y)=coeff n X-coeff n Y := by
  have hU : ∀j<n,coeff j (X-Y)=0:=by intro j hj; rw [map_sub,hXY j hj,sub_self]
  have hFU : ∀j<n,coeff j (F*(X-Y))=0:=by
    intro j hj
    rw [coeff_mul_vanish_right F _ j (fun k hk=>hU k (hk.trans hj)),hU j hj,mul_zero]
  rw [←map_sub,←adjoint_sub,adjoint,coeff_mul_vanish_left _ _ n hFU,
    coeff_mul_vanish_right F _ n hU,hF,one_mul,constantCoeff_invOfUnit]
  simp only [inv_one,Units.val_one,mul_one,map_sub]
end
end ElementaryPositivity.PowerSeriesAdjoint

end

end OAI
