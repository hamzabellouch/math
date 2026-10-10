import Mathlib

namespace OAI

section
namespace ElementaryPositivity.FiniteLog
open PowerSeries

lemma subst_one {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {g : PowerSeries S} (hg : HasSubst g) : (1 : PowerSeries R).subst g=1 :=
by
  rw [←coe_substAlgHom hg,map_one]

lemma deriv_log_mul_one_add_X :
    derivative (log ℚ) * (1+X)=1 := by
  rw [derivative_log,mul_add,mul_one]
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [map_add,coeff_mk,coeff_succ_mul_X,coeff_one,
      Nat.succ_ne_zero,ite_false,pow_succ]
    simp

lemma log_subst_exp_sub_one : (log ℚ).subst (exp ℚ-1)=X := by
  apply derivative.ext
  · rw [derivative_subst HasSubst.exp_sub_one,derivative_X,map_sub,derivative_exp,
      derivative_one,sub_zero]
    have h := congrArg (fun f : PowerSeries ℚ=>f.subst (exp ℚ-1))
      deriv_log_mul_one_add_X
    simpa only [subst_mul HasSubst.exp_sub_one,subst_add HasSubst.exp_sub_one,
      subst_one HasSubst.exp_sub_one,subst_X HasSubst.exp_sub_one,add_sub_assoc,add_comm (1 : PowerSeries ℚ),add_sub_cancel_right,sub_add_cancel] using h
  · rw [constantCoeff_X]
    exact constantCoeff_subst_eq_zero
      (show MvPowerSeries.constantCoeff (exp ℚ-1)=0 from by
        change constantCoeff (exp ℚ-1)=0
        simp) _ (constantCoeff_log)

lemma subst_reverse {R : Type*} [CommRing R] (f g : PowerSeries R)
    (hf : constantCoeff f=0) (hg : constantCoeff g=0)
    (hu : IsUnit (coeff 1 f)) (hfg : f.subst g=X) : g.subst f=X := by
  let h := f.substInvOfIsUnit hu
  have hF : HasSubst f := HasSubst.of_constantCoeff_zero' hf
  have hG : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  have hlf : PowerSeries.subst f h=X := subst_substInvOfIsUnit_left f hf hu
  have heq : g=h := by
    calc
      g=PowerSeries.subst g (X : PowerSeries R) := (subst_X hG).symm
      _=PowerSeries.subst g (PowerSeries.subst f h) := by rw [hlf]
      _=PowerSeries.subst (PowerSeries.subst g f) h := by
        rw [subst_comp_subst_apply (R := R) (S := R) (T := R) (υ := Unit) hF hG]
      _=h := by rw [hfg,X_subst]
  simpa only [heq] using hlf

lemma exp_subst_log : (exp ℚ).subst (log ℚ)=1+X := by
  have h := subst_reverse (log ℚ) (exp ℚ-1) (by simp) (by simp)
    (by simp) log_subst_exp_sub_one
  rw [subst_sub HasSubst.log,subst_one HasSubst.log] at h
  exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)

end ElementaryPositivity.FiniteLog

end
section
namespace ElementaryPositivity.FiniteLog
open PowerSeries

variable {A B : Type*} [Ring A] [Ring B] [Algebra ℚ A] [Algebra ℚ B]

noncomputable def nilEval (x : A) (f : PowerSeries ℚ) : A :=
  ∑ i ∈ Finset.range (nilpotencyClass x), coeff i f • x^i

lemma nilEval_eq_sum {x : A} {n : ℕ} (hn : x^n=0) (f : PowerSeries ℚ) :
    nilEval x f=∑ i ∈ Finset.range n,coeff i f • x^i := by
  apply Finset.sum_subset (Finset.range_mono (csInf_le' hn))
  intro i hi hni
  rw [Finset.mem_range,not_lt] at hni
  rw [pow_eq_zero_of_le hni (pow_nilpotencyClass ⟨n,hn⟩),smul_zero]

lemma map_nilEval (φ : A →ₐ[ℚ] B) {x : A} (hx : IsNilpotent x) (f : PowerSeries ℚ) :
    φ (nilEval x f)=nilEval (φ x) f := by
  obtain ⟨n,hn⟩ := hx
  rw [nilEval_eq_sum hn,nilEval_eq_sum (show (φ x)^n=0 by rw [←map_pow,hn,map_zero])]
  simp only [map_sum,map_smul,map_pow]

lemma nilEval_exp {x : A} (hx : IsNilpotent x) : nilEval x (exp ℚ)=IsNilpotent.exp x := by
  obtain ⟨n,hn⟩ := hx
  rw [nilEval_eq_sum hn,IsNilpotent.exp_eq_sum hn]
  congr 1
  ext i
  simp only [coeff_exp,one_div,Algebra.algebraMap_self,RingHom.id_apply]

section CommRing
variable {S : Type*} [CommRing S] [Algebra ℚ S]

omit [Algebra ℚ S] in
lemma substConst_hasSubst {x : S} (hx : IsNilpotent x) : HasSubst (C x : PowerSeries S) := by
  change IsNilpotent (constantCoeff (C x))
  rwa [constantCoeff_C]

lemma nilEval_eq_constantCoeff {x : S} (hx : IsNilpotent x) (f : PowerSeries ℚ) :
    nilEval x f=constantCoeff (PowerSeries.subst (C x : PowerSeries S) f) := by
  rw [show constantCoeff (PowerSeries.subst (C x : PowerSeries S) f)=
    MvPowerSeries.constantCoeff (PowerSeries.subst (C x : PowerSeries S) f) from rfl,
    constantCoeff_subst (substConst_hasSubst hx)]
  simp only [map_pow,show MvPowerSeries.constantCoeff (C x : PowerSeries S)=x from constantCoeff_C x]
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra h
  rw [Finset.mem_coe,Finset.mem_range,not_lt] at h
  apply hi
  change coeff i f • x^i=0
  rw [pow_eq_zero_of_le h (pow_nilpotencyClass hx),smul_zero]

noncomputable def nilEvalAlgHom {x : S} (hx : IsNilpotent x) : PowerSeries ℚ →ₐ[ℚ] S :=
  (constantCoeff : PowerSeries S →+* S).toRatAlgHom.comp (substAlgHom (substConst_hasSubst hx))

lemma nilEvalAlgHom_apply {x : S} (hx : IsNilpotent x) (f : PowerSeries ℚ) :
    nilEvalAlgHom hx f=nilEval x f := by
  rw [nilEval_eq_constantCoeff hx]
  change constantCoeff ((substAlgHom (substConst_hasSubst hx)) f)=_
  rw [coe_substAlgHom]

lemma subst_eq_nilEval {z : PowerSeries S} (hz : IsNilpotent z) (f : PowerSeries ℚ) :
    PowerSeries.subst z f=nilEval z f := by
  ext n
  rw [coeff_subst' (hz.map constantCoeff)]
  simp only [nilEval,map_sum]
  apply finsum_eq_sum_of_support_subset
  intro i hi
  by_contra h
  rw [Finset.mem_coe,Finset.mem_range,not_lt] at h
  apply hi
  change coeff i f • coeff n (z^i)=0
  rw [pow_eq_zero_of_le h (pow_nilpotencyClass hz),map_zero,smul_zero]

lemma subst_C_nilEval {x : S} (hx : IsNilpotent x) (f : PowerSeries ℚ) :
    PowerSeries.subst (C x : PowerSeries S) f=C (nilEval x f) := by
  rw [subst_eq_nilEval (hx.map C)]
  exact (map_nilEval (C : S →+* PowerSeries S).toRatAlgHom hx f).symm

lemma nilEval_nilpotent {x : S} (hx : IsNilpotent x) {f : PowerSeries ℚ}
    (hf : constantCoeff f=0) : IsNilpotent (nilEval x f) := by
  rw [nilEval_eq_constantCoeff hx]
  have h := (HasSubst.of_constantCoeff_zero' hf).comp (substConst_hasSubst hx)
  rwa [coe_substAlgHom] at h

lemma nilEval_subst {x : S} (hx : IsNilpotent x) {f : PowerSeries ℚ}
    (hf : constantCoeff f=0) (g : PowerSeries ℚ) :
    nilEval (nilEval x f) g=nilEval x (PowerSeries.subst f g) := by
  calc
    _=constantCoeff (PowerSeries.subst (C (nilEval x f) : PowerSeries S) g) :=
      nilEval_eq_constantCoeff (nilEval_nilpotent hx hf) g
    _=constantCoeff (PowerSeries.subst (PowerSeries.subst (C x : PowerSeries S) f) g) := by
      rw [subst_C_nilEval hx f]
    _=constantCoeff (PowerSeries.subst (C x : PowerSeries S) (PowerSeries.subst f g)) := by
      exact congrArg constantCoeff (subst_comp_subst_apply (R := ℚ) (S := ℚ) (T := S)
        (υ := Unit) (HasSubst.of_constantCoeff_zero' hf) (substConst_hasSubst hx) g).symm
    _=_ := (nilEval_eq_constantCoeff hx (PowerSeries.subst f g)).symm

lemma nilEval_X {x : S} (hx : IsNilpotent x) : nilEval x X=x := by
  rw [nilEval_eq_constantCoeff hx,subst_X (substConst_hasSubst hx),constantCoeff_C]

lemma nilEval_one {x : S} (hx : IsNilpotent x) : nilEval x 1=1 := by
  rw [←nilEvalAlgHom_apply hx,map_one]

lemma nilEval_add {x : S} (hx : IsNilpotent x) (f g : PowerSeries ℚ) :
    nilEval x (f+g)=nilEval x f+nilEval x g := by
  simp only [←nilEvalAlgHom_apply hx,map_add]

lemma nilEval_sub {x : S} (hx : IsNilpotent x) (f g : PowerSeries ℚ) :
    nilEval x (f-g)=nilEval x f-nilEval x g := by
  simp only [←nilEvalAlgHom_apply hx,map_sub]

lemma exp_nilEval_log {x : S} (hx : IsNilpotent x) :
    IsNilpotent.exp (nilEval x (log ℚ))=1+x := by
  rw [←nilEval_exp (nilEval_nilpotent hx constantCoeff_log),
    nilEval_subst hx constantCoeff_log,exp_subst_log,nilEval_add hx,nilEval_one hx,nilEval_X hx]

lemma nilEval_log_exp_sub_one {x : S} (hx : IsNilpotent x) :
    nilEval (IsNilpotent.exp x-1) (log ℚ)=x := by
  rw [←nilEval_exp hx,←nilEval_one hx,←nilEval_sub hx,
    nilEval_subst hx (by simp),log_subst_exp_sub_one,nilEval_X hx]

lemma nilEval_log_mul_comm {x y : S} (hx : IsNilpotent x) (hy : IsNilpotent y) :
    nilEval ((1+x)*(1+y)-1) (log ℚ)=nilEval x (log ℚ)+nilEval y (log ℚ) := by
  have hlx := nilEval_nilpotent hx (constantCoeff_log (A := ℚ))
  have hly := nilEval_nilpotent hy (constantCoeff_log (A := ℚ))
  have hs := nilEval_log_exp_sub_one ((Commute.all _ _).isNilpotent_add hlx hly)
  rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hlx hly,
    exp_nilEval_log hx,exp_nilEval_log hy] at hs
  exact hs

omit [Algebra ℚ S] in
lemma nilpotent_one_add_mul_sub_one {x y : S} (hx : IsNilpotent x) (hy : IsNilpotent y) :
    IsNilpotent ((1+x)*(1+y)-1) := by
  rw [show (1+x)*(1+y)-1=x+y+x*y by ring]
  exact (Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_add hx hy)
    ((Commute.all _ _).isNilpotent_mul_right hx)

end CommRing

open scoped IsMulCommutative in
lemma nilEval_log_mul_of_commute {x y : A} (hxy : Commute x y)
    (hx : IsNilpotent x) (hy : IsNilpotent y) :
    nilEval ((1+x)*(1+y)-1) (log ℚ)=nilEval x (log ℚ)+nilEval y (log ℚ) := by
  let s : Set A := {x,y}
  have hs : ∀ u ∈ s, ∀ v ∈ s, u*v=v*u := by
    intro u hu v hv
    rcases hu with rfl | hu
    · rcases hv with rfl | hv
      · rfl
      · rw [Set.mem_singleton_iff] at hv
        subst v
        exact hxy.eq
    · rw [Set.mem_singleton_iff] at hu
      subst u
      rcases hv with rfl | hv
      · exact hxy.eq.symm
      · rw [Set.mem_singleton_iff] at hv
        subst v
        rfl
  let T := Algebra.adjoin ℚ s
  let : IsMulCommutative T := Algebra.isMulCommutative_adjoin ℚ
    (fun left hleft right hright _ => hs left hleft right hright)
  let : CommRing T := inferInstance
  let tx : T := ⟨x,Algebra.subset_adjoin (Set.mem_insert x _)⟩
  let ty : T := ⟨y,Algebra.subset_adjoin (Set.mem_insert_of_mem x (Set.mem_singleton y))⟩
  have htx : IsNilpotent tx := by
    obtain ⟨n,hn⟩ := hx
    exact ⟨n,Subtype.ext hn⟩
  have hty : IsNilpotent ty := by
    obtain ⟨n,hn⟩ := hy
    exact ⟨n,Subtype.ext hn⟩
  have h := congrArg (Algebra.adjoin ℚ s).val (nilEval_log_mul_comm htx hty)
  rw [map_nilEval _ (nilpotent_one_add_mul_sub_one htx hty),map_add,
    map_nilEval _ htx,map_nilEval _ hty,map_sub,map_mul,map_add,map_add,map_one] at h
  exact h

end ElementaryPositivity.FiniteLog

end

end OAI
