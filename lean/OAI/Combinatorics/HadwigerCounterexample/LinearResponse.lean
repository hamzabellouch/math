import OAI.Combinatorics.HadwigerCounterexample.BaselineForms

namespace OAI

/-! # Linear Response -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
variable {p : Shape} {n : ℕ}

abbrev PureForms (p : Shape) (n : ℕ) := Comp p.g → Mat (JointIdx p n) (JointIdx p n)
abbrev ChanOut (p : Shape) (n : ℕ) := Place p → Mat (Chan p) (JointIdx p n)
abbrev Xpair (p : Shape) (n : ℕ) := Bool → Xspace p n

def pureSpace (p : Shape) {n} (f : Plan p n) : Space (PureForms p n) :=
  Submodule.pi Set.univ (fun e => box (annih (f (e,true))) (annih (f (e,false))))
def deltaSpace (p : Shape) {n} (f b : Plan p n) (j : Bool) : Space (ChanOut p n) :=
  Submodule.pi Set.univ (fun e => box (annih (hPin b (flipZ p e) j)) (annih (f e)))

theorem pureSpace_mem {f : Plan p n} (P : PureForms p n) :
    P∈pureSpace p f ↔ ∀ e : Comp p.g,
      P e∈box (annih (f (e,true))) (annih (f (e,false))) := by simp [pureSpace,Submodule.mem_pi]
theorem deltaSpace_mem {b f : Plan p n} {j} (C : ChanOut p n) :
    C∈deltaSpace p f b j ↔ ∀ e : Place p,
      C e∈box (annih (hPin b (flipZ p e) j)) (annih (f e)) := by simp [deltaSpace,Submodule.mem_pi]

def chanInner (p : Shape) {n} (C D : ChanOut p n) : PureForms p n :=
  fun e => (C (e,true))ᵀ * D (e,false)
def chanDeriv (p : Shape) {n} (C D : ChanOut p n) : PureForms p n :=
  chanInner p C D+chanInner p D C

def purePair (p : Shape) (n) (x : Xpair p n) : PureForms p n :=
  ∑ i : Bool,(fun e => liftM (IP p n i) (IP p n i) ((x i).val e))

def react (p : Shape) {n : ℕ} (C : ChanOut p n) :
    ChanOut p n × PureForms p n →ₗ[F] Module.Dual F (Xpair p n) where
  toFun A := {
    toFun x := ∑ e : Comp p.g,
      mpair ((chanDeriv p C A.1+A.2) e) (purePair p n x e)
    map_add' x y := by
      have hh (e) : purePair p n (x+y) e=purePair p n x e+purePair p n y e := by
        simp only [purePair,Finset.sum_apply,Pi.add_apply,Submodule.coe_add,map_add,
          Finset.sum_add_distrib]
      simp only [hh,map_add,Finset.sum_add_distrib]
    map_smul' b x := by
      have hh (e) : purePair p n (b•x) e=b • purePair p n x e := by
        simp only [purePair,Finset.sum_apply,Pi.smul_apply,Submodule.coe_smul,map_smul,
          Finset.smul_sum]
      simp only [hh,map_smul,RingHom.id_apply,Finset.smul_sum] }
  map_add' A B := LinearMap.ext fun x => by
    have h (e) : (chanDeriv p C (A+B).1 + (A+B).2) e =
        (chanDeriv p C A.1 + A.2) e + (chanDeriv p C B.1 + B.2) e := by
      simp only [chanDeriv,chanInner,Pi.add_apply,Prod.fst_add,Prod.snd_add,
        transpose_add,Matrix.add_mul,Matrix.mul_add]; abel
    simp only [LinearMap.coe_mk,AddHom.coe_mk,h,mpair_add,LinearMap.add_apply,
      Finset.sum_add_distrib]
  map_smul' b A := LinearMap.ext fun x => by
    have h (e) : (chanDeriv p C (b•A).1 + (b•A).2) e =
        b • (chanDeriv p C A.1 + A.2) e := by
      simp only [chanDeriv,chanInner,Pi.add_apply,Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,
        transpose_smul, Matrix.smul_mul, Matrix.mul_smul,smul_add]
    simp only [LinearMap.coe_mk,AddHom.coe_mk,h,mpair_smul,LinearMap.smul_apply,RingHom.id_apply,
      smul_eq_mul,Finset.mul_sum]

def orth (p : Shape) {n : ℕ} (C : ChanOut p n) (f b : Plan p n) (j) (x : Xpair p n) :=
  ∀ D∈deltaSpace p f b j,∀ A∈pureSpace p f, react p C (D,A) x=0

theorem solve_by_dual {f b : Plan p n} {C : ChanOut p n} {j : Bool}
    (G : Module.Dual F (Xpair p n))
    (h : ∀ x, orth p C f b j x → G x = 0) :
    ∃ D∈deltaSpace p f b j,∃ A∈ pureSpace p f,react p C (D,A) = G := by
  classical
  let S := ((deltaSpace p f b j).prod (pureSpace p f)).map (react p C)
  by_cases he : G∈S
  · obtain ⟨⟨D,A⟩,⟨h1,h2⟩,hh⟩ := he
    exact ⟨D,h1,A,h2,hh⟩
  obtain ⟨g,hg,hk⟩ := S.exists_le_ker_of_notMem he
  let x := (Module.evalEquiv F (Xpair p n)).symm g
  have ht (f : Module.Dual F (Xpair p n)) : f x=g f :=
    apply_evalEquiv_symm_apply ..
  have h1 : orth p C f b j x := by
    intro D hd A ha
    rw [ht]; exact hk (show react p C (D,A)∈S from ⟨_,⟨hd,ha⟩,rfl⟩)
  exact (hg ((ht G).symm.trans (h x h1))).elim

/-- Pure test annihilation vanishes in the factor quotients. -/
theorem orth_pure {f b : Plan p n} {x : Xpair p n} {C : ChanOut p n} {j}
    (h : orth p C f b j x) (e : Comp p.g) :
    vanish (f (e,true)) (f (e,false)) (purePair p n x e) := by
  classical
  intro y hy z hz
  let m : Mat (JointIdx p n) (JointIdx p n) := vecMulVec y z
  let a : PureForms p n := Pi.single e m
  have he : a∈pureSpace p f := by
    refine (pureSpace_mem _).mpr (fun i => ?_)
    by_cases h : i = e
    · subst i; rw [show a e=m from Pi.single_eq_same _ _]; exact outer_in_box _ _ hy hz
    simp [a,h]
  have hx := h 0 (Submodule.zero_mem _) a he
  change ∑ i, mpair ((chanDeriv p C 0+a) i) (purePair p n x i) = _ at hx
  have ha : chanDeriv p C 0=0 := by
    unfold chanDeriv chanInner; ext; simp
  rw [ha,zero_add,Finset.sum_eq_single e] at hx
  · rw [←mpair_outer,mpair_comm]
    rw [show a e=m from Pi.single_eq_same _ _] at hx
    exact hx
  · intro i _ h
    rw [show a i=0 from Pi.single_eq_of_ne h _,mpair_comm,map_zero]
  simp

end HadwigerCounterexample

end

end OAI
