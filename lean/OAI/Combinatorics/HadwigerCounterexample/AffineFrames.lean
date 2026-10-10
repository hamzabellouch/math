import OAI.Combinatorics.HadwigerCounterexample.QuadraticTesters
import OAI.Combinatorics.HadwigerCounterexample.SampledGraphs
import Mathlib.Data.Matrix.ColumnRowPartitioned

namespace OAI

/-! # Affine Frames -/

noncomputable section
namespace HadwigerCounterexample

open Matrix
open scoped BigOperators

structure Mixer (p : Shape) (n : ℕ) where
  mixL : Fin p.J → Comp p.g → Comp p.g → Moment p n
  mixR : Fin p.J → Comp p.g → Comp p.g → Moment p n
  mixM : Fin p.b → Mat (Fin n) (Fin n)

abbrev Pdual (p : Shape) (n : ℕ) := Profile p n →ₗ[F] F

def linTensor {V : Type} [AddCommGroup V] [Module F V] (a b : V →ₗ[F] F) : V →ₗ[F] V →ₗ[F] F :=
  a.smulRight b

theorem linTensor_val {V : Type} [AddCommGroup V] [Module F V] (a b : V →ₗ[F] F)
    (x y : V) : linTensor a b x y = a x * b y := rfl

variable {p : Shape} {n N : ℕ}

def T0 (p : Shape) (n : ℕ) : Profile p n →ₗ[F] Pdual p n :=
  linTensor (role p n) (role p n) +
    ∑ i : Tag p.g, (linTensor (roleT p n i) (sharedT p n i) +
      linTensor (sharedT p n i) (roleT p n i))

theorem T0_val (x y : Profile p n) : T0 p n x y =
    role p n x * role p n y +
      ∑ i : Tag p.g, (roleT p n i x * sharedT p n i y + sharedT p n i x * roleT p n i y) := by
  simp only [T0,LinearMap.add_apply,LinearMap.sum_apply,linTensor_val]

def B1 (m : Mixer p n) : Profile p n →ₗ[F] Pdual p n where
  toFun x := {
    toFun := fun y => ∑ j, ∑ e, ∑ f,
      mpair (x e) (liftM (m.mixL j e f) (m.mixR j e f) (y f))
    map_add' y z := by simp only [Pi.add_apply,map_add, Finset.sum_add_distrib]
    map_smul' b y := by simp only [Pi.smul_apply,map_smul,RingHom.id_apply,smul_eq_mul,
      Finset.mul_sum] }
  map_add' x y := LinearMap.ext fun z => by
    simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.add_apply,
      Pi.add_apply,mpair_add, Finset.sum_add_distrib]
  map_smul' b x := LinearMap.ext fun z => by
    simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply,RingHom.id_apply,
      Pi.smul_apply,mpair_smul,smul_eq_mul, Finset.mul_sum]

def Tmix (m : Mixer p n) := B1 m + LinearMap.flip (B1 m)
def Tsym (m : Mixer p n) := T0 p n + Tmix m

theorem Tsym_val (m : Mixer p n) (x y : Profile p n) :
    Tsym m x y = T0 p n x y + (B1 m x y + B1 m y x) := by
  change (T0 p n + (B1 m + _)) x y = _
  simp

theorem T_swap (m : Mixer p n) (x y : Profile p n) : Tsym m x y = Tsym m y x := by
  simp only [Tsym_val,T0_val]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (mul_comm _ _)
    (Finset.sum_congr rfl fun i _ => ?_)) (add_comm _ _)
  rw [mul_comm (roleT p n i x),mul_comm (sharedT p n i x),add_comm]

theorem T_diag (m : Mixer p n) (x : Profile p n) : Tsym m x x = role p n x := by
  have h (a b : F) : a*b+b*a=0 := by rw [mul_comm b a,char_two]
  simp only [Tsym_val,T0_val,char_two,h,Finset.sum_const_zero,add_zero,bit_sq]

def grad (m : Mixer p n) (x : Profile p n) := role p n + Tsym m x
theorem grad_val (m : Mixer p n) (x y : Profile p n) :
    grad m x y = role p n y + Tsym m x y := rfl

abbrev Full (p : Shape) (n : ℕ) := Row p n ⊕ Fin p.h
abbrev RawFrame (I J : Type) := Mat J I × Mat J I
abbrev Oframe (p : Shape) (n N : ℕ) := RawFrame (Full p n) (Fin N)
abbrev Orient (p : Shape) (n N : ℕ) := Comp p.g → Oframe p n N

def primary {I J E : Type} (M : Mat E (I ⊕ J)) : Mat E I := M.submatrix id Sum.inl
def channel {I J E : Type} (M : Mat E (I ⊕ J)) : Mat E J := M.submatrix id Sum.inr

theorem fromCols_frame {I J E : Type} (M : Mat E (I ⊕ J)) :
    fromCols (primary M) (channel M) = M := by ext i j; rcases j with i|j <;> rfl

theorem primary_inj {I J E : Type} [Fintype I] [Fintype J]
    {M : Mat E (I ⊕ J)} (h : Function.Injective M.mulVec) :
    Function.Injective (primary M).mulVec := by
  intro a b hab
  let v (x : Vec I) := Sum.elim x (fun _ : J => (0:F))
  have he (x : Vec I) : M *ᵥ v x = primary M *ᵥ x := by
    conv_lhs => rw [← fromCols_frame M]
    unfold v; rw [fromCols_mulVec_sumElim]
    change _ + (channel M *ᵥ 0) = _
    rw [Matrix.mulVec_zero,add_zero]
  have hh : v a = v b := h (by rw [he,he]; exact hab)
  exact funext fun i => congr_fun hh (.inl i)

def valid (M : Moment p n) (o : Oframe p n N) : Prop :=
  Function.Injective o.1.mulVec ∧ Function.Injective o.2.mulVec ∧
  (primary o.1)ᵀ * primary o.2 = M ∧ (channel o.1)ᵀ * primary o.2 = 0 ∧
  (primary o.1)ᵀ * channel o.2 = 0

def frameLaw (m : Mixer p n) (o : Orient p n N) :=
  ∀ e, valid (selfM p n m.mixM) (o e)

abbrev Ambient (p : Shape) (N : ℕ) := Comp p.g → Mat (Fin N) (Fin N)

def Uembed (o : Orient p n N) : Profile p n →ₗ[F] Ambient p N where
  toFun x e := liftM (primary (o e).1) (primary (o e).2) (x e)
  map_add' x y := by funext e; simp only [Pi.add_apply,map_add]
  map_smul' a x := by funext e; simp only [Pi.smul_apply,map_smul,RingHom.id_apply]

def ufun (o : Orient p n N) : Ambient p N →ₗ[F] F where
  toFun x := ∑ e, mpair (channel (o e).2 * (channel (o e).1)ᵀ) (x e)
  map_add' x y := by simp only [Pi.add_apply,map_add, Finset.sum_add_distrib]
  map_smul' a x := by simp only [Pi.smul_apply,map_smul,RingHom.id_apply,
    smul_eq_mul,Finset.mul_sum]

theorem Uembed_inj {m : Mixer p n} {o : Orient p n N} (h : frameLaw m o) :
    Function.Injective (Uembed o) := by
  intro x y e
  exact funext fun i =>
    liftM_inj (primary_inj (h i).1) (primary_inj (h i).2.1) (congr_fun e i)

theorem ufun_self {m : Mixer p n} {o : Orient p n N} (h : frameLaw m o) (x : Profile p n) :
    ufun o (Uembed o x) = 0 := by
  simp only [ufun,Uembed,LinearMap.coe_mk,AddHom.coe_mk]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mpair_liftM,liftM_def,← Matrix.mul_assoc,(h i).2.2.2.2,Matrix.zero_mul,
    Matrix.zero_mul,mpair_comm,map_zero]

/-- Witnesses v,w are in the cut-profile space. The gradients agree over that
*whole* space. -/
def hole (m : Mixer p n) (x y : Orient p n N) :=
  frameLaw m x ∧ frameLaw m y ∧ ∃ v w : Profile p n,
    v ∈ Xspace p n ∧ w ∈ Xspace p n ∧
    Uembed x v = Uembed y w ∧
    (∀ i ∈ Xspace p n, ufun y (Uembed x i) = grad m v i) ∧
    (∀ i ∈ Xspace p n, ufun x (Uembed y i) = grad m w i) ∧
    role p n v + role p n w = 1

theorem hole_sym {m : Mixer p n} {x y : Orient p n N} (h : hole m x y) : hole m y x := by
  obtain ⟨hx,hy,v,w,hv,hw,e,h,g,p⟩ := h
  exact ⟨hy,hx,w,v,hw,hv,e.symm,g,h,(add_comm _ _).trans p⟩

theorem not_hole_self (m : Mixer p n) (x : Orient p n N) : ¬hole m x x := by
  rintro ⟨hx,_,v,w,_,_,e,_,_,hp⟩
  rw [Uembed_inj hx e,char_two] at hp
  exact zero_ne_one hp

theorem hole_triangle {m : Mixer p n} {x y z : Orient p n N}
    (h1 : hole m x y) (h2 : hole m y z) : ¬ hole m x z := by
  intro h3
  obtain ⟨_,_,a,b,ha,hb,hab,u1,u2,p1⟩ := h1
  obtain ⟨_,_,c,d,hc,hd,hcd,u3,u4,p2⟩ := h2
  obtain ⟨_,_,e,f,he,hf,hef,u5,u6,p3⟩ := h3
  have hx : grad m b c = grad m f d := by rw [←u2 _ hc, ←u6 _ hd,hcd]
  have hy : grad m a e = grad m d f := by rw [←u1 _ he, ←u4 _ hf,hef]
  have hz : grad m e a = grad m c b := by rw [←u5 _ ha, ←u3 _ hb,hab]
  simp only [grad_val] at hx hy hz
  let A := role p n
  have hw (x y : F) (h : x=y) : x+y=0 := by rw [h,char_two]
  have hp : (A a+A b)+(A c+A d)+(A e+A f)=0 := by
    let H := Tsym m
    change A _ + H _ _ = A _ + H _ _ at hx hy hz
    calc (A a+A b)+(A c+A d)+(A e+A f)
      _ = ((A c+H b c)+(A d+H f d)) +
        ((A e+H a e)+(A f+H d f)) +
        ((A a+H e a)+(A b+H c b)) := by
          have h (x y) : H x y+H y x=0 := hw _ _ (T_swap m _ _)
          symm
          calc ((A c+H b c)+(A d+H f d)) +
            ((A e+H a e)+(A f+H d f)) +
            ((A a+H e a)+(A b+H c b))
            _ = ((A a+A b)+(A c+A d)+(A e+A f)) + (H b c+H c b) +
              (H f d+H d f)+(H a e+H e a) := by ac_rfl
            _ = _ := by simp only [h,add_zero]
      _ = 0 := by rw [hw _ _ hx, hw _ _ hy, hw _ _ hz]; simp
  unfold A at hp
  rw [p1,p2,p3,char_two,zero_add] at hp
  exact one_ne_zero hp

def rawHoles (m : Mixer p n) : Holes (Orient p n N) where
  rel := hole m
  sym := hole_sym
  irr := not_hole_self m
  ntri := hole_triangle

end HadwigerCounterexample

end

end OAI
