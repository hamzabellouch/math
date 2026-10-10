import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TensorProducts.FaithfulTensorCrossNorm
import OAI.Analysis.JiangSu.DimensionDrop.SequentialCStarInductiveLimit

namespace OAI


noncomputable section
open scoped TensorProduct CStarAlgebra

namespace Pureness.CStarAlgebraNorm
variable {R S : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  [Ring S] [StarRing S] [Algebra ℂ S]
def comapInjective (p : Pureness.CStarAlgebraNorm S) (e : R →⋆ₐ[ℂ] S)
    (he : Function.Injective e) : Pureness.CStarAlgebraNorm R where
  toFun x := p.toAlgebraNorm (e x)
  map_zero' := by simp
  add_le' x y := by rw [map_add]; exact map_add_le_add p.toAlgebraNorm (e x) (e y)
  neg' x := by simp
  mul_le' x y := by rw [map_mul]; exact map_mul_le_mul p.toAlgebraNorm (e x) (e y)
  eq_zero_of_map_eq_zero' x hx := he (by simpa using p.toAlgebraNorm.eq_zero_of_map_eq_zero' (e x) hx)
  smul' c x := by simp [map_smul_eq_mul]
  cstar x := by
    change p.toAlgebraNorm (e (star x*x))=p.toAlgebraNorm (e x)*p.toAlgebraNorm (e x)
    rw [map_mul,map_star]
    exact p.cstar (e x)
end Pureness.CStarAlgebraNorm

namespace SequentialCStar
open Pureness

universe u v
variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
variable (B : Type v) [CStarAlgebra B]

def leftStarTensor (f : A →⋆ₐ[ℂ] D) : A ⊗[ℂ] B →⋆ₐ[ℂ] D ⊗[ℂ] B :=
  { Algebra.TensorProduct.map f.toAlgHom (AlgHom.id ℂ B) with
    map_star' := by
      intro z
      change (Algebra.TensorProduct.map f.toAlgHom (AlgHom.id ℂ B)) (star z)=
        star ((Algebra.TensorProduct.map f.toAlgHom (AlgHom.id ℂ B)) z)
      induction z using TensorProduct.inductionOn with
      | tmul a b => simp only [TensorProduct.star_tmul,Algebra.TensorProduct.map_tmul,
          StarAlgHom.coe_toAlgHom,map_star,AlgHom.id_apply]
      | add x y hx hy => simp only [star_add,map_add,hx,hy] }

@[simp] lemma leftStarTensor_tmul (f : A →⋆ₐ[ℂ] D) (a : A) (b : B) :
    leftStarTensor B f (a ⊗ₜ[ℂ] b)=f a ⊗ₜ[ℂ] b := rfl

lemma leftStarTensor_injective (f : A →⋆ₐ[ℂ] D) (hf : Function.Injective f) :
    Function.Injective (leftStarTensor B f) :=
  Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf

lemma norm_tensor_sum_le (r : CStarAlgebraNorm (A ⊗[ℂ] B))
    {I : Type*} [Fintype I] (a : I → A) (b : I → B) :
    r.toAlgebraNorm (∑ i,a i ⊗ₜ[ℂ] b i)≤∑ i,‖a i‖*‖b i‖ := by
  rw [←r.completionMap_norm,map_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [r.completionMap_norm,NuclearUnitization.cstar_norm_tmul]

namespace System
variable {C : ℕ → Type u} [∀ n,CStarAlgebra (C n)] [∀ n,Nontrivial (C n)]
variable (S : System C)

lemma finite_family_common_stage {I : Type*} [Fintype I] (x : I → S.Limit)
    {ε : ℝ} (hε : 0<ε) :
    ∃ (n : ℕ) (a : I → C n),∀ i,‖x i-S.inclusion n (a i)‖<ε := by
  classical
  choose n a ha using fun i => S.finite_stage_approximation (x i) hε
  let N := Finset.univ.sup n
  have hN (i : I) : n i≤N := Finset.le_sup (f:=n) (Finset.mem_univ i)
  refine ⟨N,fun i => S.map (hN i) (a i),?_⟩
  intro i
  rw [S.inclusion_compatible]
  exact ha i

lemma nuclear_norm_eq_sum (hnuc : ∀ n,IsNuclear.{u,v} (C n))
    (r s : CStarAlgebraNorm (S.Limit ⊗[ℂ] B))
    {I : Type*} [Fintype I] (x : I → S.Limit) (b : I → B) :
    r.toAlgebraNorm (∑ i,x i ⊗ₜ[ℂ] b i)=s.toAlgebraNorm (∑ i,x i ⊗ₜ[ℂ] b i) := by
  classical
  suffices h : ∀ (p q : CStarAlgebraNorm (S.Limit ⊗[ℂ] B)),
      p.toAlgebraNorm (∑ i,x i ⊗ₜ[ℂ] b i)≤q.toAlgebraNorm (∑ i,x i ⊗ₜ[ℂ] b i) by
    exact le_antisymm (h r s) (h s r)
  intro p q
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/(2*(1+∑ i,‖b i‖))
  have hsum : 0≤∑ i,‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hd : 0<2*(1+∑ i,‖b i‖) := by positivity
  obtain ⟨n,a,ha⟩ := S.finite_family_common_stage x (div_pos hε hd : 0<δ)
  let z := ∑ i,x i ⊗ₜ[ℂ] b i
  let w := ∑ i,S.inclusion n (a i) ⊗ₜ[ℂ] b i
  have heq : p.toAlgebraNorm w=q.toAlgebraNorm w := by
    let e := leftStarTensor B (S.inclusion n)
    have he := leftStarTensor_injective B (S.inclusion n) (S.inclusion_isometry n).injective
    have h := (hnuc n B).elim (p.comapInjective e he) (q.comapInjective e he)
    have h' := congrArg (fun t : CStarAlgebraNorm (C n ⊗[ℂ] B) =>
      t.toAlgebraNorm (∑ i,a i ⊗ₜ[ℂ] b i)) h
    change p.toAlgebraNorm (e (∑ i,a i ⊗ₜ[ℂ] b i))=q.toAlgebraNorm (e (∑ i,a i ⊗ₜ[ℂ] b i)) at h'
    simpa only [e,map_sum,leftStarTensor_tmul] using h'
  have herr (t : CStarAlgebraNorm (S.Limit ⊗[ℂ] B)) : t.toAlgebraNorm (z-w)≤ε/2 := by
    have he : z-w=∑ i,(x i-S.inclusion n (a i)) ⊗ₜ[ℂ] b i := by
      simp only [z,w,TensorProduct.sub_tmul,Finset.sum_sub_distrib]
    rw [he]
    calc
      _ ≤ ∑ i,‖x i-S.inclusion n (a i)‖*‖b i‖ := norm_tensor_sum_le B t _ b
      _ ≤ ∑ i,δ*‖b i‖ := by gcongr with i; exact (ha i).le
      _ = δ*(∑ i,‖b i‖) := by rw [Finset.mul_sum]
      _ ≤ ε/2 := by
        dsimp [δ]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hd).mpr
        nlinarith
  have h1 : p.toAlgebraNorm z≤p.toAlgebraNorm (z-w)+p.toAlgebraNorm w := by
    simpa only [sub_add_cancel] using map_add_le_add p.toAlgebraNorm (z-w) w
  have h2 : q.toAlgebraNorm w≤q.toAlgebraNorm (z-w)+q.toAlgebraNorm z := by
    have hh := map_add_le_add q.toAlgebraNorm (w-z) z
    simpa only [sub_add_cancel,map_sub_rev q.toAlgebraNorm] using hh
  have hp := herr p
  have hq := herr q
  change p.toAlgebraNorm z≤q.toAlgebraNorm z+ε
  linarith

theorem nuclear (hnuc : ∀ n,IsNuclear.{u,v} (C n)) : IsNuclear.{u,v} S.Limit := by
  intro B _
  refine ⟨fun r s => ?_⟩
  have he : r.toAlgebraNorm=s.toAlgebraNorm := by
    apply AlgebraNorm.ext
    intro z
    obtain ⟨n,x,b,rfl⟩ := TensorProduct.exists_sum_tmul_eq z
    exact S.nuclear_norm_eq_sum B hnuc r s x b
  cases r; cases s; cases he; rfl

end System
end SequentialCStar

end


namespace JiangSuConstruction

def multiplicitiesOfLarge {p q : ℕ} (hp : 0<p) (hq : 0<q) (k l : ℕ)
    (hk : 8*q≤k) (hl : 8*p≤l) : Multiplicities p q := by
  let g := l/(4*p)
  let d := k/(4*q)
  let L := (p*k)*g
  let U := (q*l)*d
  let R := k*l-L-U
  have hkp : 0<k := by omega
  have hlp : 0<l := by omega
  have hgp : 0<g := Nat.div_pos (by omega) (by positivity)
  have hdp : 0<d := Nat.div_pos (by omega) (by positivity)
  have hg : (4*p)*g≤l := Nat.mul_div_le l (4*p)
  have hd : (4*q)*d≤k := Nat.mul_div_le k (4*q)
  have hg' : l<(4*p)*(g+1) := Nat.lt_mul_div_succ l (by positivity : 0<4*p)
  have hd' : k<(4*q)*(d+1) := Nat.lt_mul_div_succ k (by positivity : 0<4*q)
  have hg8 : l≤8*(p*g) := by nlinarith
  have hd8 : k≤8*(q*d) := by nlinarith
  have hL : 4*L≤k*l := by
    calc
      4*L=k*((4*p)*g) := by dsimp [L]; ring
      _≤k*l := Nat.mul_le_mul_left k hg
  have hU : 4*U≤k*l := by
    calc
      4*U=l*((4*q)*d) := by dsimp [U]; ring
      _≤k*l := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left l hd
  have hsum : L+U≤k*l := by omega
  have htotal : L+U+R=k*l := by dsimp [R]; omega
  have hRp : 0<R := by have hr : 0<k*l := Nat.mul_pos hkp hlp; omega
  have hpg : p*g≤l := by nlinarith
  have hqd : q*d≤k := by nlinarith
  refine ⟨k,l,L,U,R,g,d,hkp,hlp,hgp,hdp,hRp,rfl,rfl,htotal,?_,?_,?_,?_,?_,?_⟩
  · rw [Nat.mul_sub_left_distrib]
    have he : U=l*(q*d) := by dsimp [U]; ring
    have hr : k*l=l*k := Nat.mul_comm k l
    omega
  · rw [Nat.mul_sub_left_distrib]
    have he : L=k*(p*g) := by dsimp [L]; ring
    omega
  · rw [Nat.mul_sub_left_distrib]
    have he : p*(q*d)=(p*q)*d := by ring
    have hc := Nat.mul_le_mul_left p hqd
    omega
  · rw [Nat.mul_sub_left_distrib]
    have he : q*(p*g)=(p*q)*g := by ring
    have hc := Nat.mul_le_mul_left q hpg
    omega
  · calc
      k*l≤k*(8*(p*g)) := Nat.mul_le_mul_left k hg8
      _=8*L := by dsimp [L]; ring
  · calc
      k*l≤l*(8*(q*d)) := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left l hd8
      _=8*U := by dsimp [U]; ring

def canonicalMultiplicities {p q : ℕ} (hp : 0<p) (hq : 0<q) : Multiplicities p q :=
  multiplicitiesOfLarge hp hq (2^(8*q)) (3^(8*p))
    (Nat.lt_two_pow_self (n := 8*q)).le
    (Nat.lt_pow_self (n := 8*p) (by decide : 1<3)).le

end JiangSuConstruction

end OAI
