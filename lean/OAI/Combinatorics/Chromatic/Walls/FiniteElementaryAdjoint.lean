import Mathlib
import OAI.Combinatorics.Chromatic.Walls.CompletedInverse
import OAI.Combinatorics.Chromatic.Walls.QuantumTorusRaySeries

namespace OAI

section
namespace ElementaryPositivity.WallUnits
open PowerSeries
noncomputable section
variable {R : Type*} [CommRing R]
def DegreeBound (d : ℕ) (f : PowerSeries R) : Prop := ∀ n,d<n → coeff n f=0
lemma degreeBound_one : DegreeBound 0 (1 : PowerSeries R) := by
  intro n hn
  rw [coeff_one,ite_eq_right (by omega)]
lemma degreeBound_linear (u : R) : DegreeBound 1 (1+PowerSeries.C u*PowerSeries.X) := by
  intro n hn
  rw [map_add,coeff_one,ite_eq_right (by omega),coeff_C_mul,coeff_X,ite_eq_right (by omega),mul_zero,add_zero]
lemma DegreeBound.mul {d e : ℕ} {f g : PowerSeries R} (hf : DegreeBound d f)
    (hg : DegreeBound e g) : DegreeBound (d+e) (f*g) := by
  intro n hn
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have heq:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h : d<p.1
  · rw [hf p.1 h,zero_mul]
  · rw [hg p.2 (by omega),mul_zero]
lemma degreeBound_product_linear (u : ℕ → R) (t : ℕ) :
    DegreeBound t (∏i∈Finset.range t,(1+PowerSeries.C (u i)*PowerSeries.X)) := by
  induction t with
  | zero=>simpa using (degreeBound_one (R:=R))
  | succ t ih=>
    rw [Finset.prod_range_succ]
    exact ih.mul (degreeBound_linear (u t))
lemma DegreeBound.rescale {d : ℕ} {f : PowerSeries R} (hf : DegreeBound d f) (u : R) :
    DegreeBound d (PowerSeries.rescale u f) := by
  intro n hn
  rw [coeff_rescale,hf n hn,mul_zero]
end
section
variable {K : Type*} [Field K]
lemma elementary_ratio_degree (q u : K) (hq : q≠0)
    (hq' : ∀n : ℕ,1-q^(n+1)≠0) (t : ℕ) :
    DegreeBound t (PowerSeries.rescale (q⁻¹^t) (elementary q u)*(elementary q u)⁻¹) := by
  rw [elementary_ratio q u hq hq' t]
  exact degreeBound_product_linear _ t
lemma elementary_inverse_ratio_degree (q u : K) (hq : q≠0)
    (hq' : ∀n : ℕ,1-q^(n+1)≠0) (t : ℕ) :
    DegreeBound t (PowerSeries.rescale (q^t) (elementary q u)⁻¹*elementary q u) := by
  have he : PowerSeries.rescale (q^t) (elementary q u)⁻¹*elementary q u=
      PowerSeries.rescale (q^t) (PowerSeries.rescale (q⁻¹^t) (elementary q u)*(elementary q u)⁻¹) := by
    rw [map_mul,PowerSeries.rescale_rescale,←mul_pow,inv_mul_cancel₀ hq,one_pow,
      PowerSeries.rescale_one,RingHom.id_apply,mul_comm]
  rw [he]
  exact (elementary_ratio_degree q u hq hq' t).rescale _
end
end ElementaryPositivity.WallUnits
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)
lemma monomial_ray_support (a m x : M) (f : PowerSeries K) (t N : ℕ)
    (hf : DegreeBound t f)
    (hx : coeff N (PowerSeries.C (Torus.X v Ω m)*raySeries v Ω a f) x≠0) :
    N≤t ∧ x=m+N • a := by
  rw [coeff_C_mul,coeff_raySeries,Torus.X,Torus.monomial_mul_monomial,one_mul] at hx
  constructor
  · by_contra h
    rw [hf N (by omega),zero_mul,Torus.monomial_zero] at hx
    exact hx rfl
  · by_contra h
    exact hx (Finsupp.single_eq_of_ne h)
lemma elementary_adjoint_support (hΩ : ∀m,Ω m m=0) (a m x : M)
    (q u : K) (hq : q≠0) (hq' : ∀n : ℕ,1-q^(n+1)≠0) (t N : ℕ)
    (hshift : (↑(v^(2*Ω a m)):K)=q⁻¹^t)
    (hx : coeff N ((rayUnit v Ω a (hΩ a) (elementary q u) (constant_elementary _ _)).val *
      PowerSeries.C (Torus.X v Ω m)*
      (rayUnit v Ω a (hΩ a) (elementary q u) (constant_elementary _ _)).inv) x≠0) :
    N≤t ∧ x=m+N • a := by
  rw [ray_adjoint v Ω hΩ,hshift] at hx
  exact monomial_ray_support v Ω a m x _ t N (elementary_ratio_degree q u hq hq' t) hx
lemma elementary_inverse_adjoint_support (hΩ : ∀m,Ω m m=0) (a m x : M)
    (q u : K) (hq : q≠0) (hq' : ∀n : ℕ,1-q^(n+1)≠0) (t N : ℕ)
    (hshift : (↑(v^(2*Ω a m)):K)=q^t)
    (hx : coeff N ((rayUnit v Ω a (hΩ a) (elementary q u) (constant_elementary _ _)).inv *
      PowerSeries.C (Torus.X v Ω m)*
      (rayUnit v Ω a (hΩ a) (elementary q u) (constant_elementary _ _)).val) x≠0) :
    N≤t ∧ x=m+N • a := by
  rw [ray_inverse_adjoint v Ω hΩ,hshift] at hx
  exact monomial_ray_support v Ω a m x _ t N (elementary_inverse_ratio_degree q u hq hq' t) hx
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
lemma inverse_inverse (F : PowerSeries A) (hF : constantCoeff F=1) :
    invOfUnit (invOfUnit F 1) 1=F := by
  have hI : constantCoeff (invOfUnit F 1)=1:=by simp
  calc
    _=invOfUnit (invOfUnit F 1) 1*((invOfUnit F 1)*F):=by rw [invOfUnit_mul F 1 hF,mul_one]
    _=(invOfUnit (invOfUnit F 1) 1*(invOfUnit F 1))*F:=by rw [mul_assoc]
    _=F:=by rw [invOfUnit_mul _ 1 hI,one_mul]
lemma adjoint_one (X : PowerSeries A) : adjoint 1 X=X := by
  have hI : invOfUnit (1:PowerSeries A) 1=1:=by
    have H:=mul_invOfUnit (1:PowerSeries A) 1 (by simp)
    simpa using H
  simp only [adjoint,one_mul,hI,mul_one]
lemma adjoint_inverse (F X : PowerSeries A) (hF : constantCoeff F=1) :
    adjoint (invOfUnit F 1) X=invOfUnit F 1*X*F := by rw [adjoint,inverse_inverse F hF]
lemma adjoint_inverse_cancel (F X : PowerSeries A) (hF : constantCoeff F=1) :
    adjoint (invOfUnit F 1) (adjoint F X)=X := by
  rw [←adjoint_mul _ _ _ (by simp) hF,invOfUnit_mul F 1 hF,adjoint_one]
lemma adjoint_inverse_coeff (F X Y : PowerSeries A) (hF : constantCoeff F=1) (N : ℕ)
    (hXY : ∀n≤N,coeff n X=coeff n (adjoint F Y)) :
    coeff N (adjoint (invOfUnit F 1) X)=coeff N Y := by
  rw [adjoint_coeff_congr _ _ _ _ N (fun _ _=>rfl) hXY,adjoint_inverse_cancel F Y hF]
end
end ElementaryPositivity.PowerSeriesAdjoint

end

end OAI
