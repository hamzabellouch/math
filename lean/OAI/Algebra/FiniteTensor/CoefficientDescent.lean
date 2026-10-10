import Mathlib
import OAI.Algebra.FiniteTensor.BoxCoefficients

namespace OAI

/-! Exact coefficient descent of formal tensor models. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
universe u
variable {K : Type*} [Field K] {l m : ℕ} {σ : Fin l → Type u}
  [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)]
  {d c : ℕ} {e : ((i : Fin l) × σ i) ≃ Fin d ⊕ Fin c} {active : Fin m ↪ Fin l}

structure CoefficientsIn (R : Subring K) (M : TensorModel K σ m d c e active)
    (W : TensorPrimitives K σ m M) : Prop where
  F : ∀ i b,MvPowerSeries.coeff b (M.F i)∈R
  b : ∀ i a,MvPowerSeries.coeff a (M.b i)∈R
  H : ∀ v q b,MvPowerSeries.coeff b (boxSeries K m q (M.H v))∈R
  G : ∀ v b,MvPowerSeries.coeff b (M.G v)∈R
  left : ∀ t v q b,MvPowerSeries.coeff b (boxSeries K m q (W.left t v))∈R
  right : ∀ t v b,MvPowerSeries.coeff b (W.right t v)∈R
  det_inv : (tangent K σ m e M.H M.G).det⁻¹∈R

 theorem injective_map_series {A B τ : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (MvPowerSeries.map (σ:=τ) f) := by
  intro x y h
  ext a
  apply hf
  exact congrArg (MvPowerSeries.coeff a) h

 

def descendTensorModel (R : Subring K) (M : TensorModel K σ m d c e active)
    (W : TensorPrimitives K σ m M) (h : CoefficientsIn R M W) :
    TensorModel R σ m d c e active := by
  let F := fun i => MvPowerSeries.toSubring (M.F i) R (h.F i)
  let b := fun i => MvPowerSeries.toSubring (M.b i) R (h.b i)
  let H := fun v => liftParameterSeries R (M.H v) (h.H v)
  let G := fun v => MvPowerSeries.toSubring (M.G v) R (h.G v)
  let L := fun t v => liftParameterSeries R (W.left t v) (h.left t v)
  let U := fun t v => MvPowerSeries.toSubring (W.right t v) R (h.right t v)
  have hF : ∀ i,MvPowerSeries.map R.subtype (F i)=M.F i := fun _ => rfl
  have hb : ∀ i,MvPowerSeries.map R.subtype (b i)=M.b i := fun _ => rfl
  have hH : ∀ v,MvPowerSeries.map (mapParameters R.subtype) (H v)=M.H v :=
    fun v => map_liftParameterSeries R (M.H v) (h.H v)
  have hG : ∀ v,MvPowerSeries.map R.subtype (G v)=M.G v := fun _ => rfl
  have hL : ∀ t v,MvPowerSeries.map (mapParameters R.subtype) (L t v)=W.left t v :=
    fun t v => map_liftParameterSeries R (W.left t v) (h.left t v)
  have hU : ∀ t v,MvPowerSeries.map R.subtype (U t v)=W.right t v := fun _ _ => rfl
  have H0 : ∀ v,MvPowerSeries.constantCoeff (H v)∈parameterIdeal R m := by
    intro v
    apply (mapParameters_mem_iff R.subtype Subtype.val_injective _).mp
    have hh := congrArg MvPowerSeries.constantCoeff (hH v)
    rw [MvPowerSeries.constantCoeff_map] at hh
    rw [hh]
    exact M.H_zero v
  have G0 : ∀ v,MvPowerSeries.constantCoeff (G v)=0 := by
    intro v
    apply Subtype.val_injective
    exact M.G_zero v
  have Hsub := hasSubst_parameters R m H H0
  have Gsub := MvPowerSeries.hasSubst_of_constantCoeff_zero G0
  have hdet : R.subtype (tangent R σ m e H G).det=(tangent K σ m e M.H M.G).det := by
    rw [R.subtype.map_det]
    change ((tangent R σ m e H G).map R.subtype).det=_
    rw [map_tangent]
    simp only [hH,hG]
  have hunit : IsUnit (tangent R σ m e H G).det := by
    let v : R := ⟨(tangent K σ m e M.H M.G).det⁻¹,h.det_inv⟩
    have hn := isUnit_iff_ne_zero.mp M.tangent_unit
    have h1 : (tangent R σ m e H G).det*v=1 := by
      apply Subtype.val_injective
      change R.subtype (tangent R σ m e H G).det*(tangent K σ m e M.H M.G).det⁻¹=1
      rw [hdet,mul_inv_cancel₀ hn]
    exact ⟨⟨(tangent R σ m e H G).det,v,h1,by simpa only [mul_comm] using h1⟩,rfl⟩
  refine {
    F := F,b := b,H := H,G := G,H_zero := H0,G_zero := G0,tangent_unit := hunit
    F_zero := ?_,b_zero := ?_,left_vanishing := ?_,right_vanishing := ?_
    left_triple := ?_,right_triple := ?_ }
  · intro i
    apply Subtype.val_injective
    exact M.F_zero i
  · intro i
    apply Subtype.val_injective
    exact M.b_zero i
  · apply injective_map_series (mapParameters R.subtype) (mapParameters_injective R.subtype Subtype.val_injective)
    simpa only [MvPowerSeries.map_subst Hsub,map_deformed,hH,hF,hb,map_zero] using M.left_vanishing
  · apply injective_map_series R.subtype Subtype.val_injective
    simpa only [MvPowerSeries.map_subst Gsub,map_potential,hG,hF,map_zero] using M.right_vanishing
  · intro i j k hij hik hjk
    let q : Triple m := ⟨(i,j,k),hij,hik,hjk⟩
    apply Ideal.mem_span_range_iff_exists_fun.mpr
    refine ⟨L q,?_⟩
    apply injective_map_series (mapParameters R.subtype) (mapParameters_injective R.subtype Subtype.val_injective)
    simp only [map_sum,map_mul,hL,MvPowerSeries.map_subst Hsub,PD4Tensor.map_formal_pderiv,
      map_deformed,hH,hF,hb,MvPowerSeries.map_C,mapParameters_parameter]
    simpa only [map_mul] using W.left_eq q
  · intro i j k hij hik hjk
    let q : Triple m := ⟨(i,j,k),hij,hik,hjk⟩
    apply Ideal.mem_span_range_iff_exists_fun.mpr
    refine ⟨U q,?_⟩
    apply injective_map_series R.subtype Subtype.val_injective
    simp only [map_sum,map_mul,hU,MvPowerSeries.map_subst Gsub,PD4Tensor.map_formal_pderiv,
      map_potential,hG,hF,map_perturbation,hb]
    exact W.right_eq q

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
open scoped BigOperators
open Finsupp
variable {K σ : Type*} [Field K]

def seriesOver (A : Subring K) : Subring (MvPowerSeries σ K) :=
  (MvPowerSeries.map A.subtype).range

 theorem mem_seriesOver (A : Subring K) (F : MvPowerSeries σ K) :
    F∈seriesOver A ↔ ∀ d,MvPowerSeries.coeff d F∈A := by
  constructor
  · rintro ⟨G,rfl⟩ d
    exact (MvPowerSeries.coeff d G).property
  · intro h
    exact ⟨MvPowerSeries.toSubring F A h,rfl⟩

variable [LinearOrder σ] [WellFoundedGT σ]

 

theorem coefficients_of_product (A : Subring K) (D H : MvPowerSeries σ K)
    (a : σ →₀ ℕ) (ha : MvPowerSeries.coeff a D≠0)
    (hmin : ∀ u,toLex u<toLex a → MvPowerSeries.coeff u D=0)
    (hD : ∀ u,MvPowerSeries.coeff u D∈A)
    (hinv : (MvPowerSeries.coeff a D)⁻¹∈A)
    (hDH : ∀ u,MvPowerSeries.coeff u (D*H)∈A) :
    ∀ b,MvPowerSeries.coeff b H∈A := by
  classical
  suffices hh : ∀ b : Lex (σ →₀ ℕ),MvPowerSeries.coeff (ofLex b) H∈A by
    intro b
    exact hh (toLex b)
  intro b
  refine (wellFounded_lt : WellFounded ((· < ·) : Lex (σ →₀ ℕ) → _ → Prop)).induction (C := fun b : Lex (σ →₀ ℕ) => MvPowerSeries.coeff (ofLex b) H∈A) b ?_
  intro b ih
  let c := ofLex b
  have hin : (a,c)∈Finset.HasAntidiagonal.antidiagonal (a+c) := by simp
  have hsum : (∑ uv∈(Finset.HasAntidiagonal.antidiagonal (a+c)).erase (a,c),
      MvPowerSeries.coeff uv.1 D*MvPowerSeries.coeff uv.2 H)∈A := by
    apply A.sum_mem
    rintro ⟨u,v⟩ huv
    have huv' := (Finset.mem_erase.mp huv).2
    have hn := (Finset.mem_erase.mp huv).1
    have heq : u+v=a+c := Finset.HasAntidiagonal.mem_antidiagonal.mp huv'
    by_cases hu : toLex u<toLex a
    · rw [hmin u hu,zero_mul]
      exact A.zero_mem
    · have hau : toLex a<toLex u := by
        apply lt_of_le_of_ne (le_of_not_gt hu)
        intro he
        have hua : u=a := congrArg ofLex he.symm
        have hvc : v=c := by simpa only [hua,add_right_inj] using heq
        exact hn (Prod.ext hua hvc)
      have hvc : toLex v<toLex c := by
        have haux : toLex a+toLex v < toLex u+toLex v := by simpa only [add_comm] using add_lt_add_right hau (toLex v)
        rw [←toLex_add,←toLex_add,heq,toLex_add] at haux
        exact (add_lt_add_iff_left (toLex a)).mp haux
      exact A.mul_mem (hD u) (ih (toLex v) (by simpa only [c,toLex_ofLex] using hvc))
  have hprod : MvPowerSeries.coeff a D*MvPowerSeries.coeff c H∈A := by
    have hh := A.sub_mem (hDH (a+c)) hsum
    rw [MvPowerSeries.coeff_mul,←Finset.sum_erase_add _ _ hin] at hh
    simpa only [add_sub_cancel_left] using hh
  have hh := A.mul_mem hinv hprod
  simpa only [←mul_assoc,inv_mul_cancel₀ ha,one_mul,c] using hh

end PD4Tensor.Spreading
end

end OAI
