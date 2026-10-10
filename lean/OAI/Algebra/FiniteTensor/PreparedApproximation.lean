import Mathlib
import OAI.Algebra.FiniteTensor.JacobianAlgebraicity
import OAI.Algebra.FiniteTensor.PreparedCoefficients

namespace OAI

/-! Fixed-jet approximation of prepared systems and the aligned Artin step. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

 
theorem adic_complete_power (I : Ideal R) [IsAdicComplete I M]
    (c : ℕ) (hc : 0<c) : IsAdicComplete (I^c) M := by
  have hcn (n : ℕ) : n≤c*n := Nat.le_mul_of_pos_left n hc
  let : IsHausdorff (I^c) M := by
    constructor
    intro x hx
    apply IsHausdorff.haus' (I:=I) x
    intro n
    apply SModEq.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right (hcn n)))
    simpa only [←pow_mul] using hx n
  let : IsPrecomplete (I^c) M := by
    constructor
    intro f hf
    have hfI : ∀ {m n},m≤n→f m ≡ f n [SMOD (I^m • ⊤ : Submodule R M)] := by
      intro m n hmn
      apply SModEq.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right (hcn m)))
      simpa only [←pow_mul] using hf hmn
    obtain ⟨L,hL⟩ := IsPrecomplete.prec (I:=I) inferInstance hfI
    refine ⟨L,fun n=>?_⟩
    have h1 := hf (hcn n)
    have h2 := hL (c*n)
    rw [←pow_mul] at h1 ⊢
    exact h1.trans h2
  exact IsAdicComplete.mk

end
end PD4Tensor.Spreading

 

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
open scoped Matrix
variable {K τ σ ρ : Type*} [Field K] [Finite τ] [Fintype σ] [DecidableEq σ] [Fintype ρ] [DecidableEq ρ]

 

omit [Fintype ρ] [DecidableEq ρ] in
theorem prepared_algebraic_approximation
    (f : σ → MvPolynomial (σ ⊕ ρ) (MvPowerSeries τ K))
    (hcoeff : ∀ k d,IsAlgebraic (MvPolynomial τ K) ((f k).coeff d))
    (a u : (σ ⊕ ρ) → MvPowerSeries τ K)
    (ha : ∀ k,eval a (f k)=0)
    (hu : ∀ i : ρ,IsAlgebraic (MvPolynomial τ K) (u (Sum.inr i)))
    (n : ℕ)
    (hJ : Matrix.det (fun k i=>eval u (pderiv (Sum.inl i) (f k)))≠0)
    (hclose : ∀ i,u i-a i∈(jetIdeal (K:=K) (σ:=τ))^
      ((Matrix.det (fun k i=>eval u (pderiv (Sum.inl i) (f k)))^2).order.toNat+(n+1)))
    (hdiv : ∀ k,(Matrix.det (fun k i=>eval u (pderiv (Sum.inl i) (f k)))^2)∣eval u (f k)) :
    ∃ b : (σ ⊕ ρ) → MvPowerSeries τ K,(∀ k,eval b (f k)=0) ∧
      (∀ i,IsAlgebraic (MvPolynomial τ K) (b i)) ∧
      (∀ i : ρ,b (Sum.inr i)=u (Sum.inr i)) ∧
      ∀ i,b i-a i∈(jetIdeal (K:=K) (σ:=τ))^n := by
  let δ := Matrix.det (fun k i=>eval u (pderiv (Sum.inl i) (f k)))
  let J : Ideal (MvPowerSeries τ K) := jetIdeal
  let I := J^(n+1)
  have hδ : δ^2≠0 := pow_ne_zero _ hJ
  choose e he using hdiv
  have heI (k : σ) : e k∈I := by
    apply quotient_jet_control hδ (n+1)
    change δ^2*e k∈J^((δ^2).order.toNat+(n+1))
    rw [←he k]
    simpa only [ha,sub_zero] using mv_eval_sub_mem _ (f k) u a hclose
  let : IsAdicComplete I (MvPowerSeries τ K) :=
    adic_complete_power J (n+1) (Nat.succ_pos n)
  obtain ⟨b,hb,halg,hfree,hbu⟩ := algebraic_rectangular_tougeron I f hcoeff u hu e heI hJ he
  refine ⟨b,hb,halg,hfree,fun i=>?_⟩
  have hsmall : I≤J^n := Ideal.pow_le_pow_right (Nat.le_succ n)
  have hlarge : J^((δ^2).order.toNat+(n+1))≤J^n :=
    Ideal.pow_le_pow_right (by omega)
  have hua : u i-a i∈J^n := hlarge (hclose i)
  have hbi : b i-u i∈J^n := by
    cases i with
    | inl i =>
      obtain ⟨v,hv,hvEq⟩ := hbu i
      rw [hvEq,add_sub_cancel_left]
      exact hsmall (I.mul_mem_left _ hv)
    | inr i => simpa only [hfree,sub_self] using (J^n).zero_mem
  convert (J^n).add_mem hbi hua using 1
  abel

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPowerSeries
variable {K τ : Type*} [CommRing K] [Finite τ]

 

theorem order_eq_of_close_jet {f g : MvPowerSeries τ K} (hf : f≠0)
    (hclose : g-f∈(jetIdeal (K:=K) (σ:=τ))^(f.order.toNat+1)) :
    g.order=f.order := by
  have ho := (ne_zero_iff_order_finite.mp hf).symm
  have hh := (mem_jetIdeal_pow_iff_order _ _).mp hclose
  have hlt : f.order<(g-f).order := by
    apply lt_of_lt_of_le _ hh
    rw [ho]
    exact_mod_cast Nat.lt_succ_self f.order.toNat
  have he : f+(g-f)=g := by abel
  rw [←he,order_add_of_order_ne (ne_of_lt hlt),inf_eq_left.mpr (le_of_lt hlt)]

 theorem ne_zero_of_close_jet {f g : MvPowerSeries τ K} (hf : f≠0)
    (hclose : g-f∈(jetIdeal (K:=K) (σ:=τ))^(f.order.toNat+1)) : g≠0 := by
  intro hg
  have he := order_eq_of_close_jet hf hclose
  rw [hg,order_zero] at he
  exact hf (order_eq_top_iff.mp he.symm)

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
open scoped Matrix
variable {K τ σ ρ : Type*} [Field K] [Finite τ] [Fintype σ] [DecidableEq σ]
  [Fintype ρ] [DecidableEq ρ]

 

omit [Fintype ρ] [DecidableEq ρ] in
theorem fixed_jet_prepared_approximation
    (f : σ → MvPolynomial (σ ⊕ ρ) (MvPowerSeries τ K))
    (hcoeff : ∀ k d,IsAlgebraic (MvPolynomial τ K) ((f k).coeff d))
    (a u : (σ ⊕ ρ) → MvPowerSeries τ K)
    (ha : ∀ k,eval a (f k)=0)
    (hu : ∀ i : ρ,IsAlgebraic (MvPolynomial τ K) (u (Sum.inr i)))
    (n : ℕ)
    (hJ : Matrix.det (fun k i=>eval a (pderiv (Sum.inl i) (f k)))≠0)
    (hclose : ∀ i,u i-a i∈(jetIdeal (K:=K) (σ:=τ))^
      (2*(Matrix.det (fun k i=>eval a (pderiv (Sum.inl i) (f k)))).order.toNat+n+1))
    (hdiv : ∀ k,(Matrix.det (fun k i=>eval u (pderiv (Sum.inl i) (f k)))^2)∣eval u (f k)) :
    ∃ b : (σ ⊕ ρ) → MvPowerSeries τ K,(∀ k,eval b (f k)=0) ∧
      (∀ i,IsAlgebraic (MvPolynomial τ K) (b i)) ∧
      (∀ i : ρ,b (Sum.inr i)=u (Sum.inr i)) ∧
      ∀ i,b i-a i∈(jetIdeal (K:=K) (σ:=τ))^n := by
  let δ := Matrix.det (fun k i=>eval a (pderiv (Sum.inl i) (f k)))
  let δ' := Matrix.det (fun k i=>eval u (pderiv (Sum.inl i) (f k)))
  let J := jetIdeal (K:=K) (σ:=τ)
  have hc : ∀ i,u i-a i∈J^(δ.order.toNat+1) := fun i=>
    Ideal.pow_le_pow_right (by dsimp [δ]; omega) (hclose i)
  have hd : δ'-δ∈J^(δ.order.toNat+1) := by
    let approxJacobian : Matrix σ σ (MvPowerSeries τ K) :=
      fun row col=>eval u (pderiv (Sum.inl col) (f row))
    let baseJacobian : Matrix σ σ (MvPowerSeries τ K) :=
      fun row col=>eval a (pderiv (Sum.inl col) (f row))
    change approxJacobian.det-baseJacobian.det∈_
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub,sub_eq_zero,RingHom.map_det,RingHom.map_det]
    congr 1
    ext row col
    apply Ideal.Quotient.eq.mpr
    exact mv_eval_sub_mem _ (pderiv (Sum.inl col) (f row)) u a hc
  have hn : δ'≠0 := ne_zero_of_close_jet hJ hd
  have ho : δ'.order=δ.order := order_eq_of_close_jet hJ hd
  have hsq : (δ'^2).order.toNat=2*δ.order.toNat := by
    rw [pow_two,MvPowerSeries.order_mul,ho]
    rw [←(MvPowerSeries.ne_zero_iff_order_finite.mp hJ)]
    rw [←ENat.natCast_add]
    simp only [ENat.toNat_natCast]
    omega
  apply prepared_algebraic_approximation f hcoeff a u ha hu n hn _ hdiv
  intro i
  change u i-a i∈J^((δ'^2).order.toNat+(n+1))
  rw [hsq]
  simpa only [Nat.add_assoc] using hclose i

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
variable {K τ σ ρ : Type*} [Field K] [Finite τ]
  [Fintype σ] [DecidableEq σ] [Fintype ρ] [DecidableEq ρ]

theorem minorPolynomial_map {R S ι υ : Type*} [CommRing R] [CommRing S]
    [Fintype ι] [DecidableEq ι] (φ : R →+* S)
    (f : ι → MvPolynomial (ι ⊕ υ) R) :
    map φ (minorPolynomial f)=minorPolynomial (fun k=>map φ (f k)) := by
  unfold minorPolynomial
  calc
    _ = Matrix.det ((map φ).mapMatrix (fun k i=>pderiv (Sum.inl i) (f k))) :=
      RingHom.map_det (map φ) _
    _ = _ := by
      congr 1
      funext k i
      exact (pderiv_map).symm

 

omit [DecidableEq ρ] in
theorem aligned_artin_step
    (ih : PolynomialArtinAt K τ)
    (f : σ → MvPolynomial (σ ⊕ ρ) (Polynomial (MvPolynomial τ K)))
    (a : (σ ⊕ ρ) → PowerSeries (MvPowerSeries τ K))
    (ha : ∀ k,eval a (map (seriesCoefficientMap (B:=MvPolynomial τ K)
      (A:=MvPowerSeries τ K)) (f k))=0)
    (hreg : (eval a (map (seriesCoefficientMap (B:=MvPolynomial τ K)
      (A:=MvPowerSeries τ K)) (minorPolynomial f))).map
        (IsLocalRing.residue (MvPowerSeries τ K))≠0)
    (hnonunit : ¬IsUnit (eval a (map (seriesCoefficientMap (B:=MvPolynomial τ K)
      (A:=MvPowerSeries τ K)) (minorPolynomial f)))) (n : ℕ) :
    ∃ b : (σ ⊕ ρ) → PowerSeries (MvPowerSeries τ K),
      (∀ k,eval b (map (seriesCoefficientMap (B:=MvPolynomial τ K)
        (A:=MvPowerSeries τ K)) (f k))=0) ∧
      (∀ i,IsAlgebraic (Polynomial (MvPolynomial τ K)) (b i)) ∧
      ∀ i,(MvPowerSeries.optionEquivLeft τ K).symm (b i-a i)∈
        (jetIdeal (K:=K) (σ:=Option τ))^n := by
  let A := MvPowerSeries τ K
  let E := MvPowerSeries.optionEquivLeft τ K
  let F := fun k=>map (seriesCoefficientMap (B:=MvPolynomial τ K) (A:=A)) (f k)
  let G := fun k=>map E.symm.toRingHom (F k)
  let a' := fun i=>E.symm (a i)
  let δ := eval a (map (seriesCoefficientMap (B:=MvPolynomial τ K) (A:=A)) (minorPolynomial f))
  have hδ : δ≠0 := by
    intro h
    apply hreg
    change δ.map _=0
    simp [h]
  have hev (q : MvPolynomial (σ ⊕ ρ) (PowerSeries A))
      (v : (σ ⊕ ρ) → PowerSeries A) :
      eval (fun i=>E.symm (v i)) (map E.symm.toRingHom q)=E.symm (eval v q) := by
    rw [←eval₂_eq_eval_map]
    exact (hom_eval₂ q (RingHom.id _) E.symm.toRingHom v).symm
  have hFeval (v : (σ ⊕ ρ) → PowerSeries A) (k : σ) :
      eval (fun i=>E.symm (v i)) (G k)=E.symm (eval v (F k)) := hev (F k) v
  have hpoly : minorPolynomial G=map E.symm.toRingHom
      (map (seriesCoefficientMap (B:=MvPolynomial τ K) (A:=A)) (minorPolynomial f)) := by
    rw [minorPolynomial_map,minorPolynomial_map]
  have hminor (v : (σ ⊕ ρ) → PowerSeries A) :
      Matrix.det (fun k i=>eval (fun j=>E.symm (v j)) (pderiv (Sum.inl i) (G k)))=
        E.symm (eval v (map (seriesCoefficientMap (B:=MvPolynomial τ K) (A:=A)) (minorPolynomial f))) := by
    rw [←eval_minorPolynomial,hpoly,hev]
  have hGa (k : σ) : eval a' (G k)=0 := by
    rw [hFeval,ha,map_zero]
  have hGcoeff (k : σ) (d) : IsAlgebraic (MvPolynomial (Option τ) K) ((G k).coeff d) := by
    simp only [G,F,coeff_map]
    apply algebraic_option_series_symm
    apply polynomial_series_algebraic_coefficients
    intro m
    change IsAlgebraic (MvPolynomial τ K) ((((f k).coeff d).map (algebraMap (MvPolynomial τ K) A)).coeff m)
    rw [Polynomial.coeff_map]
    exact isAlgebraic_algebraMap (((f k).coeff d).coeff m)
  have hJa : Matrix.det (fun k i=>eval a' (pderiv (Sum.inl i) (G k)))≠0 := by
    rw [hminor]
    exact E.symm.injective.ne (by exact hδ)
  let N := 2*(E.symm δ).order.toNat+n+1
  obtain ⟨u,hu,hun,hdiv,hclose⟩ := regular_coefficient_prepared ih f (minorPolynomial f)
    a ha hreg hnonunit N (by dsimp [N]; omega)
  obtain ⟨b,hb,hbalg,hfree,hba⟩ := fixed_jet_prepared_approximation G hGcoeff a'
    (fun i=>E.symm (u i)) hGa
    (fun i=>algebraic_option_series_symm (hu (Sum.inr i))) n hJa
    (by
      intro i
      rw [hminor]
      simpa only [a',←map_sub] using hclose i)
    (by
      intro k
      rw [hminor,hFeval]
      have hd := map_dvd E.symm.toRingHom (hdiv k)
      change E.symm (_^2)∣E.symm (eval u (F k)) at hd
      rwa [map_pow] at hd)
  refine ⟨fun i=>E (b i),?_,fun i=>algebraic_option_series (hbalg i),?_⟩
  · intro k
    apply E.symm.injective
    rw [map_zero]
    rw [←hFeval]
    simpa only [AlgEquiv.symm_apply_apply] using hb k
  · intro i
    change E.symm (E (b i)-a i)∈_
    simpa only [map_sub,AlgEquiv.symm_apply_apply,a'] using hba i

end
end PD4Tensor.Spreading
end

end OAI
