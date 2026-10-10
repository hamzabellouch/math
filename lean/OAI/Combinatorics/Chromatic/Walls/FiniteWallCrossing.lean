import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FiniteElementaryAdjoint
import OAI.Combinatorics.Chromatic.QuantumTorus.SectionMonomialExpansion
import OAI.Combinatorics.Chromatic.Walls.IsotropicLiteralPositive

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits LaurentPrecision Filter RootTruncation
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
lemma inverse_adjoint_coeff_congr (F G X : PowerSeries (Torus LaurentRay.vUnit Ω)) (N : ℕ)
    (h : ∀n≤N,coeff n F=coeff n G) :
    coeff N (invOfUnit F 1*X*F)=coeff N (invOfUnit G 1*X*G) := by
  apply FormalLog.mul_coeff_congr
  · intro j hj
    exact FormalLog.mul_coeff_congr _ _ _ _ j
      (fun k hk=>PowerSeriesAdjoint.inverse_coeff_congr F G j
        (fun t ht=>h t (ht.trans hj)) k hk) (fun _ _=>rfl)
  · exact h
lemma cut_adjoint_coeff (F X : PowerSeries (Torus LaurentRay.vUnit Ω)) (N n : ℕ) (hn : n≤N) :
    coeff n (PowerSeriesAdjoint.adjoint (cut N F) X)=coeff n (PowerSeriesAdjoint.adjoint F X) :=
  PowerSeriesAdjoint.adjoint_coeff_congr _ _ _ _ n
    (fun j hj=>by rw [coeff_cut,ite_eq_left (hj.trans hn)]) (fun _ _=>rfl)
lemma cut_inverse_adjoint_coeff (F X : PowerSeries (Torus LaurentRay.vUnit Ω)) (N n : ℕ) (hn : n≤N) :
    coeff n (invOfUnit (cut N F) 1*X*cut N F)=coeff n (invOfUnit F 1*X*F) :=
  inverse_adjoint_coeff_congr Ω _ _ _ n (fun j hj=>by rw [coeff_cut,ite_eq_left (hj.trans hn)])
lemma rootClosed_isotropic_adjoint (V : AddSubmonoid M) (hΩ : ∀p,Ω p p=0)
    (hV : ∀p∈V,∀q∈V,Ω p q=0) {N : ℕ} {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : RootClosedThrough LaurentRay.vUnit Ω N (literalRootProducts Ω C (fun p=>p∈V)) F) :
    (∀m,(∀p∈V,0≤Ω p m) → ∀n≤N,TorusPositive Ω
      (coeff n (F*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1))) ∧
    (∀m,(∀p∈V,Ω p m≤0) → ∀n≤N,TorusPositive Ω
      (coeff n (invOfUnit F 1*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*F))) := by
  let g:=rootApprox LaurentRay.vUnit Ω hF
  have hg:=rootApprox_converges LaurentRay.vUnit Ω hF
  have hgg : ∀T,SeriesGraded LaurentRay.vUnit Ω C (cut N (g T)):=
    fun T=>(literalRootProducts_graded Ω C _ (rootApprox_mem LaurentRay.vUnit Ω hF T)).cut LaurentRay.vUnit Ω C N
  have hFG : SeriesGraded LaurentRay.vUnit Ω C (cut N F):=by
    apply hF.graded Ω C
    rintro G ⟨G',hG,rfl⟩
    exact (literalRootProducts_graded Ω C _ hG).cut LaurentRay.vUnit Ω C N
  have hp:=fun T=>literal_isotropic_adjoint Ω C V hΩ hV (rootApprox_mem LaurentRay.vUnit Ω hF T)
  constructor
  · intro m hm n hn r
    have H:=hg.adjoint LaurentRay.vUnit Ω C Filter.atTop hgg hFG (Torus.X LaurentRay.vUnit Ω m)
    have he : ∀G,coeff n (cut N G*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit (cut N G) 1)=
        coeff n (G*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit G 1):=
      fun G=>cut_adjoint_coeff Ω G _ N n hn
    have Hn:=H n r
    simp only [he] at Hn
    exact LaurentPositive.of_converges Filter.atTop Hn (Eventually.of_forall (fun T=>(hp T).1 m hm n r))
  · intro m hm n hn r
    have H:=hg.inverse_adjoint Ω C Filter.atTop hgg hFG (Torus.X LaurentRay.vUnit Ω m)
    have he:=fun G=>cut_inverse_adjoint_coeff Ω G (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)) N n hn
    have Hn:=H n r
    simp only [he] at Hn
    exact LaurentPositive.of_converges Filter.atTop Hn (Eventually.of_forall (fun T=>(hp T).2 m hm n r))
lemma rootClosed_ray_adjoint (hΩ : ∀p,Ω p p=0) (r : M)
    {N : ℕ} {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : RootClosedThrough LaurentRay.vUnit Ω N (literalRootProducts Ω C (OnPositiveRay r)) F) :
    (∀m,0≤Ω r m → ∀n≤N,TorusPositive Ω
      (coeff n (F*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1))) ∧
    (∀m,Ω r m≤0 → ∀n≤N,TorusPositive Ω
      (coeff n (invOfUnit F 1*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*F))) := by
  have H:=rootClosed_isotropic_adjoint Ω C (positiveRayWithZero r) hΩ
    (positiveRayWithZero_isotropic Ω hΩ r)
    (hF.mono LaurentRay.vUnit Ω (literalRootProducts_allowed_mono Ω C _ _ (fun n hn p hr hp=>Or.inr hp)))
  constructor
  · intro m hm
    apply H.1 m
    intro p hp
    rcases hp with rfl|hp
    · simp
    exact hp.pair_nonneg Ω (OnPositiveRay.refl m) hm
  · intro m hm
    apply H.2 m
    intro p hp
    rcases hp with rfl|hp
    · simp
    have he:=hp.eval (incomingCovector Ω m)
    by_contra hx
    have hp0 : (0:ℝ)<Ω p m:=by exact_mod_cast (lt_of_not_ge hx)
    have hr0:=he.1.mp hp0
    change (0:ℝ)<Ω r m at hr0
    have hr1 : (Ω r m:ℝ)≤0:=by exact_mod_cast hm
    linarith
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint LaurentPositive WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (hΩ : ∀m,Ω m m=0)
include hΩ in
lemma ray_charge_through (p : M) (F : CompletedPositive LaurentRay.vUnit Ω C) (N : ℕ)
    (hs : ∀n,0<n → n≤N → ∀m,coeff n F.val m≠0 → OnPositiveRay p m) :
    ∀n≤N,coeff n F.val∈chargeGrade LaurentRay.vUnit Ω (Ω p) 0 := by
  intro n hn
  cases n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff,F.property.1]
    exact chargeGrade_one LaurentRay.vUnit Ω (Ω p)
  | succ n =>
    intro m hm
    by_contra hx
    exact hm ((OnPositiveRay.refl p).pair_zero Ω (hs _ (by omega) hn m hx) (hΩ p))
include hΩ in
lemma ray_increment_positive (p r : M) (F : CompletedPositive LaurentRay.vUnit Ω C)
    (X : PowerSeries (Torus LaurentRay.vUnit Ω)) (N : ℕ)
    (hs : ∀n,0<n → n≤N → ∀m,coeff n F.val m≠0 → OnPositiveRay p m)
    (hF : RootClosedThrough LaurentRay.vUnit Ω N (literalRootProducts Ω C (OnPositiveRay p)) F.val)
    (hX : ∀j<N,TorusPositive Ω (coeff j X)) :
    (0≤Ω p r → Positive (coeff N (adjoint F.val X) r-coeff N X r)) ∧
    (Ω p r≤0 → Positive (coeff N (adjoint (invOfUnit F.val 1) X) r-coeff N X r)) := by
  have hq:=ray_charge_through Ω C hΩ p F N hs
  have hp:=rootClosed_ray_adjoint Ω C hΩ p hF
  constructor
  · intro hr
    apply adjoint_increment_positive Ω F.val X (Ω p) N r F.property.1 hq hX
    intro m hm j hj
    exact (hp.1 m (by rw [hm]; exact hr) j hj) r
  · intro hr
    apply adjoint_increment_positive Ω (invOfUnit F.val 1) X (Ω p) N r (by simp)
      (chargeGrade_inverse LaurentRay.vUnit Ω (Ω p) F.val N hq) hX
    intro m hm j hj
    rw [adjoint_inverse F.val _ F.property.1]
    exact (hp.2 m (by rw [hm]; exact hr) j hj) r
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint LaurentPositive WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (hΩ : ∀m,Ω m m=0)
include hΩ in
lemma monomialJump_ray_positive (p r : M) (F : CompletedPositive LaurentRay.vUnit Ω C) (N : ℕ)
    (hs : ∀n,0<n → n≤N → ∀m,coeff n F.val m≠0 → OnPositiveRay p m)
    (hF : RootClosedThrough LaurentRay.vUnit Ω N (literalRootProducts Ω C (OnPositiveRay p)) F.val) :
    (0≤Ω p r → ∀d≤N,∀m,Positive (monomialJump Ω F.val d m r)) ∧
    (Ω p r≤0 → ∀d≤N,∀m,Positive (monomialJump Ω (invOfUnit F.val 1) d m r)) := by
  have hq:=ray_charge_through Ω C hΩ p F N hs
  have hp:=rootClosed_ray_adjoint Ω C hΩ p hF
  constructor
  · intro hr d hd m
    by_cases hh:Ω p m=Ω p r
    · exact (hp.1 m (by rw [hh]; exact hr) d hd) r
    · have H:=adjoint_charge LaurentRay.vUnit Ω (Ω p) F.val d (fun n hn=>hq n (hn.trans hd)) m r (Ne.symm hh)
      change Positive (coeff d (adjoint F.val (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m))) r)
      rw [H]; exact positive_zero
  · intro hr d hd m
    by_cases hh:Ω p m=Ω p r
    · unfold monomialJump
      rw [adjoint_inverse F.val _ F.property.1]
      exact (hp.2 m (by rw [hh]; exact hr) d hd) r
    · have H:=adjoint_charge LaurentRay.vUnit Ω (Ω p) (invOfUnit F.val 1) d
        (chargeGrade_inverse LaurentRay.vUnit Ω (Ω p) F.val d (fun n hn=>hq n (hn.trans hd))) m r (Ne.symm hh)
      change Positive (coeff d (adjoint (invOfUnit F.val 1) (PowerSeries.C (Torus.X LaurentRay.vUnit Ω m))) r)
      rw [H]; exact positive_zero

end
end ElementaryPositivity.QuantumTorus

end

end OAI
