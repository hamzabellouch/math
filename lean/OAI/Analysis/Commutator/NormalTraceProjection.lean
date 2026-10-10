import Mathlib
import OAI.Analysis.Commutator.DiffuseProjection
import OAI.Analysis.Commutator.StandardTrace

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

namespace Kadison.NormalGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (hnormal : BoundedWOTContinuous M τ)

variable (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

lemma projection_subtype {p : H →L[ℂ] H} (hpM : p∈M) (hp : IsStarProjection p) :
    IsStarProjection (⟨p,hpM⟩ : M) := by
  constructor
  · exact Subtype.ext hp.isIdempotentElem.eq
  · exact Subtype.ext hp.isSelfAdjoint.star_eq

include hfaith in
lemma gns_projection_iff (a : M) :
    IsStarProjection (τ.gnsStarAlgHom a) ↔ IsStarProjection a := by
  constructor
  · intro h
    constructor
    · apply gns_injective M τ hfaith
      simpa only [map_mul τ.gnsStarAlgHom a a] using h.isIdempotentElem.eq
    · apply gns_injective M τ hfaith
      simpa only [map_star τ.gnsStarAlgHom a] using h.isSelfAdjoint.star_eq
  · exact fun h => h.map τ.gnsStarAlgHom

include hfaith in
lemma gns_projection_le_iff {a b : M} (ha : IsStarProjection a) (hb : IsStarProjection b) :
    τ.gnsStarAlgHom a ≤ τ.gnsStarAlgHom b ↔ a≤b := by
  have hsource : a≤b ↔ a*b=a := ha.le_iff_mul_eq_left hb
  have htarget : τ.gnsStarAlgHom a ≤ τ.gnsStarAlgHom b ↔
      τ.gnsStarAlgHom a * τ.gnsStarAlgHom b = τ.gnsStarAlgHom a :=
    (ha.map τ.gnsStarAlgHom).le_iff_mul_eq_left (hb.map τ.gnsStarAlgHom)
  constructor
  · intro hab
    exact hsource.mpr ((gns_injective M τ hfaith)
      ((map_mul τ.gnsStarAlgHom a b).trans (htarget.mp hab)))
  · intro hab
    exact htarget.mpr ((map_mul τ.gnsStarAlgHom a b).symm.trans
      (congrArg τ.gnsStarAlgHom (hsource.mp hab)))

include hfaith in
theorem gns_noMinimal (hM : DiffuseProjection.HasNoMinimalProjections M) :
    DiffuseProjection.HasNoMinimalProjections (algebra M τ hτ hnormal) := by
  let representation := τ.gnsStarAlgHom
  intro p hpM hp hpn
  obtain ⟨a,rfl⟩ := hpM
  have ha := (gns_projection_iff M τ hfaith a).mp hp
  have han : (a : H →L[ℂ] H)≠0 := by
    intro hz
    have haz : a=0 := Subtype.ext hz
    exact hpn (by rw [haz,map_zero])
  have hap : IsStarProjection (a : H →L[ℂ] H) := ha.map M.toStarSubalgebra.subtype
  obtain ⟨q,hqM,hq,hqn,hqa,hqle⟩ := hM a a.property hap han
  let b : M := ⟨q,hqM⟩
  have hb : IsStarProjection b := projection_subtype M hqM hq
  have hble : representation b ≤ representation a :=
    (gns_projection_le_iff M τ hfaith hb ha).mpr hqle
  refine ⟨representation b,⟨b,rfl⟩,hb.map representation,?_,?_,hble⟩
  · intro hz
    have hbz : b=0 := (gns_injective M τ hfaith)
      (hz.trans (map_zero representation).symm)
    exact hqn (congrArg Subtype.val hbz)
  · intro he
    exact hqa (congrArg Subtype.val ((gns_injective M τ hfaith) he))

include hτ hnormal hfaith in
theorem exists_prescribed_projection_trace
    (hM : DiffuseProjection.HasNoMinimalProjections M)
    (e : M) (he : IsStarProjection e) {t : ℝ} (ht : 0≤t) (hte : t≤(τ e).re) :
    ∃ p : M, IsStarProjection p ∧ p≤e ∧ (τ p).re=t := by
  have htG : t≤(trace M τ (τ.gnsStarAlgHom e)).re := by rwa [trace_gns]
  obtain ⟨p,⟨a,ha⟩,hp,hpe,hpt⟩ := DiffuseProjection.exists_prescribed_trace
    (algebra M τ hτ hnormal) (trace M τ)
    (gns_noMinimal M τ hτ hnormal hfaith hM)
    (Complex.continuous_re.comp (trace_continuous M τ))
    (show τ.gnsStarAlgHom e ∈ algebra M τ hτ hnormal from ⟨e,rfl⟩)
    (he.map τ.gnsStarAlgHom) ht htG
  subst p
  have hpa := (gns_projection_iff M τ hfaith a).mp hp
  refine ⟨a,hpa,(gns_projection_le_iff M τ hfaith hpa he).mp hpe,?_⟩
  change (trace M τ (τ.gnsStarAlgHom a)).re=t at hpt
  simpa only [trace_gns] using hpt

include hfaith in
lemma projection_zero_of_trace_re_zero (e : M) (he : IsStarProjection e)
    (ht : (τ e).re=0) : e=0 := by
  apply hfaith
  rw [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq]
  have hn := τ.map_nonneg he.nonneg
  exact Complex.ext ht hn.2.symm

include hτ hnormal hfaith in
theorem exists_projection_partition (hM : DiffuseProjection.HasNoMinimalProjections M)
    (n : ℕ) (e : M) (he : IsStarProjection e) {t : ℝ} (ht : 0≤t)
    (htrace : (τ e).re=(n:ℝ)*t) :
    ∃ p : Fin n → M, (∀ i, IsStarProjection (p i) ∧ p i≤e ∧ (τ (p i)).re=t) ∧
      (∀ i j, i≠j → p i*p j=0) ∧ ∑ i,p i=e := by
  induction n generalizing e with
  | zero =>
    have hez : e=0 := projection_zero_of_trace_re_zero M τ hfaith e he (by simpa using htrace)
    subst e
    refine ⟨Fin.elim0,?_,?_,?_⟩
    · exact fun i => Fin.elim0 i
    · exact fun i => Fin.elim0 i
    · simp
  | succ n ih =>
    have hte : t≤(τ e).re := by rw [htrace,Nat.cast_succ]; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    obtain ⟨p,hp,hple,hpt⟩ := exists_prescribed_projection_trace M τ hτ hnormal hfaith hM e he ht hte
    have her : IsStarProjection (e-p) := (hp.le_iff_sub he).mp hple
    have htr : (τ (e-p)).re=(n:ℝ)*t := by
      rw [map_sub,Complex.sub_re,htrace,hpt,Nat.cast_succ]
      ring
    obtain ⟨q,hq,hqq,hqsum⟩ := ih (e-p) her htr
    have hpq : ∀ i, p*q i=0 := by
      intro i
      have hfix := ((hq i).1.le_iff_mul_eq_right her).mp (hq i).2.1
      calc
        _=p*((e-p)*q i) := by rw [hfix]
        _=0 := by rw [←mul_assoc,mul_sub,(hp.le_iff_mul_eq_left he).mp hple,hp.isIdempotentElem.eq,sub_self,zero_mul]
    have hqp : ∀ i, q i*p=0 := by
      intro i
      simpa only [star_mul,hp.isSelfAdjoint.star_eq,(hq i).1.isSelfAdjoint.star_eq,star_zero] using congrArg star (hpq i)
    refine ⟨Fin.cons p q,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hp,hple,hpt⟩
      · exact ⟨(hq j).1,(hq j).2.1.trans (sub_le_self e hp.nonneg),(hq j).2.2⟩
    · intro i j hij
      revert hij
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j _ => hpq j) j
        exact fun h => (h rfl).elim
      · refine Fin.cases (fun _ => hqp i) (fun j h => hqq i j (by simpa using h)) j
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ,hqsum]
      abel

end Kadison.NormalGNS

end

end
end

end OAI
