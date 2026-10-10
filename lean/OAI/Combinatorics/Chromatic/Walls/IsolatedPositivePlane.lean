import Mathlib
import OAI.Combinatorics.Chromatic.Walls.RayIncomingIdentification
import OAI.Combinatorics.Chromatic.GradedAlgebra.TruncatedPrecisionClosure
import OAI.Combinatorics.Chromatic.Walls.OrderedRootReordering
import OAI.Combinatorics.Chromatic.Walls.DegreeIsolatedReordering
import OAI.Combinatorics.Chromatic.GradedAlgebra.Strict

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit RootTruncation LaurentPrecision Filter WallUnits
noncomputable section
variable {M I A : Type*} [AddCommGroup M] [Fintype I]
variable (Ω : M →+M →+ℤ) (C : (I → ℤ) →+M)
variable (hΩ : ∀m,Ω m m=0) (L h : M →+ℝ) (V : AddSubmonoid M) (t : ℝ)
variable (hplane : ∀p∈V,∀q∈V,(Ω p q:ℝ)=t*(h p*L q-L p*h q))
include hΩ hplane in
theorem isolated_positive_plane (n : ℕ) (s : List A) (active : A → Bool) (P : A → M → Prop)
    (F : A → CompletedPositive LaurentRay.vUnit Ω C)
    (hF : ∀a∈s,RootClosedThrough LaurentRay.vUnit Ω (if active a then n+1 else n)
      (literalRootProducts Ω C (P a)) (F a).val)
    (hadd : ∀a∈s,∀p q,P a p → P a q → P a (p+q))
    (hP : ∀a∈s,∀p,P a p → p∈V ∧ 0<L p)
    (hself : ∀a∈s,∀p q,P a p → P a q → 0 ≤ Ω p q)
    (hpair : s.Pairwise (fun a b=>∀p q,P a p → P b q → 0 ≤ Ω p q))
    (hker : ∀a∈s,active a=false  →  ∀p,P a p → h p≠0)
    (hsupport : ∀a∈s,SupportedOn LaurentRay.vUnit Ω (P a) (coeff (n+1) (F a).val)) :
    RootClosedThrough LaurentRay.vUnit Ω (n+1)
      (literalRootProducts Ω C (fun p=>p∈V ∧ h p=0))
      (zeroFactor (positiveProject LaurentRay.vUnit Ω h) (zeroProject LaurentRay.vUnit Ω h)
        (s.map (fun a=>(F a).val)).prod) := by
  classical
  let g (a : A) (T : Finset (PrecisionTest (M:=M))) :=
    if ha : a∈s then rootApprox LaurentRay.vUnit Ω (hF a ha) T else 1
  have hg : ∀a∈s,∀T,g a T∈literalRootProducts Ω C (P a):=by
    intro a ha T
    dsimp [g]; rw [dite_eq_left ha]
    exact rootApprox_mem LaurentRay.vUnit Ω (hF a ha) T
  have hconv : ∀a∈s,SeriesConverges LaurentRay.vUnit Ω Filter.atTop
      (fun T=>cut (if active a then n+1 else n) (g a T))
      (cut (if active a then n+1 else n) (F a).val):=by
    intro a ha
    have he : g a=rootApprox LaurentRay.vUnit Ω (hF a ha):=by
      funext T; dsimp [g]; rw [dite_eq_left ha]
    rw [he]
    exact rootApprox_converges LaurentRay.vUnit Ω (hF a ha)
  let k (a : A) (T : Finset (PrecisionTest (M:=M))) :=
    if active a then cut (n+1) (g a T) else patchTop n (g a T) (F a).val
  have hkg : ∀a∈s,∀T,SeriesGraded LaurentRay.vUnit Ω C (k a T):=by
    intro a ha T
    dsimp [k]
    split_ifs
    · exact (literalRootProducts_graded Ω C (P a) (hg a ha T)).cut LaurentRay.vUnit Ω C (n+1)
    · exact (literalRootProducts_graded Ω C (P a) (hg a ha T)).patchTop LaurentRay.vUnit Ω C n (F a).property.2
  have hkconv : ∀a∈s,SeriesConverges LaurentRay.vUnit Ω Filter.atTop (k a) (cut (n+1) (F a).val):=by
    intro a ha
    cases he : active a
    · have H:=hconv a ha
      simp only [he,Bool.false_eq_true,ite_false] at H
      simpa only [k,he,Bool.false_eq_true,ite_false] using
        H.patchTop LaurentRay.vUnit Ω Filter.atTop n
    · simpa only [k,he,ite_true] using hconv a ha
  have hcprod:=SeriesConverges.list_prod Ω C Filter.atTop s k
    (fun a=>cut (n+1) (F a).val) hkconv hkg
    (fun a ha=>SeriesGraded.cut LaurentRay.vUnit Ω C (n+1) (F a).property.2)
  have hcmid:=hcprod.zero_middle LaurentRay.vUnit Ω C Filter.atTop h
    (fun T=>SeriesGraded.list_prod Ω C s (fun a=>k a T) (fun a ha=>hkg a ha T))
    (SeriesGraded.list_prod Ω C s (fun a=>cut (n+1) (F a).val)
      (fun a ha=>SeriesGraded.cut LaurentRay.vUnit Ω C (n+1) (F a).property.2))
  have hout : RootClosedThrough LaurentRay.vUnit Ω (n+1)
      (literalRootProducts Ω C (fun p=>p∈V ∧ h p=0))
      (zeroFactor (positiveProject LaurentRay.vUnit Ω h) (zeroProject LaurentRay.vUnit Ω h)
        (s.map (fun a=>cut (n+1) (F a).val)).prod):=by
    apply RootClosedThrough.of_converges LaurentRay.vUnit Ω Filter.atTop
      (hcmid.cut LaurentRay.vUnit Ω Filter.atTop (n+1))
    apply Eventually.of_forall
    intro T
    have hraw:=orderedPlane_zero_finite Ω C L h V hΩ t hplane
      (literal_lists_ordered_product Ω C L V s P (fun a=>g a T) (fun a ha=>hg a ha T) hP hself hpair)
    have he:=joint_middle_isolated_through LaurentRay.vUnit Ω h s (fun a=>k a T) (fun a=>g a T) n
      (fun a ha=>by
        dsimp [k]; split_ifs <;>
          simpa using literalRootProducts_constant Ω C (P a) (hg a ha T))
      (fun a ha=>literalRootProducts_constant Ω C (P a) (hg a ha T))
      (fun a ha j hj=>by
        dsimp [k]; split_ifs
        · exact coeff_cut_of_le _ (by omega)
        · exact patchTop_low n _ _ j hj)
      (fun a ha m hm=>by
        dsimp [k]
        cases hn : active a
        · simp only [Bool.false_eq_true,ite_false,coeff_patchTop,Nat.not_succ_le_self,ite_true,ite_false]
          have hp : ¬P a m:=fun H=>hker a ha hn m H hm
          rw [hsupport a ha m hp,literalRootProducts_strictSupport Ω C (P a) (hadd a ha) (hg a ha T) n m hp]
        · simp only [ite_true,coeff_cut,le_refl,ite_true])
    change InPrecisionClosure LaurentRay.vUnit Ω _ _
    rw [he]
    exact hraw.cut LaurentRay.vUnit Ω (n+1)
  apply hout.congr LaurentRay.vUnit Ω
  intro j hj
  exact zero_coeff_congr _ _ _ _ j (fun z hz=>product_coeff_congr _ _ s z
    (fun a ha i hi=>coeff_cut_of_le _ (hi.trans (hz.trans hj))))
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
lemma OnPositiveRay.symm {r p : M} (H : OnPositiveRay r p) : OnPositiveRay p r := by
  obtain ⟨a,b,ha,hb,he⟩:=H
  exact ⟨b,a,hb,ha,he.symm⟩
lemma OnPositiveRay.trans {r p q : M} (H : OnPositiveRay r p) (K : OnPositiveRay p q) :
    OnPositiveRay r q := by
  obtain ⟨a,b,ha,hb,he⟩:=H
  obtain ⟨c,d,hc,hd,hf⟩:=K
  refine ⟨a*c,b*d,Nat.mul_pos ha hc,Nat.mul_pos hb hd,?_⟩
  calc
    (a*c) • q=a • (c • q):=by rw [smul_smul]
    _=a • (d • p):=by rw [hf]
    _=d • (a • p):=by rw [smul_smul,smul_smul,Nat.mul_comm]
    _=d • (b • r):=by rw [he]
    _=(b*d) • r:=by rw [smul_smul,Nat.mul_comm]
lemma OnPositiveRay.eq_pred {r p : M} (H : OnPositiveRay r p) :
    OnPositiveRay r=OnPositiveRay p := by
  funext q
  apply propext
  exact ⟨fun h=>H.symm.trans h,fun h=>H.trans h⟩
lemma OnPositiveRay.mem_submodule (e : M→+E) (V : Submodule ℝ E)
    {r p : M} (H : OnPositiveRay r p) (hr : e r∈V) : e p∈V := by
  obtain ⟨a,b,ha,hb,he⟩:=H
  have H:=congrArg e he
  simp only [map_nsmul,←Nat.cast_smul_eq_nsmul ℝ] at H
  have hA : (a:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt ha)
  exact (V.smul_mem_iff hA).mp (H.symm ▸ V.smul_mem (b:ℝ) hr)
variable (Ω : M→+M→+ℤ)
lemma OnPositiveRay.pair_nonneg {r s p q : M} (hp : OnPositiveRay r p) (hq : OnPositiveRay s q)
    (h : 0≤Ω r s) : 0≤Ω p q := by
  have hright:=hq.incomingSigns Ω r
  have hleft:=hp.eval (incomingCovector Ω q)
  by_contra hn
  have hn' : incomingCovector Ω q p < 0:=by change (Ω p q:ℝ)<0; exact_mod_cast (lt_of_not_ge hn)
  have H:=hright.2.2.mpr (hleft.2.2.mp hn')
  change (Ω r s:ℝ)<0 at H
  have h' : (0:ℝ)≤Ω r s:=by exact_mod_cast h
  linarith
lemma OnPositiveRay.pair_zero {r p q : M} (hp : OnPositiveRay r p) (hq : OnPositiveRay r q)
    (hΩ : Ω r r=0) : Ω p q=0 := by
  have hright:=hq.incomingSigns Ω r
  have hleft:=hp.eval (incomingCovector Ω q)
  have H : incomingCovector Ω r r=0:=by change (Ω r r:ℝ)=0; rw [hΩ,Int.cast_zero]
  have HH:=hleft.2.1.mpr (hright.2.1.mp H)
  change (Ω p q:ℝ)=0 at HH
  exact_mod_cast HH
lemma literalRootProducts_allowed_mono (C : (I→ℤ)→+M) (P Q : M→Prop)
    (H : ∀n,0<n → ∀p,HasRootDegree C n p → P p → Q p) :
    literalRootProducts Ω C P⊆literalRootProducts Ω C Q := by
  rintro F ⟨l,hl,rfl⟩
  refine ⟨l,?_,rfl⟩
  intro u hu
  have h:=hl u hu
  exact ⟨h.1,h.2.1,H u.degree h.1 u.root h.2.1 h.2.2⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
