import Mathlib
import OAI.Combinatorics.Chromatic.Walls.SectionRayTransition
import OAI.Combinatorics.Chromatic.Walls.FiniteWallCrossing

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (L : Module.Dual ℝ E)
variable (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include hdeg in
lemma section_positive_perturbation (F : CompletedPositive v Ω C)
    (X : PowerSeries (Torus v Ω)) (N : ℕ) (h : Module.Dual ℝ E) :
    ∃k : Module.Dual ℝ E,ChamberGeneric C N (k.toAddMonoidHom.comp e) ∧
      ∀n≤N,coeff n (sectionValue v Ω C F (k.toAddMonoidHom.comp e) X)=
        coeff n (sectionValue v Ω C F (h.toAddMonoidHom.comp e) X) := by
  let hM:=h.toAddMonoidHom.comp e
  let lM:=L.toAddMonoidHom.comp e
  obtain ⟨ε,hε,Hε⟩:=root_lex_epsilon C N hM lM
  let δ:=ε/2
  have hd : 0<δ:=by dsimp [δ]; linarith
  have hdε : δ<ε:=by dsimp [δ]; linarith
  have hk : (h+δ • L).toAddMonoidHom.comp e=hM+δ • lM:=by ext m; rfl
  refine ⟨h+δ • L,?_,?_⟩
  · rw [hk]
    intro n hn hnN m hm
    have HH:=Hε δ hd hdε n hnN m hm
    have hlpos : 0<lM m:=by change 0<L (e m); rw [hdeg n m hm]; exact_mod_cast hn
    rcases lt_trichotomy 0 (hM m) with hp|hz|hmn
    · exact ne_of_gt (HH.1 hp)
    · exact ne_of_gt ((HH.2.2 hz.symm).1 hlpos)
    · exact ne_of_lt (HH.2.1 hmn)
  · rw [hk]
    have Hneg:=chartNegative_of_positive_through v Ω C lM (chartZero v Ω C hM F) N (by
      intro n hn m hm
      change 0<L (e m)
      rw [hdeg (n+1) m (chart_root_of_ne v Ω C _ _ m hm)]
      positivity)
    intro n hn
    rw [section_refinement_through v Ω C hM lM _ F X N (Hε δ hd hdε) n hn]
    have HH:=adjoint_coeff_congr (chartNegative v Ω C lM (chartZero v Ω C hM F)).val 1
      (sectionValue v Ω C F hM X) (sectionValue v Ω C F hM X) n
      (fun j hj=>Hneg j (hj.trans hn)) (fun _ _=>rfl)
    rw [HH,adjoint_one]
include hdeg in
lemma section_generic_offset (F : CompletedPositive v Ω C)
    (X : PowerSeries (Torus v Ω)) (N : ℕ) (h dir : Module.Dual ℝ E) :
    ∃k : Module.Dual ℝ E,GenericOffset (realRootsThrough e C N) 0 dir k ∧
      ∀n≤N,coeff n (sectionValue v Ω C F (k.toAddMonoidHom.comp e) X)=
        coeff n (sectionValue v Ω C F (h.toAddMonoidHom.comp e) X) := by
  obtain ⟨h',hgen,heq⟩:=section_positive_perturbation v Ω C e L hdeg F X N h
  obtain ⟨k,Hk,Hsign⟩:=exists_generic_offset (realRootsThrough e C N) 0 dir h' (map_zero h')
  refine ⟨k,Hk,?_⟩
  have HH:=section_sign_congr_through v Ω C (h'.toAddMonoidHom.comp e)
    (k.toAddMonoidHom.comp e) F X N (by
      intro n hn hnN m hm
      have HS:=Hsign (e m) (realRoot_mem e C N n hnN m hm)
      exact ⟨HS.1,fun hh=>False.elim (hgen n hn hnN m hm hh),HS.2⟩)
  exact fun n hn=>(HH n hn).symm.trans (heq n hn)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (L : Module.Dual ℝ E)
variable (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include hdeg in
lemma uniform_section_positive_perturbation (N : ℕ) (h : Module.Dual ℝ E) :
    ∃k : Module.Dual ℝ E,ChamberGeneric C N (k.toAddMonoidHom.comp e) ∧
      ∀(F : CompletedPositive v Ω C) (X : PowerSeries (Torus v Ω)),∀n≤N,
        coeff n (sectionValue v Ω C F (k.toAddMonoidHom.comp e) X)=
        coeff n (sectionValue v Ω C F (h.toAddMonoidHom.comp e) X) := by
  let hM:=h.toAddMonoidHom.comp e
  let lM:=L.toAddMonoidHom.comp e
  obtain ⟨ε,hε,Hε⟩:=root_lex_epsilon C N hM lM
  let δ:=ε/2
  have hd : 0<δ:=by dsimp [δ]; linarith
  have hdε : δ<ε:=by dsimp [δ]; linarith
  have hk : (h+δ • L).toAddMonoidHom.comp e=hM+δ • lM:=by ext m; rfl
  refine ⟨h+δ • L,?_,?_⟩
  · rw [hk]
    intro n hn hnN m hm
    have HH:=Hε δ hd hdε n hnN m hm
    have hlpos : 0<lM m:=by change 0<L (e m); rw [hdeg n m hm]; exact_mod_cast hn
    rcases lt_trichotomy 0 (hM m) with hp|hz|hmn
    · exact ne_of_gt (HH.1 hp)
    · exact ne_of_gt ((HH.2.2 hz.symm).1 hlpos)
    · exact ne_of_lt (HH.2.1 hmn)
  · intro F X n hn
    rw [hk]
    have Hneg:=chartNegative_of_positive_through v Ω C lM (chartZero v Ω C hM F) N (by
      intro n hn m hm
      change 0<L (e m)
      rw [hdeg (n+1) m (chart_root_of_ne v Ω C _ _ m hm)]
      positivity)
    rw [section_refinement_through v Ω C hM lM _ F X N (Hε δ hd hdε) n hn]
    have HH:=adjoint_coeff_congr (chartNegative v Ω C lM (chartZero v Ω C hM F)).val 1
      (sectionValue v Ω C F hM X) (sectionValue v Ω C F hM X) n
      (fun j hj=>Hneg j (hj.trans hn)) (fun _ _=>rfl)
    rw [HH,adjoint_one]
include hdeg in
lemma uniform_section_generic_offset (N : ℕ) (h dir : Module.Dual ℝ E) :
    ∃k : Module.Dual ℝ E,GenericOffset (realRootsThrough e C N) 0 dir k ∧
      ∀(F : CompletedPositive v Ω C) (X : PowerSeries (Torus v Ω)),∀n≤N,
        coeff n (sectionValue v Ω C F (k.toAddMonoidHom.comp e) X)=
        coeff n (sectionValue v Ω C F (h.toAddMonoidHom.comp e) X) := by
  obtain ⟨h',hgen,heq⟩:=uniform_section_positive_perturbation v Ω C e L hdeg N h
  obtain ⟨k,Hk,Hsign⟩:=exists_generic_offset (realRootsThrough e C N) 0 dir h' (map_zero h')
  refine ⟨k,Hk,?_⟩
  intro F X n hn
  have HH:=section_sign_congr_through v Ω C (h'.toAddMonoidHom.comp e)
    (k.toAddMonoidHom.comp e) F X N (by
      intro n hn hnN m hm
      have HS:=Hsign (e m) (realRoot_mem e C N n hnN m hm)
      exact ⟨HS.1,fun hh=>False.elim (hgen n hn hnN m hm hh),HS.2⟩)
  exact (HH n hn).symm.trans (heq F X n hn)
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry LaurentPositive WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]

structure LineTransfer (E:Type*) [AddCommGroup E] [Module ℝ E] where
  wall : Module.Dual ℝ E
  source : Module.Dual ℝ E
  reverse : Bool

variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (e:M →+ E)
def LineTransfer.operator (F:CompletedPositive LaurentRay.vUnit Ω C) (t:LineTransfer E) :
    PowerSeries (Torus LaurentRay.vUnit Ω) :=
  if t.reverse then invOfUnit (chartZero LaurentRay.vUnit Ω C (t.wall.toAddMonoidHom.comp e) F).val 1
  else (chartZero LaurentRay.vUnit Ω C (t.wall.toAddMonoidHom.comp e) F).val
lemma LineTransfer.constantCoeff_operator (F:CompletedPositive LaurentRay.vUnit Ω C) (t:LineTransfer E) :
    constantCoeff (t.operator Ω C e F)=1 := by
  unfold LineTransfer.operator
  split
  · simp
  · exact (chartZero LaurentRay.vUnit Ω C _ F).property.1

def LineTransfer.delta (F:CompletedPositive LaurentRay.vUnit Ω C) (b:M)
    (X:PowerSeries (Torus LaurentRay.vUnit Ω)) (N:ℕ) (r:M) (t:LineTransfer E) : LaurentSeries ℚ :=
  ∑j∈Finset.range N,∑m∈gradePoints C b j,
    coeff j (sectionValue LaurentRay.vUnit Ω C F (t.source.toAddMonoidHom.comp e) X) m*
      monomialJump Ω (t.operator Ω C e F) (N-j) m r

def LineTransfer.PositiveThrough (F:CompletedPositive LaurentRay.vUnit Ω C) (N:ℕ) (r:M) (t:LineTransfer E) : Prop :=
  ∀d≤N,∀m,Positive (monomialJump Ω (t.operator Ω C e F) d m r)

variable (he:Function.Injective e) (B:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB:∀x,B x x=0)
variable (hcomp:∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in
lemma section_line_transfer (N:ℕ) (r:M) (F:CompletedPositive LaurentRay.vUnit Ω C)
    (walls:WallsPositiveThrough Ω C e N F) (k:Module.Dual ℝ E)
    (H:GenericOffset (realRootsThrough e C N) 0 (B.flip (e r)) k)
    (a:ℝ) (ha:a∈lineEvents (realRootsThrough e C N) (B.flip (e r)) k) :
    ∃ε>0,∀δ:ℝ,0<δ → δ<ε → ∃t:LineTransfer E,
      t.PositiveThrough Ω C e F N r ∧
      ∀b (X:PowerSeries (Torus LaurentRay.vUnit Ω)),ShiftGraded LaurentRay.vUnit Ω C b X →
        coeff N (sectionValue LaurentRay.vUnit Ω C F ((k+(a-δ) • B.flip (e r)).toAddMonoidHom.comp e) X) r =
        coeff N (sectionValue LaurentRay.vUnit Ω C F ((k+(a+δ) • B.flip (e r)).toAddMonoidHom.comp e) X) r +
          t.delta Ω C e F b X N r := by
  have hΩ:∀m,Ω m m=0:=by
    intro m; have HH:=hB (e m); rw [hcomp] at HH; exact_mod_cast HH
  obtain ⟨p,d,hd,hdN,hp,hv,hgen⟩:=section_event_ray C e he L hdeg N (B.flip (e r)) k H a ha
  let h:=(k+a • B.flip (e r)).toAddMonoidHom.comp e
  let dir:=(B.flip (e r)).toAddMonoidHom.comp e
  obtain ⟨εp,hεp,Hεp⟩:=root_lex_epsilon C N h dir
  obtain ⟨εm,hεm,Hεm⟩:=root_lex_epsilon C N h (-dir)
  refine ⟨min εp εm,lt_min hεp hεm,?_⟩
  intro δ hδ hδε
  have hδp:=lt_of_lt_of_le hδε (min_le_left _ _)
  have hδm:=lt_of_lt_of_le hδε (min_le_right _ _)
  let hpM:=(k+(a+δ) • B.flip (e r)).toAddMonoidHom.comp e
  let hmM:=(k+(a-δ) • B.flip (e r)).toAddMonoidHom.comp e
  have HC (X:PowerSeries (Torus LaurentRay.vUnit Ω)):=section_ray_crossing LaurentRay.vUnit Ω C F X N p h dir hpM hmM hgen
    (by simpa only [hpM,line_covector_add] using Hεp δ hδ hδp)
    (by simpa only [hmM,line_covector_sub] using Hεm δ hδ hδm)
  have HS:∀n,0<n → n≤N → ∀m,coeff n (chartZero LaurentRay.vUnit Ω C h F).val m≠0 → OnPositiveRay p m:=by
    intro n hn hnN m hm
    by_contra hh
    exact hm ((hgen.ray_supported LaurentRay.vUnit Ω C F n hn hnN) m hh)
  have HI:=monomialJump_ray_positive Ω C hΩ p r (chartZero LaurentRay.vUnit Ω C h F) N HS
    (walls p d hd hp (k+a • B.flip (e r)) hgen)
  have Hpair:dir p=(Ω p r:ℝ):=hcomp p r
  have Hne:dir p≠0:=hv
  rcases lt_or_gt_of_ne Hne with hneg|hpos
  · let t:LineTransfer E:=⟨k+a • B.flip (e r),k+(a+δ) • B.flip (e r),true⟩
    refine ⟨t,HI.2 (by exact_mod_cast (le_of_lt (Hpair ▸ hneg))),?_⟩
    intro b X hX
    change coeff N (sectionValue LaurentRay.vUnit Ω C F hmM X) r=_
    rw [(HC X).2 hneg N le_rfl]
    exact adjoint_lower_grade_expansion Ω C (t.operator Ω C e F) _ (t.constantCoeff_operator Ω C e F) b
      (hX.sectionValue LaurentRay.vUnit Ω C F hpM) N r
  · let t:LineTransfer E:=⟨k+a • B.flip (e r),k+(a+δ) • B.flip (e r),false⟩
    refine ⟨t,HI.1 (by exact_mod_cast (le_of_lt (Hpair ▸ hpos))),?_⟩
    intro b X hX
    change coeff N (sectionValue LaurentRay.vUnit Ω C F hmM X) r=_
    rw [(HC X).1 hpos N le_rfl]
    exact adjoint_lower_grade_expansion Ω C (t.operator Ω C e F) _ (t.constantCoeff_operator Ω C e F) b
      (hX.sectionValue LaurentRay.vUnit Ω C F hpM) N r
end
end ElementaryPositivity.QuantumTorus

end

end OAI
