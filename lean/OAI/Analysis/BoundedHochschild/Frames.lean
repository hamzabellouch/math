import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.TypeIIStructure

namespace OAI

/-! Orthogonal frames of partial isometries and maximal frame construction. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildComparison
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace PartialIso

def ofProjection (p : M) (hp : IsStarProjection p) : PartialIso M :=
  ⟨p,by rw [hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq,hp.isIdempotentElem.eq]⟩
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma ofProjection_coe (p : M) (hp : IsStarProjection p) :
    ((ofProjection p hp : PartialIso M):M)=p := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma ofProjection_initial (p : M) (hp : IsStarProjection p) :
    (ofProjection p hp).initial=p := by simp only [initial,ofProjection_coe,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma ofProjection_final (p : M) (hp : IsStarProjection p) :
    (ofProjection p hp).final=p := by simp only [final,ofProjection_coe,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]

omit [PartialOrder M] [StarOrderedRing M] in
lemma initial_ne_zero {v : PartialIso M} (hv : (v:M) ≠ 0) : v.initial ≠ 0 := by
  intro h
  apply hv
  have hh := v.mul_initial
  simpa only [h,mul_zero,eq_comm] using hh

lemma restrict_square (v : PartialIso M) {p : M} (hp : IsStarProjection p)
    (hpv : p ≤ v.initial) : star ((v:M)*p)*((v:M)*p)=p := by
  calc
    star ((v:M)*p)*((v:M)*p) = p*v.initial*p := by
      simp only [star_mul,hp.isSelfAdjoint.star_eq,initial,mul_assoc]
    _ = p := by rw [(hp.le_iff_mul_eq_left v.initial_proj).mp hpv,hp.isIdempotentElem.eq]

def restrict (v : PartialIso M) {p : M} (hp : IsStarProjection p)
    (hpv : p ≤ v.initial) : PartialIso M :=
  ⟨(v:M)*p,by rw [mul_assoc,restrict_square v hp hpv,mul_assoc,hp.isIdempotentElem.eq]⟩
@[simp] lemma restrict_coe (v : PartialIso M) {p : M} (hp : IsStarProjection p)
    (hpv : p ≤ v.initial) : ((v.restrict hp hpv : PartialIso M):M)=(v:M)*p := rfl
@[simp] lemma restrict_initial (v : PartialIso M) {p : M} (hp : IsStarProjection p)
    (hpv : p ≤ v.initial) : (v.restrict hp hpv).initial=p := restrict_square v hp hpv
lemma restrict_le (v : PartialIso M) {p : M} (hp : IsStarProjection p)
    (hpv : p ≤ v.initial) : v.restrict hp hpv ≤ v := by
  exact ⟨by simpa only [restrict_initial] using hpv,by simp only [restrict_initial,restrict_coe]⟩
end PartialIso

lemma projection_orthogonal_mono {p q r s : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hr : IsStarProjection r) (hs : IsStarProjection s)
    (hpr : p ≤ r) (hqs : q ≤ s) (hrs : r*s=0) : p*q=0 := by
  calc
    p*q = (p*r)*(s*q) := by
      rw [(hp.le_iff_mul_eq_left hr).mp hpr,(hq.le_iff_mul_eq_right hs).mp hqs]
    _ = p*(r*s)*q := by simp only [mul_assoc]
    _ = 0 := by rw [hrs,mul_zero,zero_mul]

structure Frame (M : Type*) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] (n : ℕ) where
  part : Fin (n+1) → PartialIso M
  common : ∀ i, (part i).initial=(part 0).initial
  anchor : (part 0 : M)=(part 0).initial
  orthogonal : ∀ i j, i ≠ j → (part i).final*(part j).final=0

namespace Frame
variable {n : ℕ}
@[ext] lemma ext {v w : Frame M n} (h : ∀ i, v.part i=w.part i) : v=w := by
  have he := funext h
  cases v; cases w; congr

def base (v : Frame M n) : M := (v.part 0).initial
def support (v : Frame M n) : M := ∑ i, (v.part i).final
lemma base_proj (v : Frame M n) : IsStarProjection v.base := (v.part 0).initial_proj
lemma final_zero (v : Frame M n) : (v.part 0).final=v.base := by
  change (v.part 0:M)*star (v.part 0:M)=v.base
  change (v.part 0:M)*star (v.part 0:M)=(v.part 0).initial
  rw [v.anchor,(v.part 0).initial_proj.isSelfAdjoint.star_eq,
    (v.part 0).initial_proj.isIdempotentElem.eq]
lemma initial_eq (v : Frame M n) (i : Fin (n+1)) : (v.part i).initial=v.base := v.common i
lemma support_proj (v : Frame M n) : IsStarProjection v.support := by
  classical
  have he (i j : Fin (n+1)) : (v.part i).final*(v.part j).final=
      if i=j then (v.part i).final else 0 := by
    by_cases h : i=j
    · subst j; rw [ite_eq_left rfl]; exact (v.part i).final_proj.isIdempotentElem.eq
    · rw [ite_eq_right h]; exact v.orthogonal i j h
  constructor
  · change (∑ i, (v.part i).final)*(∑ j, (v.part j).final)=∑ i, (v.part i).final
    rw [Finset.sum_mul_sum]
    simp only [he,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  · change star (∑ i, (v.part i).final)=∑ i, (v.part i).final
    simp only [star_sum,(v.part _).final_proj.isSelfAdjoint.star_eq]
lemma final_le_support (v : Frame M n) (i : Fin (n+1)) : (v.part i).final ≤ v.support := by
  apply ((v.part i).final_proj.le_iff_mul_eq_left v.support_proj).mpr
  change (v.part i).final*(∑ j, (v.part j).final)=(v.part i).final
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · exact (v.part i).final_proj.isIdempotentElem.eq
  · intro j _ hji
    exact v.orthogonal i j hji.symm
  · simp
lemma base_le_support (v : Frame M n) : v.base ≤ v.support := by
  rw [← v.final_zero]; exact v.final_le_support 0
lemma support_le {p : M} (v : Frame M n) (hp : IsStarProjection p)
    (hv : ∀ i, (v.part i).final ≤ p) : v.support ≤ p := by
  apply (v.support_proj.le_iff_mul_eq_left hp).mpr
  change (∑ i, (v.part i).final)*p=∑ i, (v.part i).final
  simp only [Finset.sum_mul,((v.part _).final_proj.le_iff_mul_eq_left hp).mp (hv _)]

instance : Zero (Frame M n) := ⟨⟨fun _ => 0,fun _ => rfl,by simp,by intros; simp⟩⟩
@[simp] lemma zero_part (i : Fin (n+1)) : (0:Frame M n).part i=0 := rfl
@[simp] lemma zero_base : (0:Frame M n).base=0 := by simp only [base,zero_part,PartialIso.initial_zero]
@[simp] lemma zero_support : (0:Frame M n).support=0 := by simp only [support,zero_part,PartialIso.final_zero,Finset.sum_const_zero]
instance : LE (Frame M n) := ⟨fun v w => ∀ i, v.part i ≤ w.part i⟩
instance : PartialOrder (Frame M n) where
  le_refl _ _ := le_rfl
  le_trans _ _ _ h1 h2 i := (h1 i).trans (h2 i)
  le_antisymm _ _ h1 h2 := ext fun i => le_antisymm (h1 i) (h2 i)
lemma zero_le (v : Frame M n) : 0 ≤ v := fun i => PartialIso.zero_le (v.part i)
lemma base_mono {v w : Frame M n} (h : v ≤ w) : v.base ≤ w.base := (h 0).1
lemma eq_of_le_of_base_eq {v w : Frame M n} (h : v ≤ w) (he : v.base=w.base) : v=w := by
  apply ext
  intro i
  apply PartialIso.ext
  have hh := (h i).2
  rw [v.initial_eq,he,← w.initial_eq i,(w.part i).mul_initial] at hh
  exact hh.symm

lemma cross_final_zero {v w : Frame M n} (h : v.support*w.support=0)
    (i j : Fin (n+1)) : (v.part i).final*(w.part j).final=0 :=
  projection_orthogonal_mono (v.part i).final_proj (w.part j).final_proj
    v.support_proj w.support_proj (v.final_le_support i) (w.final_le_support j) h
lemma cross_initial_zero {v w : Frame M n} (h : v.support*w.support=0)
    (i j : Fin (n+1)) : (v.part i).initial*(w.part j).initial=0 := by
  rw [v.initial_eq,w.initial_eq]
  exact projection_orthogonal_mono v.base_proj w.base_proj v.support_proj w.support_proj
    v.base_le_support w.base_le_support h
lemma support_orthogonal_symm {v w : Frame M n} (h : v.support*w.support=0) :
    w.support*v.support=0 := by
  simpa only [star_mul,v.support_proj.isSelfAdjoint.star_eq,
    w.support_proj.isSelfAdjoint.star_eq,star_zero] using congrArg star h

def orthogonalSum (v w : Frame M n) (h : v.support*w.support=0) : Frame M n where
  part i := (v.part i).orthogonalSum (w.part i) (cross_initial_zero h i i) (cross_final_zero h i i)
  common i := by simp only [PartialIso.orthogonalSum_initial,v.common,w.common]
  anchor := by
    change (v.part 0:M)+(w.part 0:M)=_
    rw [PartialIso.orthogonalSum_initial,v.anchor,w.anchor]
  orthogonal i j hij := by
    simp only [PartialIso.orthogonalSum_final,add_mul,mul_add,v.orthogonal i j hij,
      w.orthogonal i j hij,cross_final_zero h i j,cross_final_zero (support_orthogonal_symm h) i j,
      zero_add]
lemma orthogonalSum_support (v w : Frame M n) (h : v.support*w.support=0) :
    (v.orthogonalSum w h).support=v.support+w.support := by
  simp only [support,orthogonalSum,PartialIso.orthogonalSum_final,Finset.sum_add_distrib]
lemma orthogonalSum_base (v w : Frame M n) (h : v.support*w.support=0) :
    (v.orthogonalSum w h).base=v.base+w.base := by
  exact PartialIso.orthogonalSum_initial (v.part 0) (w.part 0)
    (cross_initial_zero h 0 0) (cross_final_zero h 0 0)
lemma le_orthogonalSum (v w : Frame M n) (h : v.support*w.support=0) :
    v ≤ v.orthogonalSum w h := fun i => PartialIso.le_orthogonalSum (v.part i) (w.part i)
      (cross_initial_zero h i i) (cross_final_zero h i i)

end Frame
end HochschildComparison

open Filter Topology
open scoped ComplexOrder
namespace HochschildComparison
open BoundedHochschild HochschildRigidity HochschildTypeII FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

namespace Frame
variable {n : ℕ}
include e hτ htr hfaith in
lemma exists_local (hII : TypeII1 M) (n : ℕ) {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ v : Frame M n, v.base ≠ 0 ∧ v.support ≤ p := by
  induction n with
  | zero =>
    let v : Frame M 0 := ⟨fun _ => PartialIso.ofProjection p hp,fun _ => rfl,
      by simp,by intro i j hij; exact (hij (Fin.ext (by omega))).elim⟩
    refine ⟨v,?_,?_⟩
    · simpa only [Frame.base,v,PartialIso.ofProjection_initial] using hp0
    · apply v.support_le hp
      intro i
      exact le_of_eq (PartialIso.ofProjection_final p hp)
  | succ n ih =>
    obtain ⟨v,hv0,hvp⟩ := ih
    obtain ⟨w,hw0,hwi,hwf,hwo⟩ := exists_orthogonal_equivalent e τ hτ htr hfaith hII v.base_proj hv0
    let r := w.initial
    have hr : IsStarProjection r := w.initial_proj
    have hrv (i : Fin (n+1)) : r ≤ (v.part i).initial := by rw [v.initial_eq]; exact hwi
    let u (i : Fin (n+1)) := (v.part i).restrict hr (hrv i)
    have hui (i : Fin (n+1)) : (u i).initial=r := PartialIso.restrict_initial _ _ _
    have huf (i : Fin (n+1)) : (u i).final ≤ (v.part i).final :=
      PartialIso.final_mono (PartialIso.restrict_le _ _ _)
    have hu0 : (u 0:M)=r := by
      change (v.part 0:M)*r=r
      rw [v.anchor]
      exact (hr.le_iff_mul_eq_right v.base_proj).mp hwi
    have hu0f : (u 0).final=r := by
      change (u 0:M)*star (u 0:M)=r
      rw [hu0,hr.isSelfAdjoint.star_eq,hr.isIdempotentElem.eq]
    have hwuj (j : Fin (n+1)) : w.final*(u j).final=0 := by
      by_cases hj : j=0
      · subst j
        rw [hu0f]
        simpa only [star_mul,w.initial_proj.isSelfAdjoint.star_eq,w.final_proj.isSelfAdjoint.star_eq,
          star_zero] using congrArg star hwo
      · apply projection_orthogonal_mono w.final_proj (u j).final_proj
          (v.part 0).final_proj (v.part j).final_proj
        · rwa [v.final_zero]
        · exact huf j
        · exact v.orthogonal 0 j (Ne.symm hj)
    let a : Fin (n+1+1) → PartialIso M := Fin.lastCases w u
    have halast : a (Fin.last (n+1))=w := by simp only [a,Fin.lastCases_last]
    have hacast (i : Fin (n+1)) : a i.castSucc=u i := by simp only [a,Fin.lastCases_castSucc]
    have hai (i : Fin (n+1+1)) : (a i).initial=r := by
      induction i using Fin.lastCases with
      | last => rw [halast]
      | cast i => rw [hacast]; exact hui i
    have ha0 : (a 0:M)=r := by
      change (a (Fin.castSucc (0:Fin (n+1))) : M)=r
      rw [hacast]; exact hu0
    have hao (i j : Fin (n+1+1)) (hij : i ≠ j) : (a i).final*(a j).final=0 := by
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact (hij rfl).elim
        | cast j => rw [halast,hacast]; exact hwuj j
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          rw [hacast,halast]
          simpa only [star_mul,w.final_proj.isSelfAdjoint.star_eq,(u i).final_proj.isSelfAdjoint.star_eq,
            star_zero] using congrArg star (hwuj i)
        | cast j =>
          rw [hacast,hacast]
          exact projection_orthogonal_mono (u i).final_proj (u j).final_proj
            (v.part i).final_proj (v.part j).final_proj (huf i) (huf j)
            (v.orthogonal i j (fun he => hij (congrArg Fin.castSucc he)))
    let z : Frame M (n+1) := ⟨a,fun i => (hai i).trans (hai 0).symm,
      ha0.trans (hai 0).symm,hao⟩
    refine ⟨z,?_,?_⟩
    · change (a 0).initial ≠ 0
      rw [hai]
      exact PartialIso.initial_ne_zero hw0
    · apply z.support_le hp
      intro i
      induction i using Fin.lastCases with
      | last => change (a (Fin.last (n+1))).final ≤ p; rw [halast]; exact hwf.trans (v.base_le_support.trans hvp)
      | cast i => change (a i.castSucc).final ≤ p; rw [hacast]; exact (huf i).trans ((v.final_le_support i).trans hvp)

include hfaith in
lemma le_of_comparable_trace_le {v w : Frame M n} (hc : v ≤ w ∨ w ≤ v)
    (ht : (τ v.base).re ≤ (τ w.base).re) : v ≤ w := by
  rcases hc with h|h
  · exact h
  · have hh := HochschildDiffuse.projection_le_of_comparable_trace_le τ hfaith
      v.base_proj w.base_proj (Or.inr (base_mono h)) ht
    exact le_of_eq (eq_of_le_of_base_eq h (le_antisymm (base_mono h) hh)).symm

include e hτ htr hfaith in
lemma chain_upper (c : Set (Frame M n)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ s : Frame M n, ∀ v ∈ c, v ≤ s := by
  classical
  let T : Set ℝ := (fun v : Frame M n => (τ v.base).re) '' c
  have hTne : T.Nonempty := Set.Nonempty.image _ hne
  have hTbd : BddAbove T := ⟨(τ 1).re,by
    rintro _ ⟨v,hv,rfl⟩
    exact Complex.re_le_re (τ.monotone v.base_proj.le_one)⟩
  obtain ⟨b,hbm,_hbL,hbt,hb⟩ := (isLUB_csSup hTne hTbd).exists_seq_monotone_tendsto hTne
  choose a ha hab using hb
  change ∀ m, (τ (a m).base).re=b m at hab
  have ham : Monotone a := by
    intro j k hjk
    apply le_of_comparable_trace_le τ hfaith (hc.total (ha j) (ha k))
    rw [hab,hab]
    exact hbm hjk
  let L := HochschildSakai.mul_hasPreadjoint e
  choose v ht hle hleast using fun i : Fin (n+1) =>
    PartialIso.exists_monotone_limit e τ L hτ htr hfaith
      (fun m => (a m).part i) (fun j k hjk => ham hjk i)
  have hfin (i : Fin (n+1)) : GNSTendsto τ (fun m => ((a m).part i).final) atTop (v i).final :=
    (ht i).mul τ htr ((ht i).star τ htr) 1 (fun m => ((a m).part i).norm_le_one)
  have hini (i : Fin (n+1)) : GNSTendsto τ (fun m => ((a m).part i).initial) atTop (v i).initial :=
    ((ht i).star τ htr).mul τ htr (ht i) 1
      (fun m => by simpa only [norm_star] using ((a m).part i).norm_le_one)
  have hcommon (i : Fin (n+1)) : (v i).initial=(v 0).initial := by
    apply GNSTendsto.unique τ hfaith (hini i)
    simpa only [(a _).common] using hini 0
  have hanchor : (v 0:M)=(v 0).initial := by
    apply GNSTendsto.unique τ hfaith (ht 0)
    simpa only [(a _).anchor] using hini 0
  have horth (i j : Fin (n+1)) (hij : i ≠ j) : (v i).final*(v j).final=0 := by
    apply GNSTendsto.unique τ hfaith ((hfin i).mul τ htr (hfin j) 1
      (fun m => ((a m).part i).final_proj.norm_le _))
    simpa only [(a _).orthogonal i j hij] using GNSTendsto.const τ (0:M) atTop
  let s : Frame M n := ⟨v,hcommon,hanchor,horth⟩
  have htrace : (τ s.base).re=sSup T := by
    have hz := trace_predual_tendsto e τ hτ
      (predual_tendsto_of_preGNS e τ L hτ hfaith 1
        (fun m => ((a m).part 0).initial_proj.norm_le _) (hini 0))
    apply tendsto_nhds_unique (Complex.continuous_re.tendsto _ |>.comp hz)
    have hbb : ∀ m, (τ ((a m).part 0).initial).re=b m := hab
    simpa only [Function.comp_def,hbb] using hbt
  have has (m : ℕ) : a m ≤ s := fun i => hle i m
  refine ⟨s,?_⟩
  intro z hz
  by_cases hex : ∃ m, z ≤ a m
  · obtain ⟨m,hm⟩ := hex
    exact hm.trans (has m)
  · have haz : ∀ m, a m ≤ z := fun m =>
      (hc.total (ha m) hz).resolve_right (fun h => hex ⟨m,h⟩)
    have hsz : s ≤ z := fun i => hleast i (z.part i) (fun m => haz m i)
    apply le_of_comparable_trace_le τ hfaith (Or.inr hsz)
    rw [htrace]
    exact le_csSup hTbd ⟨z,hz,rfl⟩

include e hτ htr hfaith in

theorem exists_full (hII : TypeII1 M) (n : ℕ) : ∃ v : Frame M n, v.support=1 := by
  classical
  obtain ⟨v,_hv0,hmax⟩ := zorn_le_nonempty₀ (Set.univ : Set (Frame M n))
    (fun c _hc hchain y hy => by
      obtain ⟨s,hs⟩ := chain_upper e τ hτ htr hfaith c hchain ⟨y,hy⟩
      exact ⟨s,Set.mem_univ _,hs⟩) 0 (Set.mem_univ _)
  refine ⟨v,?_⟩
  by_contra hv
  obtain ⟨w,hw0,hw⟩ := exists_local e τ hτ htr hfaith hII n
    v.support_proj.one_sub (sub_ne_zero.mpr (Ne.symm hv))
  have horth := projection_orthogonal_of_le_complement v.support_proj w.support_proj hw
  have hle := v.le_orthogonalSum w horth
  have he := le_antisymm (hmax.2 (Set.mem_univ _) hle) hle
  have hh := congrArg Frame.base he
  rw [orthogonalSum_base] at hh
  exact hw0 (add_eq_left.mp hh)

end Frame
end HochschildComparison

end

end OAI
