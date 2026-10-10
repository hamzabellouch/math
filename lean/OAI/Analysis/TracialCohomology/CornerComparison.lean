import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts

namespace OAI

/-! Corner comparison for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCorners
open BoundedHochschild HochschildRigidity HochschildDixmier HochschildDiffuse
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (h1 : τ 1 = 1)
  (htr : ∀ a b : M, τ (a*b) = τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a) = 0 → a = 0)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b = c • (1 : M))

include e hτ h1 htr hfaith hfactor in

theorem connecting_corner {p q : M} (hp : IsStarProjection p)
    (_hq : IsStarProjection q) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    ∃ a : M, q*a*p ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hL := (HochschildSakai.abstract_multiplication_normal e).1
  have hs := scalar_mem_orbit_closure e τ hL hτ h1 htr hfaith hfactor p
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp hs
  choose c hc hcy using hy
  have hker : convexHull ℝ (Set.range (fun u : unitary M => conjugate u p)) ⊆
      {x : M | q*x = 0} := by
    apply convexHull_min
    · rintro _ ⟨u,rfl⟩
      change q * ((u : M)*p*star (u : M)) = 0
      rw [← mul_assoc, ← mul_assoc, hn (u : M), zero_mul]
    · intro a ha b hb r s _hr _hs _hrs
      change q*a=0 at ha
      change q*b=0 at hb
      change q * (r • a + s • b) = 0
      simp only [mul_add, mul_smul_comm, ha, hb, smul_zero, add_zero]
  have hc0 : ∀ n, q*c n = 0 := fun n => hker (hc n)
  have ht : Tendsto (fun n => ‖τ.toPreGNS (c n - (τ p) • (1 : M))‖)
      atTop (𝓝 0) := by
    have hh := tendsto_iff_norm_sub_tendsto_zero.mp hyt
    simpa only [← hcy, ← map_sub, gnsVector_norm] using hh
  have htq : Tendsto (fun n => ‖τ.toPreGNS (q*(c n - (τ p) • (1 : M)))‖)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => preGNS_norm_mul_le τ q (c n - (τ p) • (1 : M)))
    simpa only [mul_zero] using ht.const_mul ‖q‖
  have hzero : ‖τ.toPreGNS ((τ p) • q)‖ = 0 := by
    apply tendsto_nhds_unique (l := (atTop : Filter ℕ)) tendsto_const_nhds
    simpa only [mul_sub, hc0, zero_sub, mul_smul_comm, mul_one,
      map_neg, norm_neg] using htq
  have he : (τ p) • q = 0 := (preGNS_norm_eq_zero_iff τ hfaith _).mp hzero
  have hpτ : τ p ≠ 0 := by
    intro h
    have := projection_trace_pos τ hfaith hp hp0
    simp only [h, Complex.zero_re, lt_self_iff_false] at this
  exact (smul_eq_zero.mp he).elim hpτ hq0

include e in

theorem corner_polar {p q b : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hbp : b*p=b) (hqb : q*b=b) :
    ∃ v r s : M, IsStarProjection r ∧ IsStarProjection s ∧
      r ≤ p ∧ s ≤ q ∧ star v*v=r ∧ v*star v=s ∧ v*r=v ∧ s*v=v ∧
      b=v*CFC.abs b := by
  obtain ⟨v,r,s,hr,hi,hf,hs,hb,hvr,hsb⟩ :=
    HochschildPolar.exists_polar_partial_isometry e b
  have habs : star v*b=CFC.abs b := by
    calc
      star v*b = star v*(v*CFC.abs b) := congrArg (fun x => star v*x) hb
      _ = CFC.abs b := by rw [← mul_assoc,hi,hr.left]
  have hrp : r ≤ p := hr.le_of_support hp (by
    rw [← habs,mul_assoc,hbp])
  have hqv : q*v=v := by
    have hz : (q*v-v)*CFC.abs b=0 := by
      rw [sub_mul,mul_assoc,← hb,hqb,sub_self]
    have hzr := HochschildPolar.support_right_annihilate hr
      (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg b)) hz
    simpa only [sub_mul,mul_assoc,hvr,sub_eq_zero] using hzr
  have hsq : s ≤ q := (hs.le_iff_mul_eq_right hq).mpr (by
    rw [← hf,← mul_assoc,hqv])
  have hsv : s*v=v := by rw [← hf,mul_assoc,hi,hvr]
  exact ⟨v,r,s,hr.proj,hs,hrp,hsq,hi,hf,hvr,hsv,hb⟩

include e hτ h1 htr hfaith hfactor in

theorem nonzero_partial_isometry {p q : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    ∃ v r s : M, IsStarProjection r ∧ IsStarProjection s ∧
      r ≤ p ∧ s ≤ q ∧ star v*v=r ∧ v*star v=s ∧ v*r=v ∧ s*v=v ∧
      v ≠ 0 := by
  obtain ⟨a,ha⟩ := connecting_corner e τ hτ h1 htr hfaith hfactor hp hq hp0 hq0
  have hbp : (q*a*p)*p=q*a*p := by rw [mul_assoc,hp.isIdempotentElem.eq]
  have hqb : q*(q*a*p)=q*a*p := by
    rw [← mul_assoc,← mul_assoc,hq.isIdempotentElem.eq]
  obtain ⟨v,r,s,hr,hs,hrp,hsq,hi,hf,hvr,hsv,hb⟩ := corner_polar e hp hq hbp hqb
  exact ⟨v,r,s,hr,hs,hrp,hsq,hi,hf,hvr,hsv,fun hv => ha (by
    simpa only [hv,zero_mul] using hb)⟩

end PopaCorners

open Filter Topology
open scoped ComplexOrder
namespace PopaCorners
open BoundedHochschild HochschildRigidity HochschildDixmier HochschildDiffuse
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

structure CornerIso (p q : M) where
  val : M
  init_proj : IsStarProjection (star val*val)
  absorb : val*(star val*val)=val
  init_le : star val*val ≤ p
  final_le : val*star val ≤ q

namespace CornerIso
variable {p q : M}
instance : CoeOut (CornerIso p q) M := ⟨CornerIso.val⟩

omit [StarOrderedRing M] in
@[ext] theorem ext {v w : CornerIso p q} (h : (v:M)=(w:M)) : v=w := by
  cases v; cases w; cases h; rfl

def initial (v : CornerIso p q) : M := star (v:M)*(v:M)
def final (v : CornerIso p q) : M := (v:M)*star (v:M)

omit [StarOrderedRing M] in
lemma initial_proj (v : CornerIso p q) : IsStarProjection v.initial := v.init_proj
omit [StarOrderedRing M] in
lemma final_proj (v : CornerIso p q) : IsStarProjection v.final := by
  refine ⟨?_,IsSelfAdjoint.mul_star_self _⟩
  change ((v:M)*star (v:M))*((v:M)*star (v:M))=(v:M)*star (v:M)
  calc
    _ = ((v:M)*(star (v:M)*(v:M)))*star (v:M) := by simp only [mul_assoc]
    _ = (v:M)*star (v:M) := by rw [v.absorb]

omit [StarOrderedRing M] in
lemma mul_initial (v : CornerIso p q) : (v:M)*v.initial=(v:M) := v.absorb
omit [StarOrderedRing M] in
lemma final_mul (v : CornerIso p q) : v.final*(v:M)=(v:M) := by
  simpa only [final,mul_assoc] using v.absorb

omit [StarOrderedRing M] in
lemma norm_le_one (v : CornerIso p q) : ‖(v:M)‖ ≤ 1 := by
  have hn := v.init_proj.norm_le
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (v:M)]

instance : PartialOrder (CornerIso p q) where
  le v w := v.initial ≤ w.initial ∧ (w:M)*v.initial=(v:M)
  le_refl v := ⟨le_rfl,v.absorb⟩
  le_trans v w z hvw hwz := by
    refine ⟨hvw.1.trans hwz.1,?_⟩
    have hvwi := (v.initial_proj.le_iff_mul_eq_right w.initial_proj).mp hvw.1
    calc
      (z:M)*v.initial = (z:M)*(w.initial*v.initial) := by rw [hvwi]
      _ = ((z:M)*w.initial)*v.initial := by rw [mul_assoc]
      _ = (v:M) := by rw [hwz.2,hvw.2]
  le_antisymm v w hvw hwv := by
    apply ext
    have hi := le_antisymm hvw.1 hwv.1
    rw [hi,w.mul_initial] at hvw
    exact hvw.2.symm

lemma le_def {v w : CornerIso p q} : v ≤ w ↔
    v.initial ≤ w.initial ∧ (w:M)*v.initial=(v:M) := Iff.rfl

lemma initial_mono {v w : CornerIso p q} (h : v ≤ w) : v.initial ≤ w.initial := h.1
lemma mul_initial_of_le {v w : CornerIso p q} (h : v ≤ w) :
    (w:M)*v.initial=(v:M) := h.2

lemma star_mul_of_le {v w : CornerIso p q} (h : v ≤ w) :
    star (v:M)*(w:M)=v.initial := by
  have he := congrArg star h.2
  simp only [star_mul,v.initial_proj.isSelfAdjoint.star_eq] at he
  calc
    star (v:M)*(w:M) = (v.initial*star (w:M))*(w:M) := by rw [he]
    _ = v.initial*w.initial := by simp only [initial,mul_assoc]
    _ = v.initial := (v.initial_proj.le_iff_mul_eq_left w.initial_proj).mp h.1

lemma star_mul_of_ge {v w : CornerIso p q} (h : v ≤ w) :
    star (w:M)*(v:M)=v.initial := by
  simpa only [star_mul,star_star,v.initial_proj.isSelfAdjoint.star_eq]
    using congrArg star (star_mul_of_le h)

lemma sub_star_mul {v w : CornerIso p q} (h : v ≤ w) :
    star ((w:M)-(v:M))*((w:M)-(v:M))=w.initial-v.initial := by
  simp only [star_sub,sub_mul,mul_sub,star_mul_of_le h,star_mul_of_ge h]
  change w.initial-v.initial-(v.initial-v.initial)=w.initial-v.initial
  rw [sub_self,sub_zero]

lemma final_mono {v w : CornerIso p q} (h : v ≤ w) : v.final ≤ w.final := by
  apply (v.final_proj.le_iff_mul_eq_right w.final_proj).mpr
  change ((w:M)*star (w:M))*((v:M)*star (v:M))=(v:M)*star (v:M)
  calc
    _ = ((w:M)*(star (w:M)*(v:M)))*star (v:M) := by simp only [mul_assoc]
    _ = (v:M)*star (v:M) := by rw [star_mul_of_ge h,h.2]

def rank (τ : M →ₚ[ℂ] ℂ) (v : CornerIso p q) : ℝ := (τ v.initial).re

lemma rank_mono (τ : M →ₚ[ℂ] ℂ) : Monotone (rank τ : CornerIso p q → ℝ) := by
  intro v w h
  exact Complex.re_le_re (τ.monotone h.1)

lemma gns_sub_sq (τ : M →ₚ[ℂ] ℂ) {v w : CornerIso p q} (h : v ≤ w) :
    ‖τ.toPreGNS ((w:M)-(v:M))‖^2=rank τ w-rank τ v := by
  rw [← trace_star_mul_self_re,sub_star_mul h,map_sub,Complex.sub_re]
  rfl

lemma le_of_comparable_rank_le (τ : M →ₚ[ℂ] ℂ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) {v w : CornerIso p q}
    (hc : v ≤ w ∨ w ≤ v) (ht : rank τ v ≤ rank τ w) : v ≤ w := by
  rcases hc with h|h
  · exact h
  · have ha : (v:M)=(w:M) := by
      apply sub_eq_zero.mp
      apply (preGNS_norm_eq_zero_iff τ hfaith _).mp
      have hh := gns_sub_sq τ h
      nlinarith [norm_nonneg (τ.toPreGNS ((v:M)-(w:M)))]
    exact (ext ha).le

lemma monotone_cauchy (τ : M →ₚ[ℂ] ℂ) (v : ℕ → CornerIso p q)
    (hv : Monotone v) : CauchySeq (fun n => τ.toPreGNS (v n : M)) := by
  have hm : Monotone (fun n => rank τ (v n)) := (rank_mono τ).comp hv
  have hb : BddAbove (Set.range (fun n => rank τ (v n))) := by
    refine ⟨(τ 1).re,?_⟩
    rintro _ ⟨n,rfl⟩
    exact Complex.re_le_re (τ.monotone (v n).initial_proj.le_one)
  have hc := (tendsto_atTop_ciSup hm hb).cauchySeq
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff'.mp hc (ε^2) (sq_pos_of_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have hs := gns_sub_sq τ (hv hn)
  have hd := hN n hn
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hm hn))] at hd
  rw [dist_eq_norm]
  rw [map_sub] at hs
  nlinarith [norm_nonneg (τ.toPreGNS (v n:M)-τ.toPreGNS (v N:M))]

lemma projection_mul_zero_of_le_sub {p r t : M} (hp : IsStarProjection p)
    (hr : IsStarProjection r) (ht : IsStarProjection t) (hrp : r ≤ p) (htr : t ≤ p-r) :
    r*t=0 := by
  have hpr : IsStarProjection (p-r) := (hr.le_iff_sub hp).mp hrp
  have hh := (ht.le_iff_mul_eq_right hpr).mp htr
  calc
    r*t = r*((p-r)*t) := by rw [hh]
    _ = (r*p-r*r)*t := by noncomm_ring
    _ = 0 := by rw [(hr.le_iff_mul_eq_left hp).mp hrp,hr.isIdempotentElem.eq,
      sub_self,zero_mul]

lemma add_orthogonal (hp : IsStarProjection p) (hq : IsStarProjection q)
    (v : CornerIso p q) (u : CornerIso (p-v.initial) (q-v.final)) :
    ∃ w : CornerIso p q, (w:M)=(v:M)+(u:M) ∧ v ≤ w := by
  have hi : v.initial*u.initial=0 := projection_mul_zero_of_le_sub hp
    v.initial_proj u.initial_proj v.init_le u.init_le
  have hir : u.initial*v.initial=0 := by
    simpa only [star_mul,v.initial_proj.isSelfAdjoint.star_eq,
      u.initial_proj.isSelfAdjoint.star_eq,star_zero] using congrArg star hi
  have hf : v.final*u.final=0 := projection_mul_zero_of_le_sub hq
    v.final_proj u.final_proj v.final_le u.final_le
  have hvf : star (v:M)*v.final=star (v:M) := by
    simpa only [star_mul,v.final_proj.isSelfAdjoint.star_eq] using congrArg star v.final_mul
  have hui : u.initial*star (u:M)=star (u:M) := by
    simpa only [star_mul,u.initial_proj.isSelfAdjoint.star_eq] using congrArg star u.mul_initial
  have hcrossi : star (v:M)*(u:M)=0 := by
    calc
      _ = (star (v:M)*v.final)*(u.final*(u:M)) := by rw [hvf,u.final_mul]
      _ = star (v:M)*(v.final*u.final)*(u:M) := by simp only [mul_assoc]
      _ = 0 := by rw [hf,mul_zero,zero_mul]
  have hcrossir : star (u:M)*(v:M)=0 := by
    simpa only [star_mul,star_star,star_zero] using congrArg star hcrossi
  have hcrossf : (v:M)*star (u:M)=0 := by
    calc
      _ = ((v:M)*v.initial)*(u.initial*star (u:M)) := by rw [v.mul_initial,hui]
      _ = (v:M)*(v.initial*u.initial)*star (u:M) := by simp only [mul_assoc]
      _ = 0 := by rw [hi,mul_zero,zero_mul]
  have hcrossfr : (u:M)*star (v:M)=0 := by
    simpa only [star_mul,star_star,star_zero] using congrArg star hcrossf
  have hinit : star ((v:M)+(u:M))*((v:M)+(u:M))=v.initial+u.initial := by
    simp only [star_add,add_mul,mul_add,hcrossi,hcrossir,zero_add,add_zero,initial]
  have hfin : ((v:M)+(u:M))*star ((v:M)+(u:M))=v.final+u.final := by
    simp only [star_add,add_mul,mul_add,hcrossf,hcrossfr,zero_add,add_zero,final]
  have hvui : (v:M)*u.initial=0 := by
    calc
      _ = ((v:M)*v.initial)*u.initial := by rw [v.mul_initial]
      _ = 0 := by rw [mul_assoc,hi,mul_zero]
  have huvi : (u:M)*v.initial=0 := by
    calc
      _ = ((u:M)*u.initial)*v.initial := by rw [u.mul_initial]
      _ = 0 := by rw [mul_assoc,hir,mul_zero]
  have hsum : IsStarProjection (v.initial+u.initial) :=
    v.initial_proj.add u.initial_proj hi
  have hsum_le : v.initial+u.initial ≤ p := by
    calc
      _ ≤ v.initial+(p-v.initial) := add_le_add le_rfl u.init_le
      _ = p := by abel
  have hsumf_le : v.final+u.final ≤ q := by
    calc
      _ ≤ v.final+(q-v.final) := add_le_add le_rfl u.final_le
      _ = q := by abel
  let w : CornerIso p q := ⟨(v:M)+(u:M),by rw [hinit]; exact hsum,
    by rw [hinit]; simp only [add_mul,mul_add,v.mul_initial,u.mul_initial,hvui,huvi,
      zero_add,add_zero],by rw [hinit]; exact hsum_le,by rw [hfin]; exact hsumf_le⟩
  refine ⟨w,rfl,?_,?_⟩
  · change v.initial ≤ star ((v:M)+(u:M))*((v:M)+(u:M))
    rw [hinit]
    exact le_add_of_nonneg_right u.initial_proj.nonneg
  · change ((v:M)+(u:M))*v.initial=(v:M)
    rw [add_mul,v.mul_initial,huvi,add_zero]

section Dual
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in
lemma rank_tendsto {v : ℕ → CornerIso p q} {w : CornerIso p q}
    (ht : GNSTendsto τ (fun n => (v n:M)) atTop (w:M)) :
    Tendsto (fun n => rank τ (v n)) atTop (𝓝 (rank τ w)) := by
  have hL := (HochschildSakai.abstract_multiplication_normal e).1
  have hi := (ht.star τ htr).mul τ htr ht 1 (fun n => by
    simpa only [norm_star] using (v n).norm_le_one)
  have hp := predual_tendsto_of_preGNS e τ hL hτ hfaith 1
    (fun n => (v n).initial_proj.norm_le _) hi
  exact Complex.continuous_re.tendsto _ |>.comp (trace_predual_tendsto e τ hτ hp)

include e hτ htr hfaith in

theorem monotone_limit (hp : IsStarProjection p) (hq : IsStarProjection q)
    (v : ℕ → CornerIso p q) (hv : Monotone v) :
    ∃ w : CornerIso p q, GNSTendsto τ (fun n => (v n:M)) atTop (w:M) ∧
      (∀ n, v n ≤ w) ∧ (∀ z, (∀ n, v n ≤ z) → w ≤ z) := by
  have hL := (HochschildSakai.abstract_multiplication_normal e).1
  obtain ⟨r,hr,hrt,hrn,hrle⟩ := exists_monotone_projection_limit e τ hL hτ htr hfaith
    (fun n => (v n).initial) (fun n => (v n).initial_proj)
    (fun _ _ h => (hv h).1)
  obtain ⟨s,hs,hst,hsn,hsle⟩ := exists_monotone_projection_limit e τ hL hτ htr hfaith
    (fun n => (v n).final) (fun n => (v n).final_proj)
    (fun _ _ h => final_mono (hv h))
  obtain ⟨w,hw,hwt⟩ := exists_bounded_preGNS_limit e τ hL hτ 1
    (fun n => (v n).norm_le_one) (monotone_cauchy τ v hv)
  change GNSTendsto τ (fun n => (v n:M)) atTop w at hwt
  have hwi : star w*w=r := GNSTendsto.unique τ hfaith
    ((hwt.star τ htr).mul τ htr hwt 1 (fun n => by
      simpa only [norm_star] using (v n).norm_le_one)) hrt
  have hwf : w*star w=s := GNSTendsto.unique τ hfaith
    (hwt.mul τ htr (hwt.star τ htr) 1 (fun n => (v n).norm_le_one)) hst
  have hwa : w*r=w := by
    apply GNSTendsto.unique τ hfaith
      (hwt.mul τ htr hrt 1 (fun n => (v n).norm_le_one))
    simpa only [(v _).mul_initial] using hwt
  let W : CornerIso p q := ⟨w,by rw [hwi]; exact hr,
    by rw [hwi]; exact hwa,
    by rw [hwi]; exact hrle p hp (fun n => (v n).init_le),
    by rw [hwf]; exact hsle q hq (fun n => (v n).final_le)⟩
  refine ⟨W,hwt,?_,?_⟩
  · intro n
    change (v n).initial ≤ star w*w ∧ w*(v n).initial=(v n:M)
    refine ⟨by rw [hwi]; exact hrn n,?_⟩
    apply GNSTendsto.unique τ hfaith
      (hwt.mul τ htr (GNSTendsto.const τ (v n).initial atTop) 1
        (fun m => (v m).norm_le_one))
    change Tendsto (fun m => ‖τ.toPreGNS ((v m:M)*(v n).initial-(v n:M))‖) atTop (𝓝 0)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with m hm
    simp only [(hv hm).2,sub_self,map_zero,norm_zero]
  · intro z hz
    change star w*w ≤ z.initial ∧ (z:M)*(star w*w)=w
    rw [hwi]
    refine ⟨hrle z.initial z.initial_proj (fun n => (hz n).1),?_⟩
    apply GNSTendsto.unique τ hfaith
      ((GNSTendsto.const τ (z:M) atTop).mul τ htr hrt 1
        (fun _ => z.norm_le_one))
    simpa only [(hz _).2] using hwt

include e hτ htr hfaith in

theorem chain_upper (hp : IsStarProjection p) (hq : IsStarProjection q)
    (c : Set (CornerIso p q)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
    ∃ w : CornerIso p q, ∀ v ∈ c, v ≤ w := by
  classical
  let T : Set ℝ := rank τ '' c
  have hTne : T.Nonempty := Set.Nonempty.image _ hne
  have hTbd : BddAbove T := by
    refine ⟨(τ p).re,?_⟩
    rintro _ ⟨v,hv,rfl⟩
    exact Complex.re_le_re (τ.monotone v.init_le)
  obtain ⟨t,htm,_htL,htt,htc⟩ := (isLUB_csSup hTne hTbd).exists_seq_monotone_tendsto hTne
  choose a ha hat using htc
  change ∀ n, rank τ (a n)=t n at hat
  have ham : Monotone a := by
    intro m n hmn
    apply le_of_comparable_rank_le τ hfaith (hc.total (ha m) (ha n))
    rw [hat,hat]
    exact htm hmn
  obtain ⟨w,hwt,hwn,hwl⟩ := monotone_limit e τ hτ htr hfaith hp hq a ham
  have hwr : rank τ w=sSup T := by
    apply tendsto_nhds_unique (rank_tendsto e τ hτ htr hfaith hwt)
    simpa only [hat] using htt
  refine ⟨w,?_⟩
  intro v hv
  by_cases hex : ∃ n, v ≤ a n
  · obtain ⟨n,hn⟩ := hex
    exact hn.trans (hwn n)
  · have haw : ∀ n, a n ≤ v := by
      intro n
      exact (hc.total (ha n) hv).resolve_right (fun h => hex ⟨n,h⟩)
    apply le_of_comparable_rank_le τ hfaith (Or.inr (hwl v haw))
    rw [hwr]
    exact le_csSup hTbd ⟨v,hv,rfl⟩

def zero (hp : IsStarProjection p) (hq : IsStarProjection q) : CornerIso p q :=
  ⟨0,by simpa only [star_zero,zero_mul] using IsStarProjection.zero M,
    by simp only [zero_mul],by simpa only [zero_mul,star_zero] using hp.nonneg,
    by simpa only [zero_mul,star_zero] using hq.nonneg⟩

include e hτ htr hfaith in
lemma exists_maximal (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ v : CornerIso p q, ∀ w : CornerIso p q, v ≤ w → w ≤ v := by
  classical
  obtain ⟨v,_hv,hmax⟩ := zorn_le_nonempty₀ (Set.univ : Set (CornerIso p q))
    (fun c hc hchain y hy => by
      obtain ⟨w,hw⟩ := chain_upper e τ hτ htr hfaith hp hq c hchain ⟨y,hy⟩
      exact ⟨w,Set.mem_univ w,hw⟩) (zero hp hq) (Set.mem_univ _)
  exact ⟨v,fun w hw => hmax.2 (Set.mem_univ w) hw⟩

include e hτ htr hfaith in

theorem maximal_fills (h1 : τ 1=1)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))
    (hp : IsStarProjection p) (hq : IsStarProjection q) (v : CornerIso p q)
    (hv : ∀ w : CornerIso p q, v ≤ w → w ≤ v) : v.initial=p ∨ v.final=q := by
  by_contra hn
  push Not at hn
  have hpv : IsStarProjection (p-v.initial) := (v.initial_proj.le_iff_sub hp).mp v.init_le
  have hqv : IsStarProjection (q-v.final) := (v.final_proj.le_iff_sub hq).mp v.final_le
  have hpv0 : p-v.initial ≠ 0 := fun h => hn.1 (sub_eq_zero.mp h).symm
  have hqv0 : q-v.final ≠ 0 := fun h => hn.2 (sub_eq_zero.mp h).symm
  obtain ⟨t,r,s,hr,hs,hrp,hsq,hti,htf,htrt,hstt,ht0⟩ :=
    nonzero_partial_isometry e τ hτ h1 htr hfaith hfactor hpv hqv hpv0 hqv0
  let u : CornerIso (p-v.initial) (q-v.final) :=
    ⟨t,by rw [hti]; exact hr,by rw [hti]; exact htrt,
      by rw [hti]; exact hrp,by rw [htf]; exact hsq⟩
  obtain ⟨w,hw,hle⟩ := add_orthogonal hp hq v u
  have he : w=v := le_antisymm (hv w hle) hle
  have hsum : (v:M)+t=(v:M) := by simpa only [he] using hw.symm
  exact ht0 (add_eq_left.mp hsum)

include e hτ htr hfaith in

theorem exists_full_initial (h1 : τ 1=1)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : (τ p).re ≤ (τ q).re) :
    ∃ v : CornerIso p q, v.initial=p := by
  obtain ⟨v,hv⟩ := exists_maximal e τ hτ htr hfaith hp hq
  refine ⟨v,?_⟩
  rcases maximal_fills e τ hτ htr hfaith h1 hfactor hp hq v hv with h|h
  · exact h
  · have htrace : (τ v.initial).re=(τ v.final).re :=
      congrArg Complex.re (htr (star (v:M)) (v:M))
    have hpi : p ≤ v.initial := by
      apply projection_le_of_comparable_trace_le τ hfaith hp v.initial_proj (Or.inr v.init_le)
      rw [htrace,h]
      exact hpq
    exact le_antisymm v.init_le hpi

include e hτ htr hfaith in

theorem equivalent_of_trace_eq (h1 : τ 1=1)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : (τ p).re=(τ q).re) :
    ∃ v : M, star v*v=p ∧ v*star v=q ∧ v*p=v ∧ q*v=v := by
  obtain ⟨v,hvp⟩ := exists_full_initial e τ hτ htr hfaith h1 hfactor hp hq hpq.le
  have htrace : (τ v.final).re=(τ q).re := by
    change (τ ((v:M)*star (v:M))).re=(τ q).re
    rw [htr]
    change (τ v.initial).re=(τ q).re
    rw [hvp,hpq]
  have hqv : q ≤ v.final := projection_le_of_comparable_trace_le τ hfaith hq v.final_proj
    (Or.inr v.final_le) htrace.ge
  have hvq : v.final=q := le_antisymm v.final_le hqv
  exact ⟨(v:M),hvp,hvq,by simpa only [hvp] using v.mul_initial,
    by simpa only [hvq] using v.final_mul⟩

end Dual

end CornerIso
end PopaCorners

end

end OAI
