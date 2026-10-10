import Mathlib
import OAI.Analysis.BoundedHochschild.DiffuseProjections
import OAI.Analysis.BoundedHochschild.OperatorPrimitives

namespace OAI

/-! Partial isometries and comparison of equal-trace projections. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped ComplexOrder
namespace HochschildComparison
variable {M : Type*} [CStarAlgebra M]

structure PartialIso (M : Type*) [CStarAlgebra M] where
  val : M
  mul_star_mul : val * star val * val = val

namespace PartialIso
instance : Coe (PartialIso M) M := ⟨val⟩
@[ext] lemma ext {v w : PartialIso M} (h : (v : M) = w) : v = w := by
  cases v; cases w; congr

def initial (v : PartialIso M) : M := star (v : M) * v
def final (v : PartialIso M) : M := (v : M) * star (v : M)
lemma mul_initial (v : PartialIso M) : (v : M) * v.initial = v := by
  simpa only [initial, ← mul_assoc] using v.mul_star_mul
lemma final_mul (v : PartialIso M) : v.final * (v : M) = v := v.mul_star_mul
lemma initial_proj (v : PartialIso M) : IsStarProjection v.initial := by
  refine ⟨?_, IsSelfAdjoint.star_mul_self _⟩
  change (star (v : M) * v) * (star (v : M) * v) = star (v : M) * v
  calc
    _ = star (v : M) * ((v : M) * star (v : M) * v) := by simp only [mul_assoc]
    _ = _ := by rw [v.mul_star_mul]
lemma final_proj (v : PartialIso M) : IsStarProjection v.final := by
  refine ⟨?_, IsSelfAdjoint.mul_star_self _⟩
  change ((v : M) * star (v : M)) * ((v : M) * star (v : M)) = (v : M) * star (v : M)
  calc
    _ = ((v : M) * star (v : M) * v) * star (v : M) := by simp only [mul_assoc]
    _ = _ := by rw [v.mul_star_mul]
lemma norm_le_one (v : PartialIso M) : ‖(v : M)‖ ≤ 1 := by
  have hi := v.initial_proj.norm_le _
  have he : ‖(v : M)‖ * ‖(v : M)‖ = ‖v.initial‖ := by
    exact CStarRing.norm_star_mul_self.symm
  nlinarith [norm_nonneg (v : M)]

variable [PartialOrder M]

instance : LE (PartialIso M) := ⟨fun v w => v.initial ≤ w.initial ∧ (w : M) * v.initial = v⟩
lemma le_def {v w : PartialIso M} : v ≤ w ↔
    v.initial ≤ w.initial ∧ (w : M) * v.initial = v := Iff.rfl
variable [StarOrderedRing M]

instance : PartialOrder (PartialIso M) where
  le_refl v := ⟨le_rfl, v.mul_initial⟩
  le_trans v w z hvw hwz := by
    refine ⟨hvw.1.trans hwz.1, ?_⟩
    calc
      (z : M) * v.initial = (z : M) * (w.initial * v.initial) := by
        rw [(v.initial_proj.le_iff_mul_eq_right w.initial_proj).mp hvw.1]
      _ = (w : M) * v.initial := by rw [← mul_assoc,hwz.2]
      _ = v := hvw.2
  le_antisymm v w hvw hwv := by
    apply ext
    have he := le_antisymm hvw.1 hwv.1
    have hh := hvw.2
    rw [he, w.mul_initial] at hh
    exact hh.symm

omit [StarOrderedRing M] in
lemma initial_mono {v w : PartialIso M} (h : v ≤ w) : v.initial ≤ w.initial := h.1
omit [StarOrderedRing M] in
lemma mul_initial_of_le {v w : PartialIso M} (h : v ≤ w) : (w : M) * v.initial = v := h.2
lemma star_mul_of_le {v w : PartialIso M} (h : v ≤ w) : star (v : M) * w = v.initial := by
  have hv := congrArg star h.2
  simp only [star_mul, v.initial_proj.isSelfAdjoint.star_eq] at hv
  calc
    star (v : M) * w = (v.initial * star (w : M)) * w := by rw [hv]
    _ = v.initial * w.initial := by simp only [initial,mul_assoc]
    _ = v.initial := (v.initial_proj.le_iff_mul_eq_left w.initial_proj).mp h.1
lemma star_mul_of_ge {v w : PartialIso M} (h : v ≤ w) : star (w : M) * v = v.initial := by
  simpa only [star_mul,star_star,v.initial_proj.isSelfAdjoint.star_eq]
    using congrArg star (star_mul_of_le h)
lemma final_mono {v w : PartialIso M} (h : v ≤ w) : v.final ≤ w.final := by
  apply (v.final_proj.le_iff_mul_eq_right w.final_proj).mpr
  calc
    w.final * v.final = (w : M) * (star (w : M) * v) * star (v : M) := by
      simp only [final,mul_assoc]
    _ = (w : M) * v.initial * star (v : M) := by rw [star_mul_of_ge h]
    _ = v.final := by rw [h.2]; rfl
lemma diff_square {v w : PartialIso M} (h : v ≤ w) :
    star ((w : M) - v) * ((w : M) - v) = w.initial - v.initial := by
  simp only [star_sub, sub_mul, mul_sub, star_mul_of_le h, star_mul_of_ge h,
    ]
  simp only [initial]
  abel

instance : Zero (PartialIso M) := ⟨⟨0, by simp⟩⟩
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma coe_zero : ((0 : PartialIso M) : M) = 0 := rfl
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma initial_zero : (0 : PartialIso M).initial = 0 := by simp [initial]
omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma final_zero : (0 : PartialIso M).final = 0 := by simp [final]
lemma zero_le (v : PartialIso M) : 0 ≤ v := by
  exact ⟨by simpa using v.initial_proj.nonneg, by simp⟩

section
omit [PartialOrder M] [StarOrderedRing M]

lemma star_mul_eq_zero_of_final_orthogonal {v w : PartialIso M}
    (h : v.final*w.final=0) : star (v : M)*w=0 := by
  have hv : star (v : M)*v.final=star (v : M) := by
    simpa only [star_mul,star_star,v.final_proj.isSelfAdjoint.star_eq]
      using congrArg star v.final_mul
  calc
    star (v : M)*w = (star (v : M)*v.final)*(w.final*(w : M)) := by
      rw [hv,w.final_mul]
    _ = star (v : M)*(v.final*w.final)*(w : M) := by simp only [mul_assoc]
    _ = 0 := by rw [h,mul_zero,zero_mul]

lemma mul_star_eq_zero_of_initial_orthogonal {v w : PartialIso M}
    (h : v.initial*w.initial=0) : (v : M)*star (w : M)=0 := by
  have hw : w.initial*star (w : M)=star (w : M) := by
    simpa only [star_mul,star_star,w.initial_proj.isSelfAdjoint.star_eq]
      using congrArg star w.mul_initial
  calc
    (v : M)*star (w : M) = ((v : M)*v.initial)*(w.initial*star (w : M)) := by
      rw [v.mul_initial,hw]
    _ = (v : M)*(v.initial*w.initial)*star (w : M) := by simp only [mul_assoc]
    _ = 0 := by rw [h,mul_zero,zero_mul]

lemma orthogonal_initial_symm {v w : PartialIso M} (h : v.initial*w.initial=0) :
    w.initial*v.initial=0 := by
  simpa only [star_mul,v.initial_proj.isSelfAdjoint.star_eq,
    w.initial_proj.isSelfAdjoint.star_eq,star_zero] using congrArg star h
lemma orthogonal_final_symm {v w : PartialIso M} (h : v.final*w.final=0) :
    w.final*v.final=0 := by
  simpa only [star_mul,v.final_proj.isSelfAdjoint.star_eq,
    w.final_proj.isSelfAdjoint.star_eq,star_zero] using congrArg star h

def orthogonalSum (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : PartialIso M where
  val := (v : M)+w
  mul_star_mul := by
    have hab := mul_star_eq_zero_of_initial_orthogonal hi
    have hba := mul_star_eq_zero_of_initial_orthogonal (orthogonal_initial_symm hi)
    have hab' := star_mul_eq_zero_of_final_orthogonal hf
    have hba' := star_mul_eq_zero_of_final_orthogonal (orthogonal_final_symm hf)
    simp only [star_add,mul_add,add_mul,hab,hba,zero_add,add_zero]
    rw [v.mul_star_mul,w.mul_star_mul,mul_assoc,mul_assoc,hab',hba',mul_zero,mul_zero]
    abel

lemma orthogonalSum_initial (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : (orthogonalSum v w hi hf).initial=v.initial+w.initial := by
  change star ((v : M)+w)*((v : M)+w)=_
  simp only [star_add,mul_add,add_mul,star_mul_eq_zero_of_final_orthogonal hf,
    star_mul_eq_zero_of_final_orthogonal (orthogonal_final_symm hf),zero_add,add_zero,initial]
lemma orthogonalSum_final (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : (orthogonalSum v w hi hf).final=v.final+w.final := by
  change ((v : M)+w)*star ((v : M)+w)=_
  simp only [star_add,mul_add,add_mul,mul_star_eq_zero_of_initial_orthogonal hi,
    mul_star_eq_zero_of_initial_orthogonal (orthogonal_initial_symm hi),zero_add,add_zero,final]
end

lemma le_orthogonalSum (v w : PartialIso M) (hi : v.initial*w.initial=0)
    (hf : v.final*w.final=0) : v ≤ orthogonalSum v w hi hf := by
  constructor
  · rw [orthogonalSum_initial]
    exact le_add_of_nonneg_right w.initial_proj.nonneg
  · change ((v : M)+w)*v.initial=v
    rw [add_mul,v.mul_initial]
    have hh : (w : M)*v.initial=0 := by
      calc
        (w : M)*v.initial = ((w : M)*w.initial)*v.initial := by rw [w.mul_initial]
        _ = 0 := by rw [mul_assoc,orthogonal_initial_symm hi,mul_zero]
    rw [hh,add_zero]

end PartialIso
end HochschildComparison

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildComparison
open BoundedHochschild HochschildRigidity HochschildDixmier
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

namespace PartialIso
omit [StarOrderedRing M] in
lemma eq_of_le_of_initial_eq {v w : PartialIso M} (h : v ≤ w)
    (hi : v.initial=w.initial) : v=w := by
  apply ext
  have hh := h.2
  rw [hi,w.mul_initial] at hh
  exact hh.symm

include hfaith in
lemma le_of_comparable_trace_le {v w : PartialIso M} (hc : v ≤ w ∨ w ≤ v)
    (ht : (τ v.initial).re ≤ (τ w.initial).re) : v ≤ w := by
  rcases hc with h|h
  · exact h
  · have hr := HochschildDiffuse.projection_le_of_comparable_trace_le τ hfaith
      v.initial_proj w.initial_proj (Or.inr h.1) ht
    have he := eq_of_le_of_initial_eq h (le_antisymm h.1 hr)
    exact le_of_eq he.symm

lemma diff_gns_sq {v w : PartialIso M} (h : v ≤ w) :
    ‖τ.toPreGNS ((w : M)-v)‖^2 = (τ w.initial).re-(τ v.initial).re := by
  have ht := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS ((w : M)-v)))
  simpa only [PositiveLinearMap.ofPreGNS_toPreGNS, ← Complex.ofReal_pow,
    Complex.ofReal_re,diff_square h,map_sub,Complex.sub_re] using ht

lemma monotone_gns_cauchy (v : ℕ → PartialIso M) (hv : Monotone v) :
    CauchySeq (fun n => τ.toPreGNS (v n : M)) := by
  have hm : Monotone (fun n => (τ (v n).initial).re) := fun i j hij =>
    Complex.re_le_re (τ.monotone (hv hij).1)
  have hb : BddAbove (Set.range (fun n => (τ (v n).initial).re)) :=
    ⟨(τ 1).re, fun _ ⟨n,hn⟩ => hn ▸ Complex.re_le_re (τ.monotone (v n).initial_proj.le_one)⟩
  have hc := (tendsto_atTop_ciSup hm hb).cauchySeq
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff'.mp hc (ε^2) (sq_pos_of_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have he := diff_gns_sq τ (hv hn)
  have hdiff := hN n hn
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hm hn))] at hdiff
  rw [dist_eq_norm,← map_sub]
  nlinarith [norm_nonneg (τ.toPreGNS ((v n : M)-v N))]

include e hL hτ htr hfaith in
lemma exists_monotone_limit (v : ℕ → PartialIso M) (hv : Monotone v) :
    ∃ w : PartialIso M, GNSTendsto τ (fun n => (v n : M)) atTop (w : M) ∧
      (∀ n, v n ≤ w) ∧ ∀ z : PartialIso M, (∀ n, v n ≤ z) → w ≤ z := by
  obtain ⟨w,hw,ht⟩ := exists_bounded_preGNS_limit e τ hL hτ 1
    (fun n => (v n).norm_le_one) (monotone_gns_cauchy τ v hv)
  change GNSTendsto τ (fun n => (v n : M)) atTop w at ht
  have hstar := ht.star τ htr
  have hin := hstar.mul τ htr ht 1 (fun n => by simpa only [norm_star] using (v n).norm_le_one)
  have hfin := ht.mul τ htr hstar 1 (fun n => (v n).norm_le_one)
  have hww : w*star w*w=w := by
    apply GNSTendsto.unique τ hfaith (hfin.mul τ htr ht 1 (fun n => (v n).final_proj.norm_le _))
    simpa only [(v _).mul_star_mul] using ht
  let s : PartialIso M := ⟨w,hww⟩
  change GNSTendsto τ (fun n => (v n).initial) atTop s.initial at hin
  refine ⟨s,ht,?_,?_⟩
  · intro n
    have him : (v n).initial ≤ s.initial := by
      apply ((v n).initial_proj.le_iff_mul_eq_left s.initial_proj).mpr
      apply GNSTendsto.unique τ hfaith
        ((GNSTendsto.const τ (v n).initial atTop).mul τ htr hin 1
          (fun _ => (v n).initial_proj.norm_le _))
      change Tendsto (fun m => ‖τ.toPreGNS ((v n).initial*(v m).initial-(v n).initial)‖) atTop (𝓝 0)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with m hm
      simp only [((v n).initial_proj.le_iff_mul_eq_left (v m).initial_proj).mp
        (hv hm).1,sub_self,map_zero,norm_zero]
    refine ⟨him,?_⟩
    apply GNSTendsto.unique τ hfaith (ht.mul τ htr (GNSTendsto.const τ (v n).initial atTop)
      1 (fun m => (v m).norm_le_one))
    change Tendsto (fun m => ‖τ.toPreGNS ((v m : M)*(v n).initial-(v n : M))‖) atTop (𝓝 0)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with m hm
    simp only [(hv hm).2,sub_self,map_zero,norm_zero]
  · intro z hz
    have him : s.initial ≤ z.initial := by
      apply (s.initial_proj.le_iff_mul_eq_left z.initial_proj).mpr
      apply GNSTendsto.unique τ hfaith (hin.mul τ htr (GNSTendsto.const τ z.initial atTop)
        1 (fun m => (v m).initial_proj.norm_le _))
      simpa only [((v _).initial_proj.le_iff_mul_eq_left z.initial_proj).mp (hz _).1]
        using hin
    refine ⟨him,?_⟩
    apply GNSTendsto.unique τ hfaith
      ((GNSTendsto.const τ (z : M) atTop).mul τ htr hin 1 (fun _ => z.norm_le_one))
    simpa only [(hz _).2] using ht

include e hL hτ htr hfaith in
lemma chain_upper {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (c : Set (PartialIso M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hs : ∀ v ∈ c, v.initial ≤ p ∧ v.final ≤ q) :
    ∃ s : PartialIso M, s.initial ≤ p ∧ s.final ≤ q ∧ ∀ v ∈ c, v ≤ s := by
  classical
  let T : Set ℝ := (fun v : PartialIso M => (τ v.initial).re) '' c
  have hTne : T.Nonempty := Set.Nonempty.image _ hne
  have hTbd : BddAbove T := ⟨(τ p).re,by
    rintro _ ⟨v,hv,rfl⟩
    exact Complex.re_le_re (τ.monotone (hs v hv).1)⟩
  obtain ⟨b,hbm,_hbub,hbt,hb⟩ := (isLUB_csSup hTne hTbd).exists_seq_monotone_tendsto hTne
  choose a ha hab using hb
  change ∀ n, (τ (a n).initial).re=b n at hab
  have ham : Monotone a := by
    intro m n hmn
    apply le_of_comparable_trace_le τ hfaith (hc.total (ha m) (ha n))
    rw [hab,hab]
    exact hbm hmn
  obtain ⟨s,ht,has,hsleast⟩ := exists_monotone_limit e τ hL hτ htr hfaith a ham
  have hi := (ht.star τ htr).mul τ htr ht 1
    (fun n => by simpa only [norm_star] using (a n).norm_le_one)
  have hf := ht.mul τ htr (ht.star τ htr) 1 (fun n => (a n).norm_le_one)
  change GNSTendsto τ (fun n => (a n).initial) atTop s.initial at hi
  change GNSTendsto τ (fun n => (a n).final) atTop s.final at hf
  have htrace : (τ s.initial).re=sSup T := by
    have hz := trace_predual_tendsto e τ hτ
      (predual_tendsto_of_preGNS e τ hL hτ hfaith 1
        (fun n => (a n).initial_proj.norm_le _) hi)
    apply tendsto_nhds_unique (Complex.continuous_re.tendsto _ |>.comp hz)
    simpa only [Function.comp_def,hab] using hbt
  refine ⟨s,?_,?_,?_⟩
  · apply (s.initial_proj.le_iff_mul_eq_left hp).mpr
    apply GNSTendsto.unique τ hfaith
      (hi.mul τ htr (GNSTendsto.const τ p atTop) 1 (fun n => (a n).initial_proj.norm_le _))
    simpa only [((a _).initial_proj.le_iff_mul_eq_left hp).mp (hs _ (ha _)).1] using hi
  · apply (s.final_proj.le_iff_mul_eq_left hq).mpr
    apply GNSTendsto.unique τ hfaith
      (hf.mul τ htr (GNSTendsto.const τ q atTop) 1 (fun n => (a n).final_proj.norm_le _))
    simpa only [((a _).final_proj.le_iff_mul_eq_left hq).mp (hs _ (ha _)).2] using hf
  · intro z hz
    by_cases hex : ∃ n, z ≤ a n
    · obtain ⟨n,hn⟩ := hex
      exact hn.trans (has n)
    · have haz : ∀ n, a n ≤ z := fun n =>
        (hc.total (ha n) hz).resolve_right (fun h => hex ⟨n,h⟩)
      apply le_of_comparable_trace_le τ hfaith (Or.inr (hsleast z haz))
      rw [htrace]
      exact le_csSup hTbd ⟨z,hz,rfl⟩
end PartialIso

include e hL hτ htr hfaith in
lemma exists_nonzero_corner (h1 : τ 1=1)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) : ∃ a : M, p*a*q ≠ 0 := by
  classical
  by_contra hex
  push Not at hex
  have hh := scalar_mem_orbit_closure e τ hL hτ h1 htr hfaith hfactor q
  obtain ⟨b,hb,hbt⟩ := mem_closure_iff_seq_limit.mp hh
  choose a ha hab using hb
  have han : ∀ n, p*a n=0 := by
    have hk : convexHull ℝ (Set.range (fun u : unitary M => conjugate u q)) ⊆
        {a : M | p*a=0} := by
      apply convexHull_min
      · rintro _ ⟨u,rfl⟩
        change p*((u : M)*q*star (u : M))=0
        rw [← mul_assoc,← mul_assoc,hex (u : M),zero_mul]
      · intro x hx y hy r t _hr _ht _hrt
        change p*x=0 at hx
        change p*y=0 at hy
        change p*(r • x+t • y)=0
        simp only [mul_add,mul_smul_comm,hx,hy,smul_zero,add_zero]
    exact fun n => hk (ha n)
  have ht : GNSTendsto τ a atTop ((τ q) • (1 : M)) := by
    have hz := tendsto_iff_norm_sub_tendsto_zero.mp hbt
    simpa only [GNSTendsto,← hab,← map_sub,gnsVector_norm] using hz
  have hpq : p*((τ q) • (1 : M))=0 := by
    apply GNSTendsto.unique τ hfaith
      ((GNSTendsto.const τ p atTop).mul τ htr ht 1 (fun _ => hp.norm_le _))
    simpa only [han] using (GNSTendsto.const τ (0 : M) (atTop : Filter ℕ))
  have htq : τ q ≠ 0 := by
    intro hzero
    apply hq0
    apply hfaith q
    simpa only [hq.isSelfAdjoint.star_eq,hq.isIdempotentElem.eq] using hzero
  rw [mul_smul_comm,mul_one,smul_eq_zero] at hpq
  exact hpq.elim htq hp0

include e in
lemma partialIso_of_nonzero_corner [CompleteSpace X]
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (b : M) (hb : b ≠ 0) (hpb : p*b=b) (hbq : b*q=b) :
    ∃ v : PartialIso M, (v : M) ≠ 0 ∧ v.initial ≤ q ∧ v.final ≤ p := by
  obtain ⟨v,r,s,hr,hvr,hvs,hs,hbabs,hvrv,_hsb⟩ :=
    HochschildPolar.exists_polar_partial_isometry e b
  have hva : star v*b=CFC.abs b := by
    calc
      star v*b = star v*(v*CFC.abs b) := congrArg (star v * ·) hbabs
      _ = CFC.abs b := by rw [← mul_assoc,hvr,hr.left]
  have hvp : p*v=v := by
    have hz : ((1-p)*v)*CFC.abs b=0 := by
      rw [mul_assoc,← hbabs,sub_mul,one_mul,hpb,sub_self]
    have hz' := HochschildPolar.support_right_annihilate hr
      (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg b)) hz
    rw [mul_assoc,hvrv,sub_mul,one_mul,sub_eq_zero] at hz'
    exact hz'.symm
  have hrq : r*q=r := by
    have ha : CFC.abs b*(1-q)=0 := by
      rw [← hva,mul_assoc,mul_sub,mul_one,hbq,sub_self,mul_zero]
    have hz := hr.annihilate (1-q) ha
    simpa only [mul_sub,mul_one,sub_eq_zero,eq_comm] using hz
  have hvpartial : v*star v*v=v := by rw [mul_assoc,hvr,hvrv]
  let w : PartialIso M := ⟨v,hvpartial⟩
  refine ⟨w,?_,?_,?_⟩
  · intro hv0
    change v=0 at hv0
    apply hb
    simpa only [hv0,zero_mul] using hbabs
  · change star v*v ≤ q
    rw [hvr]
    exact (hr.proj.le_iff_mul_eq_left hq).mpr hrq
  · apply (w.final_proj.le_iff_mul_eq_right hp).mpr
    change p*(v*star v)=v*star v
    rw [← mul_assoc,hvp]

private lemma projection_orthogonal_of_le_sub {p r t : M}
    (hp : IsStarProjection p) (hr : IsStarProjection r) (ht : IsStarProjection t)
    (hrp : r ≤ p) (htr : t ≤ p-r) : r*t=0 := by
  have hpr := (hr.le_iff_sub hp).mp hrp
  have hh := (ht.le_iff_mul_eq_right hpr).mp htr
  calc
    r*t = r*((p-r)*t) := by rw [hh]
    _ = (r*p-r*r)*t := by noncomm_ring
    _ = 0 := by rw [(hr.le_iff_mul_eq_left hp).mp hrp,hr.isIdempotentElem.eq,sub_self,zero_mul]

include e hτ htr hfaith in
 

theorem exists_partialIso_of_equal_trace [CompleteSpace X] (h1 : τ 1=1)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q) (ht : τ p=τ q) :
    ∃ v : M, star v*v=p ∧ v*star v=q := by
  classical
  let L := HochschildSakai.mul_hasPreadjoint e
  let S : Set (PartialIso M) := {v | v.initial ≤ p ∧ v.final ≤ q}
  have hzero : (0 : PartialIso M) ∈ S := by
    exact ⟨by simpa using hp.nonneg,by simpa using hq.nonneg⟩
  obtain ⟨v,_hzero,hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨s,hsp,hsq,hsup⟩ := PartialIso.chain_upper e τ L hτ htr hfaith hp hq
      c hchain ⟨y,hy⟩ (fun z hz => hc hz)
    exact ⟨s,⟨hsp,hsq⟩,hsup⟩) 0 hzero
  have hvp : v.initial ≤ p := hmax.1.1
  have hvq : v.final ≤ q := hmax.1.2
  have hfull : v.initial=p ∨ v.final=q := by
    by_contra hnot
    push Not at hnot
    have hp' := (v.initial_proj.le_iff_sub hp).mp hvp
    have hq' := (v.final_proj.le_iff_sub hq).mp hvq
    obtain ⟨a,ha⟩ := exists_nonzero_corner e τ L hτ htr hfaith h1 hfactor
      hq' hp' (sub_ne_zero.mpr hnot.2.symm) (sub_ne_zero.mpr hnot.1.symm)
    obtain ⟨w,hw0,hwp,hwq⟩ := partialIso_of_nonzero_corner e hq' hp'
      ((q-v.final)*a*(p-v.initial)) ha
      (by rw [← mul_assoc,← mul_assoc,hq'.isIdempotentElem.eq])
      (by rw [mul_assoc,hp'.isIdempotentElem.eq])
    have hi := projection_orthogonal_of_le_sub hp v.initial_proj w.initial_proj hvp hwp
    have hf := projection_orthogonal_of_le_sub hq v.final_proj w.final_proj hvq hwq
    have hs : v.orthogonalSum w hi hf ∈ S := by
      constructor
      · rw [PartialIso.orthogonalSum_initial]
        calc
          v.initial+w.initial ≤ v.initial+(p-v.initial) := add_le_add_right hwp _
          _ = p := by abel
      · rw [PartialIso.orthogonalSum_final]
        calc
          v.final+w.final ≤ v.final+(q-v.final) := add_le_add_right hwq _
          _ = q := by abel
    have hle := v.le_orthogonalSum w hi hf
    have he := le_antisymm (hmax.2 hs hle) hle
    have hvw : (v : M)+w=v := congrArg (fun z : PartialIso M => (z : M)) he
    exact hw0 (add_eq_left.mp hvw)
  have he : τ v.initial=τ v.final := htr _ _
  rcases hfull with hi|hf
  · have hback : q ≤ v.final := by
      apply HochschildDiffuse.projection_le_of_comparable_trace_le τ hfaith hq v.final_proj
        (Or.inr hvq)
      rw [← he,hi,ht]
    exact ⟨v,hi,le_antisymm hvq hback⟩
  · have hback : p ≤ v.initial := by
      apply HochschildDiffuse.projection_le_of_comparable_trace_le τ hfaith hp v.initial_proj
        (Or.inr hvp)
      rw [he,hf,ht]
    exact ⟨v,le_antisymm hvp hback,hf⟩

end HochschildComparison
end

end OAI
