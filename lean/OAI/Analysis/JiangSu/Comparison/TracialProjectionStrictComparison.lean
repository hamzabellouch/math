import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.ExactRelativeCut
import OAI.Analysis.JiangSu.Traces.UnitalNormToTracial
import OAI.Analysis.JiangSu.MatrixAlgebras.ProjectionLiftTraces
import OAI.Analysis.JiangSu.CentralSequences.SmallTraceNormUltrapower

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
local notation "T" => (fun τ : TracialState A => τ)
local notation "D" => FamilyUltrapower T U
local notation "L" => familyLimitTrace T U

 theorem tracial_projection_strict_comparison (hfree : (U : Filter ℕ)≤atTop)
    (hcmp : StrictComparison A) {p q : D} (hp : IsStarProjection p) (hq : IsStarProjection q)
    {c : ℝ} (hc : 0<c)
    (hgap : ∀ s : ℕ → TracialState A,
      ((L s).functional p).re+2*c≤((L s).functional q).re) :
    ∃ v : D,star v*v=p ∧ q*v=v := by
  let J := familyNullIdeal T (U : Filter ℕ)
  obtain ⟨e,hep,hen,he⟩ := positive_contraction_lift J hp.nonneg hp.norm_le
  obtain ⟨f,hfp,hfn,hf⟩ := positive_contraction_lift J hq.nonneg hq.norm_le
  have ep (n : ℕ) : 0≤e n := map_nonneg (boundedFamilyEval n) hep
  have fp (n : ℕ) : 0≤f n := map_nonneg (boundedFamilyEval n) hfp
  have en (n : ℕ) : ‖e n‖≤1 := (lp.norm_apply_le_norm ENNReal.top_ne_zero e n).trans hen
  have fn (n : ℕ) : ‖f n‖≤1 := (lp.norm_apply_le_norm ENNReal.top_ne_zero f n).trans hfn
  have he' : IsStarProjection (J.quotientStarHom e) := he ▸ hp
  have hf' : IsStarProjection (J.quotientStarHom f) := hf ▸ hq
  have hg : ∀ᶠ n in (U : Filter ℕ),∀ τ : TracialState A,
      (τ.functional (e n)).re+c≤(τ.functional (f n)).re := by
    apply uniform_trace_gap_eventually U e f hc
    intro s
    change ((L s).functional (J.quotientMap e)).re+2*c≤((L s).functional (J.quotientMap f)).re
    rw [he,hf]
    exact hgap s
  obtain ⟨v,hv,hqv⟩ := projection_gap_norm_ultrapower hcmp U hfree e f ep en fp fn c hc
    (fun _ hr => projection_lift_defect U e he' hr) hg
    (fun _ hr => projection_lift_defect U f hf' hr)
  refine ⟨normToTracial (A := A) U v,?_,?_⟩
  · have h := congrArg (normToTracial (A := A) U) hv
    simp only [map_mul,map_star,normToTracial_mk] at h
    change star (normToTracial (A := A) U v)*normToTracial (A := A) U v=J.quotientMap e at h
    exact h.trans he
  · have h := congrArg (normToTracial (A := A) U) hqv
    simp only [map_mul,normToTracial_mk] at h
    change J.quotientMap f*normToTracial (A := A) U v=normToTracial (A := A) U v at h
    rwa [hf] at h

end DirectComparison

end
end

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
local notation "T" => (fun τ : TracialState A => τ)
local notation "D" => FamilyUltrapower T U
local notation "L" => familyLimitTrace T U

 theorem tracial_projection_approx_comparison (hfree : (U : Filter ℕ)≤atTop)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : StrictComparison A) (hnuc : IsNuclear A)
    {p q : D} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hord : ∀ s : ℕ → TracialState A,((L s).functional p).re≤((L s).functional q).re)
    {t : ℝ} (ht : 0<t) (ht1 : t≤1) :
    ∃ w : D, ‖w‖≤1 ∧ familyTwoNorm L (star w*w-p)≤Real.sqrt t ∧
      familyTwoNorm L (q*w-w)≤Real.sqrt t := by
  classical
  let S : Set D := {1,p,q}
  have hS : S.Countable := Set.to_countable _
  obtain ⟨r,hr,_,htr⟩ := comparison_exact_relative_cut U hfree hsimple hinf hcmp hnuc
    S hS (IsStarProjection.one D) (fun a _ => Commute.one_left a) ⟨ht.le,ht1⟩
  have hrs := htr 1 (by simp [S])
  have hrp := htr p (by simp [S])
  have hrq := htr q (by simp [S])
  have hrt (s : ℕ → TracialState A) : (L s).functional r=(t:ℂ) := by
    simpa only [mul_one,(L s).normalized] using hrs.2 s
  have hrpt (s : ℕ → TracialState A) : (L s).functional (r*p)=(t:ℂ)*(L s).functional p := by
    simpa only [one_mul] using hrp.2 s
  have hrqt (s : ℕ → TracialState A) : (L s).functional (r*q)=(t:ℂ)*(L s).functional q := by
    simpa only [one_mul] using hrq.2 s
  let p' := (1-r)*p
  let q' := 1-(1-r)*(1-q)
  have hp' : IsStarProjection p' := hr.one_sub.mul hp ((Commute.one_left p).sub_left hrp.1)
  have hq' : IsStarProjection q' :=
    (hr.one_sub.mul hq.one_sub ((Commute.one_right (1-r)).sub_right ((Commute.one_left q).sub_left hrq.1))).one_sub
  have hpt (s : ℕ → TracialState A) :
      ((L s).functional p').re=(1-t)*((L s).functional p).re := by
    rw [show p'=p-r*p by dsimp [p']; noncomm_ring,map_sub,hrpt s]
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  have hqt (s : ℕ → TracialState A) :
      ((L s).functional q').re=(1-t)*((L s).functional q).re+t := by
    rw [show q'=q+r-r*q by dsimp [q']; noncomm_ring,map_sub,map_add,hrt s,hrqt s]
    simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  have hg (s : ℕ → TracialState A) :
      ((L s).functional p').re+2*(t/2)≤((L s).functional q').re := by
    rw [hpt,hqt]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (hord s))]
  obtain ⟨w,hw,hqw⟩ := tracial_projection_strict_comparison U hfree hcmp hp' hq'
    (show 0<t/2 by positivity) hg
  have hwn : ‖w‖≤1 := by
    have hh : ‖w‖*‖w‖≤1 := by rw [←CStarRing.norm_star_mul_self,hw]; exact hp'.norm_le
    nlinarith [norm_nonneg w]
  have hrn : familyTwoNorm L r≤Real.sqrt t := by
    apply ciSup_le
    intro s
    have hs := traceTwoNorm_projection_sq (L s) hr
    rw [hrt s,Complex.ofReal_re] at hs
    nlinarith [traceTwoNorm_nonneg (L s) r,Real.sqrt_nonneg t,Real.sq_sqrt ht.le]
  refine ⟨w,hwn,?_,?_⟩
  · rw [hw,show p'-p= -(r*p) by dsimp [p']; noncomm_ring,familyTwoNorm_neg]
    exact (familyTwoNorm_mul_right L r p).trans ((mul_le_mul_of_nonneg_left hp.norm_le
      (familyTwoNorm_nonneg L r)).trans (by simpa only [mul_one] using hrn))
  · have he : q*w-w= -(r*(1-q)*w) := by
      calc
        q*w-w=(q-q')*w := by rw [sub_mul,hqw]
        _ = -(r*(1-q)*w) := by dsimp [q']; noncomm_ring
    rw [he,familyTwoNorm_neg]
    apply (familyTwoNorm_mul_right L (r*(1-q)) w).trans
    apply (mul_le_mul_of_nonneg_left hwn (familyTwoNorm_nonneg L _)).trans
    rw [mul_one]
    exact (familyTwoNorm_mul_right L r (1-q)).trans
      ((mul_le_mul_of_nonneg_left hq.one_sub.norm_le (familyTwoNorm_nonneg L r)).trans
        (by simpa only [mul_one] using hrn))

end DirectComparison

end
end

end OAI
