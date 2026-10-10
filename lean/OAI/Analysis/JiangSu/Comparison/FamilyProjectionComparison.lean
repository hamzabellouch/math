import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.FamilyDyadicApproximation
import OAI.Analysis.JiangSu.Comparison.FiniteMatrixModels

namespace OAI

section

noncomputable section
namespace FamilyProjection
open Pureness CurrentMain DirectComparison Filter Topology
open scoped ComplexOrder ENNReal

variable {A I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty I] (T : I → TracialState A) (U : Ultrafilter ℕ)
local notation "D" => FamilyUltrapower T U
local notation "L" => familyLimitTrace T U
variable (hfree : (U : Filter ℕ)≤atTop)
variable (hsupply : SpectralProjectionSupply (familyLimitTrace T U)) (hnuc : IsNuclear A)
variable (hstrict : ∀ {p q : FamilyUltrapower T U},IsStarProjection p → IsStarProjection q →
  ∀ {c : ℝ},0<c → (∀ s : ℕ → I,((familyLimitTrace T U s).functional p).re+2*c≤((familyLimitTrace T U s).functional q).re) →
    ∃ v : FamilyUltrapower T U,star v*v=p ∧ q*v=v)

include hfree hsupply hnuc hstrict

 theorem projection_approx_comparison
    {p q : D} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hord : ∀ s : ℕ → I,((L s).functional p).re≤((L s).functional q).re)
    {t : ℝ} (ht : 0<t) (ht1 : t≤1) :
    ∃ w : D, ‖w‖≤1 ∧ familyTwoNorm L (star w*w-p)≤Real.sqrt t ∧
      familyTwoNorm L (q*w-w)≤Real.sqrt t := by
  classical
  let S : Set D := {1,p,q}
  have hS : S.Countable := Set.to_countable _
  obtain ⟨r,hr,_,htr⟩ := FamilyComparison.comparison_exact_relative_cut T U hfree hsupply hnuc
    S hS (IsStarProjection.one D) (fun a _ => Commute.one_left a) ⟨ht.le,ht1⟩
  have hrs := htr 1 (by simp [S])
  have hrp := htr p (by simp [S])
  have hrq := htr q (by simp [S])
  have hrt (s : ℕ → I) : (L s).functional r=(t:ℂ) := by
    simpa only [mul_one,(L s).normalized] using hrs.2 s
  have hrpt (s : ℕ → I) : (L s).functional (r*p)=(t:ℂ)*(L s).functional p := by
    simpa only [one_mul] using hrp.2 s
  have hrqt (s : ℕ → I) : (L s).functional (r*q)=(t:ℂ)*(L s).functional q := by
    simpa only [one_mul] using hrq.2 s
  let p' := (1-r)*p
  let q' := 1-(1-r)*(1-q)
  have hp' : IsStarProjection p' := hr.one_sub.mul hp ((Commute.one_left p).sub_left hrp.1)
  have hq' : IsStarProjection q' :=
    (hr.one_sub.mul hq.one_sub ((Commute.one_right (1-r)).sub_right ((Commute.one_left q).sub_left hrq.1))).one_sub
  have hpt (s : ℕ → I) :
      ((L s).functional p').re=(1-t)*((L s).functional p).re := by
    rw [show p'=p-r*p by dsimp [p']; noncomm_ring,map_sub,hrpt s]
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  have hqt (s : ℕ → I) :
      ((L s).functional q').re=(1-t)*((L s).functional q).re+t := by
    rw [show q'=q+r-r*q by dsimp [q']; noncomm_ring,map_sub,map_add,hrt s,hrqt s]
    simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  have hg (s : ℕ → I) :
      ((L s).functional p').re+2*(t/2)≤((L s).functional q').re := by
    rw [hpt,hqt]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (hord s))]
  obtain ⟨w,hw,hqw⟩ := hstrict hp' hq'
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

 theorem projection_comparison
    {p q : D} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hord : ∀ s : ℕ → I,((L s).functional p).re≤((L s).functional q).re) :
    ∃ w : D,star w*w=p ∧ q*w=w := by
  let t : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have ht (n : ℕ) : 0<t n := by dsimp [t]; positivity
  have ht1 (n : ℕ) : t n≤1 := by
    dsimp [t]
    exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have ht0 : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose w hwn hw hqw using fun n => projection_approx_comparison T U hfree hsupply hnuc hstrict hp hq hord (ht n) (ht1 n)
  have hlim : Tendsto (fun n => Real.sqrt (t n)) atTop (𝓝 0) := by
    convert (Real.continuous_sqrt.tendsto 0).comp ht0 using 1 <;> first | rfl | rw [Real.sqrt_zero]
  exact tracial_isometry_saturation T U hfree p q w hwn
    (squeeze_zero (fun n => familyTwoNorm_nonneg L _) hw hlim)
    (squeeze_zero (fun n => familyTwoNorm_nonneg L _) hqw hlim)

 theorem projection_equivalence
    {p q : D} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (heq : ∀ s : ℕ → I,((L s).functional p).re=((L s).functional q).re) :
    ∃ w : D,star w*w=p ∧ w*star w=q := by
  obtain ⟨w,hw,hqw⟩ := projection_comparison T U hfree hsupply hnuc hstrict hp hq
    (fun s => (heq s).le)
  have hwp := partialIsometry_right_support hp hw
  have hr : IsStarProjection (w*star w) := by
    constructor
    · change w*star w*(w*star w)=w*star w
      rw [mul_assoc w,←mul_assoc (star w),hw,←mul_assoc,hwp]
    · exact (mul_star_self_nonneg w).isSelfAdjoint
  have hrq : w*star w≤q := (hr.le_iff_mul_eq_right hq).mpr (by rw [←mul_assoc,hqw])
  have hz : q-w*star w=0 := by
    apply limitTrace_detects_positive_zero T U _ (sub_nonneg.mpr hrq)
    intro s
    rw [map_sub,Complex.sub_re,((L s).tracial w (star w)),hw,heq s,sub_self]
  exact ⟨w,hw,(sub_eq_zero.mp hz).symm⟩

 theorem tracial_matrix_corner
    (m : ℕ) (hm : 0 < m) {r : D} (hr : IsStarProjection r) :
    ∃ p : D, ∃ R : ProjectionRow (Fin m) p,R.sample p=r := by
  classical
  obtain ⟨p,hp,hortho,hsum,htr⟩ := FamilyComparison.comparison_relative_partition T U hfree hsupply hnuc {1} (Set.countable_singleton _) m hm hr
    (fun a ha => by simpa only [Set.mem_singleton_iff] using ha ▸ Commute.one_right r)
  let i₀ : Fin m := ⟨0,hm⟩
  have heq (i : Fin m) (s : ℕ → I) :
      ((L s).functional (p i₀)).re=((L s).functional (p i)).re := by
    have h0 := (htr i₀ 1 (Set.mem_singleton _)).2 s
    have hi := (htr i 1 (Set.mem_singleton _)).2 s
    simp only [mul_one] at h0 hi
    rw [h0,hi]
  choose v hv hvr using fun i => projection_equivalence T U hfree hsupply hnuc hstrict (hp i₀).1 (hp i).1 (heq i)
  have hright (i : Fin m) : star (v i)*p i=star (v i) :=
    partialIsometry_right_support (hp i).1 (by simpa only [star_star] using hvr i)
  have hleft (i : Fin m) : p i*v i=v i := by
    simpa only [star_mul,star_star,(hp i).1.isSelfAdjoint.star_eq] using congrArg star (hright i)
  let R : ProjectionRow (Fin m) (p i₀) := {
    projection := (hp i₀).1
    entry := v
    gram_diag := hv
    gram_offdiag := by
      intro i j hij
      calc
        star (v i)*v j=(star (v i)*p i)*(p j*v j) := by rw [hright,hleft]
        _ = star (v i)*(p i*p j)*v j := by noncomm_ring
        _ = 0 := by rw [hortho hij,mul_zero,zero_mul] }
  refine ⟨p i₀,R,?_⟩
  change (∑ i,v i*p i₀*star (v i))=r
  simp only [show ∀ i,v i*p i₀=v i from fun i => partialIsometry_right_support (hp i₀).1 (hv i),hvr]
  exact hsum

end FamilyProjection

end
end

section

noncomputable section
namespace FamilyProjection
open Pureness CurrentMain DirectPacking Filter
open scoped ComplexOrder

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] {I : Type} [Nonempty I] (T : I → TracialState A) (U : Ultrafilter ℕ)
local notation "D" => FamilyUltrapower T U
local notation "L" => familyLimitTrace T U
local notation "ι" => familyUltrapowerMap T U

 theorem comparison_finite_matrix_models (hfree : (U : Filter ℕ)≤atTop)
    (hsupply : DirectComparison.SpectralProjectionSupply L) (hnuc : IsNuclear A)
    (hstrict : ∀ {p q : D},IsStarProjection p → IsStarProjection q →
      ∀ {c : ℝ},0<c → (∀ s : ℕ → I,((L s).functional p).re+2*c≤((L s).functional q).re) →
        ∃ v : D,star v*v=p ∧ q*v=v)
    (m : ℕ) (hm : 0 < m) (K : Finset (unitary A)) {ε : ℝ} (hε : 0<ε) :
    Nonempty (TracialMatrixModel L ι m K ε) := by
  let := FamilyComparison.limitTraceFamily T U
  let := FamilyComparison.limitTraceFamily_nonempty T U
  obtain ⟨hs,hc,hi⟩ := FamilyComparison.source_tools T U hfree hsupply
  obtain ⟨M⟩ := matrix_models_from_packing hnuc ι hs hc hi hm
    (fun e he => tracial_matrix_corner T U hfree hsupply hnuc hstrict m hm he) K hε
  have h2 (a : D) : familyTwoNorm L a≤familyTwoNorm (fun τ : RestrictedTracialState D => (τ : TracialState D)) a := by
    apply ciSup_le
    intro s
    exact traceTwoNorm_le_family (fun τ : RestrictedTracialState D => (τ : TracialState D)) ⟨L s,⟨s,rfl⟩⟩ a
  exact ⟨{
    entry := M.entry
    norm_entry := M.norm_entry
    star_error := fun i j => (h2 _).trans_lt (M.star_error i j)
    mul_error := fun i j k l => (h2 _).trans_lt (M.mul_error i j k l)
    unit_error := (h2 _).trans_lt M.unit_error
    comm_error := fun i j u hu => (h2 _).trans_lt (M.comm_error i j u hu)}⟩

end FamilyProjection

end
end

end OAI
