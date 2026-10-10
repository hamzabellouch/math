import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.ExactLocalSupply

namespace OAI

noncomputable section
namespace FamilyComparison
open Pureness CurrentMain DirectComparison Filter Topology
open scoped ComplexOrder ENNReal NNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] {I : Type} [Nonempty I] (θ : I → TracialState A)
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
local notation "D" => FamilyUltrapower θ U
local notation "Λ" => familyLimitTrace θ U

include hfree in
lemma exact_local_projection (hsupply : SpectralProjectionSupply (familyLimitTrace θ U))
    {q : D} (hq : IsStarProjection q) {x : D}
    (hx : IsSelfAdjoint x) (hxn : ‖x‖ ≤ 1) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hf01 : ∀ t ∈ Set.Icc (-1:ℝ) 1, f t ∈ Set.Icc 0 1)
    (hsupp : ∀ t ∈ Set.Icc (-1:ℝ) 1, f t ≠ 0 → g t=1) :
    ∃ p : D, IsStarProjection p ∧ p ≤ q ∧
      directCutoff (1/2) (cornerCFC hq x g)*p=p ∧
      p*directCutoff (1/2) (cornerCFC hq x g)=p ∧
      ∀ s : ℕ → I, (Λ s).functional p=(Λ s).functional (cornerCFC hq x f) := by
  classical
  let h := cornerCFC hq x f
  let k := directCutoff (1/2) (cornerCFC hq x g)
  have hh : 0 ≤ h := cornerCFC_nonneg hq hx hxn hf (fun t ht => (hf01 t ht).1)
  have hhn : ‖h‖ ≤ 1 := cornerCFC_norm_le_one hq hx hxn hf01
  let e : ℕ → ℝ := fun m => 1/((m:ℝ)+2)
  have he (m : ℕ) : 0 < e m := by dsimp [e]; positivity
  have he1 (m : ℕ) : e m < 1 := by
    dsimp [e]
    rw [div_lt_one (by positivity)]
    have := Nat.cast_nonneg (α := ℝ) m
    linarith
  have helim : Tendsto e atTop (𝓝 0) := by
    have ht : Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have ht2 := ht.comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun m : ℕ => 1/(((m+1:ℕ):ℝ)+1)) atTop (𝓝 0) at ht2
    simpa only [e,Nat.cast_add,Nat.cast_one,add_assoc,
      show (1:ℝ)+1=2 from by norm_num] using ht2
  choose p hp hleft hright htrace using fun m =>
    hsupply h hh hhn (e m) (he m) (he1 m)
  have hfix (m : ℕ) (a : D) (ha : a ∈ ({q,k} : Finset D)) : a*p m=p m := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · rw [←hleft m,←mul_assoc,(localized_cutoff_mem hq x f (e m)).1,hleft m]
    · rw [←hleft m,←mul_assoc]
      rw [corner_cutoff_fixes_cutoff hq hx hxn hf hg hsupp (e m) (1/2)
        (by norm_num) (by norm_num),hleft m]
  have htr : Tendsto (fun m => familyTraceNorm Λ (p m-h)) atTop (𝓝 0) := by
    apply squeeze_zero (fun m => familyTraceNorm_nonneg Λ _) _ helim
    intro m
    apply ciSup_le
    intro s
    rw [map_sub,htrace m,←map_sub]
    exact (trace_norm_le_norm (Λ s) _).trans (by
      rw [norm_sub_rev]
      exact norm_sub_directPositiveCut_le h hh (e m) (he m).le)
  obtain ⟨P,hP,hPf,hPt⟩ := projection_saturation θ U hfree
    {q,k} h p hp hfix htr
  have hqP : q*P=P := hPf q (by simp)
  have hkP : k*P=P := hPf k (by simp)
  have hPk : P*k=P := by
    have hksa : IsSelfAdjoint k := cfc_predicate _ _
    have he := congrArg star hkP
    simpa only [star_mul,hP.isSelfAdjoint.star_eq,hksa.star_eq] using he
  exact ⟨P,hP,(hP.le_iff_mul_eq_right hq).mpr hqP,hkP,hPk,hPt⟩

end FamilyComparison

namespace FamilyComparison
open Pureness CurrentMain DirectComparison Filter Topology
open scoped ComplexOrder ENNReal NNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] {I : Type} [Nonempty I] (θ : I → TracialState A)
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
local notation "D" => FamilyUltrapower θ U
local notation "Λ" => familyLimitTrace θ U

theorem proportional_subprojection (hsupply : SpectralProjectionSupply (familyLimitTrace θ U))
    {q : D} (hq : IsStarProjection q) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ∃ p : D, IsStarProjection p ∧ p ≤ q ∧
      ∀ s : ℕ → I, (Λ s).functional p = (t : ℂ)*(Λ s).functional q := by
  rcases eq_or_lt_of_le ht.1 with he | ht0
  · subst t
    exact ⟨0,IsStarProjection.zero _,hq.nonneg,by intro s;simp⟩
  rcases eq_or_lt_of_le ht.2 with he | ht1
  · subst t
    exact ⟨q,hq,le_rfl,by intro s;simp⟩
  obtain ⟨p,hp,hqp,hpq,htr⟩ := hsupply q
    hq.nonneg hq.norm_le (1-t) (by linarith) (by linarith)
  rw [cutoff_projection hq (by linarith : 0 < 1-t) (by linarith)] at hqp hpq
  refine ⟨p,hp,(hp.le_iff_mul_eq_left hq).mpr hpq,?_⟩
  intro s
  rw [htr s,positiveCut_projection hq (by linarith) (by linarith),sub_sub_cancel]
  exact ((Λ s).functional.toLinearMap.restrictScalars ℝ).map_smul t q

theorem corner_symmetry (hsupply : SpectralProjectionSupply (familyLimitTrace θ U))
    {q : D} (hq : IsStarProjection q) :
    ∃ r : D, IsSelfAdjoint r ∧ q*r=r ∧ r*q=r ∧ r*r=q ∧
      ∀ s : ℕ → I, (Λ s).functional r=0 := by
  obtain ⟨p,hp,hpq,htr⟩ := proportional_subprojection θ U hsupply hq
    (show (1/2 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  have hpq' := (hp.le_iff_mul_eq_left hq).mp hpq
  have hqp' := (hp.le_iff_mul_eq_right hq).mp hpq
  refine ⟨2*p-q,?_,?_,?_,?_,?_⟩
  · rw [two_mul]
    exact (hp.isSelfAdjoint.add hp.isSelfAdjoint).sub hq.isSelfAdjoint
  · simp only [mul_sub,mul_assoc,←mul_assoc q 2,Commute.ofNat_right q 2 |>.eq,
      mul_assoc,hqp',hq.isIdempotentElem.eq]
  · simp only [sub_mul,mul_assoc,hpq',hq.isIdempotentElem.eq]
  · noncomm_ring [hp.isIdempotentElem.eq,hq.isIdempotentElem.eq,hpq',hqp']
  · intro s
    rw [two_mul,map_sub,map_add,htr s]
    push_cast
    ring

end FamilyComparison

namespace FamilyComparison
open Pureness CurrentMain DirectComparison Filter Topology
open scoped ComplexOrder ENNReal NNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def smallHat (t : ℝ) : ℝ := max (1-3*|t|) 0
def wideHat (t : ℝ) : ℝ := max 0 (min 1 (5-8*|t|))
lemma smallHat_cont : Continuous smallHat := by unfold smallHat; fun_prop
lemma wideHat_cont : Continuous wideHat := by unfold wideHat; fun_prop
lemma smallHat_bounds (t : ℝ) : smallHat t ∈ Set.Icc 0 1 := by
  constructor
  · exact le_max_right _ _
  · exact max_le (by linarith [abs_nonneg t]) zero_le_one
lemma wideHat_bounds (t : ℝ) : wideHat t ∈ Set.Icc 0 1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩
lemma smallHat_supported (t : ℝ) (ht : smallHat t ≠ 0) : wideHat t=1 := by
  have hf : 0 < 1-3*|t| := by
    have hpos : 0 < smallHat t := lt_of_le_of_ne (smallHat_bounds t).1 (Ne.symm ht)
    exact (lt_max_iff.mp hpos).resolve_right (lt_irrefl 0)
  have hg : 1 ≤ 5-8*|t| := by linarith
  simp only [wideHat,min_eq_left hg,max_eq_right zero_le_one]
lemma wideHat_supported (t : ℝ) (ht : wideHat t ≠ 0) : |t| ≤ 5/8 := by
  have hpos : 0 < wideHat t := lt_of_le_of_ne (wideHat_bounds t).1 (Ne.symm ht)
  have hf : 0 < min 1 (5-8*|t|) := (lt_max_iff.mp hpos).resolve_left (lt_irrefl 0)
  have := (lt_min_iff.mp hf).2
  linarith

lemma corner_smallHat_lower {y z : A} (hy : IsStarProjection y)
    (hz : IsStarProjection z) : y-(3:ℝ) • (y*z*y) ≤ cornerCFC hy z smallHat := by
  let a := ProjectionCorner.compress hy z
  have ha : 0 ≤ a := ProjectionCorner.compress_nonneg hy hz.nonneg
  have he : (1 : ProjectionCorner hy)-(3:ℝ) • a =
      cfc (fun t : ℝ => 1-3*t) a := by
    rw [cfc_sub _ _ a (by fun_prop) (by fun_prop),cfc_const 1 a ha.isSelfAdjoint,
      cfc_const_mul_id 3 a ha.isSelfAdjoint]
    simp only [map_one]
  have hb : (1 : ProjectionCorner hy)-(3:ℝ) • a ≤ cfc smallHat a := by
    rw [he]
    apply (cfc_le_iff _ _ a (by fun_prop) smallHat_cont.continuousOn ha.isSelfAdjoint).mpr
    intro t ht
    dsimp [smallHat]
    rw [abs_of_nonneg (spectrum_nonneg_of_nonneg ha ht)]
    exact le_max_left _ _
  exact hb

lemma real_smul_mono_nonneg {a b : ℝ} {p : A} (hab : a ≤ b) (hp : 0 ≤ p) :
    a • p ≤ b • p := smul_le_smul_of_nonneg_right hab hp

variable [Nontrivial A] {I : Type} [Nonempty I] (θ : I → TracialState A)
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
local notation "D" => FamilyUltrapower θ U
local notation "Λ" => familyLimitTrace θ U

include hfree in
lemma good_column_projection (hsupply : SpectralProjectionSupply (familyLimitTrace θ U))
    {y z : D} (hy : IsStarProjection y) (hz : IsStarProjection z) :
    ∃ f : D, IsStarProjection f ∧ f ≤ y ∧ f*z*f ≤ (5/8:ℝ) • f ∧
      ∀ s : ℕ → I,
        ((Λ s).functional y).re-3*((Λ s).functional (y*z)).re ≤ ((Λ s).functional f).re := by
  obtain ⟨f,hf,hfy,hkf,hfk,htr⟩ := exact_local_projection θ U hfree hsupply hy
    hz.isSelfAdjoint hz.norm_le smallHat_cont wideHat_cont
    (fun t _ => smallHat_bounds t) (fun t _ => smallHat_supported t)
  have hnorm : ‖f*z*f‖ ≤ (5/8:ℝ) := by
    have he := (localized_cutoff_compression hy hf hz.isSelfAdjoint hz.norm_le
      wideHat_cont (fun t _ => wideHat_bounds t)
      (hα := (by norm_num : (0:ℝ)<1/2)) (hε := (by norm_num : (0:ℝ)≤5/8))
      (μ := 0) (fun t _ ht => by simpa only [sub_zero] using wideHat_supported t ht) hkf hfk).2.2
    simpa only [zero_smul,sub_zero] using he
  have hupper : f*z*f ≤ (5/8:ℝ) • f := by
    have he := (compress_selfAdjoint hf hz.isSelfAdjoint).le_algebraMap_norm_self
    change f*z*f ≤ ‖f*z*f‖ • f at he
    exact he.trans (real_smul_mono_nonneg hnorm hf.nonneg)
  refine ⟨f,hf,hfy,hupper,?_⟩
  intro s
  rw [htr s]
  have he := (Complex.le_def.mp ((Λ s).functional.monotone (corner_smallHat_lower hy hz))).1
  change ((Λ s).functional (y-(3:ℝ) • (y*z*y))).re ≤ _ at he
  rw [map_sub,Complex.sub_re,(Λ s).functional.map_smul_of_tower,
    Complex.smul_re,smul_eq_mul,trace_projection_corner (Λ s) hy] at he
  exact he

include hfree in

theorem orthogonal_insertion (hsupply : SpectralProjectionSupply (familyLimitTrace θ U))
    {z y : D} (hz : IsStarProjection z) (hy : IsStarProjection y) :
    ∃ t : D, IsStarProjection t ∧ t ≤ 1-z ∧ ∀ s : ℕ → I,
      (((Λ s).functional y).re-3*((Λ s).functional (y*z)).re ≤ ((Λ s).functional t).re ∧
      ((Λ s).functional t).re ≤ ((Λ s).functional y).re) ∧
      traceTwoNorm (Λ s) (t-y)^2 ≤ 5*((Λ s).functional (y*z)).re ∧
      ∀ x : D, ‖x‖ ≤ 1 → ‖(Λ s).functional ((t-y)*x)‖ ≤
        2*Real.sqrt ((Λ s).functional y).re*traceTwoNorm (Λ s) (t-y) := by
  obtain ⟨f,hf,hfy,hupp,hlow⟩ := good_column_projection θ U hfree hsupply hy hz
  have hbound : (3/8:ℝ) • f ≤ f*(1-z)*f := by
    have heq : f*(1-z)*f=f-f*z*f := by
      rw [mul_sub f 1 z,mul_one,sub_mul,hf.isIdempotentElem]
    rw [heq]
    have heqf : f-(5/8:ℝ) • f=(3/8:ℝ) • f := by module
    have he := sub_le_sub (le_refl f) hupp
    rwa [heqf] at he
  obtain ⟨t,ht,htz,hftf,htrace⟩ := projection_insert_normalized hf hz.one_sub
    (by norm_num : (0:ℝ)<3/8) hbound
  refine ⟨t,ht,htz,?_⟩
  intro s
  let τ := Λ s
  have htf : (τ.functional t).re=(τ.functional f).re := congrArg Complex.re (htrace τ)
  have hmasslow : (τ.functional y).re-3*(τ.functional (y*z)).re ≤ (τ.functional t).re := by
    rw [htf]; exact hlow s
  have hmassup : (τ.functional t).re ≤ (τ.functional y).re := by
    rw [htf]; exact (Complex.le_def.mp (τ.functional.monotone hfy)).1
  have hty : (τ.functional f).re-(τ.functional (f*z)).re ≤ (τ.functional (t*y)).re := by
    have heqt : τ.functional (t*f)=τ.functional f-τ.functional (f*z) := by
      rw [τ.tracial t f,←trace_projection_corner τ hf t,hftf,
        trace_projection_corner τ hf (1-z),mul_sub,mul_one,map_sub]
    rw [←Complex.sub_re,←heqt]
    exact trace_mul_mono_right τ ht.nonneg hfy
  have hfz : (τ.functional (f*z)).re ≤ (τ.functional (y*z)).re :=
    trace_mul_mono_left τ hz.nonneg hfy
  refine ⟨⟨hmasslow,hmassup⟩,?_,fun x hx => projection_difference_linear τ ht hy hmassup hx⟩
  rw [trace_projection_difference_sq τ ht hy]
  linarith

end FamilyComparison

end

end OAI
