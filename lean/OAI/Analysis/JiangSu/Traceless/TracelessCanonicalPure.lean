import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.CuntzPeakSupport
import OAI.Analysis.JiangSu.Traceless.TracelessStabilizedPure

namespace OAI

section

noncomputable section
namespace CurrentMain.Traceless
open Pureness CurrentMain.Spatial

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def CanonicalStabilization :=
  SpatialStabilization (stateHilbertRepresentation A).toNonUnitalStarAlgHom

instance : NonUnitalCStarAlgebra (CanonicalStabilization A) :=
  inferInstanceAs (NonUnitalCStarAlgebra
    (SpatialStabilization (stateHilbertRepresentation A).toNonUnitalStarAlgHom))

instance : PartialOrder (CanonicalStabilization A) :=
  CStarAlgebra.spectralOrder _

instance : StarOrderedRing (CanonicalStabilization A) :=
  CStarAlgebra.spectralOrderedRing _

def EmptyTraceComparison : Prop :=
  ∀ a b : CanonicalStabilization A, 0 ≤ a → 0 ≤ b → b ≠ 0 → CuntzSubequiv a b

def PurelyInfinite : Prop :=
  ∀ E : NonUnitalStarSubalgebra ℂ A, IsHereditary E → E ≠ ⊥ →
    ∃ p : A, IsInfiniteProjectionIn E p

theorem pure_infiniteness_of_empty_trace_comparison [Nontrivial A]
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcomparison : EmptyTraceComparison A) : PurelyInfinite A := by
  let π := (stateHilbertRepresentation A).toNonUnitalStarAlgHom
  have hπ : Function.Injective π := stateHilbertRepresentation_injective A
  have hmap (a : A) (ha : 0 ≤ a) :
      0 ≤ (spatialCornerInto π a : CanonicalStabilization A) := by
    have hs : star (CFC.sqrt a) * CFC.sqrt a = a := by
      rw [(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self a ha]
    rw [← hs, map_mul, map_star]
    exact star_mul_self_nonneg (spatialCornerInto π (CFC.sqrt a) : CanonicalStabilization A)
  apply infinite_projection_in_nonzero_hereditary hsimple hinf
  intro b hb hb0
  apply cuntz_reflect_spatial π hπ
  exact hcomparison _ _ (hmap 1 (by positivity)) (hmap b hb) (fun he =>
    hb0 (spatialCornerInto_injective π hπ (he.trans (map_zero _).symm)))

end CurrentMain.Traceless

end
end

section

noncomputable section
namespace CurrentMain.Traceless
open Pureness CurrentMain.Spatial DirectComparison

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

theorem unit_cuntz_of_empty_comparison (hcmp : EmptyTraceComparison A)
    {b : A} (hb : 0 ≤ b) (hb0 : b ≠ 0) : CuntzSubequiv 1 b := by
  let π := (stateHilbertRepresentation A).toNonUnitalStarAlgHom
  have hπ : Function.Injective π := stateHilbertRepresentation_injective A
  have hmap (a : A) (ha : 0 ≤ a) :
      0 ≤ (spatialCornerInto π a : CanonicalStabilization A) := by
    have hs : star (CFC.sqrt a) * CFC.sqrt a = a := by
      rw [(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self a ha]
    rw [←hs, map_mul, map_star]
    exact star_mul_self_nonneg _
  apply cuntz_reflect_spatial π hπ
  exact hcmp _ _ (hmap 1 (by positivity)) (hmap b hb) (fun he =>
    hb0 (spatialCornerInto_injective π hπ (he.trans (map_zero _).symm)))

omit [PartialOrder A] [StarOrderedRing A] in
lemma isometry_norm_one {w : A} (hw : star w*w=1) : ‖w‖=1 := by
  have h : ‖star w*w‖=‖w‖*‖w‖ := CStarRing.norm_star_mul_self
  rw [hw,norm_one] at h
  nlinarith [norm_nonneg w]

omit [PartialOrder A] [StarOrderedRing A] [Nontrivial A] in
lemma orthogonal_isometries_of_ranges {u v : A} (hu : star u*u=1) (hv : star v*v=1)
    (h : (u*star u)*(v*star v)=0) : star u*v=0 := by
  have he : star u*((u*star u)*(v*star v))*v=star u*v := by
    calc
      _=(star u*u)*(star u*v)*(star v*v) := by simp only [mul_assoc]
      _=_ := by rw [hu,hv,one_mul,mul_one]
  rw [h,mul_zero,zero_mul] at he
  exact he.symm

theorem exists_two_isometries (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hcmp : EmptyTraceComparison A) :
    ∃ u v : A,star u*u=1 ∧ star v*v=1 ∧ star u*v=0 := by
  obtain ⟨b,c,hb,hc,hb0,hc0,hbc,_hbm,_hcm⟩ :=
    exists_orthogonal_positive_pair hsimple hinf (show (0:A)≤1 by positivity) one_ne_zero
  obtain ⟨u,hu,hup,hum⟩ := exists_hereditary_isometry_range hb
    (unit_cuntz_of_empty_comparison hcmp hb hb0)
  obtain ⟨v,hv,hvp,hvm⟩ := exists_hereditary_isometry_range hc
    (unit_cuntz_of_empty_comparison hcmp hc hc0)
  have hpc : (u*star u)*c=0 := hereditaryCorner_mul_eq_zero hb hbc hum
  have hcp : c*(u*star u)=0 := by
    have hh := congrArg star hpc
    simpa only [star_mul,hc.isSelfAdjoint.star_eq,hup.isSelfAdjoint.star_eq,star_zero] using hh
  have hqp := hereditaryCorner_mul_eq_zero hc hcp hvm
  have hpq : (u*star u)*(v*star v)=0 := by
    have hh := congrArg star hqp
    simpa only [star_mul,hup.isSelfAdjoint.star_eq,hvp.isSelfAdjoint.star_eq,star_zero] using hh
  exact ⟨u,v,hu,hv,orthogonal_isometries_of_ranges hu hv hpq⟩

omit [PartialOrder A] [StarOrderedRing A] [Nontrivial A] in
theorem finite_isometries_of_two {u v : A} (hu : star u*u=1) (hv : star v*v=1)
    (huv : star u*v=0) (m : ℕ) :
    ∃ r : Fin m→A,∀ i j,star (r i)*r j=if i=j then 1 else 0 := by
  classical
  have hvu : star v*u=0 := by
    simpa only [star_mul,star_star,star_zero] using congrArg star huv
  induction m with
  | zero => exact ⟨Fin.elim0,fun i=>Fin.elim0 i⟩
  | succ m ih =>
    obtain ⟨r,hr⟩ := ih
    refine ⟨Fin.cases v (fun i=>u*r i),?_⟩
    intro i j
    refine Fin.cases ?_ (fun i=>?_) i <;> refine Fin.cases ?_ (fun j=>?_) j
    · simp [hv]
    · simp [←mul_assoc,hvu,Ne.symm (Fin.succ_ne_zero j)]
    · simp [star_mul,mul_assoc,huv]
    · simp only [Fin.cases_succ,star_mul]
      have he : star (r i)*star u*(u*r j)=star (r i)*r j := by
        rw [mul_assoc,←mul_assoc (star u),hu,one_mul]
      rw [he,hr]
      simp

end CurrentMain.Traceless

end
end

section

noncomputable section
namespace CurrentMain.Traceless
open Pureness DirectComparison
open scoped ComplexOrder

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

omit [Nontrivial A] in
lemma high_cut_ne_zero (φ : A →ₚ[ℂ] ℂ) (hφ : φ 1=1) {g : A} (hg : 0≤g)
    {δ : ℝ} (hδ : δ≤1) (hlarge : 1-δ<(φ g).re) :
    directPositiveCut (1-δ) g≠0 := by
  intro hz
  have he := norm_sub_directPositiveCut_le g hg (1-δ) (sub_nonneg.mpr hδ)
  rw [hz,sub_zero] at he
  have hn := φ.norm_apply_le_of_nonneg g hg
  rw [hφ,norm_one,one_mul] at hn
  exact (not_lt_of_ge ((Complex.re_le_norm _).trans (hn.trans he))) hlarge

lemma isometry_peak_bound {g : A} (hg : 0≤g) (hgn : ‖g‖≤1)
    {δ : ℝ} (hδ : 0≤δ) {w : A} (hw : star w*w=1)
    (hwm : w*star w∈hereditaryCorner (directPositiveCut (1-δ) g)
      (directPositiveCut_nonneg _ _)) : ‖g*w-w‖≤δ := by
  let b := directPositiveCut (1-δ) g
  have hb : 0≤b := directPositiveCut_nonneg _ _
  obtain ⟨h,hhn,hh⟩ := peak_multiplier g hg hgn δ hδ
  let z := g-1-h
  have hzs : z*CFC.sqrt b=0 := by
    change (g-1-h)*CFC.sqrt b=0
    rw [sub_mul,hh,sub_self]
  have hzb : z*b=0 := by
    rw [←CFC.sqrt_mul_sqrt_self b hb,←mul_assoc,hzs,zero_mul]
  have hbz : b*star z=0 := by
    simpa only [star_mul,hb.isSelfAdjoint.star_eq,star_zero] using congrArg star hzb
  have hpz := hereditaryCorner_mul_eq_zero hb hbz hwm
  have hzp : z*(w*star w)=0 := by
    simpa only [star_mul,star_star,star_zero] using congrArg star hpz
  have hzw : z*w=0 := by
    calc
      _=z*((w*star w)*w) := by rw [mul_assoc w,hw,mul_one]
      _=0 := by rw [←mul_assoc,hzp,zero_mul]
  have he : g*w-w=h*w := by
    have hh : (g*w-w)-h*w=z*w := by
      dsimp [z]
      rw [sub_mul, sub_mul, one_mul]
    exact sub_eq_zero.mp (hh.trans hzw)
  rw [he]
  calc
    _≤‖h‖*‖w‖ := norm_mul_le _ _
    _≤δ := by rw [isometry_norm_one hw,mul_one]; exact hhn

omit [PartialOrder A] [StarOrderedRing A] [Nontrivial A] in
lemma cross_compression_bound {g u v c : A} (hg : IsSelfAdjoint g)
    (hgn : ‖g‖≤1) (hun : ‖u‖≤1) (hvn : ‖v‖≤1)
    {δ : ℝ} (hδ : 0≤δ) (hu : ‖g*u-u‖≤δ) (hv : ‖g*v-v‖≤δ) :
    ‖star u*c*v‖≤‖g*c*g‖+2*‖c‖*δ := by
  have hgu : ‖g*u‖≤1 := (norm_mul_le _ _).trans
    ((mul_le_mul hgn hun (norm_nonneg _) zero_le_one).trans_eq (mul_one 1))
  have hleft : ‖star (u-g*u)*c*v‖≤δ*‖c‖ := by
    calc
      _≤(‖u-g*u‖*‖c‖)*‖v‖ := by
        rw [←norm_star (u-g*u)]
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (norm_mul_le _ _) (norm_nonneg _))
      _≤(δ*‖c‖)*1 := mul_le_mul
        (mul_le_mul_of_nonneg_right (by simpa only [norm_sub_rev] using hu) (norm_nonneg _))
        hvn (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))
      _=δ*‖c‖ := mul_one _
  have hright : ‖star (g*u)*c*(v-g*v)‖≤‖c‖*δ := by
    calc
      _≤(‖g*u‖*‖c‖)*‖v-g*v‖ := by
        rw [←norm_star (g*u)]
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (norm_mul_le _ _) (norm_nonneg _))
      _≤(1*‖c‖)*δ := mul_le_mul (mul_le_mul_of_nonneg_right hgu (norm_nonneg _))
        (by simpa only [norm_sub_rev] using hv) (norm_nonneg _) (by positivity)
      _=‖c‖*δ := by rw [one_mul]
  have hmiddle : ‖star u*(g*c*g)*v‖≤‖g*c*g‖ := by
    calc
      _≤(‖u‖*‖g*c*g‖)*‖v‖ := by
        rw [←norm_star u]
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          (norm_mul_le _ _) (norm_nonneg _))
      _≤(1*‖g*c*g‖)*1 := mul_le_mul
        (mul_le_mul_of_nonneg_right hun (norm_nonneg _)) hvn (norm_nonneg _) (by positivity)
      _=‖g*c*g‖ := by ring
  have he : star u*c*v=star (u-g*u)*c*v+star (g*u)*c*(v-g*v)+star u*(g*c*g)*v := by
    simp only [star_sub,star_mul,hg.star_eq]
    noncomm_ring
  rw [he]
  have hh := (norm_add_le (star (u-g*u)*c*v+star (g*u)*c*(v-g*v))
    (star u*(g*c*g)*v)).trans (add_le_add (norm_add_le _ _) le_rfl)
  linarith

end CurrentMain.Traceless

end
end

end OAI
