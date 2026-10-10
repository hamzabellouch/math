import OAI.Geometry.Convex.GeneralMahler.Reduction

namespace OAI

/-!
## Santaló center

Rather than the spherical integral, we use equivalently
the cone Laplace integral and its divergence at the dual boundary. This way
of proving the center claims includes dimension 1 without a separate case.
-/
noncomputable section
open Set Filter MeasureTheory Topology
open scoped RealInnerProductSpace ENNReal
namespace GeneralMahler
variable {n : ℕ}
namespace Body

def polarVol (K : Body n) (z : Rn n) : ℝ := (volume (polarAt K z)).toReal

lemma chi_pair_one {K : Body n} {x : Rn n} (hx : x ∈ interior (K:Set (Rn n))) :
    chi (posDual K.cone) (pair 1 x) = (n.factorial:ℝ)*polarVol K x := by
  have H := cone_volume K _ hx 1 zero_lt_one
  rw [chi_axis _ 1 zero_lt_one] at H
  let v := (volume (K:Set (Rn n))).toReal
  simp only [one_pow, one_smul, inv_one, one_mul] at H
  apply mul_left_cancel₀ (show (n.factorial:ℝ)*v ≠ 0 from mul_ne_zero (by positivity) K.vol_pos.ne')

  change (n.factorial:ℝ)*v*_ = _* (v*polarVol K x) at H
  rw [H]; ring

lemma mem_int' (K : Body n) (x : Rn n) :
    pair 1 x ∈ interior ((posDual (posDual K.cone)): Set (LiftSpace n)) ↔
      x ∈ interior (K:Set (Rn n)) := by
  have h : posDual (posDual K.cone) = K.cone := ProperCone.innerDual_innerDual _
  simpa [h] using ((K.pair_mem_interior_cone_iff 1 zero_lt_one x))


lemma polarVol_strict (K : Body n) :
    StrictConvexOn ℝ (interior (K:Set (Rn n))) K.polarVol := by
  refine ⟨K.convex.interior,?_⟩
  intro x hx y hy hn a b ha hb hab
  have hr : pair 1 x ≠ pair 1 y := by
    intro he
    exact hn (congrArg horiz he)
  have H := (chi_strictConvex (C := posDual K.cone)
    ⟨_, axis_dual_interior K 1 zero_lt_one⟩).2 ((K.mem_int' _).mpr hx)
      ((K.mem_int' _).mpr hy) hr ha hb hab
  have he : a • pair 1 x + b • pair 1 y = pair 1 (a • x + b • y) := calc
    _ = pair (a*1+b*1) (a • x + b • y) := rfl
    _ = _ := by rw [mul_one,mul_one,hab]
  rw [he, chi_pair_one hx, chi_pair_one hy,
    chi_pair_one (K.convex.interior hx hy ha.le hb.le hab)] at H
  simp only [smul_eq_mul] at *
  apply lt_of_mul_lt_mul_left (a := (n.factorial:ℝ))
  · convert H using 1
    ring
  · positivity

/-- Existence and uniqueness of the polar-volume minimizer. -/
theorem santalo_exists (K : Body n) :
    ∃! x, x ∈ interior (K : Set (Rn n)) ∧ IsMinOn K.polarVol (interior (K:Set (Rn n))) x := by
  let D := posDual K.cone
  let f := fun x : Rn n => chiExt D (pair 1 x)
  have hsc : LowerSemicontinuous f := by
    intro x b hb
    have hc : Continuous (fun z : Rn n => pair 1 z) := by fun_prop
    exact (hc.tendsto x).eventually (chiExt_lsc D _ _ hb)
  have hpos' : (interior (D : Set (LiftSpace n))).Nonempty :=
    ⟨_, axis_dual_interior K 1 zero_lt_one⟩
  obtain ⟨x₀,h₀⟩ := K.has_interior
  have hpos : (interior (posDual D : Set (LiftSpace n))).Nonempty :=
    ⟨_, (K.mem_int' _).mpr h₀⟩
  obtain ⟨x,hx,he⟩ := LowerSemicontinuousOn.exists_isMinOn K.nonempty K.isCompact
    (hsc.lowerSemicontinuousOn _)
  have hh (y : Rn n) (hy : y ∈ interior (K : Set (Rn n))) :
      f y = ENNReal.ofReal ((n.factorial:ℝ)*polarVol K y) := by
    rw [← chi_pair_one hy]
    exact chiExt_eq ((K.mem_int' _).mpr hy)
  have hx' : x ∈ interior (K : Set (Rn n)) := by
    by_contra hn
    have htop : f x = ∞ := chiExt_top hpos' hpos (mt (K.mem_int' _).mp hn)
    have H : f x ≤ f x₀ := he (interior_subset h₀)
    rw [hh x₀ h₀, htop] at H
    exact ENNReal.ofReal_ne_top (top_le_iff.mp H)
  have he' : IsMinOn K.polarVol (interior (K:Set (Rn n))) x := by
    intro y hy
    have H : f x ≤ f y := he (interior_subset hy)
    rw [hh x hx', hh y hy] at H
    have hnon : 0 ≤ (n.factorial:ℝ)*polarVol K y :=
      mul_nonneg (by positivity) ENNReal.toReal_nonneg
    exact le_of_mul_le_mul_left ((ENNReal.ofReal_le_ofReal_iff hnon).mp H) (by positivity)
  exact ⟨x, ⟨hx',he'⟩, fun y hy =>
    (K.polarVol_strict).eq_of_isMinOn hy.2 he' hy.1 hx'⟩

def santalo (K : Body n) : Rn n := (santalo_exists K).exists.choose

theorem santalo_spec (K : Body n) :
    santalo K ∈ interior (K : Set (Rn n)) ∧
      IsMinOn K.polarVol (interior (K:Set (Rn n))) (santalo K) :=
  (santalo_exists K).exists.choose_spec

def productAt (K : Body n) (z : Rn n) := (volume (K : Set (Rn n))).toReal * K.polarVol z
def P (K : Body n) := K.productAt K.santalo

theorem product_min {K : Body n} {z : Rn n} (hz : z ∈ interior (K : Set (Rn n))) :
    K.P ≤ K.productAt z :=
  mul_le_mul_of_nonneg_left ((K.santalo_spec).2 hz) K.vol_pos.le

theorem product_inf (K : Body n) :
    K.P = sInf (K.productAt '' interior (K : Set (Rn n))) := by
  have hm : K.P ∈ K.productAt '' interior (K : Set (Rn n)) :=
    ⟨_,K.santalo_spec.1,rfl⟩
  have hl : K.P ∈ lowerBounds (K.productAt '' interior (K : Set (Rn n))) := by
    rintro x ⟨z,hz,rfl⟩
    exact product_min hz
  exact le_antisymm (le_csInf ⟨_,hm⟩ hl) (csInf_le ⟨_,hl⟩ hm)

end Body
end GeneralMahler

end

end OAI
