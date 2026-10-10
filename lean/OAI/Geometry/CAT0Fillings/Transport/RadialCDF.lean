import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Basic

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.RadialSobolev

noncomputable def cumulativeOrderIso {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b)) :
    Icc a b ≃o Icc (F a) (F b) := by
  let f : Icc a b → Icc (F a) (F b) := fun x =>
    ⟨F x,⟨hm.monotoneOn ⟨le_rfl,hab⟩ x.property x.property.1,
      hm.monotoneOn x.property ⟨hab,le_rfl⟩ x.property.2⟩⟩
  apply StrictMono.orderIsoOfSurjective f
  · intro x y hxy
    exact hm x.property y.property hxy
  · intro y
    obtain ⟨x,hx,he⟩ := intermediate_value_Icc hab hF y.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩

lemma cumulativeOrderIso_apply {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b)) (x : Icc a b) :
    (cumulativeOrderIso hab hF hm x : ℝ) = F x := rfl

noncomputable def cumulativeInverse {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b)) (y : ℝ) : ℝ :=
  ((cumulativeOrderIso hab hF hm).symm
    (projIcc (F a) (F b) (hm.monotoneOn ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab) y) : ℝ)

lemma cumulativeInverse_mem {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b)) (y : ℝ) :
    cumulativeInverse hab hF hm y ∈ Icc a b := Subtype.property _

lemma cumulativeInverse_continuous {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b)) :
    Continuous (cumulativeInverse hab hF hm) :=
  continuous_subtype_val.comp ((cumulativeOrderIso hab hF hm).symm.continuous.comp continuous_projIcc)

lemma cumulativeInverse_right {F : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b))
    (hy : y ∈ Icc (F a) (F b)) : F (cumulativeInverse hab hF hm y) = y := by
  have hh := congrArg Subtype.val ((cumulativeOrderIso hab hF hm).apply_symm_apply
    (projIcc (F a) (F b) (hm.monotoneOn ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab) y))
  rw [cumulativeOrderIso_apply] at hh
  simpa only [cumulativeInverse,projIcc_of_mem _ hy] using hh

lemma cumulativeInverse_left {F : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b)) (hx : x ∈ Icc a b) :
    cumulativeInverse hab hF hm (F x) = x := by
  apply hm.injOn (cumulativeInverse_mem hab hF hm _) hx
  exact cumulativeInverse_right hab hF hm
    ⟨hm.monotoneOn ⟨le_rfl,hab⟩ hx hx.1,hm.monotoneOn hx ⟨hab,le_rfl⟩ hx.2⟩

lemma cumulativeInverse_interior {F : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b))
    (hy : y ∈ Ioo (F a) (F b)) : cumulativeInverse hab hF hm y ∈ Ioo a b := by
  have hb := cumulativeInverse_mem hab hF hm y
  have he := cumulativeInverse_right hab hF hm ⟨hy.1.le,hy.2.le⟩
  refine ⟨lt_of_le_of_ne hb.1 ?_,lt_of_le_of_ne hb.2 ?_⟩
  · intro hh
    rw [←hh] at he
    exact hy.1.ne he
  · intro hh
    rw [hh] at he
    exact hy.2.ne' he

lemma cumulativeInverse_hasDerivAt {F : ℝ → ℝ} {a b y d : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hm : StrictMonoOn F (Icc a b))
    (hy : y ∈ Ioo (F a) (F b))
    (hd : HasDerivAt F d (cumulativeInverse hab hF hm y)) (hd0 : d ≠ 0) :
    HasDerivAt (cumulativeInverse hab hF hm) d⁻¹ y := by
  apply HasDerivAt.of_local_left_inverse (cumulativeInverse_continuous hab hF hm).continuousAt hd hd0
  filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
  exact cumulativeInverse_right hab hF hm ⟨hz.1.le,hz.2.le⟩

lemma cumulativeTransport_hasDerivAt {F G : ℝ → ℝ} {a b r f' g' : ℝ} (hab : a ≤ b)
    (hG : ContinuousOn G (Icc a b)) (hm : StrictMonoOn G (Icc a b))
    (hy : F r ∈ Ioo (G a) (G b)) (hF : HasDerivAt F f' r)
    (hd : HasDerivAt G g' (cumulativeInverse hab hG hm (F r))) (hd0 : g' ≠ 0) :
    HasDerivAt (fun s => cumulativeInverse hab hG hm (F s)) (f'/g') r := by
  simpa only [Function.comp_def,div_eq_mul_inv,mul_comm] using
    (cumulativeInverse_hasDerivAt hab hG hm hy hd hd0).comp r hF

end CAT0Fillings.RadialSobolev
end

section

open Set Filter MeasureTheory
open scoped Topology

namespace CAT0Fillings.RadialSobolev

noncomputable def radialCDF (n : ℕ) (ω : ℝ) (f : ℝ → ℝ) (p r : ℝ) : ℝ :=
  (n:ℝ)*ω*∫ s in (0:ℝ)..r, s^(n-1)*(f s)^p

lemma radialCDF_hasDerivAt {n : ℕ} {ω p r : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hp : 0 < p) :
    HasDerivAt (radialCDF n ω f p)
      ((n:ℝ)*ω*r^(n-1)*(f r)^p) r := by
  have hc : Continuous (fun s : ℝ => s^(n-1)*(f s)^p) :=
    (continuous_id.pow _).mul (hf.rpow_const (fun _ => Or.inr hp.le))
  change HasDerivAt (fun y => (n:ℝ)*ω*∫ s in (0:ℝ)..y, s^(n-1)*(f s)^p) _ r
  simpa only [mul_assoc] using
    (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul ((n:ℝ)*ω)

lemma radialCDF_continuous {n : ℕ} {ω p : ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) (hp : 0 < p) : Continuous (radialCDF n ω f p) :=
  continuous_iff_continuousAt.mpr fun _ => (radialCDF_hasDerivAt hf hp).continuousAt

lemma radialCDF_zero (n : ℕ) (ω : ℝ) (f : ℝ → ℝ) (p : ℝ) :
    radialCDF n ω f p 0 = 0 := by simp [radialCDF]

lemma radialCDF_strictMonoOn {n : ℕ} {ω p R : ℝ} {f : ℝ → ℝ}
    (hn : 0 < n) (hω : 0 < ω) (hf : Continuous f) (hp : 0 < p)
    (hpos : ∀ r ∈ Ioo 0 R, 0 < f r) :
    StrictMonoOn (radialCDF n ω f p) (Icc 0 R) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (radialCDF_continuous hf hp).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    rw [(radialCDF_hasDerivAt hf hp).deriv]
    exact mul_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hn) hω) (pow_pos hx.1 _))
      (Real.rpow_pos_of_pos (hpos x hx) _)

noncomputable def radialTransport {n : ℕ} {ω p D : ℝ} {f g : ℝ → ℝ}
    (hD : 0 ≤ D) (hn : 0 < n) (hω : 0 < ω) (hg : Continuous g) (hp : 0 < p)
    (hgp : ∀ r ∈ Ioo 0 D, 0 < g r) (r : ℝ) : ℝ :=
  cumulativeInverse hD (radialCDF_continuous hg hp).continuousOn
    (radialCDF_strictMonoOn hn hω hg hp hgp) (radialCDF n ω f p r)

lemma radialTransport_mem {n : ℕ} {ω p D : ℝ} {f g : ℝ → ℝ}
    (hD : 0 ≤ D) (hn : 0 < n) (hω : 0 < ω) (hg : Continuous g) (hp : 0 < p)
    (hgp : ∀ r ∈ Ioo 0 D, 0 < g r) (r : ℝ) :
    radialTransport (f := f) hD hn hω hg hp hgp r ∈ Icc 0 D :=
  cumulativeInverse_mem _ _ _ _

lemma radialTransport_continuous {n : ℕ} {ω p D : ℝ} {f g : ℝ → ℝ}
    (hD : 0 ≤ D) (hn : 0 < n) (hω : 0 < ω) (hf : Continuous f) (hg : Continuous g)
    (hp : 0 < p) (hgp : ∀ r ∈ Ioo 0 D, 0 < g r) :
    Continuous (radialTransport (f := f) hD hn hω hg hp hgp) :=
  (cumulativeInverse_continuous _ _ _).comp (radialCDF_continuous hf hp)

lemma radialTransport_cdf {n : ℕ} {ω p R D r : ℝ} {f g : ℝ → ℝ}
    (hD : 0 ≤ D) (hn : 0 < n) (hω : 0 < ω) (hf : Continuous f) (hg : Continuous g)
    (hp : 0 < p) (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r ∈ Ioo 0 D, 0 < g r)
    (hmass : radialCDF n ω f p R = radialCDF n ω g p D) (hr : r ∈ Icc 0 R) :
    radialCDF n ω g p (radialTransport (f := f) hD hn hω hg hp hgp r) =
      radialCDF n ω f p r := by
  apply cumulativeInverse_right
  have hm := (radialCDF_strictMonoOn hn hω hf hp hfp).monotoneOn
  constructor
  · simpa only [radialCDF_zero] using hm (show 0 ∈ Icc 0 R from ⟨le_rfl,hr.1.trans hr.2⟩) hr hr.1
  · rw [←hmass]
    exact hm hr ⟨hr.1.trans hr.2,le_rfl⟩ hr.2

lemma radialTransport_interior {n : ℕ} {ω p R D r : ℝ} {f g : ℝ → ℝ}
    (hD : 0 ≤ D) (hn : 0 < n) (hω : 0 < ω) (hf : Continuous f) (hg : Continuous g)
    (hp : 0 < p) (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r ∈ Ioo 0 D, 0 < g r)
    (hmass : radialCDF n ω f p R = radialCDF n ω g p D) (hr : r ∈ Ioo 0 R) :
    radialTransport (f := f) hD hn hω hg hp hgp r ∈ Ioo 0 D := by
  apply cumulativeInverse_interior
  have hm := radialCDF_strictMonoOn hn hω hf hp hfp
  constructor
  · simpa only [radialCDF_zero] using hm
      (show 0 ∈ Icc 0 R from ⟨le_rfl,(hr.1.trans hr.2).le⟩) ⟨hr.1.le,hr.2.le⟩ hr.1
  · rw [←hmass]
    exact hm ⟨hr.1.le,hr.2.le⟩ ⟨(hr.1.trans hr.2).le,le_rfl⟩ hr.2

lemma radialTransport_hasDerivAt {n : ℕ} {ω p R D r : ℝ} {f g : ℝ → ℝ}
    (hD : 0 ≤ D) (hn : 0 < n) (hω : 0 < ω) (hf : Continuous f) (hg : Continuous g)
    (hp : 0 < p) (hfp : ∀ r ∈ Ioo 0 R, 0 < f r) (hgp : ∀ r ∈ Ioo 0 D, 0 < g r)
    (hmass : radialCDF n ω f p R = radialCDF n ω g p D) (hr : r ∈ Ioo 0 R) :
    HasDerivAt (radialTransport (f := f) hD hn hω hg hp hgp)
      (((n:ℝ)*ω*r^(n-1)*(f r)^p) /
        ((n:ℝ)*ω*(radialTransport (f := f) hD hn hω hg hp hgp r)^(n-1)*
          (g (radialTransport (f := f) hD hn hω hg hp hgp r))^p)) r := by
  have ht := radialTransport_interior hD hn hω hf hg hp hfp hgp hmass hr
  have hv : radialCDF n ω f p r ∈ Ioo (radialCDF n ω g p 0) (radialCDF n ω g p D) := by
    rw [←radialTransport_cdf hD hn hω hf hg hp hfp hgp hmass ⟨hr.1.le,hr.2.le⟩]
    have hm := radialCDF_strictMonoOn hn hω hg hp hgp
    exact ⟨hm ⟨le_rfl,hD⟩ ⟨ht.1.le,ht.2.le⟩ ht.1,
      hm ⟨ht.1.le,ht.2.le⟩ ⟨hD,le_rfl⟩ ht.2⟩
  apply cumulativeTransport_hasDerivAt hD (radialCDF_continuous hg hp).continuousOn
    (radialCDF_strictMonoOn hn hω hg hp hgp) hv
    (radialCDF_hasDerivAt hf hp) (radialCDF_hasDerivAt hg hp)
  exact ne_of_gt (mul_pos (mul_pos (mul_pos (Nat.cast_pos.mpr hn) hω) (pow_pos ht.1 _))
    (Real.rpow_pos_of_pos (hgp _ ht) _))

end CAT0Fillings.RadialSobolev
end

end OAI
