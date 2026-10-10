import OAI.Geometry.Relativity.CKS.MixedSqrtJet

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev LapseInput := ℝ × (ScalarJet × ScalarJet × ScalarJet)

def radicandJet (j : LapseInput) : ScalarJet :=
  (1/(1+j.1^2)) • (constantJet (j.1^2)+productJet j.2.1 j.2.1-(2:ℝ) • j.2.2.1)

def reconstructedLapse (j : LapseInput) : ScalarJet :=
  productJet (sqrtJet (radicandJet j)) (reciprocalJet j.2.2.2)

def lapseRegion : Set LapseInput := {j | 0 < (radicandJet j).1 ∧ 0 < j.2.2.2.1}

def lapseReference (z : ℝ) : LapseInput := (z,constantJet 1,constantJet 0,constantJet 1)

def lapseReferenceFamily : Set LapseInput := lapseReference '' Icc 0 1

lemma radicandJet_smooth : ContDiff ℝ ∞ radicandJet := by
  have hc : ContDiff ℝ ∞ (fun j : LapseInput => (1:ℝ)/(1+j.1^2)) := by
    apply ContDiff.fun_div contDiff_const (by fun_prop)
    intro x
    positivity
  have h0 : ContDiff ℝ ∞ (fun j : LapseInput => constantJet (j.1^2)) := by
    unfold constantJet
    fun_prop
  have hp : ContDiff ℝ ∞ (fun j : LapseInput => productJet j.2.1 j.2.1) :=
    productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun j : LapseInput => (j.2.1,j.2.1)))
  exact hc.fun_smul ((h0.add hp).sub (by fun_prop))

lemma reconstructedLapse_smooth {j : LapseInput} (hj : j ∈ lapseRegion) :
    ContDiffAt ℝ ∞ reconstructedLapse j := by
  have hd : ContDiffAt ℝ ∞ (fun j : LapseInput => j.2.2.2) j := by fun_prop
  exact productJet_smooth.contDiffAt.comp j
    (((sqrtJet_smooth hj.1).comp j radicandJet_smooth.contDiffAt).prodMk
      ((reciprocalJet_smooth hj.2.ne').comp j hd))

lemma lapseRegion_open : IsOpen lapseRegion := by
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (continuous_fst.comp radicandJet_smooth.continuous)
  · exact isOpen_lt continuous_const (by fun_prop : Continuous (fun j : LapseInput => j.2.2.2.1))

lemma radicand_reference (z : ℝ) : radicandJet (lapseReference z) = constantJet 1 := by
  have hz : 1+z^2 ≠ 0 := by positivity
  ext a b <;> simp [radicandJet,lapseReference,constantJet,productJet,smul_eq_mul,Pi.smul_apply] <;> field_simp
  · ring
  · change (1/(1+z^2)) * (0:ℝ) = 0
    exact mul_zero _

lemma reconstructed_reference (z : ℝ) : reconstructedLapse (lapseReference z) = constantJet 1 := by
  rw [reconstructedLapse,radicand_reference]
  ext a b <;> simp [sqrtJet,reciprocalJet,constantJet,productJet,lapseReference]

lemma lapseReferenceFamily_compact : IsCompact lapseReferenceFamily :=
  isCompact_Icc.image (by unfold lapseReference constantJet; fun_prop)

lemma lapseReferenceFamily_regular : lapseReferenceFamily ⊆ lapseRegion := by
  rintro j ⟨z,hz,rfl⟩
  constructor
  · rw [radicand_reference]
    norm_num [constantJet]
  · norm_num [lapseReference,constantJet]

theorem lapse_uniform_lipschitz :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0,
      LipschitzOnWith C reconstructedLapse (Metric.cthickening δ lapseReferenceFamily) := by
  obtain ⟨δ,hδ,hsub⟩ := lapseReferenceFamily_compact.exists_cthickening_subset_open
    lapseRegion_open lapseReferenceFamily_regular
  refine ⟨δ,hδ,?_⟩
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (lapseReferenceFamily_compact.cthickening (r := δ))
  intro j hj
  obtain ⟨C,t,ht,hC⟩ := ((reconstructedLapse_smooth (hsub hj)).of_le
    (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
  exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩

lemma actual_radicandJet (z : ℝ) {t b : Point → ℝ} {x : Point}
    (ht : ContDiffAt ℝ 2 t x) (hb : ContDiffAt ℝ 2 b x) (d : ScalarJet) :
    actualScalarJet (fun y => (z^2+t y*t y-2*b y)/(1+z^2)) x =
      radicandJet (z,actualScalarJet t x,actualScalarJet b x,d) := by
  have hh : (fun y => (z^2+t y*t y-2*b y)/(1+z^2)) =
      (fun y => (1/(1+z^2))*(z^2+t y*t y-2*b y)) := by funext y; ring
  have h2 : ContDiffAt ℝ 2 (fun y => (2:ℝ)*b y) x := hb.const_smul (2:ℝ)
  have harg : ContDiffAt ℝ 2 (fun y => z^2+t y*t y) x := contDiffAt_const.add (ht.mul ht)
  rw [hh,actualScalarJet_smul _ (harg.sub h2),actualScalarJet_sub harg h2,
    actualScalarJet_add (contDiffAt_const (c := z^2)) (ht.mul ht),actualScalarJet_const,
    actualScalarJet_mul ht ht,actualScalarJet_smul _ hb]
  rfl

theorem actual_reconstructedLapse (z : ℝ) {t b d : Point → ℝ} {x : Point}
    (ht : ContDiffAt ℝ 2 t x) (hb : ContDiffAt ℝ 2 b x) (hd : ContDiffAt ℝ 2 d x)
    (ha : 0 < (z^2+t x*t x-2*b x)/(1+z^2)) (hd0 : d x ≠ 0) :
    actualScalarJet (fun y => Real.sqrt ((z^2+t y*t y-2*b y)/(1+z^2))/d y) x =
      reconstructedLapse (z,actualScalarJet t x,actualScalarJet b x,actualScalarJet d x) := by
  have harg : ContDiffAt ℝ 2 (fun y => (z^2+t y*t y-2*b y)/(1+z^2)) x :=
    ((contDiffAt_const.add (ht.mul ht)).sub (hb.const_smul (2:ℝ))).div_const _
  have hh : (fun y => Real.sqrt ((z^2+t y*t y-2*b y)/(1+z^2))/d y) =
      (fun y => Real.sqrt ((z^2+t y*t y-2*b y)/(1+z^2))*(1/d y)) := by
    funext y
    simp [div_eq_mul_inv]
  have hi : ContDiffAt ℝ 2 (fun y => 1/d y) x := contDiffAt_const.fun_div hd hd0
  rw [hh,actualScalarJet_mul (harg.sqrt ha.ne') hi,
    actualScalarJet_sqrt harg ha,actual_reciprocal hd hd0,actual_radicandJet z ht hb (actualScalarJet d x)]
  rfl

lemma radial_normalization {r v F d : ℝ} (hr : 0 < r) :
    Real.sqrt ((1/r)^2+(v/r)*(v/r)-2*(F/r^3)) / Real.sqrt (1+(1/r)^2) / d =
      Real.sqrt (1+v^2-2*F/r) / Real.sqrt (1+r^2) / d := by
  have harg : (1/r)^2+(v/r)*(v/r)-2*(F/r^3) = (1+v^2-2*F/r)/r^2 := by field_simp
  have hbase : 1+(1/r)^2 = (1+r^2)/r^2 := by
    field_simp
    ring
  rw [harg,hbase,Real.sqrt_div' _ (sq_nonneg r),Real.sqrt_div' _ (sq_nonneg r),
    Real.sqrt_sq_eq_abs,abs_of_pos hr]
  field_simp

end
end CKSAngularGeometry

end

end OAI
