import OAI.Dynamics.StandardMap.HalfDecomposition

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
structure TreeLine (d : ℝ → ℝ → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ d x y
  symm : ∀ x y, d x y=d y x
  triangle : ∀ x y z, d x z ≤ d x y+d y z
  unit : ∀ x y, d x y ≤ |y-x|
  tree : ∀ v x y z,
    min (d v x+d v y-d x y) (d v y+d v z-d y z) ≤ d v x+d v z-d x z
lemma realArray_treeLine (d : DistanceArray) (hu : UnitArray d) (ht : TreeArray d) :
    TreeLine (realArray d) :=
  ⟨realArray_nonneg d hu,realArray_symm d hu,realArray_triangle d hu,
    realArray_le d hu,realArray_tree d hu ht⟩
noncomputable def lineB (d : ℝ → ℝ → ℝ) (v x y : ℝ) : ℝ := d v x+d v y-d x y
namespace TreeLine
variable {d : ℝ → ℝ → ℝ} (hd : TreeLine d)
include hd
lemma self (x : ℝ) : d x x=0 := by
  have h := hd.unit x x
  simp only [sub_self,abs_zero] at h
  exact le_antisymm h (hd.nonneg _ _)
lemma reverse (x y z : ℝ) : d x y-d y z ≤ d x z := by
  have h := hd.triangle x z y
  rw [hd.symm z y] at h
  linarith
lemma b_nonneg (v x y : ℝ) : 0 ≤ lineB d v x y := by
  have h := hd.triangle x v y
  rw [hd.symm x v] at h
  dsimp [lineB]; linarith
lemma b_symm (v x y : ℝ) : lineB d v x y=lineB d v y x := by
  unfold lineB; rw [hd.symm x y]; ring
lemma min_b (v x y z : ℝ) : min (lineB d v x y) (lineB d v y z) ≤ lineB d v x z :=
  hd.tree v x y z
lemma b_nonbacktrack (v x u y : ℝ) (hp : 0 < lineB d v x u) (hz : lineB d v u y=0) :
    lineB d v x y=0 := by
  have hb := hd.min_b v u x y
  rw [hd.b_symm v u x,hz] at hb
  have hh := (min_le_iff.mp hb).resolve_left (not_le.mpr hp)
  exact le_antisymm hh (hd.b_nonneg _ _ _)
end TreeLine

def NoFastCancellation (d : ℝ → ℝ → ℝ) (δ : ℝ) : Prop :=
  ∀ z t : ℝ, 0 < t → ¬ ((1-δ)*t < d (z-t) z ∧ (1-δ)*t < d z (z+t) ∧ d (z-t) (z+t) < δ*t)

def ExteriorUnitRays (d : ℝ → ℝ → ℝ) (a b : ℝ) : Prop :=
  (∀ x y : ℝ, x ≤ a → y ≤ a → d x y=|y-x|) ∧
  (∀ x y : ℝ, b ≤ x → b ≤ y → d x y=|y-x|)
lemma matched_ray_distance {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {a b u v s : ℝ}
    (_hab : a ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s)
    (hsu : s ≤ u) (hsv : s ≤ v) (hr : ExteriorUnitRays d a b)
    (hmatch : d (a-u) (b+v)=u+v-d a b-2*s) :
    d (a-s) (b+s) ≤ 3*d a b := by
  have hu0 : d a (a-u)=u := by rw [hr.1 _ _ (le_refl _) (by linarith)]; rw [abs_of_nonpos (by linarith)]; ring
  have hs0 : d a (a-s)=s := by rw [hr.1 _ _ (le_refl _) (by linarith)]; rw [abs_of_nonpos (by linarith)]; ring
  have hus : d (a-u) (a-s)=u-s := by rw [hr.1 _ _ (by linarith) (by linarith)]; rw [abs_of_nonneg (by linarith)]; ring
  have hv0 : d b (b+v)=v := by rw [hr.2 _ _ (le_refl _) (by linarith)]; rw [abs_of_nonneg (by linarith)]; ring
  have hs1 : d b (b+s)=s := by rw [hr.2 _ _ (le_refl _) (by linarith)]; rw [abs_of_nonneg (by linarith)]; ring
  have hvs : d (b+v) (b+s)=v-s := by rw [hr.2 _ _ (by linarith) (by linarith)]; rw [abs_of_nonpos (by linarith)]; ring
  have hvlow : v-d a b ≤ d a (b+v) := by
    have h := hd.triangle b a (b+v)
    rw [hv0,hd.symm b a] at h
    linarith
  have hslow : s-d a b ≤ d a (b+s) := by
    have h := hd.triangle b a (b+s)
    rw [hs1,hd.symm b a] at h
    linarith
  have hshigh : d a (b+s) ≤ d a b+s := by simpa only [hs1] using hd.triangle a b (b+s)
  have hB1 : 2*s ≤ lineB d a (a-s) (a-u) := by
    rw [hd.b_symm a (a-s) (a-u)]
    simp only [lineB,hu0,hs0,hus]; linarith
  have hB2 : 2*s ≤ lineB d a (a-u) (b+v) := by simp only [lineB,hu0,hmatch]; linarith
  have hB3 : 2*s-2*d a b ≤ lineB d a (b+v) (b+s) := by simp only [lineB,hvs]; linarith
  have hB4 : 2*s ≤ lineB d a (a-s) (b+v) :=
    (le_min hB1 hB2).trans (hd.min_b a (a-s) (a-u) (b+v))
  have hB5 : 2*s-2*d a b ≤ lineB d a (a-s) (b+s) :=
    (le_min (by linarith [hd.nonneg a b]) hB3).trans (hd.min_b a (a-s) (b+v) (b+s))
  simp only [lineB,hs0] at hB5
  linarith
lemma crossing_excess_bound {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {a b u v δ : ℝ}
    (hab : a ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v) (hδ : 0 < δ)
    (hr : ExteriorUnitRays d a b) (hc : NoFastCancellation d δ) :
    (u+v-d a b-d (a-u) (b+v))/2 ≤ 3*(b-a)/δ := by
  let s := (u+v-d a b-d (a-u) (b+v))/2
  have hD : d a b ≤ b-a := by simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hd.unit a b
  by_contra hn
  have hbad : 3*(b-a)/δ < s := lt_of_not_ge hn
  have hs : 0 < s := lt_of_le_of_lt (div_nonneg (by linarith) hδ.le) hbad
  have hv0 : d b (b+v)=v := by rw [hr.2 _ _ (le_refl _) (by linarith),abs_of_nonneg (by linarith)]; ring
  have hu0 : d (a-u) a=u := by rw [hr.1 _ _ (by linarith) (le_refl _),abs_of_nonneg (by linarith)]; ring
  have hlowu : u-d a b-v ≤ d (a-u) (b+v) := by
    have h1 := hd.triangle (a-u) (b+v) a
    have h2 := hd.triangle (b+v) b a
    rw [hu0] at h1
    rw [hd.symm (b+v) b,hv0,hd.symm b a] at h2
    linarith
  have hlowv : v-d a b-u ≤ d (a-u) (b+v) := by
    have h1 := hd.triangle b (a-u) (b+v)
    have h2 := hd.triangle b a (a-u)
    rw [hv0] at h1
    rw [hd.symm b a,hd.symm a (a-u),hu0] at h2
    linarith
  have hsu : s ≤ u := by dsimp [s]; linarith
  have hsv : s ≤ v := by dsimp [s]; linarith
  have hmatch : d (a-u) (b+v)=u+v-d a b-2*s := by dsimp [s]; ring
  have hm := matched_ray_distance hd hab hu hv hs.le hsu hsv hr hmatch
  let m := (a+b)/2
  let t := s+(b-a)/2
  have ht : 0 < t := by dsimp [t]; linarith
  have hxl : m-t=a-s := by dsimp [m,t]; ring
  have hxr : m+t=b+s := by dsimp [m,t]; ring
  have hsa : d (a-s) a=s := by rw [hr.1 _ _ (by linarith) (le_refl _),abs_of_nonneg (by linarith)]; ring
  have hbs : d b (b+s)=s := by rw [hr.2 _ _ (le_refl _) (by linarith),abs_of_nonneg (by linarith)]; ring
  have hma : d m a ≤ (b-a)/2 := by
    have h := hd.unit m a
    rw [abs_of_nonpos (by dsimp [m]; linarith)] at h
    dsimp [m] at h; linarith
  have hmb : d m b ≤ (b-a)/2 := by
    have h := hd.unit m b
    rw [abs_of_nonneg (by dsimp [m]; linarith)] at h
    dsimp [m] at h; linarith
  have hl := hd.triangle (a-s) m a
  have hh := hd.triangle b m (b+s)
  rw [hsa] at hl
  rw [hbs,hd.symm b m] at hh
  have hprod : 3*(b-a) < δ*s := by simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hbad
  apply hc m t ht
  rw [hxl,hxr]
  refine ⟨?_,?_,?_⟩
  · dsimp [t]; nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hab)]
  · dsimp [t]; nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hab)]
  · dsimp [t]; nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hab)]
lemma exterior_ray_crossloss {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hr : ExteriorUnitRays d a b) (hc : NoFastCancellation d δ)
    (x y : ℝ) (hxy : x ≤ y) :
    0 ≤ (y-x)-d x y ∧ (y-x)-d x y ≤ (2+6/δ)*(b-a) := by
  have hL : 0 ≤ b-a := sub_nonneg.mpr hab
  have hC : 2*(b-a) ≤ (2+6/δ)*(b-a) := by
    have hz : 0 ≤ 6/δ := by positivity
    nlinarith
  have hunit : d x y ≤ y-x := by simpa only [abs_of_nonneg (sub_nonneg.mpr hxy)] using hd.unit x y
  refine ⟨by linarith,?_⟩
  by_cases hya : y ≤ a
  · rw [hr.1 x y (hxy.trans hya) hya,abs_of_nonneg (sub_nonneg.mpr hxy)]
    nlinarith
  by_cases hbx : b ≤ x
  · rw [hr.2 x y hbx (hbx.trans hxy),abs_of_nonneg (sub_nonneg.mpr hxy)]
    nlinarith
  have hay : a ≤ y := le_of_lt (lt_of_not_ge hya)
  have hxb : x ≤ b := le_of_lt (lt_of_not_ge hbx)
  by_cases hxa : x ≤ a
  · by_cases hby : b ≤ y
    · have hh := crossing_excess_bound hd hab (sub_nonneg.mpr hxa) (sub_nonneg.mpr hby) hδ hr hc
      rw [show a-(a-x)=x by ring,show b+(y-b)=y by ring] at hh
      have hD : d a b ≤ b-a := by simpa only [abs_of_nonneg hL] using hd.unit a b
      have he : 6*(b-a)/δ=(6/δ)*(b-a) := by ring
      have he3 : 2*(3*(b-a)/δ)=6*(b-a)/δ := by ring
      nlinarith
    · have hyb : y ≤ b := le_of_lt (lt_of_not_ge hby)
      have hxaD : d x a=a-x := by rw [hr.1 x a hxa (le_refl _),abs_of_nonneg (sub_nonneg.mpr hxa)]
      have hyaD : d y a ≤ y-a := by
        have hh := hd.unit y a
        rw [abs_of_nonpos (by linarith)] at hh
        linarith
      have hh := hd.triangle x y a
      rw [hxaD] at hh
      linarith
  · have hax : a ≤ x := le_of_lt (lt_of_not_ge hxa)
    by_cases hby : b ≤ y
    · have hbyD : d b y=y-b := by rw [hr.2 b y (le_refl _) hby,abs_of_nonneg (sub_nonneg.mpr hby)]
      have hbxD : d b x ≤ b-x := by
        have hh := hd.unit b x
        rw [abs_of_nonpos (by linarith)] at hh
        linarith
      have hh := hd.triangle b x y
      rw [hbyD] at hh
      linarith
    · have hyb : y ≤ b := le_of_lt (lt_of_not_ge hby)
      linarith [hd.nonneg x y]
lemma exterior_ray_shortfall {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hr : ExteriorUnitRays d a b) (hc : NoFastCancellation d δ)
    (z t : ℝ) (ht : 0 < t) :
    0 ≤ 1-d z (z+t)/t ∧ 1-d z (z+t)/t ≤ (2+6/δ)*(b-a)/t := by
  obtain ⟨h0,h1⟩ := exterior_ray_crossloss hd hab hδ hr hc z (z+t) (by linarith)
  constructor
  · have hh := (div_le_one ht).mpr (show d z (z+t) ≤ t by linarith)
    linarith
  · apply (le_div_iff₀ ht).mpr
    have he : (1-d z (z+t)/t)*t=t-d z (z+t) := by field_simp
    rw [he]; linarith
lemma exterior_rays_nondegenerate {d : ℝ → ℝ → ℝ} (hd : TreeLine d) {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hr : ExteriorUnitRays d a b) (hc : NoFastCancellation d δ)
    (hne : ¬ ∀ x y : ℝ, d x y=|y-x|) : a < b := by
  by_contra h
  have he : b=a := by linarith
  apply hne
  intro x y
  by_cases hxy : x ≤ y
  · have hh := exterior_ray_crossloss hd hab hδ hr hc x y hxy
    rw [he,sub_self,mul_zero,abs_of_nonneg (sub_nonneg.mpr hxy)] at *
    linarith [hh.1,hh.2]
  · have hyx : y ≤ x := le_of_lt (lt_of_not_ge hxy)
    have hh := exterior_ray_crossloss hd hab hδ hr hc y x hyx
    rw [he,sub_self,mul_zero] at hh
    rw [hd.symm x y,abs_of_nonpos (by linarith)]
    linarith [hh.1,hh.2]
end StandardMapEntropy

end OAI
