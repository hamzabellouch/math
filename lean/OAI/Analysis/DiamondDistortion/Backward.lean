import OAI.Analysis.DiamondDistortion.AMUC

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Midpoint
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Symmetry and convexity along a ray, proved by the explicit two-endpoint
    convex combinations. -/
lemma lens_shrink {a R : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (u v : X)
    (hp : ‖u+v‖ ≤ R) (hm : ‖u-v‖ ≤ R) :
    max ‖u+a • v‖ ‖u-a • v‖ ≤ R := by
  have hn1 : 0 ≤ (1+a)/2 := by positivity
  have hn2 : 0 ≤ (1-a)/2 := by linarith
  have hn (v w : X) (hv : ‖v‖ ≤ R) (hw : ‖w‖ ≤ R) :
      ‖((1+a)/2) • v+((1-a)/2) • w‖ ≤ R := by
    calc
      _ ≤ ‖((1+a)/2) • v‖+‖((1-a)/2) • w‖ := norm_add_le _ _
      _ = ((1+a)/2)*‖v‖+((1-a)/2)*‖w‖ := by
        rw [norm_smul,norm_smul,Real.norm_of_nonneg hn1,Real.norm_of_nonneg hn2]
      _ ≤ ((1+a)/2)*R+((1-a)/2)*R := add_le_add
        (mul_le_mul_of_nonneg_left hv hn1) (mul_le_mul_of_nonneg_left hw hn2)
      _ = R := by ring
  apply max_le
  · have he : u+a • v=((1+a)/2) • (u+v)+((1-a)/2) • (u-v) := by module
    rw [he]
    exact hn _ _ hp hm
  · have he : u-a • v=((1+a)/2) • (u-v)+((1-a)/2) • (u+v) := by module
    rw [he]
    exact hn _ _ hm hp

/-- The unit-sphere finite-codimensional version of the local midpoint input. -/
def LocalQuotientGain (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (t g : ℝ) : Prop :=
  ∀ u : X,‖u‖=1 → ∃ F : Submodule ℝ X,IsClosed (F : Set X) ∧
    FiniteDimensional ℝ (X ⧸ F) ∧
    ∀ y : X,y ∈ F → ‖y‖=1 → 1+g ≤ max ‖u+t • y‖ ‖u-t • y‖

lemma LocalQuotientGain.large_step {t g : ℝ} (ht : 0 < t)
    (h : LocalQuotientGain X t g) : QuotientGain X t g := by
  intro u hu
  obtain ⟨F,hclosed,hfinite,hF⟩ := h u hu
  refine ⟨F,hclosed,hfinite,?_⟩
  intro v hv htv
  have hv0 : 0 < ‖v‖ := ht.trans_le htv
  have hunit : ‖‖v‖⁻¹ • v‖=1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hv0.le),inv_mul_cancel₀ hv0.ne']
  have hl := hF (‖v‖⁻¹ • v) (F.smul_mem _ hv) hunit
  have hle := lens_shrink (show 0 ≤ t/‖v‖ by positivity)
    ((div_le_one₀ hv0).mpr htv) u v
    (le_max_left ‖u+v‖ ‖u-v‖) (le_max_right ‖u+v‖ ‖u-v‖)
  simp only [smul_smul,← div_eq_mul_inv] at hl
  exact hl.trans hle

/-- Closed finite-codimensional subspaces, with the two conditions separately
    retained, not replaced by a coordinate-null convention. -/
def Cof (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :=
  {F : Submodule ℝ X // IsClosed (F : Set X) ∧ FiniteDimensional ℝ (X ⧸ F)}

def maximumModulus (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (t : ℝ) : EReal :=
  ⨅ u : {u : X // ‖u‖=1}, ⨆ F : Cof X,
    ⨅ y : {y : X // y ∈ F.val ∧ ‖y‖=1},
      ((max ‖u.val+t • y.val‖ ‖u.val-t • y.val‖-1 : ℝ) : EReal)

def AMUC (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ t : ℝ,0 < t → t < 1 → 0 < maximumModulus X t

lemma positive_modulus_gain {t : ℝ} (h : 0 < maximumModulus X t) :
    ∃ g : ℝ,0 < g ∧ LocalQuotientGain X t g := by
  obtain ⟨g,hg,hgδ⟩ := EReal.exists_between_coe_real h
  refine ⟨g,by exact_mod_cast hg,?_⟩
  intro u hu
  let M : {w : X // ‖w‖=1} → EReal := fun w =>
    ⨆ F : Cof X, ⨅ y : {y : X // y ∈ F.val ∧ ‖y‖=1},
      ((max ‖w.val+t • y.val‖ ‖w.val-t • y.val‖-1 : ℝ) : EReal)
  have hmu : maximumModulus X t ≤ M ⟨u,hu⟩ :=
    iInf_le M (⟨u,hu⟩ : {w : X // ‖w‖=1})
  have hgu := hgδ.trans_le hmu
  change (g : EReal) < ⨆ F : Cof X,
    ⨅ y : {y : X // y ∈ F.val ∧ ‖y‖=1},
      ((max ‖u+t • y.val‖ ‖u-t • y.val‖-1 : ℝ) : EReal) at hgu
  obtain ⟨F,hF⟩ := lt_iSup_iff.mp hgu
  refine ⟨F.val,F.property.1,F.property.2,?_⟩
  intro y hyF hy1
  have hvalue : (⨅ z : {z : X // z ∈ F.val ∧ ‖z‖=1},
      ((max ‖u+t • z.val‖ ‖u-t • z.val‖-1 : ℝ) : EReal)) ≤
      ((max ‖u+t • y‖ ‖u-t • y‖-1 : ℝ) : EReal) :=
    iInf_le (fun z : {z : X // z ∈ F.val ∧ ‖z‖=1} =>
      ((max ‖u+t • z.val‖ ‖u-t • z.val‖-1 : ℝ) : EReal))
      (⟨y,hyF,hy1⟩ : {z : X // z ∈ F.val ∧ ‖z‖=1})
  have hb := hF.trans_le hvalue
  have hh : g < max ‖u+t • y‖ ‖u-t • y‖-1 := by exact_mod_cast hb
  linarith

end Midpoint

namespace Diamond
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- AMUC forbids a single distortion bound for the normalized countably branching
    diamonds. Finite dimensional spaces are automatically covered as well. -/
theorem amuc_obstruction (hX : Midpoint.AMUC X) : ¬ UniformEmbeddings X := by
  rintro ⟨D,h⟩
  obtain ⟨f₀,s₀,h₀⟩ := h 0
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) h₀.1
  let t := 1/(2*D)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := (div_lt_one (by positivity : 0 < 2*D)).mpr (by linarith [h₀.1])
  obtain ⟨g,hg,hgX⟩ := Midpoint.positive_modulus_gain (hX t ht ht1)
  obtain ⟨k,hk'⟩ := exists_nat_gt (D/g)
  have hkg : D < (k:ℝ)*g := (div_lt_iff₀ hg).mp hk'
  have hBern := one_add_mul_le_pow (by linarith : (-2:ℝ) ≤ g) k
  have hk : D < (1+g)^k := by linarith
  obtain ⟨f,s,hf⟩ := h k
  have hh := quotient_full_gain ht hg (le_refl t) (hgX.large_step ht) k f hf
  have hp : 0 < (1+g)^k := by positivity
  have hpow : (1+g)^k ≤ D := by simpa only [one_mul] using (le_div_iff₀ hp).mp hh
  exact (not_lt_of_ge hpow) hk

/-- Transport of distortion under exact two-sided norm equivalence. The linear
    equivalence is simply the identification of the original space with its
    equivalent-norm copy; there is no change of graph or choice of scales. -/
lemma equivalent_distortion (e : X ≃ₗ[ℝ] Y) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (he : ∀ x : X,a*‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ b*‖x‖)
    {k : ℕ} (f : Vertex k → X) {D s : ℝ} (hf : HasDistortion k f D s) :
    HasDistortion k (fun v => e (f v)) ((b/a)*D) (a*s) := by
  have hab : a ≤ b := by
    have hl := slope_lower f (fun u v => (hf.2.2 u v).1) (baseEdge k)
    have hn : 0 < ‖slope f (baseEdge k)‖ := hf.2.1.trans_le hl
    have h := (he (slope f (baseEdge k))).1.trans (he (slope f (baseEdge k))).2
    exact (mul_le_mul_iff_left₀ hn).mp (by simpa only [mul_comm] using h)
  have hba : 1 ≤ b/a := (one_le_div ha).mpr hab
  refine ⟨?_,mul_pos ha hf.2.1,?_⟩
  · nlinarith [hf.1]
  · intro u v
    rw [← map_sub]
    constructor
    · have hh := mul_le_mul_of_nonneg_left (hf.2.2 u v).1 ha.le
      have hh' : (a*s)*distance k u v ≤ a*‖f u-f v‖ := by simpa only [mul_assoc] using hh
      exact hh'.trans (he (f u-f v)).1
    · have hh := ((he (f u-f v)).2).trans
        (mul_le_mul_of_nonneg_left (hf.2.2 u v).2 hb.le)
      have hid : b*(D*s*distance k u v)=((b/a)*D)*(a*s)*distance k u v := by
        field_simp
      rwa [hid] at hh

theorem equivalent_amuc [CompleteSpace X] [CompleteSpace Y]
    (e : X ≃ₗ[ℝ] Y) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (he : ∀ x : X,a*‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ b*‖x‖)
    (hY : Midpoint.AMUC Y) : ¬ UniformEmbeddings X := by
  rintro ⟨D,h⟩
  apply amuc_obstruction hY
  refine ⟨(b/a)*D,?_⟩
  intro k
  obtain ⟨f,s,hf⟩ := h k
  exact ⟨fun v => e (f v),a*s,equivalent_distortion e ha hb he f hf⟩

end Diamond

end DiamondDistortion

end

end OAI
