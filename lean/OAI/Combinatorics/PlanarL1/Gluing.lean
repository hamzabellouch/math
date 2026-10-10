import OAI.Combinatorics.PlanarL1.Threshold

namespace OAI

section

namespace PlanarL1.Gluing
open Set
open scoped NNReal
attribute [local instance] Classical.propDecidable

lemma frontier_between_right {S : Set ℝ} (hS : IsClosed S) {x y : ℝ}
    (hxy : x ≤ y) (hx : x ∈ S) (hy : y ∉ S) :
    ∃ z ∈ frontier S, x ≤ z ∧ z ≤ y := by
  have hc : IsCompact (Icc x y ∩ S) := isCompact_Icc.inter_right hS
  obtain ⟨z,hz,hmax⟩ := hc.exists_isGreatest ⟨x,⟨⟨le_rfl,hxy⟩,hx⟩⟩
  refine ⟨z,?_,hz.1⟩
  rw [frontier,mem_sdiff,hS.closure_eq]
  refine ⟨hz.2,?_⟩
  intro hzi
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzi
  have hzy : z < y := lt_of_le_of_ne hz.1.2 (fun h => hy (h ▸ hz.2))
  let t := z + min ε (y-z)/2
  have ht1 : z < t := by dsimp [t]; have := lt_min hε (sub_pos.mpr hzy); linarith
  have ht2 : t ≤ y := by dsimp [t]; have := min_le_right ε (y-z); linarith
  have htd : dist t z < ε := by
    rw [Real.dist_eq,abs_of_pos (sub_pos.mpr ht1)]
    dsimp [t]
    have := min_le_left ε (y-z)
    linarith
  have htS := interior_subset (hball htd)
  exact (not_le.mpr ht1) (hmax ⟨⟨hz.1.1.trans ht1.le,ht2⟩,htS⟩)

lemma frontier_between_left {S : Set ℝ} (hS : IsClosed S) {x y : ℝ}
    (hxy : x ≤ y) (hx : x ∉ S) (hy : y ∈ S) :
    ∃ z ∈ frontier S, x ≤ z ∧ z ≤ y := by
  have hc : IsCompact (Icc x y ∩ S) := isCompact_Icc.inter_right hS
  obtain ⟨z,hz,hmin⟩ := hc.exists_isLeast ⟨y,⟨⟨hxy,le_rfl⟩,hy⟩⟩
  refine ⟨z,?_,hz.1⟩
  rw [frontier,mem_sdiff,hS.closure_eq]
  refine ⟨hz.2,?_⟩
  intro hzi
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzi
  have hxz : x < z := lt_of_le_of_ne hz.1.1 (fun h => hx (h.symm ▸ hz.2))
  let t := z - min ε (z-x)/2
  have ht1 : t < z := by dsimp [t]; have := lt_min hε (sub_pos.mpr hxz); linarith
  have ht2 : x ≤ t := by dsimp [t]; have := min_le_right ε (z-x); linarith
  have htd : dist t z < ε := by
    rw [Real.dist_eq,abs_of_neg (sub_neg.mpr ht1)]
    dsimp [t]
    have := min_le_left ε (z-x)
    linarith
  have htS := interior_subset (hball htd)
  exact (not_le.mpr ht1) (hmin ⟨⟨ht2,ht1.le.trans hz.1.2⟩,htS⟩)

lemma monotone_piecewise {S : Set ℝ} (hS : IsClosed S)
    {β : Type*} [Preorder β] {f g : ℝ → β}
    (hf : Monotone f) (hg : MonotoneOn g S) (he : EqOn g f (frontier S)) :
    Monotone (S.piecewise g f) := by
  classical
  intro x y hxy
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simpa only [piecewise_eq_of_mem _ _ _ hx,piecewise_eq_of_mem _ _ _ hy] using hg hx hy hxy
  · obtain ⟨z,hz,hxz,hzy⟩ := frontier_between_right hS hxy hx hy
    have hzS : z ∈ S := hS.frontier_subset hz
    have h : g x ≤ f y := (hg hx hzS hxz).trans (by rw [he hz]; exact hf hzy)
    simpa only [piecewise_eq_of_mem _ _ _ hx,piecewise_eq_of_notMem _ _ _ hy] using h
  · obtain ⟨z,hz,hxz,hzy⟩ := frontier_between_left hS hxy hx hy
    have hzS : z ∈ S := hS.frontier_subset hz
    have h : f x ≤ g y := (hf hxz).trans (by rw [← he hz]; exact hg hzS hy hzy)
    simpa only [piecewise_eq_of_notMem _ _ _ hx,piecewise_eq_of_mem _ _ _ hy] using h
  · simpa only [piecewise_eq_of_notMem _ _ _ hx,piecewise_eq_of_notMem _ _ _ hy] using hf hxy

lemma lipschitz_piecewise {S : Set ℝ} (hS : IsClosed S)
    {β : Type*} [PseudoMetricSpace β] {f g : ℝ → β} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzOnWith K g S)
    (he : EqOn g f (frontier S)) : LipschitzWith K (S.piecewise g f) := by
  classical
  have hb (x y : ℝ) (hxy : x ≤ y) :
      dist (S.piecewise g f x) (S.piecewise g f y) ≤ K * (y-x) := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · simpa only [piecewise_eq_of_mem _ _ _ hx,piecewise_eq_of_mem _ _ _ hy,
        Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] using hg.dist_le_mul x hx y hy
    · obtain ⟨z,hz,hxz,hzy⟩ := frontier_between_right hS hxy hx hy
      have hzS : z ∈ S := hS.frontier_subset hz
      have h1 := hg.dist_le_mul x hx z hzS
      have h2 := hf.dist_le_mul z y
      rw [he hz] at h1
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxz),neg_sub] at h1
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hzy),neg_sub] at h2
      have h3 := dist_triangle (g x) (f z) (f y)
      simp only [piecewise_eq_of_mem _ _ _ hx,piecewise_eq_of_notMem _ _ _ hy]
      nlinarith
    · obtain ⟨z,hz,hxz,hzy⟩ := frontier_between_left hS hxy hx hy
      have hzS : z ∈ S := hS.frontier_subset hz
      have h1 := hf.dist_le_mul x z
      have h2 := hg.dist_le_mul z hzS y hy
      rw [he hz] at h2
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxz),neg_sub] at h1
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hzy),neg_sub] at h2
      have h3 := dist_triangle (f x) (f z) (g y)
      simp only [piecewise_eq_of_notMem _ _ _ hx,piecewise_eq_of_mem _ _ _ hy]
      nlinarith
    · simpa only [piecewise_eq_of_notMem _ _ _ hx,piecewise_eq_of_notMem _ _ _ hy,
        Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] using hf.dist_le_mul x y
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain hxy | hyx := le_total x y
  · simpa only [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] using hb x y hxy
  · simpa only [dist_comm (S.piecewise g f y),Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hyx)] using hb y x hyx

end PlanarL1.Gluing



end

section

namespace PlanarL1.Gluing
open MeasureTheory Set
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The upper-bound invariant on a set of heights, stated on differences
because individual half-line indicators need not be integrable. -/
def VerticalBound (μ : Measure Ω) (f : ℝ → Ω → ℝ) (S : Set ℝ) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, Integrable (fun ω => f s ω-f t ω) μ ∧
    (∫ ω, |f s ω-f t ω| ∂μ) ≤ |s-t|

lemma difference_triangle {f g h : Ω → ℝ}
    (hf : Integrable (fun ω => f ω-g ω) μ)
    (hg : Integrable (fun ω => g ω-h ω) μ) :
    Integrable (fun ω => f ω-h ω) μ ∧
      (∫ ω, |f ω-h ω| ∂μ) ≤ (∫ ω, |f ω-g ω| ∂μ)+(∫ ω, |g ω-h ω| ∂μ) := by
  have hadd : Integrable (fun ω => (f ω-g ω)+(g ω-h ω)) μ := hf.add hg
  have hi : Integrable (fun ω => f ω-h ω) μ := by
    simpa only [sub_add_sub_cancel] using hadd
  have hfn : Integrable (fun ω => |f ω-g ω|) μ := hf.norm
  have hgn : Integrable (fun ω => |g ω-h ω|) μ := hg.norm
  have hin : Integrable (fun ω => |f ω-h ω|) μ := hi.norm
  have hsum : Integrable (fun ω => |f ω-g ω|+|g ω-h ω|) μ := hfn.add hgn
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω, |f ω-g ω|+|g ω-h ω| ∂μ := by
      exact integral_mono hin hsum (fun ω => abs_sub_le _ _ _)
    _ = _ := integral_add hfn hgn

lemma verticalBound_piecewise {S : Set ℝ} (hS : IsClosed S)
    {f g : ℝ → Ω → ℝ} (hf : VerticalBound μ f univ)
    (hg : VerticalBound μ g S) (he : EqOn g f (frontier S)) :
    VerticalBound μ (S.piecewise g f) univ := by
  classical
  have hb (x y : ℝ) (hxy : x ≤ y) :
      Integrable (fun ω => S.piecewise g f x ω-S.piecewise g f y ω) μ ∧
      (∫ ω, |S.piecewise g f x ω-S.piecewise g f y ω| ∂μ) ≤ y-x := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
    · simpa only [piecewise_eq_of_mem _ _ _ hx,piecewise_eq_of_mem _ _ _ hy,
        abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] using hg x hx y hy
    · obtain ⟨z,hz,hxz,hzy⟩ := frontier_between_right hS hxy hx hy
      have hgz := hg x hx z (hS.frontier_subset hz)
      have hfz := hf z (mem_univ z) y (mem_univ y)
      rw [he hz] at hgz
      obtain ⟨hi,hb⟩ := difference_triangle hgz.1 hfz.1
      simp only [piecewise_eq_of_mem _ _ _ hx,piecewise_eq_of_notMem _ _ _ hy]
      refine ⟨hi,?_⟩
      have h1 := hgz.2
      have h2 := hfz.2
      rw [abs_of_nonpos (sub_nonpos.mpr hxz),neg_sub] at h1
      rw [abs_of_nonpos (sub_nonpos.mpr hzy),neg_sub] at h2
      linarith
    · obtain ⟨z,hz,hxz,hzy⟩ := frontier_between_left hS hxy hx hy
      have hfz := hf x (mem_univ x) z (mem_univ z)
      have hgz := hg z (hS.frontier_subset hz) y hy
      rw [he hz] at hgz
      obtain ⟨hi,hb⟩ := difference_triangle hfz.1 hgz.1
      simp only [piecewise_eq_of_notMem _ _ _ hx,piecewise_eq_of_mem _ _ _ hy]
      refine ⟨hi,?_⟩
      have h1 := hfz.2
      have h2 := hgz.2
      rw [abs_of_nonpos (sub_nonpos.mpr hxz),neg_sub] at h1
      rw [abs_of_nonpos (sub_nonpos.mpr hzy),neg_sub] at h2
      linarith
    · simpa only [piecewise_eq_of_notMem _ _ _ hx,piecewise_eq_of_notMem _ _ _ hy,
        abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] using hf x (mem_univ x) y (mem_univ y)
  intro x _ y _
  rcases le_total x y with hxy | hyx
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub] using hb x y hxy
  · obtain ⟨hi,hb⟩ := hb y x hyx
    constructor
    · have hn : Integrable (fun ω => -(S.piecewise g f y ω-S.piecewise g f x ω)) μ := hi.neg
      simpa only [neg_sub] using hn
    · simpa only [abs_sub_comm (S.piecewise g f x _),abs_of_nonneg (sub_nonneg.mpr hyx)] using hb

end PlanarL1.Gluing

namespace PlanarL1.Columns.Model
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Local update data on closed full-column pieces. Cross-domain switches
must be unchanged, as ensured by the strict frontier margins in the source. -/
structure SetPatch (A : SetSystem M Ω μ) where
  domain : Fin n → Set ℝ
  closed : ∀ i, IsClosed (domain i)
  active : Ω → Fin n → ℝ → Prop
  measurable_active : ∀ i H, MeasurableSet {ω | active ω i H}
  increasing : ∀ ω i, MonotoneOn (active ω i) (domain i)
  boundary : ∀ ω i H, H ∈ frontier (domain i) →
    (active ω i H ↔ (A.activity ω).active i H)
  switch_inside : ∀ ω i j H, H ∈ M.heights i j → H ∈ domain i → H ∈ domain j →
    (active ω i H ↔ active ω j H)
  switch_outside : ∀ ω i j H, H ∈ M.heights i j → H ∈ domain i → H ∉ domain j →
    (active ω i H ↔ (A.activity ω).active i H)
  vertical : ∀ i, Gluing.VerticalBound μ (fun H ω => if active ω i H then 1 else 0) (domain i)

namespace SetPatch
variable {A : SetSystem M Ω μ} (P : SetPatch A)

noncomputable def patchedActivity (ω : Ω) : Activity M where
  active i H := if H ∈ P.domain i then P.active ω i H else (A.activity ω).active i H
  increasing i s t hst := by
    have hf : Monotone ((A.activity ω).active i) := by
      intro s t hst
      exact (A.activity ω).increasing i s t hst
    have hm := Gluing.monotone_piecewise (P.closed i)
      hf (P.increasing ω i)
      (fun H hH => propext (P.boundary ω i H hH))
    exact hm hst
  switch i j H hs := by
    by_cases hi : H ∈ P.domain i <;> by_cases hj : H ∈ P.domain j
    · simpa only [ite_eq_left hi,ite_eq_left hj] using P.switch_inside ω i j H hs hi hj
    · simpa only [ite_eq_left hi,ite_eq_right hj] using
        (P.switch_outside ω i j H hs hi hj).trans ((A.activity ω).switch i j H hs)
    · have hs' : H ∈ M.heights j i := by rwa [M.symm]
      simpa only [ite_eq_right hi,ite_eq_left hj] using
        ((A.activity ω).switch i j H hs).trans (P.switch_outside ω j i H hs' hj hi).symm
    · simpa only [ite_eq_right hi,ite_eq_right hj] using (A.activity ω).switch i j H hs

lemma indicator_eq (ω : Ω) (i : Fin n) (H : ℝ) :
    (P.patchedActivity ω).indicator i H =
      (P.domain i).piecewise (fun H ω => if P.active ω i H then (1:ℝ) else 0)
        (fun H ω => (A.activity ω).indicator i H) H ω := by
  unfold patchedActivity Activity.indicator
  by_cases h : H ∈ P.domain i <;> simp [h,Set.piecewise]

lemma verticalBound (i : Fin n) : Gluing.VerticalBound μ
    (fun H ω => (P.patchedActivity ω).indicator i H) univ := by
  have hf : Gluing.VerticalBound μ (fun H ω => (A.activity ω).indicator i H) univ := by
    intro s _ t _
    constructor
    · apply (integrable_norm_iff ((A.measurable_indicator i s).sub
        (A.measurable_indicator i t)).aestronglyMeasurable).mp
      simpa only [Real.norm_eq_abs,Pi.sub_apply] using A.vertical_integrable i s t
    · exact A.vertical_bound i s t
  have he : EqOn (fun H ω => if P.active ω i H then (1:ℝ) else 0)
      (fun H ω => (A.activity ω).indicator i H) (frontier (P.domain i)) := by
    intro H hH
    ext ω
    simp only [Activity.indicator,P.boundary ω i H hH]
  have hb := Gluing.verticalBound_piecewise (P.closed i) hf (P.vertical i) he
  simpa only [indicator_eq] using hb

noncomputable def apply : SetSystem M Ω μ where
  activity := P.patchedActivity
  measurable_active i H := by
    by_cases h : H ∈ P.domain i
    · simpa only [patchedActivity,ite_eq_left h] using P.measurable_active i H
    · simpa only [patchedActivity,ite_eq_right h] using A.measurable_active i H
  vertical_integrable i s t := by
    exact (P.verticalBound i s (mem_univ s) t (mem_univ t)).1.norm
  vertical_bound i s t := (P.verticalBound i s (mem_univ s) t (mem_univ t)).2

lemma unchanged {i : Fin n} {H : ℝ} (h : H ∉ P.domain i) (ω : Ω) :
    (P.apply.activity ω).active i H ↔ (A.activity ω).active i H := by
  simp only [apply,patchedActivity,ite_eq_right h]

lemma inside {i : Fin n} {H : ℝ} (h : H ∈ P.domain i) (ω : Ω) :
    (P.apply.activity ω).active i H ↔ P.active ω i H := by
  simp only [apply,patchedActivity,ite_eq_left h]

end SetPatch
end PlanarL1.Columns.Model

namespace PlanarL1.Threshold
open MeasureTheory Set
open scoped NNReal
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma active_verticalBound (Z : Variables Ω μ) {S : Set ℝ} {P : ℝ → ℝ}
    (hP : LipschitzOnWith 1 P S) : Gluing.VerticalBound μ
      (fun H ω => if active Z H (P H) ω then (1:ℝ) else 0) S := by
  intro s hs t ht
  simp only [active_indicator]
  refine ⟨Z.integrable_difference s (P s) t (P t),?_⟩
  rw [Z.distance]
  have h := hP.dist_le_mul s hs t ht
  rw [Real.dist_eq,Real.dist_eq,NNReal.coe_one,one_mul] at h
  exact max_le le_rfl h

/-- A literal common-label scalar chart replacement yields local patch data.
P already contains the source κ and comparison-orientation factors. -/
noncomputable def chartPatch {n : ℕ} {M : Columns.Model n}
    (A : M.SetSystem Ω μ) (Z : Variables Ω μ) (D : Fin n → Set ℝ)
    (hD : ∀ i, IsClosed (D i)) (P : Fin n → ℝ → ℝ)
    (hP : ∀ i, LipschitzOnWith 1 (P i) (D i))
    (hb : ∀ ω i H, H ∈ frontier (D i) →
      (active Z H (P i H) ω ↔ (A.activity ω).active i H))
    (hs : ∀ i j H, H ∈ M.heights i j → H ∈ D i → H ∈ D j → P i H = P j H)
    (hc : ∀ ω i j H, H ∈ M.heights i j → H ∈ D i → H ∉ D j →
      (active Z H (P i H) ω ↔ (A.activity ω).active i H)) : Columns.Model.SetPatch A where
  domain := D
  closed := hD
  active ω i H := active Z H (P i H) ω
  measurable_active i H := measurable_active Z H (P i H)
  increasing ω i := active_increasing Z (hP i) ω
  boundary := hb
  switch_inside ω i j H hij hi hj := by rw [hs i j H hij hi hj]
  switch_outside := hc
  vertical i := active_verticalBound Z (hP i)

end PlanarL1.Threshold


end

section

namespace PlanarL1.Columns.Model
open MeasureTheory
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma Activity.indicator_mono (A : Activity M) (i : Fin n) : Monotone (A.indicator i) := by
  intro s t hst
  by_cases hs : A.active i s
  · simp only [Activity.indicator,ite_eq_left hs,ite_eq_left (A.increasing i s t hst hs),le_refl]
  · simp only [Activity.indicator,ite_eq_right hs]
    split_ifs <;> norm_num

/-- Balanced changes of one-point marginals preserve the exact vertical bound
once genuine nestedness has been established. This avoids an unjustified
finite-boundary assumption on chart regions. -/
noncomputable def SetSystem.balancedUpdate (S : SetSystem M Ω μ) (A : Ω → Activity M)
    (hm : ∀ i H, MeasurableSet {ω | (A ω).active i H})
    (hi : ∀ i H, Integrable (fun ω => (A ω).indicator i H-(S.activity ω).indicator i H) μ)
    (hz : ∀ i H, (∫ ω, (A ω).indicator i H-(S.activity ω).indicator i H ∂μ)=0) :
    SetSystem M Ω μ := by
  have hoi (i : Fin n) (s t : ℝ) :
      Integrable (fun ω => (S.activity ω).indicator i s-(S.activity ω).indicator i t) μ := by
    apply (integrable_norm_iff ((S.measurable_indicator i s).sub
      (S.measurable_indicator i t)).aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using S.vertical_integrable i s t
  have hnew (i : Fin n) (s t : ℝ) :
      Integrable (fun ω => (A ω).indicator i s-(A ω).indicator i t) μ ∧
      (∫ ω, (A ω).indicator i s-(A ω).indicator i t ∂μ)=
        ∫ ω, (S.activity ω).indicator i s-(S.activity ω).indicator i t ∂μ := by
    have he : (fun ω => (A ω).indicator i s-(A ω).indicator i t) = fun ω =>
        ((A ω).indicator i s-(S.activity ω).indicator i s)+
        ((S.activity ω).indicator i s-(S.activity ω).indicator i t)-
        ((A ω).indicator i t-(S.activity ω).indicator i t) := by funext ω; ring
    rw [he]
    constructor
    · exact ((hi i s).add (hoi i s t)).sub (hi i t)
    · have hsum : Integrable (fun ω =>
          ((A ω).indicator i s-(S.activity ω).indicator i s)+
          ((S.activity ω).indicator i s-(S.activity ω).indicator i t)) μ :=
        (hi i s).add (hoi i s t)
      rw [integral_sub hsum (hi i t),
        integral_add (hi i s) (hoi i s t),hz i s,hz i t,zero_add,sub_zero]
  have habs (i : Fin n) (s t : ℝ) :
      (∫ ω, |(A ω).indicator i s-(A ω).indicator i t| ∂μ)=
        ∫ ω, |(S.activity ω).indicator i s-(S.activity ω).indicator i t| ∂μ := by
    rcases le_total t s with h | h
    · simp only [abs_of_nonneg (sub_nonneg.mpr ((A _).indicator_mono i h)),
        abs_of_nonneg (sub_nonneg.mpr ((S.activity _).indicator_mono i h))]
      exact (hnew i s t).2
    · simp only [abs_of_nonpos (sub_nonpos.mpr ((A _).indicator_mono i h)),
        abs_of_nonpos (sub_nonpos.mpr ((S.activity _).indicator_mono i h)),integral_neg]
      rw [(hnew i s t).2]
  exact {
    activity := A
    measurable_active := hm
    vertical_integrable := fun i s t => (hnew i s t).1.norm
    vertical_bound := fun i s t => (habs i s t).trans_le (S.vertical_bound i s t)
  }
end PlanarL1.Columns.Model



end

section

namespace PlanarL1.Columns.Model.SetPatch
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {A : SetSystem M Ω μ}

/-- A patch can be installed after other patches which have not changed its
closed domain. Its actual activity and all clipping data are retained. -/
def rebase (P : SetPatch A) (B : SetSystem M Ω μ)
    (hB : ∀ ω i H, H ∈ P.domain i → ((B.activity ω).active i H ↔ (A.activity ω).active i H)) :
    SetPatch B where
  domain := P.domain
  closed := P.closed
  active := P.active
  measurable_active := P.measurable_active
  increasing := P.increasing
  boundary ω i H hH := (P.boundary ω i H hH).trans
    (hB ω i H ((P.closed i).frontier_subset hH)).symm
  switch_inside := P.switch_inside
  switch_outside ω i j H hs hi hj := (P.switch_outside ω i j H hs hi hj).trans (hB ω i H hi).symm
  vertical := P.vertical

def UnchangedOverlap (P Q : SetPatch A) : Prop :=
  ∀ ω i H, H ∈ P.domain i → H ∈ Q.domain i →
    (P.active ω i H ↔ (A.activity ω).active i H) ∧
      (Q.active ω i H ↔ (A.activity ω).active i H)

/-- The deterministic tie rule chooses the first closed cell containing a
point. On all main-cell overlaps every proposal is the original activity. -/
noncomputable def selectActive : List (SetPatch A) → Ω → Fin n → ℝ → Prop
  | [],ω,i,H => (A.activity ω).active i H
  | P::L,ω,i,H => if H ∈ P.domain i then P.active ω i H else selectActive L ω i H

lemma selectActive_old (L : List (SetPatch A)) (ω : Ω) (i : Fin n) (H : ℝ)
    (h : ∀ P ∈ L, H ∈ P.domain i → (P.active ω i H ↔ (A.activity ω).active i H)) :
    selectActive L ω i H ↔ (A.activity ω).active i H := by
  induction L with
  | nil => rfl
  | cons P L ih =>
    dsimp only [selectActive]
    split_ifs with hi
    · exact h P (List.mem_cons_self) hi
    · exact ih (fun Q hQ => h Q (List.mem_cons_of_mem P hQ))

lemma exists_batch (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap) :
    ∃ B : SetSystem M Ω μ, ∀ ω i H, (B.activity ω).active i H ↔ selectActive L ω i H := by
  induction L with
  | nil => exact ⟨A,fun _ _ _ => Iff.rfl⟩
  | cons P L ih =>
    obtain ⟨hPL,hL⟩ := List.pairwise_cons.mp hL
    obtain ⟨B,hB⟩ := ih hL
    have hB0 (ω i H) (hi : H ∈ P.domain i) :
        (B.activity ω).active i H ↔ (A.activity ω).active i H := by
      rw [hB]
      exact selectActive_old L ω i H (fun Q hQ hj => (hPL Q hQ ω i H hi hj).2)
    refine ⟨(P.rebase B hB0).apply,?_⟩
    intro ω i H
    by_cases hi : H ∈ P.domain i
    · exact ((P.rebase B hB0).inside hi ω).trans (by simp only [selectActive,ite_eq_left hi,rebase])
    · exact ((P.rebase B hB0).unchanged hi ω).trans (by simpa only [selectActive,ite_eq_right hi] using hB ω i H)

noncomputable def batch (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap) : SetSystem M Ω μ :=
  (exists_batch L hL).choose

lemma batch_active (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap) (ω i H) :
    ((batch L hL).activity ω).active i H ↔ selectActive L ω i H :=
  (exists_batch L hL).choose_spec ω i H

lemma selectActive_choice (L : List (SetPatch A)) (i : Fin n) (H : ℝ) :
    (∀ ω, selectActive L ω i H ↔ (A.activity ω).active i H) ∨
      ∃ P ∈ L, ∀ ω, selectActive L ω i H ↔ (P.apply.activity ω).active i H := by
  induction L with
  | nil => exact Or.inl (fun _ => Iff.rfl)
  | cons P L ih =>
    by_cases hi : H ∈ P.domain i
    · right
      refine ⟨P,List.mem_cons_self,?_⟩
      intro ω
      simpa only [selectActive,ite_eq_left hi] using (P.inside hi ω).symm
    · rcases ih with h | ⟨Q,hQ,h⟩
      · left
        intro ω
        simpa only [selectActive,ite_eq_right hi] using h ω
      · right
        refine ⟨Q,List.mem_cons_of_mem P hQ,?_⟩
        intro ω
        simpa only [selectActive,ite_eq_right hi] using h ω

/-- Simultaneous disjoint main clipping has the one-patch movement bound,
not the sum over cells. Covers all points, not just the listed vertices. -/
lemma batch_movement (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap)
    {b : ℝ} (hb : 0 ≤ b)
    (hp : ∀ P ∈ L, ∀ i H, (∫ ω, |(P.apply.activity ω).indicator i H-(A.activity ω).indicator i H| ∂μ) ≤ b)
    (i : Fin n) (H : ℝ) :
    (∫ ω, |((batch L hL).activity ω).indicator i H-(A.activity ω).indicator i H| ∂μ) ≤ b := by
  rcases selectActive_choice L i H with h | ⟨P,hP,h⟩
  · have he : (fun ω => |((batch L hL).activity ω).indicator i H-(A.activity ω).indicator i H|) =
        fun _ => 0 := by
      funext ω
      simp only [Activity.indicator,batch_active,h,sub_self,abs_zero]
    rw [he,integral_zero]
    exact hb
  · have he : (fun ω => |((batch L hL).activity ω).indicator i H-(A.activity ω).indicator i H|) =
        fun ω => |(P.apply.activity ω).indicator i H-(A.activity ω).indicator i H| := by
      funext ω
      simp only [Activity.indicator,batch_active,h]
    rw [he]
    exact hp P hP i H

lemma batch_movement_integrable (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap)
    (hp : ∀ P ∈ L, ∀ i H, Integrable
      (fun ω => (P.apply.activity ω).indicator i H-(A.activity ω).indicator i H) μ)
    (i : Fin n) (H : ℝ) : Integrable
      (fun ω => ((batch L hL).activity ω).indicator i H-(A.activity ω).indicator i H) μ := by
  rcases selectActive_choice L i H with h | ⟨P,hP,h⟩
  · have he : (fun ω => ((batch L hL).activity ω).indicator i H-(A.activity ω).indicator i H) =
        fun _ => 0 := by
      funext ω
      simp only [Activity.indicator,batch_active,h,sub_self]
    rw [he]
    exact integrable_zero _ _ _
  · have he : (fun ω => ((batch L hL).activity ω).indicator i H-(A.activity ω).indicator i H) =
        fun ω => (P.apply.activity ω).indicator i H-(A.activity ω).indicator i H := by
      funext ω
      simp only [Activity.indicator,batch_active,h]
    rw [he]
    exact hp P hP i H

end PlanarL1.Columns.Model.SetPatch


namespace PlanarL1.Columns.Model.SetPatch
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {M : Model n} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {A : SetSystem M Ω μ}

lemma selectActive_inside (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap)
    {P : SetPatch A} (hP : P ∈ L) (ω i H) (hi : H ∈ P.domain i) :
    selectActive L ω i H ↔ P.active ω i H := by
  induction L with
  | nil => simp only [List.not_mem_nil] at hP
  | cons Q L ih =>
    obtain ⟨hQL,hL⟩ := List.pairwise_cons.mp hL
    rcases List.mem_cons.mp hP with hP | hP
    · subst P
      simp only [selectActive,ite_eq_left hi]
    · by_cases hj : H ∈ Q.domain i
      · simp only [selectActive,ite_eq_left hj]
        exact (hQL P hP ω i H hj hi).1.trans (hQL P hP ω i H hj hi).2.symm
      · simpa only [selectActive,ite_eq_right hj] using ih hL hP

lemma batch_inside (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap)
    {P : SetPatch A} (hP : P ∈ L) (ω i H) (hi : H ∈ P.domain i) :
    ((batch L hL).activity ω).active i H ↔ (P.apply.activity ω).active i H :=
  (batch_active L hL ω i H).trans ((selectActive_inside L hL hP ω i H hi).trans
    (P.inside hi ω).symm)

lemma batch_old (L : List (SetPatch A)) (hL : L.Pairwise UnchangedOverlap)
    (ω i H) (hp : ∀ P ∈ L, (P.apply.activity ω).active i H ↔ (A.activity ω).active i H) :
    ((batch L hL).activity ω).active i H ↔ (A.activity ω).active i H := by
  apply (batch_active L hL ω i H).trans
  exact selectActive_old L ω i H (fun P hP hi => (P.inside hi ω).symm.trans (hp P hP))
end PlanarL1.Columns.Model.SetPatch


end

end OAI
