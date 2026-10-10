import Mathlib
import OAI.Geometry.Cannon.Modulus.Clip
import OAI.Geometry.Cannon.Modulus.Cost

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace

namespace CannonPotential

open Set CannonCells

variable {X ι : Type*} [TopologicalSpace X] [PathConnectedSpace X] [Fintype ι]

variable (C : ι → Set X) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)

def pathCosts (A : Set X) (x : X) : Set ℝ :=
  {c | ∃ a ∈ A, ∃ p : Path a x, cost C w (range p) = c}

noncomputable def distanceFrom (A : Set X) (x : X) : ℝ := sInf (pathCosts C w A x)

lemma pathCosts_nonempty {A : Set X} (hA : A.Nonempty) (x : X) :
    (pathCosts C w A x).Nonempty := by
  obtain ⟨a,ha⟩ := hA
  let p := PathConnectedSpace.somePath a x
  exact ⟨cost C w (range p),a,ha,p,rfl⟩

include hw

omit [PathConnectedSpace X] in
lemma pathCosts_bddBelow (A : Set X) (x : X) : BddBelow (pathCosts C w A x) := by
  refine ⟨0,?_⟩
  rintro c ⟨a,ha,p,rfl⟩
  exact cost_nonneg C hw _

lemma distanceFrom_nonneg {A : Set X} (hA : A.Nonempty) (x : X) :
    0 ≤ distanceFrom C w A x := by
  apply le_csInf (pathCosts_nonempty C w hA x)
  rintro c ⟨a,ha,p,rfl⟩
  exact cost_nonneg C hw _

omit [PathConnectedSpace X] in
lemma distanceFrom_le_path {A : Set X} {a x : X} (ha : a ∈ A) (p : Path a x) :
    distanceFrom C w A x ≤ cost C w (range p) :=
  csInf_le (pathCosts_bddBelow C w hw A x) ⟨a,ha,p,rfl⟩

lemma distanceFrom_triangle {A : Set X} (hA : A.Nonempty) {x y : X} (p : Path x y) :
    distanceFrom C w A y ≤ distanceFrom C w A x + cost C w (range p) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  have hc : distanceFrom C w A x < b - cost C w (range p) := by linarith
  obtain ⟨c,⟨a,ha,q,rfl⟩,hc⟩ :=
    (csInf_lt_iff (pathCosts_bddBelow C w hw A x) (pathCosts_nonempty C w hA x)).mp hc
  have h₁ := distanceFrom_le_path C w hw ha (q.trans p)
  rw [Path.trans_range] at h₁
  have h₂ := cost_union_le C hw (range q) (range p)
  linarith

noncomputable def raw (A : Set X) (x : X) : ℝ := by
  classical
  exact if x ∈ A then 0 else min 1 (distanceFrom C w A x)

omit hw [PathConnectedSpace X] in
lemma raw_on_top {A : Set X} {x : X} (hx : x ∈ A) : raw C w A x = 0 := by
  classical
  simp [raw,hx]

lemma raw_bounds {A : Set X} (hA : A.Nonempty) (x : X) : raw C w A x ∈ Icc 0 1 := by
  classical
  by_cases hx : x ∈ A
  · simp [raw,hx]
  · simp only [raw,ite_eq_right hx,mem_Icc]
    exact ⟨le_min zero_le_one (distanceFrom_nonneg C w hw hA x),min_le_left _ _⟩

lemma raw_le_add_cost {A : Set X} (hA : A.Nonempty) {x y : X} (p : Path x y) :
    raw C w A y ≤ raw C w A x + cost C w (range p) := by
  classical
  have hn := cost_nonneg C hw (range p)
  by_cases hy : y ∈ A
  · rw [raw_on_top C w hy]
    exact add_nonneg (raw_bounds C w hw hA x).1 hn
  by_cases hx : x ∈ A
  · rw [raw_on_top C w hx,zero_add]
    simp only [raw,ite_eq_right hy]
    exact (min_le_right _ _).trans (distanceFrom_le_path C w hw hx p)
  simp only [raw,ite_eq_right hx,ite_eq_right hy]
  have ht := distanceFrom_triangle C w hw hA p
  by_cases hb : distanceFrom C w A x ≤ 1
  · rw [min_eq_right hb]
    exact (min_le_right _ _).trans ht
  · rw [min_eq_left (le_of_not_ge hb)]
    exact (min_le_left _ _).trans (by linarith)

theorem raw_path_variation {A : Set X} (hA : A.Nonempty) {x y : X} (p : Path x y) :
    |raw C w A x - raw C w A y| ≤ cost C w (range p) := by
  have h₁ := raw_le_add_cost C w hw hA p
  have h₂ := raw_le_add_cost C w hw hA p.symm
  rw [Path.symm_range] at h₂
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

omit hw in
lemma raw_on_bottom {A B : Set X} (hA : A.Nonempty) (hAB : Disjoint A B)
    (hadm : ∀ a ∈ A, ∀ b ∈ B, ∀ p : Path a b, 1 ≤ cost C w (range p))
    {b : X} (hb : b ∈ B) : raw C w A b = 1 := by
  classical
  have hba : b ∉ A := fun ha => Set.disjoint_left.mp hAB ha hb
  simp only [raw,ite_eq_right hba]
  apply min_eq_left
  apply le_csInf (pathCosts_nonempty C w hA b)
  rintro c ⟨a,ha,p,rfl⟩
  exact hadm a ha b hb p

end CannonPotential

open Set unitInterval

namespace CannonBands

open Set unitInterval

variable {X : Type*} [TopologicalSpace X]

lemma last_level_suffix (g : I → ℝ) (hg : Continuous g) (a : ℝ)
    (hne : ∃ t, g t = a) (hone : a ≤ g 1) :
    ∃ s : I, g s = a ∧ ∀ t, s ≤ t → a ≤ g t := by
  have hK : IsCompact (g ⁻¹' {a}) := (isClosed_singleton.preimage hg).isCompact
  obtain ⟨s,hs,hmax⟩ := hK.exists_isMaxOn hne continuous_id.continuousOn
  refine ⟨s,hs,?_⟩
  intro t ht
  by_contra hn
  have hlt := lt_of_not_ge hn
  obtain ⟨z,hz,hza⟩ := intermediate_value_Icc (show t ≤ (1:I) from t.property.2)
    hg.continuousOn ⟨hlt.le,hone⟩
  have hzs : z ≤ s := hmax hza
  have hst : s < t := lt_of_le_of_ne ht (by intro he; rw [← he,hs] at hlt; exact lt_irrefl _ hlt)
  exact (not_lt_of_ge hzs) (hst.trans_le hz.1)

lemma value_le_cost_of_top
    (g : X → ℝ) (hg : Continuous g) (a b : ℝ)
    (f : X → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hTop : ∀ x, g x ≤ a → f x = 0)
    (c : Set X → ℝ) (hc0 : ∀ S, 0 ≤ c S)
    (hcmono : ∀ S T, S ⊆ T → c S ≤ c T)
    (hcore : ∀ u v : X, ∀ p : Path u v,
      (∀ t, g (p t) ∈ Icc a b) → |f u-f v| ≤ c (range p))
    {u v : X} (p : Path u v) (hup : ∀ t, g (p t) ≤ b)
    (htop : ∃ t, g (p t) ≤ a) (t : I) : f (p t) ≤ c (range p) := by
  by_cases ht : g (p t) ≤ a
  · rw [hTop _ ht]
    exact hc0 _
  obtain ⟨s,hs⟩ := htop
  let q := p.subpath s t
  have hstart : g (q 0) ≤ a := by simpa [q] using hs
  have hend : a ≤ g (q 1) := by simpa [q] using le_of_not_ge ht
  have hne : ∃ z, g (q z) = a := by
    obtain ⟨z,_,hz⟩ := intermediate_value_Icc (show (0:I) ≤ 1 from zero_le)
      (hg.comp q.continuous).continuousOn ⟨hstart,hend⟩
    exact ⟨z,hz⟩
  obtain ⟨s',hs',hafter⟩ := last_level_suffix (fun z => g (q z))
    (hg.comp q.continuous) a hne hend
  have hqr : range q ⊆ range p := by
    rw [show range q = p '' uIcc s t from Path.range_subpath p s t]
    exact image_subset_range _ _
  have hq'r : range (q.subpath s' 1) ⊆ range q := by
    rw [Path.range_subpath]
    exact image_subset_range _ _
  have hq := hcore (q s') (q 1) (q.subpath s' 1) (by
    intro z
    have hz : (q.subpath s' 1) z ∈ range (q.subpath s' 1) := mem_range_self z
    rw [Path.range_subpath_of_le _ _ _ (show s' ≤ (1:I) from s'.property.2)] at hz
    obtain ⟨w,hw,hwz⟩ := hz
    rw [← hwz]
    refine ⟨hafter w hw.1,?_⟩
    obtain ⟨z,hz⟩ := hqr (mem_range_self w)
    rw [← hz]
    exact hup z)
  rw [hTop _ hs'.le,zero_sub,abs_neg,abs_of_nonneg (hf0 _)] at hq
  have hh := hq.trans (hcmono _ _ (hq'r.trans hqr))
  simpa [q] using hh

theorem extended_path_variation
    (g : X → ℝ) (hg : Continuous g) (a b : ℝ) (hab : a < b)
    (f : X → ℝ) (hf : ∀ x, f x ∈ Icc 0 1)
    (hTop : ∀ x, g x ≤ a → f x = 0) (hBot : ∀ x, b ≤ g x → f x = 1)
    (c : Set X → ℝ) (hc0 : ∀ S, 0 ≤ c S)
    (hcmono : ∀ S T, S ⊆ T → c S ≤ c T)
    (hcore : ∀ u v : X, ∀ p : Path u v,
      (∀ t, g (p t) ∈ Icc a b) → |f u-f v| ≤ c (range p))
    {u v : X} (p : Path u v) : |f u-f v| ≤ c (range p) := by
  by_cases hT : ∃ t, g (p t) ≤ a
  · by_cases hB : ∃ t, b ≤ g (p t)
    · obtain ⟨s,hs⟩ := hT
      obtain ⟨t,ht⟩ := hB
      let q := p.subpath s t
      obtain ⟨v₀,v₁,hv,hv₀,hv₁,hbetween⟩ := CannonAnnular.radial_subinterval
        (fun z => g (q z)) (hg.comp q.continuous) a b hab
        (by simpa [q] using hs) (by simpa [q] using ht)
      have hsq : range (q.subpath v₀ v₁) ⊆ range q := by
        rw [Path.range_subpath]
        exact image_subset_range _ _
      have hsp : range q ⊆ range p := by
        rw [show range q = p '' uIcc s t from Path.range_subpath p s t]
        exact image_subset_range _ _
      have hc := hcore (q v₀) (q v₁) (q.subpath v₀ v₁) (by
        intro z
        have hz : (q.subpath v₀ v₁) z ∈ range (q.subpath v₀ v₁) := mem_range_self z
        rw [Path.range_subpath_of_le _ _ _ hv.le] at hz
        obtain ⟨w,hw,hwz⟩ := hz
        rw [← hwz]
        exact hbetween w hw)
      rw [hTop _ hv₀.le,hBot _ hv₁.ge] at hc
      norm_num only [zero_sub,abs_neg,abs_one] at hc
      have hc' := hc.trans (hcmono _ _ (hsq.trans hsp))
      apply le_trans _ hc'
      exact abs_sub_le_iff.mpr ⟨by linarith [(hf u).2,(hf v).1],by linarith [(hf v).2,(hf u).1]⟩
    · have hup : ∀ t, g (p t) ≤ b := by
        intro t
        exact (lt_of_not_ge (fun ht => hB ⟨t,ht⟩)).le
      have hval := value_le_cost_of_top g hg a b f (fun x => (hf x).1) hTop
        c hc0 hcmono hcore p hup hT
      have hu : f u ≤ c (range p) := by simpa using hval 0
      have hv : f v ≤ c (range p) := by simpa using hval 1
      exact abs_sub_le_iff.mpr ⟨by linarith [(hf v).1],by linarith [(hf u).1]⟩
  · by_cases hB : ∃ t, b ≤ g (p t)
    · have hcore' : ∀ u v : X, ∀ p : Path u v,
          (∀ t, -g (p t) ∈ Icc (-b) (-a)) →
          |(1-f u)-(1-f v)| ≤ c (range p) := by
        intro u v p hp
        have hh := hcore u v p (fun t => ⟨by linarith [(hp t).2],by linarith [(hp t).1]⟩)
        simpa only [sub_sub_sub_cancel_left,abs_sub_comm] using hh
      have hval := value_le_cost_of_top (fun x => -g x) hg.neg (-b) (-a)
        (fun x => 1-f x) (fun x => by linarith [(hf x).2])
        (fun x hx => by rw [hBot x (by linarith)]; ring)
        c hc0 hcmono hcore' p (fun t => by
          have ht : a < g (p t) := lt_of_not_ge (fun ht => hT ⟨t,ht⟩)
          linarith) (by obtain ⟨t,ht⟩ := hB; exact ⟨t,by linarith⟩)
      have hu : 1-f u ≤ c (range p) := by simpa using hval 0
      have hv : 1-f v ≤ c (range p) := by simpa using hval 1
      exact abs_sub_le_iff.mpr ⟨by linarith [(hf u).2],by linarith [(hf v).2]⟩
    · apply hcore u v p
      intro t
      exact ⟨(lt_of_not_ge (fun ht => hT ⟨t,ht⟩)).le,
        (lt_of_not_ge (fun ht => hB ⟨t,ht⟩)).le⟩

end CannonBands

namespace CannonBands

open Set CannonCells CannonPotential

variable {X ι : Type*} [TopologicalSpace X] [Fintype ι]

abbrev Strip (g : X → ℝ) (a b : ℝ) := {x : X // g x ∈ Icc a b}

def extend (g : X → ℝ) (a b : ℝ) (f : Strip g a b → ℝ) (x : X) : ℝ := by
  classical
  exact if hx : g x ∈ Icc a b then f ⟨x,hx⟩ else if g x ≤ a then 0 else 1

omit [TopologicalSpace X] in
lemma extend_on_strip (g : X → ℝ) (a b : ℝ) (f : Strip g a b → ℝ) (x : X)
    (hx : g x ∈ Icc a b) : extend g a b f x = f ⟨x,hx⟩ := by
  simp [extend,hx]

omit [TopologicalSpace X] in
lemma extend_bounds (g : X → ℝ) (a b : ℝ) (f : Strip g a b → ℝ)
    (hf : ∀ x, f x ∈ Icc 0 1) (x : X) : extend g a b f x ∈ Icc 0 1 := by
  classical
  unfold extend
  split
  · exact hf _
  · split <;> norm_num

omit [TopologicalSpace X] in
lemma extend_top (g : X → ℝ) (a b : ℝ) (f : Strip g a b → ℝ)
    (hf : ∀ x, g x.val = a → f x = 0) (x : X) (hx : g x ≤ a) :
    extend g a b f x = 0 := by
  classical
  unfold extend
  split
  · exact hf _ (le_antisymm hx ‹g x ∈ Icc a b›.1)
  · simp

omit [TopologicalSpace X] in
lemma extend_bottom (g : X → ℝ) (a b : ℝ) (hab : a < b) (f : Strip g a b → ℝ)
    (hf : ∀ x, g x.val = b → f x = 1) (x : X) (hx : b ≤ g x) :
    extend g a b f x = 1 := by
  classical
  unfold extend
  split
  · exact hf _ (le_antisymm ‹g x ∈ Icc a b›.2 hx)
  · simp [show ¬g x ≤ a by linarith]

omit [TopologicalSpace X] in
lemma cost_preimage_image {Y : Type*} (e : Y → X) (C : ι → Set X) (w : ι → ℝ)
    (A : Set Y) : cost (fun i => e ⁻¹' C i) w A = cost C w (e '' A) := by
  unfold cost
  congr 1
  ext i
  rw [mem_indices,mem_indices]
  constructor
  · rintro ⟨x,hx,hc⟩
    exact ⟨e x,⟨x,hx,rfl⟩,hc⟩
  · rintro ⟨z,⟨x,hx,rfl⟩,hc⟩
    exact ⟨x,hx,hc⟩

def stripPath (g : X → ℝ) (a b : ℝ) {u v : X} (p : Path u v)
    (hp : ∀ t, g (p t) ∈ Icc a b) :
    Path (⟨u,by simpa using hp 0⟩ : Strip g a b) ⟨v,by simpa using hp 1⟩ where
  toFun := fun t => ⟨p t,hp t⟩
  continuous_toFun := p.continuous.subtype_mk hp
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

lemma stripPath_image_range (g : X → ℝ) (a b : ℝ) {u v : X} (p : Path u v)
    (hp : ∀ t, g (p t) ∈ Icc a b) :
    Subtype.val '' range (stripPath g a b p hp) = range p := by
  rw [← range_comp]
  rfl

def rawExtended (g : X → ℝ) (a b : ℝ) (C : ι → Set X) (w : ι → ℝ)
    [PathConnectedSpace (Strip g a b)] : X → ℝ :=
  extend g a b (raw (fun i => Subtype.val ⁻¹' C i) w {x : Strip g a b | g x.val = a})

theorem rawExtended_properties
    (g : X → ℝ) (hg : Continuous g) (a b : ℝ) (hab : a < b)
    (C : ι → Set X) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    [PathConnectedSpace (Strip g a b)]
    (hTop : ({x : Strip g a b | g x.val = a} : Set (Strip g a b)).Nonempty)
    (hcross : ∀ u : Strip g a b, g u.val = a → ∀ v : Strip g a b, g v.val = b →
      ∀ p : Path u v, 1 ≤ cost (fun i => Subtype.val ⁻¹' C i) w (range p)) :
    (∀ x, rawExtended g a b C w x ∈ Icc 0 1) ∧
    (∀ x, g x ≤ a → rawExtended g a b C w x = 0) ∧
    (∀ x, b ≤ g x → rawExtended g a b C w x = 1) ∧
    (∀ u v : X, ∀ p : Path u v,
      |rawExtended g a b C w u-rawExtended g a b C w v| ≤ cost C w (range p)) := by
  let C' : ι → Set (Strip g a b) := fun i => Subtype.val ⁻¹' C i
  let A : Set (Strip g a b) := {x | g x.val = a}
  let B : Set (Strip g a b) := {x | g x.val = b}
  have hbare : ∀ x, raw C' w A x ∈ Icc 0 1 := raw_bounds C' w hw hTop
  have hA : ∀ x : Strip g a b, g x.val = a → raw C' w A x = 0 := by
    intro x hx
    exact raw_on_top C' w hx
  have hB : ∀ x : Strip g a b, g x.val = b → raw C' w A x = 1 := by
    intro x hx
    apply raw_on_bottom C' w hTop (B := B) _ hcross hx
    rw [Set.disjoint_left]
    intro z hzA hzB
    exact hab.ne (hzA.symm.trans hzB)
  have hbnd : ∀ x, rawExtended g a b C w x ∈ Icc 0 1 :=
    extend_bounds g a b _ hbare
  have htop : ∀ x, g x ≤ a → rawExtended g a b C w x = 0 :=
    extend_top g a b _ hA
  have hbot : ∀ x, b ≤ g x → rawExtended g a b C w x = 1 :=
    extend_bottom g a b hab _ hB
  refine ⟨hbnd,htop,hbot,?_⟩
  intro u v p
  apply extended_path_variation g hg a b hab _ hbnd htop hbot (cost C w)
    (cost_nonneg C hw) (fun _ _ h => cost_mono C hw h) _ p
  intro u v q hq
  let q' := stripPath g a b q hq
  have hh := raw_path_variation C' w hw hTop q'
  have hu : g u ∈ Icc a b := by simpa using hq 0
  have hv : g v ∈ Icc a b := by simpa using hq 1
  change |extend g a b (raw C' w A) u-extend g a b (raw C' w A) v| ≤ _
  rw [extend_on_strip g a b _ u hu,extend_on_strip g a b _ v hv]
  apply hh.trans
  change cost (fun i => Subtype.val ⁻¹' C i) w (range (stripPath g a b q hq)) ≤ _
  rw [cost_preimage_image,stripPath_image_range]

end CannonBands

namespace CannonBands

open Set unitInterval

abbrev ChartSquare := I × I

def height (z : ChartSquare) : ℝ := z.2

def stripHomeomorph (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    Strip height a b ≃ₜ I × Icc a b where
  toFun := fun z => (z.val.1,⟨z.val.2,z.property⟩)
  invFun := fun z => ⟨(z.1,⟨z.2.val,⟨ha.trans z.2.property.1,z.2.property.2.trans hb⟩⟩),
    z.2.property⟩
  left_inv := by intro z; rfl
  right_inv := by intro z; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma strip_pathConnected (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    PathConnectedSpace (Strip height a b) := by
  let : PathConnectedSpace I := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0:ℝ) 1).isPathConnected ⟨0,by norm_num⟩)
  let : PathConnectedSpace (Icc a b) := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc a b).isPathConnected ⟨a,le_rfl,hab⟩)
  exact (stripHomeomorph a b ha hb).symm.surjective.pathConnectedSpace
    (stripHomeomorph a b ha hb).symm.continuous

lemma strip_top_nonempty (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    ({x : Strip height a b | height x.val = a} : Set (Strip height a b)).Nonempty := by
  exact ⟨⟨(0,⟨a,ha,hab.trans hb⟩),le_rfl,hab⟩,rfl⟩

end CannonBands

end
end
end
end
end
end
end
end
end

end OAI
