import Mathlib

namespace OAI

namespace StrictFilling

def clip (lo hi t : ℝ) : ℝ := max lo (min t hi)

lemma clip_eq_self {lo hi t : ℝ} (hl : lo ≤ t) (hu : t ≤ hi) :
    clip lo hi t = t := by
  simp [clip, min_eq_left hu, max_eq_right hl]

lemma clip_same (c t : ℝ) : clip c c t = c := by
  exact max_eq_left (min_le_right _ _)

lemma clip_between_zero {lo hi t : ℝ}
    (hl : lo ≤ max 0 t) (hu : min 0 t ≤ hi) :
    clip lo hi t ∈ Set.uIcc 0 t := by
  change min 0 t ≤ max lo (min t hi) ∧ max lo (min t hi) ≤ max 0 t
  constructor
  · exact (le_min (min_le_right _ _) hu).trans (le_max_right _ _)
  · exact max_le hl ((min_le_left _ _).trans (le_max_right _ _))

def medianZero (a b : ℝ) : ℝ := max (min a b) (min (max a b) 0)

lemma medianZero_properties (a b : ℝ) :
    medianZero a b ∈ Set.uIcc 0 a ∧
    medianZero a b ∈ Set.uIcc 0 b ∧
    |medianZero a b - a| ≤ |a - b| ∧
    |medianZero a b - b| ≤ |a - b| := by
  unfold medianZero
  change (min 0 a ≤ _ ∧ _ ≤ max 0 a) ∧
    (min 0 b ≤ _ ∧ _ ≤ max 0 b) ∧ _
  simp only [min_def, max_def]
  split_ifs <;> simp_all only [abs_le] <;>
    and_intros <;> first | trivial | linarith [le_abs_self (a-b), neg_le_abs (a-b)]

section Metric

variable {X : Type*} [PseudoMetricSpace X]

lemma lipschitz_add_const {f : X → ℝ} (hf : LipschitzWith 1 f) (c : ℝ) :
    LipschitzWith 1 (fun x => c + f x) := by
  apply LipschitzWith.mk_one
  intro x y
  simpa only [Real.dist_eq, add_sub_add_left_eq_sub, NNReal.coe_one, one_mul] using
    hf.dist_le_mul x y

lemma lipschitz_const_sub {f : X → ℝ} (hf : LipschitzWith 1 f) (c : ℝ) :
    LipschitzWith 1 (fun x => c - f x) := by
  simpa only [sub_eq_add_neg, Pi.neg_apply] using lipschitz_add_const hf.neg c

lemma lipschitz_clip {h r : X → ℝ} (hh : LipschitzWith 1 h)
    (hr : LipschitzWith 1 r) (c : ℝ) :
    LipschitzWith 1 (fun x => clip (c - r x) (c + r x) (h x)) := by
  simpa only [clip, max_self] using
    (lipschitz_const_sub hr c).max (hh.min (lipschitz_add_const hr c))

lemma endpoint_lower {h : X → ℝ} (hh : LipschitzWith 1 h)
    {u : X} {c : ℝ} (hc : c ∈ Set.uIcc 0 (h u)) (x : X) :
    c - dist x u ≤ max 0 (h x) := by
  have hc' : c ≤ max 0 (h u) := hc.2
  have hd := hh.dist_le_mul u x
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, abs_le] at hd
  have hd0 : 0 ≤ dist x u := dist_nonneg
  rw [dist_comm u x] at hd
  rcases le_total 0 (h u) with hu | hu
  · rw [max_eq_right hu] at hc'
    exact (show c - dist x u ≤ h x by linarith).trans (le_max_right _ _)
  · rw [max_eq_left hu] at hc'
    exact (show c - dist x u ≤ 0 by linarith).trans (le_max_left _ _)

lemma endpoint_upper {h : X → ℝ} (hh : LipschitzWith 1 h)
    {u : X} {c : ℝ} (hc : c ∈ Set.uIcc 0 (h u)) (x : X) :
    min 0 (h x) ≤ c + dist x u := by
  have hc' : min 0 (h u) ≤ c := hc.1
  have hd := hh.dist_le_mul u x
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, abs_le] at hd
  have hd0 : 0 ≤ dist x u := dist_nonneg
  rw [dist_comm u x] at hd
  rcases le_total 0 (h u) with hu | hu
  · rw [min_eq_left hu] at hc'
    exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_right hu] at hc'
    exact (min_le_right _ _).trans (show h x ≤ c + dist x u by linarith)

lemma cone_preserves_interval {h : X → ℝ} (hh : LipschitzWith 1 h)
    {u : X} {c : ℝ} (hc : c ∈ Set.uIcc 0 (h u)) (x : X) :
    clip (c - dist x u) (c + dist x u) (h x) ∈ Set.uIcc 0 (h x) :=
  clip_between_zero (endpoint_lower hh hc x) (endpoint_upper hh hc x)

def twoRadius (u v x : X) : ℝ := min (dist x u) (dist x v)

def twoClip (h : X → ℝ) (u v : X) (c : ℝ) (x : X) : ℝ :=
  clip (c - twoRadius u v x) (c + twoRadius u v x) (h x)

lemma twoRadius_lipschitz (u v : X) : LipschitzWith 1 (twoRadius u v) := by
  change LipschitzWith 1 (fun x => min (dist x u) (dist x v))
  simpa only [max_self] using
    (LipschitzWith.dist_left u).min (LipschitzWith.dist_left v)

lemma twoClip_lipschitz {h : X → ℝ} (hh : LipschitzWith 1 h)
    (u v : X) (c : ℝ) : LipschitzWith 1 (twoClip h u v c) :=
  lipschitz_clip hh (twoRadius_lipschitz u v) c

lemma twoClip_between_zero {h : X → ℝ} (hh : LipschitzWith 1 h)
    {u v : X} {c : ℝ}
    (hcu : c ∈ Set.uIcc 0 (h u)) (hcv : c ∈ Set.uIcc 0 (h v)) (x : X) :
    twoClip h u v c x ∈ Set.uIcc 0 (h x) := by
  unfold twoClip twoRadius
  rcases le_total (dist x u) (dist x v) with hd | hd
  · rw [min_eq_left hd]
    exact cone_preserves_interval hh hcu x
  · rw [min_eq_right hd]
    exact cone_preserves_interval hh hcv x

lemma twoClip_endpoints (h : X → ℝ) (u v : X) (c : ℝ) :
    twoClip h u v c u = c ∧ twoClip h u v c v = c := by
  simp only [twoClip, twoRadius, dist_self, min_eq_left dist_nonneg,
    min_eq_right dist_nonneg, sub_zero, add_zero, clip_same, and_self]

lemma cone_eq_self_of_dist {h : X → ℝ} {u : X} {c : ℝ} (x : X)
    (hc : |c - h x| ≤ dist x u) :
    clip (c - dist x u) (c + dist x u) (h x) = h x := by
  apply clip_eq_self <;> have := (abs_le.mp hc) <;> linarith

lemma twoClip_eq_self {h : X → ℝ} {u v : X} {c : ℝ} (x : X)
    (hcu : |c - h x| ≤ dist x u) (hcv : |c - h x| ≤ dist x v) :
    twoClip h u v c x = h x := by
  apply clip_eq_self <;>
    have hl := (abs_le.mp hcu) <;> have hr := (abs_le.mp hcv) <;>
    unfold twoRadius <;> rw [min_def] <;> split_ifs <;> linarith

lemma pin_compatible {h : X → ℝ} (hh : LipschitzWith 1 h)
    {u s : X} {c : ℝ} (hc : c ∈ Set.uIcc 0 (h u))
    (hs : |h s| ≤ 1 / 2) (hsep : 1 ≤ dist s u) :
    |c - h s| ≤ dist s u := by
  have hd := hh.dist_le_mul u s
  rw [dist_comm u s] at hd
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, abs_le] at hd
  have hs' := abs_le.mp hs
  rcases Set.mem_uIcc.mp hc with h | h <;>
    apply abs_le.mpr <;> constructor <;> linarith

lemma room_compatible {h : X → ℝ} {u s : X} {c : ℝ}
    (hc : |c - h u| ≤ 2)
    (hroom : |h u - h s| ≤ dist u s - 2) :
    |c - h s| ≤ dist s u := by
  rw [dist_comm s u]
  calc
    |c - h s| ≤ |c - h u| + |h u - h s| := abs_sub_le c (h u) (h s)
    _ ≤ 2 + (dist u s - 2) := add_le_add hc hroom
    _ = dist u s := by ring

theorem strict_filling_movable_first
    (h : X → ℝ) (shell pins : Set X) (I : X → Set ℝ) (u v : X)
    (hsep : ∀ x y : X, x ≠ y → 1 ≤ dist x y)
    (hedge : dist u v = 1) (hh : LipschitzWith 1 h)
    (hpin : ∀ s ∈ pins, |h s| ≤ 1 / 2)
    (hI : ∀ x ∉ shell ∪ pins, (I x).OrdConnected ∧ 0 ∈ I x ∧ h x ∈ I x)
    (hu : u ∉ shell ∪ pins)
    (hroom : ∀ x, (x = u ∨ x = v) → x ∉ shell ∪ pins →
      ∀ s ∈ shell, |h x - h s| ≤ dist x s - 2) :
    ∃ g : X → ℝ, LipschitzWith 1 g ∧
      (∀ s ∈ shell ∪ pins, g s = h s) ∧
      (∀ x ∉ shell ∪ pins, g x ∈ I x) ∧ |g u - g v| ≤ 1 / 2 := by
  have hdist : |h u - h v| ≤ 1 := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, hedge] using hh.dist_le_mul u v
  have hsep_u : ∀ s ∈ shell ∪ pins, 1 ≤ dist s u := by
    intro s hs
    exact hsep s u (by intro hsu; subst s; exact hu hs)
  by_cases hv : v ∈ shell ∪ pins
  · have hvshell : v ∉ shell := by
      intro hvs
      have hr := hroom u (Or.inl rfl) hu v hvs
      rw [hedge] at hr
      linarith [abs_nonneg (h u - h v)]
    have hvpin : v ∈ pins := hv.resolve_left hvshell
    have hvbound := hpin v hvpin
    have hubound : |0 - h u| ≤ 2 := by
      have ht := abs_sub_le (h u) (h v) 0
      rw [sub_zero, sub_zero] at ht
      simpa only [zero_sub, abs_neg] using
        (show |h u| ≤ 2 by linarith)
    let g := twoClip h u u 0
    refine ⟨g, twoClip_lipschitz hh u u 0, ?_, ?_, ?_⟩
    · intro s hs
      change twoClip h u u 0 s = h s
      have hc : |0 - h s| ≤ dist s u := by
        rcases hs with hss | hsp
        · exact room_compatible hubound (hroom u (Or.inl rfl) hu s hss)
        · simpa only [zero_sub, abs_neg] using
            (hpin s hsp).trans (by linarith [hsep_u s (Or.inr hsp)])
      exact twoClip_eq_self s hc hc
    · intro x hx
      exact (hI x hx).1.uIcc_subset (hI x hx).2.1 (hI x hx).2.2
        (twoClip_between_zero hh (Set.left_mem_uIcc) (Set.left_mem_uIcc) x)
    · have hgu : g u = 0 := (twoClip_endpoints h u u 0).1
      have hgv : g v = h v := by
        apply twoClip_eq_self
        all_goals simpa only [zero_sub, abs_neg] using
          hvbound.trans (by linarith [hsep_u v hv])
      rw [hgu, hgv, zero_sub, abs_neg]
      exact hvbound
  · let c := medianZero (h u) (h v)
    have hc := medianZero_properties (h u) (h v)
    have hcu : c ∈ Set.uIcc 0 (h u) := hc.1
    have hcv : c ∈ Set.uIcc 0 (h v) := hc.2.1
    have hcu2 : |c - h u| ≤ 2 := (hc.2.2.1.trans hdist).trans (by norm_num)
    have hcv2 : |c - h v| ≤ 2 := (hc.2.2.2.trans hdist).trans (by norm_num)
    let g := twoClip h u v c
    refine ⟨g, twoClip_lipschitz hh u v c, ?_, ?_, ?_⟩
    · intro s hs
      have hc1 : |c - h s| ≤ dist s u := by
        rcases hs with hss | hsp
        · exact room_compatible hcu2 (hroom u (Or.inl rfl) hu s hss)
        · exact pin_compatible hh hcu (hpin s hsp) (hsep_u s (Or.inr hsp))
      have hc2 : |c - h s| ≤ dist s v := by
        rcases hs with hss | hsp
        · exact room_compatible hcv2 (hroom v (Or.inr rfl) hv s hss)
        · exact pin_compatible hh hcv (hpin s hsp)
            (hsep s v (by intro hsv; subst s; exact hv (Or.inr hsp)))
      exact twoClip_eq_self s hc1 hc2
    · intro x hx
      exact (hI x hx).1.uIcc_subset (hI x hx).2.1 (hI x hx).2.2
        (twoClip_between_zero hh hcu hcv x)
    · have he := twoClip_endpoints h u v c
      change |twoClip h u v c u - twoClip h u v c v| ≤ _
      rw [he.1, he.2, sub_self, abs_zero]
      norm_num

theorem strict_filling
    (h : X → ℝ) (shell pins : Set X) (I : X → Set ℝ) (u v : X)
    (hsep : ∀ x y : X, x ≠ y → 1 ≤ dist x y)
    (hedge : dist u v = 1) (hh : LipschitzWith 1 h)
    (hpin : ∀ s ∈ pins, |h s| ≤ 1 / 2)
    (hI : ∀ x ∉ shell ∪ pins, (I x).OrdConnected ∧ 0 ∈ I x ∧ h x ∈ I x)
    (hnotfixed : ¬ (u ∈ shell ∪ pins ∧ v ∈ shell ∪ pins))
    (hroom : ∀ x, (x = u ∨ x = v) → x ∉ shell ∪ pins →
      ∀ s ∈ shell, |h x - h s| ≤ dist x s - 2) :
    ∃ g : X → ℝ, LipschitzWith 1 g ∧
      (∀ s ∈ shell ∪ pins, g s = h s) ∧
      (∀ x ∉ shell ∪ pins, g x ∈ I x) ∧ |g u - g v| ≤ 1 / 2 := by
  by_cases hu : u ∈ shell ∪ pins
  · have hv : v ∉ shell ∪ pins := fun hv => hnotfixed ⟨hu, hv⟩
    obtain ⟨g, hg, hgf, hgi, hge⟩ := strict_filling_movable_first h shell pins I v u
      hsep (by rw [dist_comm]; exact hedge) hh hpin hI hv
      (fun x hx => hroom x hx.symm)
    refine ⟨g, hg, hgf, hgi, ?_⟩
    simpa only [abs_sub_comm] using hge
  · exact strict_filling_movable_first h shell pins I u v hsep hedge hh hpin hI hu hroom

end Metric

abbrev Component {V : Type*} (G : SimpleGraph V) (u : V) := {x : V // G.Reachable u x}

noncomputable instance componentMetric {V : Type*} (G : SimpleGraph V) (u : V) :
    MetricSpace (Component G u) where
  dist x y := (G.dist x.val y.val : ℝ)
  dist_self x := by simp
  dist_comm x y := by rw [G.dist_comm]
  dist_triangle x y z := by
    exact_mod_cast (x.property.symm.trans y.property).dist_triangle_left z.val
  eq_of_dist_eq_zero := by
    intro x y h
    apply Subtype.ext
    exact (x.property.symm.trans y.property).dist_eq_zero_iff.mp (by exact_mod_cast h)

lemma edge_bound_walk {V : Type*} {G : SimpleGraph V} {h : V → ℝ}
    (hh : ∀ x y, G.Adj x y → |h x - h y| ≤ 1)
    {x y : V} (p : G.Walk x y) : |h x - h y| ≤ (p.length : ℝ) := by
  induction p with
  | nil => simp
  | @cons x y z hxy p ih =>
    calc
      |h x - h z| ≤ |h x - h y| + |h y - h z| := abs_sub_le _ _ _
      _ ≤ 1 + (p.length : ℝ) := add_le_add (hh _ _ hxy) ih
      _ = ((SimpleGraph.Walk.cons hxy p).length : ℝ) := by simp; ring

lemma edge_bound_dist {V : Type*} {G : SimpleGraph V} {h : V → ℝ}
    (hh : ∀ x y, G.Adj x y → |h x - h y| ≤ 1)
    {x y : V} (hr : G.Reachable x y) : |h x - h y| ≤ (G.dist x y : ℝ) := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  simpa only [hp] using edge_bound_walk hh p

lemma component_lipschitz {V : Type*} {G : SimpleGraph V} {h : V → ℝ}
    (hh : ∀ x y, G.Adj x y → |h x - h y| ≤ 1) (u : V) :
    LipschitzWith 1 (fun x : Component G u => h x.val) := by
  apply LipschitzWith.mk_one
  intro x y
  exact edge_bound_dist hh (x.property.symm.trans y.property)

lemma component_separated {V : Type*} {G : SimpleGraph V} {u : V}
    (x y : Component G u) (hxy : x ≠ y) : 1 ≤ dist x y := by
  change (1 : ℝ) ≤ (G.dist x.val y.val : ℝ)
  exact_mod_cast (x.property.symm.trans y.property).pos_dist_of_ne
    (by intro h; exact hxy (Subtype.ext h))

theorem graph_strict_filling {V : Type*} [Finite V]
    (G : SimpleGraph V) (h : V → ℝ) (shell pins : Set V) (I : V → Set ℝ)
    (u v : V) (hedge : G.Adj u v)
    (hh : ∀ x y, G.Adj x y → |h x - h y| ≤ 1)
    (hpin : ∀ s ∈ pins, |h s| ≤ 1 / 2)
    (hI : ∀ x ∉ shell ∪ pins, (I x).OrdConnected ∧ 0 ∈ I x ∧ h x ∈ I x)
    (hnotfixed : ¬ (u ∈ shell ∪ pins ∧ v ∈ shell ∪ pins))
    (hroom : ∀ x, (x = u ∨ x = v) → x ∉ shell ∪ pins →
      ∀ s ∈ shell, G.Reachable x s → |h x - h s| ≤ (G.dist x s : ℝ) - 2) :
    ∃ g : V → ℝ,
      (∀ x y, G.Adj x y → |g x - g y| ≤ 1) ∧
      (∀ s ∈ shell ∪ pins, g s = h s) ∧
      (∀ x ∉ shell ∪ pins, g x ∈ I x) ∧ |g u - g v| ≤ 1 / 2 := by
  classical
  let C := Component G u
  let uC : C := ⟨u, .refl u⟩
  let vC : C := ⟨v, hedge.reachable⟩
  let shellC : Set C := {x | x.val ∈ shell}
  let pinsC : Set C := {x | x.val ∈ pins}
  have hedgeC : dist uC vC = 1 := by
    change (G.dist u v : ℝ) = 1
    exact_mod_cast SimpleGraph.dist_eq_one_iff_adj.mpr hedge
  obtain ⟨gc, hgclip, hgcf, hgci, hgce⟩ :=
    strict_filling (fun x : C => h x.val) shellC pinsC (fun x => I x.val) uC vC
      (fun x y hxy => component_separated x y hxy) hedgeC (component_lipschitz hh u)
      (fun s hs => hpin s.val hs) (fun x hx => hI x.val hx) hnotfixed
      (by
        intro x hx hxnot s hs
        change |h x.val - h s.val| ≤ (G.dist x.val s.val : ℝ) - 2
        apply hroom x.val _ hxnot s.val hs (x.property.symm.trans s.property)
        rcases hx with hx | hx
        · exact Or.inl (congrArg Subtype.val hx)
        · exact Or.inr (congrArg Subtype.val hx))
  let g : V → ℝ := fun x => if hx : G.Reachable u x then gc ⟨x, hx⟩ else h x
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : G.Reachable u x
    · have hy := hx.trans hxy.reachable
      have hc := hgclip.dist_le_mul (⟨x, hx⟩ : C) (⟨y, hy⟩ : C)
      change |gc ⟨x, hx⟩ - gc ⟨y, hy⟩| ≤ 1 * (G.dist x y : ℝ) at hc
      simpa only [g, dite_eq_left hx, dite_eq_left hy, one_mul,
        SimpleGraph.dist_eq_one_iff_adj.mpr hxy, Nat.cast_one] using hc
    · have hy : ¬ G.Reachable u y := fun hy => hx (hy.trans hxy.symm.reachable)
      simpa only [g, dite_eq_right hx, dite_eq_right hy] using hh x y hxy
  · intro s hs
    by_cases hx : G.Reachable u s
    · exact (dite_eq_left hx).trans (hgcf ⟨s, hx⟩ hs)
    · exact dite_eq_right hx
  · intro x hx
    by_cases hr : G.Reachable u x
    · simpa only [g, dite_eq_left hr] using hgci ⟨x, hr⟩ hx
    · simpa only [g, dite_eq_right hr] using (hI x hx).2.2
  · simpa only [g, dite_eq_left (SimpleGraph.Reachable.refl u),
      dite_eq_left hedge.reachable] using hgce

end StrictFilling

end OAI
