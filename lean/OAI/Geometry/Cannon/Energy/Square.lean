import Mathlib

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
open Set unitInterval

namespace CannonPlanar

abbrev Square := I × I

def clampSquare (z : ℝ × ℝ) : Square :=
  (projIcc 0 1 zero_le_one z.1, projIcc 0 1 zero_le_one z.2)

lemma continuous_clampSquare : Continuous clampSquare :=
  (continuous_projIcc.comp continuous_fst).prodMk
    (continuous_projIcc.comp continuous_snd)

lemma clampSquare_coe (z : Square) : clampSquare (z.1, z.2) = z := by
  ext <;> simp [clampSquare, projIcc_of_mem, z.1.property, z.2.property]

theorem square_root {g : Square → ℂ} (hg : Continuous g) (h0 : ∀ z, g z ≠ 0) :
    ∃ f : Square → ℂ, Continuous f ∧ ∀ z, f z ^ 2 = g z := by
  let G : ℝ × ℝ → ℂ := g ∘ clampSquare
  have hG : Continuous G := hg.comp continuous_clampSquare
  have huc : IsSimplyConnected (univ : Set (ℝ × ℝ)) := by
    let : ContractibleSpace (univ : Set (ℝ × ℝ)) :=
      (convex_univ : Convex ℝ (univ : Set (ℝ × ℝ))).contractibleSpace univ_nonempty
    change SimplyConnectedSpace (univ : Set (ℝ × ℝ))
    infer_instance
  obtain ⟨f, hf, hp⟩ := Complex.exists_continuousOn_pow_eq huc isOpen_univ
    hG.continuousOn (by rintro ⟨z, _, hz⟩; exact h0 _ hz) (n := 2) (by decide)
  refine ⟨fun z => f (z.1, z.2), (continuousOn_univ.mp hf).comp ?_, ?_⟩
  · exact (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  · intro z
    simpa [G, Function.comp_def, clampSquare_coe] using hp (z.1, z.2)

lemma positive_everywhere {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) (h0 : ∀ x, f x ≠ 0) {x : X}
    (hx : 0 < f x) : ∀ y, 0 < f y := by
  intro y
  by_contra hn
  have hy : f y ≤ 0 := le_of_not_gt hn
  obtain ⟨z, _, hz⟩ := isPreconnected_univ.intermediate_value
    (mem_univ y) (mem_univ x) hf.continuousOn ⟨hy, hx.le⟩
  exact h0 z hz

lemma squared_parts {g f : Square → ℂ} (hp : ∀ z, f z ^ 2 = g z) (z : Square) :
    (f z).re ^ 2 - (f z).im ^ 2 = (g z).re ∧
      2 * (f z).re * (f z).im = (g z).im := by
  have hr := congrArg Complex.re (hp z)
  have hi := congrArg Complex.im (hp z)
  simp only [pow_two, Complex.mul_re, Complex.mul_im] at hr hi
  constructor <;> nlinarith

theorem square_zero {g : Square → ℂ} (hg : Continuous g)
    (hL : ∀ t, (g (0, t)).re ≤ 0) (hR : ∀ t, 0 ≤ (g (1, t)).re)
    (hB : ∀ s, (g (s, 0)).im ≤ 0) (hT : ∀ s, 0 ≤ (g (s, 1)).im) :
    ∃ z, g z = 0 := by
  by_contra hn
  have h0 : ∀ z, g z ≠ 0 := by simpa only [not_exists] using hn
  obtain ⟨f, hf, hp⟩ := square_root hg h0
  have fnz : ∀ z, (f z).re ≠ 0 ∨ (f z).im ≠ 0 := by
    intro z
    by_contra hz
    simp only [not_or, not_not] at hz
    have : f z = 0 := Complex.ext hz.1 hz.2
    exact h0 z (by rw [← hp z, this]; simp)
  have hright : ∀ t, (f (1, t)).re ≠ 0 := by
    intro t ht
    have he := (squared_parts hp (1, t)).1
    have h := hR t
    have hi : (f (1, t)).im = 0 := by nlinarith [sq_nonneg (f (1, t)).im]
    exact (fnz (1, t)).elim (fun hh => hh ht) (fun hh => hh hi)
  have hleft : ∀ t, (f (0, t)).im ≠ 0 := by
    intro t ht
    have he := (squared_parts hp (0, t)).1
    have h := hL t
    have hr : (f (0, t)).re = 0 := by nlinarith [sq_nonneg (f (0, t)).re]
    exact (fnz (0, t)).elim (fun hh => hh hr) (fun hh => hh ht)
  have hbottom : ∀ s, (f (s, 0)).re - (f (s, 0)).im ≠ 0 := by
    intro s hs
    have he := (squared_parts hp (s, 0)).2
    have h := hB s
    have hr : (f (s, 0)).re = 0 := by nlinarith [sq_nonneg (f (s, 0)).re]
    have hi : (f (s, 0)).im = 0 := by linarith
    exact (fnz (s, 0)).elim (fun hh => hh hr) (fun hh => hh hi)
  have htop : ∀ s, (f (s, 1)).re + (f (s, 1)).im ≠ 0 := by
    intro s hs
    have he := (squared_parts hp (s, 1)).2
    have h := hT s
    have hr : (f (s, 1)).re = 0 := by nlinarith [sq_nonneg (f (s, 1)).re]
    have hi : (f (s, 1)).im = 0 := by linarith
    exact (fnz (s, 1)).elim (fun hh => hh hr) (fun hh => hh hi)
  have impossible : ∀ f : Square → ℂ, Continuous f →
      (∀ z, f z ^ 2 = g z) →
      (∀ t, (f (1,t)).re ≠ 0) → (∀ t, (f (0,t)).im ≠ 0) →
      (∀ s, (f (s,0)).re - (f (s,0)).im ≠ 0) →
      (∀ s, (f (s,1)).re + (f (s,1)).im ≠ 0) →
      0 < (f (1,0)).re → False := by
    intro f hf hp hright hleft hbottom htop hr0
    have hr1 : 0 < (f (1,1)).re := positive_everywhere
      (Complex.continuous_re.comp (hf.comp (continuous_const.prodMk continuous_id))) hright hr0 1
    have hbim : (f (1,0)).im ≤ 0 := by
      have he := (squared_parts hp (1,0)).2
      have h := hB 1
      nlinarith
    have hbd : 0 < (f (0,0)).re - (f (0,0)).im := positive_everywhere
      ((Complex.continuous_re.comp (hf.comp (continuous_id.prodMk continuous_const))).sub
        (Complex.continuous_im.comp (hf.comp (continuous_id.prodMk continuous_const)))) hbottom
      (show 0 < (f (1,0)).re - (f (1,0)).im by linarith) 0
    have hli0 : (f (0,0)).im < 0 := by
      have he := (squared_parts hp (0,0)).1
      have h := hL 0
      by_contra hh
      have hh' := le_of_not_gt hh
      nlinarith [sq_nonneg ((f (0,0)).re - (f (0,0)).im)]
    have hli1 : (f (0,1)).im < 0 := by
      have hh := positive_everywhere
        (Complex.continuous_im.comp (hf.comp (continuous_const.prodMk continuous_id))).neg
        (fun t => neg_ne_zero.mpr (hleft t)) (neg_pos.mpr hli0) 1
      change 0 < -(f (0,1)).im at hh
      linarith
    have hlr1 : (f (0,1)).re ≤ 0 := by
      have he := (squared_parts hp (0,1)).2
      have h := hT 0
      nlinarith
    have hts : (f (1,1)).re + (f (1,1)).im < 0 := by
      have hh := positive_everywhere
        (((Complex.continuous_re.comp (hf.comp (continuous_id.prodMk continuous_const))).add
          (Complex.continuous_im.comp (hf.comp (continuous_id.prodMk continuous_const)))).neg)
        (fun s => neg_ne_zero.mpr (htop s))
        (show 0 < -((f (0,1)).re + (f (0,1)).im) by linarith) 1
      change 0 < -((f (1,1)).re + (f (1,1)).im) at hh
      linarith
    have hri1 : 0 ≤ (f (1,1)).im := by
      have he := (squared_parts hp (1,1)).2
      have h := hT 1
      nlinarith
    linarith
  rcases lt_or_gt_of_ne (hright 0) with hneg | hpos
  · apply impossible (fun z => -f z) hf.neg
    · intro z; simpa only [neg_sq] using hp z
    · intro t; exact neg_ne_zero.mpr (hright t)
    · intro t; exact neg_ne_zero.mpr (hleft t)
    · intro s; change -((f (s,0)).re) - -((f (s,0)).im) ≠ 0
      intro he; apply hbottom s; linarith
    · intro s; change -((f (s,1)).re) + -((f (s,1)).im) ≠ 0
      intro he; apply htop s; linarith
    · simpa using neg_pos.mpr hneg
  · exact impossible f hf hp hright hleft hbottom htop hpos

instance : LocallyPathConnectedSpace I :=
  (isQuotientMap_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).locallyPathConnectedSpace

def toComplex (z : Square) : ℂ := (z.1 : ℝ) + (z.2 : ℝ) * Complex.I

lemma continuous_toComplex : Continuous toComplex := by unfold toComplex; fun_prop

lemma toComplex_re (z : Square) : (toComplex z).re = (z.1 : ℝ) := by simp [toComplex]

lemma toComplex_im (z : Square) : (toComplex z).im = (z.2 : ℝ) := by simp [toComplex]

lemma toComplex_injective : Function.Injective toComplex := by
  intro z w h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [toComplex_re, toComplex_im] at hr hi
  exact Prod.ext (Subtype.ext hr) (Subtype.ext hi)

theorem paths_cross {p q : I → Square} (hp : Continuous p) (hq : Continuous q)
    (hp0 : (p 0).1 = 0) (hp1 : (p 1).1 = 1)
    (hq0 : (q 0).2 = 1) (hq1 : (q 1).2 = 0) :
    ∃ s t, p s = q t := by
  let g : Square → ℂ := fun z => toComplex (p z.1) - toComplex (q z.2)
  have hg : Continuous g := (continuous_toComplex.comp (hp.comp continuous_fst)).sub
    (continuous_toComplex.comp (hq.comp continuous_snd))
  have hr (s t : I) : (g (s,t)).re = (p s).1 - (q t).1 := by
    simp [g, toComplex_re]
  have hi (s t : I) : (g (s,t)).im = (p s).2 - (q t).2 := by
    simp [g, toComplex_im]
  obtain ⟨⟨s,t⟩, hz⟩ := square_zero hg
    (fun t => by rw [hr, hp0]; simpa using (q t).1.property.1)
    (fun t => by rw [hr, hp1]; simpa using (q t).1.property.2)
    (fun s => by rw [hi, hq0]; simpa using (p s).2.property.2)
    (fun s => by rw [hi, hq1]; simpa using (p s).2.property.1)
  exact ⟨s, t, toComplex_injective (sub_eq_zero.mp hz)⟩

theorem connected_joinedIn_open {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {K V : Set X} (hK : IsPreconnected K)
    (hV : IsOpen V) (hKV : K ⊆ V) {x y : X} (hx : x ∈ K) (hy : y ∈ K) :
    JoinedIn V x y := by
  let : PreconnectedSpace K := Subtype.preconnectedSpace hK
  let : LocallyPathConnectedSpace V := hV.locallyPathConnectedSpace
  let f : K → V := fun z => ⟨z.val, hKV z.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hconn : IsPreconnected (range f) := isPreconnected_range hf
  have hmem : f ⟨y,hy⟩ ∈ connectedComponent (f ⟨x,hx⟩) :=
    hconn.subset_connectedComponent ⟨⟨x,hx⟩, rfl⟩ ⟨⟨y,hy⟩, rfl⟩
  rw [← pathComponent_eq_connectedComponent] at hmem
  obtain ⟨p⟩ := hmem
  exact ⟨p.map continuous_subtype_val, fun t => (p t).property⟩

theorem continuum_crosses_path {K : Set Square} (hK : IsPreconnected K)
    {a b : Square} (ha : a ∈ K) (hb : b ∈ K) (ha0 : a.1 = 0) (hb1 : b.1 = 1)
    {q : I → Square} (hq : Continuous q) (hq0 : (q 0).2 = 1) (hq1 : (q 1).2 = 0) :
    ∃ t, q t ∈ K := by
  by_contra hn
  have hKV : K ⊆ (range q)ᶜ := by
    rintro x hx ⟨t, rfl⟩
    exact hn ⟨t, hx⟩
  obtain ⟨p, hp⟩ := connected_joinedIn_open hK
    (isCompact_range hq).isClosed.isOpen_compl hKV ha hb
  obtain ⟨s,t,hst⟩ := paths_cross p.continuous hq
    (by simpa using ha0) (by simpa using hb1) hq0 hq1
  exact hp s ⟨t, hst.symm⟩

lemma clopen_neighborhood_of_component {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] (x : X) {U : Set X} (hU : IsOpen U)
    (hC : connectedComponent x ⊆ U) :
    ∃ W : Set X, IsClopen W ∧ x ∈ W ∧ W ⊆ U := by
  let S := {s : Set X // IsClopen s ∧ x ∈ s}
  have hnull : Disjoint Uᶜ (⋂ s : S, (s : Set X)) := by
    rw [← connectedComponent_eq_iInter_isClopen]
    exact disjoint_compl_left_iff_subset.mpr hC
  obtain ⟨T, hT⟩ := hU.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun s : S => (s : Set X)) (fun s => s.property.1.isClosed) hnull
  refine ⟨⋂ s ∈ T, (s : Set X), isClopen_biInter_finset (fun s _ => s.property.1),
    mem_iInter₂.mpr (fun s _ => s.property.2), ?_⟩
  exact disjoint_compl_left_iff_subset.mp hT

lemma clopen_separator_of_components {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hcomp : ∀ x ∈ A, connectedComponent x ⊆ Bᶜ) :
    ∃ W : Set X, IsClopen W ∧ A ⊆ W ∧ Disjoint W B := by
  classical
  have hh (x : A) : ∃ W : Set X, IsClopen W ∧ x.val ∈ W ∧ W ⊆ Bᶜ :=
    clopen_neighborhood_of_component x.val hB.isOpen_compl (hcomp x.val x.property)
  choose W hW hxW hWB using hh
  have hcover : A ⊆ ⋃ x : A, W x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩, hxW ⟨x,hx⟩⟩
  obtain ⟨T, hT⟩ := hA.isCompact.elim_finite_subcover W (fun x => (hW x).isOpen) hcover
  refine ⟨⋃ x ∈ T, W x, isClopen_biUnion_finset (fun x _ => hW x), hT, ?_⟩
  rw [disjoint_left]
  rintro z hz hzB
  obtain ⟨x, _, hx⟩ := mem_iUnion₂.mp hz
  exact hWB x hx hzB

theorem level_continuum {f : Square → ℝ} (hf : Continuous f) {c : ℝ}
    (hbottom : ∀ s, f (s,0) ≤ c) (htop : ∀ s, c ≤ f (s,1)) :
    ∃ C : Set Square, IsCompact C ∧ IsConnected C ∧
      (∀ z ∈ C, f z = c) ∧ (∃ z ∈ C, z.1 = 0) ∧ (∃ z ∈ C, z.1 = 1) := by
  classical
  let Z : Set Square := {z | f z = c}
  have hZ : IsClosed Z := isClosed_eq hf continuous_const
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  let A : Set Z := {z | z.val.1 = 0}
  let B : Set Z := {z | z.val.1 = 1}
  have hA : IsClosed A := isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  have hB : IsClosed B := isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  have hex : ∃ x ∈ A, ∃ y ∈ B, y ∈ connectedComponent x := by
    by_contra hn
    have hc : ∀ x ∈ A, connectedComponent x ⊆ Bᶜ := by
      intro x hx y hy hyB
      exact hn ⟨x,hx,y,hyB,hy⟩
    obtain ⟨W,hW,hAW,hWB⟩ := clopen_separator_of_components hA hB hc
    let L : Set Square := {z | z.1 = 0}
    let R : Set Square := {z | z.1 = 1}
    have hL : IsClosed L := isClosed_eq continuous_fst continuous_const
    have hR : IsClosed R := isClosed_eq continuous_fst continuous_const
    let C0 : Set Square := Subtype.val '' W ∪ L
    let C1 : Set Square := Subtype.val '' Wᶜ ∪ R
    have hC0 : IsClosed C0 := (hZ.isClosedMap_subtype_val W hW.isClosed).union hL
    have hC1 : IsClosed C1 := (hZ.isClosedMap_subtype_val Wᶜ hW.compl.isClosed).union hR
    have hd : Disjoint C0 C1 := by
      rw [disjoint_left]
      intro z hz0 hz1
      rcases hz0 with ⟨w,hw,hwz⟩ | hzL
      · rcases hz1 with ⟨v,hv,hvz⟩ | hzR
        · have hvw : v = w := Subtype.ext (hvz.trans hwz.symm)
          exact hv (hvw.symm ▸ hw)
        · apply disjoint_left.mp hWB hw
          change w.val.1 = 1
          rw [hwz]
          exact hzR
      · rcases hz1 with ⟨v,hv,hvz⟩ | hzR
        · apply hv
          apply hAW
          change v.val.1 = 0
          rw [hvz]
          exact hzL
        · have hn01 : (0 : I) ≠ 1 := by norm_num
          exact hn01 ((show z.1 = 0 from hzL).symm.trans hzR)
    obtain ⟨v,hv0,hv1,hvr⟩ := exists_continuous_zero_one_of_isClosed hC0 hC1 hd
    let g : Square → ℂ := fun z => ((2 * v z - 1 : ℝ) : ℂ) +
      ((f z - c : ℝ) : ℂ) * Complex.I
    have hg : Continuous g := by unfold g; fun_prop
    have hr (z) : (g z).re = 2 * v z - 1 := by simp [g]
    have hi (z) : (g z).im = f z - c := by simp [g]
    obtain ⟨z,hgz⟩ := square_zero hg
      (fun t => by rw [hr, hv0 (show (0,t) ∈ C0 from Or.inr rfl)]; norm_num)
      (fun t => by rw [hr, hv1 (show (1,t) ∈ C1 from Or.inr rfl)]; norm_num)
      (fun s => by rw [hi]; linarith [hbottom s])
      (fun s => by rw [hi]; linarith [htop s])
    have hre := congrArg Complex.re hgz
    have him := congrArg Complex.im hgz
    rw [hr, Complex.zero_re] at hre
    rw [hi, Complex.zero_im] at him
    have hz : z ∈ Z := by change f z = c; linarith
    by_cases hw : (⟨z,hz⟩ : Z) ∈ W
    · have he := hv0 (show z ∈ C0 from Or.inl ⟨⟨z,hz⟩,hw,rfl⟩)
      change v z = 0 at he
      linarith
    · have he := hv1 (show z ∈ C1 from Or.inl ⟨⟨z,hz⟩,hw,rfl⟩)
      change v z = 1 at he
      linarith
  obtain ⟨x,hx,y,hy,hyx⟩ := hex
  refine ⟨Subtype.val '' connectedComponent x,
    isClosed_connectedComponent.isCompact.image continuous_subtype_val,
    isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn, ?_, ?_, ?_⟩
  · rintro z ⟨w,hw,rfl⟩
    exact w.property
  · exact ⟨x.val, ⟨x,mem_connectedComponent,rfl⟩,hx⟩
  · exact ⟨y.val, ⟨y,hyx,rfl⟩,hy⟩

end CannonPlanar

namespace CannonRegularization

variable {X : Type*} [TopologicalSpace X]

def FloodThresholds (f : X → ℝ) (A : Set X) (x : X) : Set ℝ :=
  {c | ∃ y ∈ A, ∃ p : Path x y, ∀ t, f (p t) ≤ c}

def flood (f : X → ℝ) (A : Set X) (x : X) : ℝ :=
  sInf (FloodThresholds f A x)

lemma floodThresholds_bddBelow (f : X → ℝ) (A : Set X) (x : X) :
    BddBelow (FloodThresholds f A x) := by
  refine ⟨f x, ?_⟩
  rintro c ⟨y, hy, p, hp⟩
  simpa using hp 0

lemma floodThresholds_nonempty [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, f x ≤ B) (x : X) :
    (FloodThresholds f A x).Nonempty := by
  obtain ⟨y, hy⟩ := hA
  exact ⟨B, y, hy, PathConnectedSpace.somePath x y, fun t => hf _⟩

lemma le_flood [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, f x ≤ B) (x : X) : f x ≤ flood f A x := by
  apply le_csInf (floodThresholds_nonempty hA hf x)
  rintro c ⟨y, hy, p, hp⟩
  simpa using hp 0

lemma flood_le_of_path {f : X → ℝ} {A : Set X} {x y : X}
    (hy : y ∈ A) (p : Path x y) {B : ℝ} (hp : ∀ t, f (p t) ≤ B) :
    flood f A x ≤ B :=
  csInf_le (floodThresholds_bddBelow f A x) ⟨y, hy, p, hp⟩

lemma flood_eq_on_band [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, f x ≤ B) {x : X} (hx : x ∈ A) : flood f A x = f x := by
  apply le_antisymm _ (le_flood hA hf x)
  exact flood_le_of_path hx (Path.refl x) (by simp)

lemma flood_le_upper [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, f x ≤ B) (x : X) : flood f A x ≤ B := by
  obtain ⟨y, hy⟩ := hA
  exact flood_le_of_path hy (PathConnectedSpace.somePath x y) (fun t => hf _)

lemma flood_le_max [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, f x ≤ B) {x y : X} (p : Path x y) {M : ℝ}
    (hp : ∀ t, f (p t) ≤ M) : flood f A x ≤ max M (flood f A y) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  have hcy : flood f A y < c := (le_max_right _ _).trans_lt hc
  obtain ⟨d, hd, hdc⟩ := (csInf_lt_iff (floodThresholds_bddBelow f A y)
    (floodThresholds_nonempty hA hf y)).mp hcy
  obtain ⟨z, hz, q, hq⟩ := hd
  apply flood_le_of_path hz (p.trans q)
  intro t
  have ht : (p.trans q) t ∈ range p ∪ range q := by
    rw [← Path.trans_range]
    exact mem_range_self t
  rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [← hs]
    exact (hp s).trans ((le_max_left _ _).trans hc.le)
  · rw [← hs]
    exact (hq s).trans hdc.le

theorem flood_path_variation [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, f x ≤ B) {x y : X} (p : Path x y) {m M : ℝ}
    (hp : ∀ t, f (p t) ∈ Icc m M) :
    |flood f A x - flood f A y| ≤ M - m := by
  have hxy := flood_le_max hA hf p (fun t => (hp t).2)
  have hyx := flood_le_max hA hf p.symm (fun t => (hp (unitInterval.symm t)).2)
  have hx : m ≤ flood f A x := by
    have : m ≤ f x := by simpa using (hp 0).1
    exact this.trans (le_flood hA hf x)
  have hy : m ≤ flood f A y := by
    have : m ≤ f y := by simpa using (hp 1).1
    exact this.trans (le_flood hA hf y)
  have hmM : m ≤ M := (hp 0).1.trans (hp 0).2
  rw [abs_le]
  constructor
  · rcases le_max_iff.mp hyx with h | h <;> linarith
  · rcases le_max_iff.mp hxy with h | h <;> linarith

theorem continuous_flood [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : Continuous f) (hfB : ∀ x, f x ≤ B) : Continuous (flood f A) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hfn : {y | dist (f y) (f x) < ε / 4} ∈ 𝓝 x :=
    (Metric.tendsto_nhds.mp hf.continuousAt) (ε / 4) (by positivity)
  obtain ⟨S, ⟨hSn, hSc⟩, hSf⟩ := (path_connected_basis x).mem_iff.mp hfn
  filter_upwards [hSn] with y hy
  obtain ⟨p, hp⟩ := hSc.joinedIn x (mem_of_mem_nhds hSn) y hy
  have hosc := flood_path_variation hA hfB p (m := f x - ε / 4)
    (M := f x + ε / 4) (fun t => ?_)
  · rw [Real.dist_eq, abs_sub_comm]
    exact hosc.trans_lt (by linarith)
  · have hft := hSf (hp t)
    change dist (f (p t)) (f x) < ε / 4 at hft
    rw [Real.dist_eq, abs_sub_lt_iff] at hft
    constructor <;> linarith [hft.1, hft.2]

def drain (f : X → ℝ) (A : Set X) (x : X) : ℝ :=
  -flood (fun z => -f z) A x

lemma drain_le [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, B ≤ f x) (x : X) : drain f A x ≤ f x := by
  have := le_flood (f := fun z => -f z) hA (B := -B) (by intro z; linarith [hf z]) x
  dsimp [drain]
  linarith

lemma drain_eq_on_band [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, B ≤ f x) {x : X} (hx : x ∈ A) : drain f A x = f x := by
  dsimp [drain]
  rw [flood_eq_on_band hA (B := -B) (by intro z; linarith [hf z]) hx]
  simp

lemma drain_lower [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, B ≤ f x) (x : X) : B ≤ drain f A x := by
  have := flood_le_upper (f := fun z => -f z) hA (B := -B) (by intro z; linarith [hf z]) x
  dsimp [drain]
  linarith

theorem continuous_drain [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : Continuous f) (hfB : ∀ x, B ≤ f x) : Continuous (drain f A) :=
  (continuous_flood hA (B := -B) hf.neg (by intro x; change -f x ≤ -B; linarith [hfB x])).neg

theorem drain_path_variation [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : ∀ x, B ≤ f x) {x y : X} (p : Path x y) {m M : ℝ}
    (hp : ∀ t, f (p t) ∈ Icc m M) :
    |drain f A x - drain f A y| ≤ M - m := by
  have h := flood_path_variation (f := fun z => -f z) hA (B := -B) (by intro z; linarith [hf z]) p
    (m := -M) (M := -m) (by intro t; constructor <;> linarith [(hp t).1, (hp t).2])
  simpa only [drain, neg_sub_neg, abs_sub_comm, neg_sub_neg] using h

def pathMaximum (f : X → ℝ) {x y : X} (p : Path x y) : ℝ :=
  sSup (range (f ∘ p))

lemma pathMaximum_le_iff {f : X → ℝ} (hf : Continuous f) {x y : X}
    (p : Path x y) (c : ℝ) : pathMaximum f p ≤ c ↔ ∀ t, f (p t) ≤ c := by
  have hne : (range (f ∘ p)).Nonempty := range_nonempty _
  have hb : BddAbove (range (f ∘ p)) :=
    (isCompact_range (hf.comp p.continuous)).bddAbove
  exact csSup_le_iff hb hne |>.trans (by simp only [forall_mem_range, Function.comp_apply])

theorem flood_eq_inf_pathMaximum [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hf : Continuous f) (hfB : ∀ x, f x ≤ B) (x : X) :
    flood f A x = sInf {c | ∃ y ∈ A, ∃ p : Path x y, pathMaximum f p = c} := by
  let S : Set ℝ := {c | ∃ y ∈ A, ∃ p : Path x y, pathMaximum f p = c}
  have hSne : S.Nonempty := by
    obtain ⟨y, hy⟩ := hA
    exact ⟨_, y, hy, PathConnectedSpace.somePath x y, rfl⟩
  have hSb : BddBelow S := by
    refine ⟨f x, ?_⟩
    rintro c ⟨y, hy, p, rfl⟩
    have h := (pathMaximum_le_iff hf p (pathMaximum f p)).mp le_rfl 0
    simpa using h
  apply le_antisymm
  · apply le_csInf hSne
    rintro c ⟨y, hy, p, rfl⟩
    exact flood_le_of_path hy p ((pathMaximum_le_iff hf p _).mp le_rfl)
  · apply le_csInf (floodThresholds_nonempty hA hfB x)
    rintro c ⟨y, hy, p, hp⟩
    exact (csInf_le hSb ⟨y, hy, p, rfl⟩).trans ((pathMaximum_le_iff hf p c).mpr hp)

def pathPrefix {x y : X} (p : Path x y) (t : I) : Path x (p t) where
  toFun s := p (min s t)
  continuous_toFun := p.continuous.comp (continuous_id.min continuous_const)
  source' := by rw [min_eq_left (show (0 : I) ≤ t from t.property.1)]; exact p.source
  target' := by rw [min_eq_right (show t ≤ (1 : I) from t.property.2)]

def suffix {x y : X} (p : Path x y) (t : I) : Path (p t) y where
  toFun s := p (max s t)
  continuous_toFun := p.continuous.comp (continuous_id.max continuous_const)
  source' := by rw [max_eq_right (show (0 : I) ≤ t from t.property.1)]
  target' := by rw [max_eq_left (show t ≤ (1 : I) from t.property.2)]; exact p.target

theorem flood_strict_side [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hfB : ∀ x, f x ≤ B) {x : X} {t : ℝ} (hxt : flood f A x < t) :
    ∃ y ∈ A, ∃ p : Path x y, ∀ s, flood f A (p s) < t := by
  obtain ⟨c, hc, hct⟩ := (csInf_lt_iff (floodThresholds_bddBelow f A x)
    (floodThresholds_nonempty hA hfB x)).mp hxt
  obtain ⟨y, hy, p, hp⟩ := hc
  refine ⟨y, hy, p, fun s => ?_⟩
  exact (flood_le_of_path hy (suffix p s) (fun u => hp (max u s))).trans_lt hct

theorem drain_strict_side [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hfB : ∀ x, B ≤ f x) {x : X} {t : ℝ} (hxt : t < drain f A x) :
    ∃ y ∈ A, ∃ p : Path x y, ∀ s, t < drain f A (p s) := by
  have hnegb : ∀ z, -f z ≤ -B := fun z => neg_le_neg (hfB z)
  have hneg : flood (fun z => -f z) A x < -t := by dsimp [drain] at hxt; linarith
  obtain ⟨y, hy, p, hp⟩ := flood_strict_side hA hnegb hneg
  refine ⟨y, hy, p, fun s => ?_⟩
  dsimp [drain]
  have := hp s
  linarith

lemma drain_min_le [PathConnectedSpace X]
    {f : X → ℝ} {A : Set X} (hA : A.Nonempty) {B : ℝ}
    (hfB : ∀ x, B ≤ f x) {x y : X} (p : Path x y) {m : ℝ}
    (hp : ∀ t, m ≤ f (p t)) : min m (drain f A y) ≤ drain f A x := by
  have h := flood_le_max (f := fun z => -f z) hA (B := -B)
    (fun z => neg_le_neg (hfB z)) p (M := -m) (fun t => neg_le_neg (hp t))
  rcases le_max_iff.mp h with h | h
  · exact (min_le_left _ _).trans (by dsimp [drain]; linarith)
  · exact (min_le_right _ _).trans (by dsimp [drain]; linarith)

lemma first_level_prefix {f : X → ℝ} (hf : Continuous f) {x y : X}
    (p : Path x y) {s : ℝ} (hx : s ≤ f x) (hy : f y ≤ s) :
    ∃ z : X, ∃ q : Path x z, f z = s ∧ ∀ t, s ≤ f (q t) := by
  let g : I → ℝ := f ∘ p
  have hg : Continuous g := hf.comp p.continuous
  have hgne : {t : I | g t = s}.Nonempty := by
    have hs : s ∈ Icc (g 1) (g 0) := by simpa [g] using And.intro hy hx
    obtain ⟨t, ht⟩ := intermediate_value_univ (1 : I) 0 hg hs
    exact ⟨t, ht⟩
  have hgc : IsCompact {t : I | g t = s} := (isClosed_eq hg continuous_const).isCompact
  obtain ⟨t₀, ht₀, hmin⟩ := hgc.exists_isMinOn hgne
    (continuous_subtype_val.continuousOn : ContinuousOn (fun t : I => (t : ℝ)) _)
  change g t₀ = s at ht₀
  have hbefore : ∀ u : I, u ≤ t₀ → s ≤ g u := by
    intro u hu
    by_contra hgus
    have hgus : g u < s := lt_of_not_ge hgus
    have huts : u < t₀ := lt_of_le_of_ne hu (by intro h; rw [h, ht₀] at hgus; exact lt_irrefl _ hgus)
    have hs : s ∈ Icc (g u) (g 0) := ⟨hgus.le, by simpa [g] using hx⟩
    obtain ⟨v, hv, hvs⟩ := intermediate_value_Icc'
      (show (0 : I) ≤ u from u.property.1) hg.continuousOn hs
    have htv : (t₀ : ℝ) ≤ v := hmin hvs
    have hvt : v < t₀ := hv.2.trans_lt huts
    exact (not_lt_of_ge htv) hvt
  refine ⟨p t₀, pathPrefix p t₀, ht₀, fun t => ?_⟩
  exact hbefore (min t t₀) (min_le_right _ _)

theorem regularized_low_side [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {f : X → ℝ} {A B : Set X} (hA : A.Nonempty) (hB : B.Nonempty)
    (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1)
    (hAtop : ∀ z ∈ A, f z = 0) {x : X} {t : ℝ} (ht : 0 < t)
    (hxt : drain (flood f A) B x < t) :
    ∃ y ∈ A, ∃ p : Path x y, ∀ s, drain (flood f A) B (p s) < t := by
  let F := flood f A
  let H := drain F B
  have hF0 : ∀ z, 0 ≤ F z := fun z => (hf0 z).trans (le_flood hA hf1 z)
  have hHF : ∀ z, H z ≤ F z := drain_le hB hF0
  have hlow (z : X) (hz : F z < t) :
      ∃ y ∈ A, ∃ p : Path z y, ∀ s, H (p s) < t := by
    obtain ⟨y, hy, p, hp⟩ := flood_strict_side hA hf1 hz
    exact ⟨y, hy, p, fun s => (hHF _).trans_lt (hp s)⟩
  by_cases hxF : F x < t
  · exact hlow x hxF
  obtain ⟨s, hms, hst⟩ := exists_between (max_lt (show H x < t from hxt) ht)
  have hxs : H x < s := (le_max_left _ _).trans_lt hms
  have hs0 : 0 < s := (le_max_right _ _).trans_lt hms
  have hAcopy := hA
  obtain ⟨y, hy⟩ := hAcopy
  have hFy : F y = 0 := (flood_eq_on_band hA hf1 hy).trans (hAtop y hy)
  obtain ⟨z, q, hzs, hq⟩ := first_level_prefix (continuous_flood hA hf hf1)
    (PathConnectedSpace.somePath x y) (hst.le.trans (le_of_not_gt hxF))
    (by dsimp [F] at hFy; linarith)
  have hqH : ∀ u, H (q u) < t := by
    intro u
    have hm := drain_min_le hB hF0 (pathPrefix q u) (m := s)
      (fun v => hq (min v u))
    change min s (H (q u)) ≤ H x at hm
    have hle : H (q u) ≤ H x := by
      rcases le_total s (H (q u)) with h | h
      · rw [min_eq_left h] at hm
        exact False.elim ((not_le_of_gt hxs) hm)
      · simpa only [min_eq_right h] using hm
    exact hle.trans_lt hxt
  obtain ⟨w, hw, p, hp⟩ := hlow z (by simpa only [F, hzs] using hst)
  refine ⟨w, hw, q.trans p, fun u => ?_⟩
  have hu : (q.trans p) u ∈ range q ∪ range p := by
    rw [← Path.trans_range]
    exact mem_range_self u
  rcases hu with ⟨v, hv⟩ | ⟨v, hv⟩
  · rw [← hv]; exact hqH v
  · rw [← hv]; exact hp v

end CannonRegularization

namespace CannonRegularization

variable {X : Type*} [TopologicalSpace X]

lemma path_bounds_of_pairwise {f : X → ℝ} (hf : Continuous f) {x y : X}
    (p : Path x y) {E : ℝ} (hE : ∀ s t, |f (p s)-f (p t)| ≤ E) :
    ∃ m M : ℝ, (∀ t, f (p t) ∈ Icc m M) ∧ M-m ≤ E := by
  obtain ⟨s,_,hs⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (Set.univ : Set I).Nonempty)
    (hf.comp p.continuous).continuousOn
  obtain ⟨t,_,ht⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (Set.univ : Set I).Nonempty)
    (hf.comp p.continuous).continuousOn
  refine ⟨f (p s),f (p t),fun q => ⟨hs (mem_univ q),ht (mem_univ q)⟩,?_⟩
  exact (le_abs_self _).trans (hE t s)

theorem flood_drain_path_osc [PathConnectedSpace X] [LocallyPathConnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) {A B : Set X}
    (hA : A.Nonempty) (hB : B.Nonempty) (hfI : ∀ x, f x ∈ Icc 0 1)
    {x y : X} (p : Path x y) {E : ℝ}
    (hE : ∀ s t, |f (p s)-f (p t)| ≤ E) :
    |drain (flood f A) B x-drain (flood f A) B y| ≤ E := by
  obtain ⟨m,M,hp,hmM⟩ := path_bounds_of_pairwise hf p hE
  have hupper : ∀ x, f x ≤ 1 := fun x => (hfI x).2
  have hg := continuous_flood hA hf hupper
  have hpair : ∀ s t, |flood f A (p s)-flood f A (p t)| ≤ E := by
    intro s t
    apply (flood_path_variation hA hupper (p.subpath s t) (m := m) (M := M) ?_).trans hmM
    intro q
    exact hp _
  obtain ⟨m',M',hp',hwidth⟩ := path_bounds_of_pairwise hg p hpair
  apply (drain_path_variation hB (B := 0) ?_ p hp').trans hwidth
  intro z
  exact (hfI z).1.trans (le_flood hA hupper z)

end CannonRegularization

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
