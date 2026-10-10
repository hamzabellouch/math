import OAI.RepresentationTheory.KazhdanLusztig.CharacterReciprocity

namespace OAI

/-!
Finite character cancellation, reflection-ratio orders and adapted Dyer decreasing paths.
-/

section

namespace KLInvariance
universe u v
variable {V : Type u} [Fintype V] {C : Type v} [CommRing C]

 theorem finite_character_cancellation (t : V) (m : V → C) (r : V → C)
    (p : V → V → C) (q : V → C) (hm : m t=1)
    (hword : (∑ y, m y*q y)=∑ z, r z*(∑ y, m y*p y z))
    (hlower : ∀ y, y≠t → q y=∑ z, r z*p y z) : q t=∑ z, r z*p t z := by
  classical
  have hexpand : (∑ z, r z*(∑ y, m y*p y z))=∑ y, m y*(∑ z, r z*p y z) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hexpand] at hword
  have hzero : (∑ y, m y*(q y-∑ z, r z*p y z))=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,hword,sub_self]
  have hsingle : (∑ y, m y*(q y-∑ z, r z*p y z))=q t-∑ z, r z*p t z := by
    rw [Finset.sum_eq_single t]
    · rw [hm,one_mul]
    · intro y _ hy
      rw [hlower y hy,sub_self,mul_zero]
    · simp
  rw [hsingle] at hzero
  exact sub_eq_zero.mp hzero

end KLInvariance

end


section

/-! R-reciprocity for the ACTUAL minimal-boundary BMP character, obtained
by simultaneous word stalk/costalk decomposition and unipotent cancellation.
This is not a character identification: strict halfdegree remains separate. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance bmpRecInterval (b : W) : Fintype (Interval cs 1 b) := by
  let := interval_finite cs 1 b
  exact Fintype.ofFinite _

 theorem stalkCharacter_reciprocity (b : W) (x : Interval cs 1 b) :
    reflect (rankDifference cs x.val b) (stalkCharacter cs 1 b basis (one_bruhat cs b) x)=
      ∑ z : Interval cs 1 b, OrdinaryR.polynomial cs x.val z.val*
        stalkCharacter cs 1 b basis (one_bruhat cs b) z := by
  generalize hn : cs.length b=n
  induction n using Nat.strong_induction_on generalizing b with
  | h n ih =>
    obtain ⟨l,hl,rfl⟩ := cs.exists_isReduced b
    let b := cs.wordProd l
    let t : Interval cs 1 b := ⟨b,one_bruhat cs b,bruhat_refl cs b⟩
    obtain ⟨m,_hm,hs,hk⟩ := bottCharacter_decomposition_both cs basis l hl
    have hmt : m t=1 := by
      have hh := hs t
      rw [bottStalkCharacter_top cs basis l hl] at hh
      rw [Finset.sum_eq_single t] at hh
      · simpa only [lowerCharacter_diagonal,mul_one] using hh.symm
      · intro y _ hy
        have hv : y.val≠b := fun h => hy (Subtype.ext h)
        rw [lowerCharacter_at_top,ite_eq_right hv,mul_zero]
      · simp
    have ht (z : Interval cs 1 b) : lowerCharacter cs b basis t z=
        stalkCharacter cs 1 b basis (one_bruhat cs b) z := dite_eq_left z.property.2
    have hw : (∑ y, m y*reflect (rankDifference cs x.val y.val) (lowerCharacter cs b basis y x))=
        ∑ z : Interval cs 1 b, OrdinaryR.polynomial cs x.val z.val*
          (∑ y, m y*lowerCharacter cs b basis y z) := by
      rw [←hk x,bottKernelCharacter_rConvolution cs basis l hl x]
      simp only [hs]
      rfl
    have hh := finite_character_cancellation t m
      (fun z : Interval cs 1 b => OrdinaryR.polynomial cs x.val z.val)
      (fun y z => lowerCharacter cs b basis y z)
      (fun y => reflect (rankDifference cs x.val y.val) (lowerCharacter cs b basis y x))
      hmt hw (fun y hy => ?_)
    · simpa only [ht] using hh
    · apply lowerCharacter_reciprocity_lift
      intro z
      apply ih (cs.length y.val) _ y.val z rfl
      rw [←hn]
      exact length_lt_of_bruhat_ne cs y.property.2 (fun he => hy (Subtype.ext he))

end
end KLInvariance.BruhatGraph

end


section

/-! Removing the finite-rank restriction from the actual graph bridge,
using the already established standard-parabolic embedding. -/
namespace KLInvariance.StandardParabolic
open CoxeterSystem
universe u v
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
variable (cs : CoxeterSystem M W) (J : Set I)
noncomputable section

theorem leftInvSeq_inclusion (ω : List J) :
    ((system (M := M) J).leftInvSeq ω).map (inclusion cs J) =
      cs.leftInvSeq (ω.map Subtype.val) := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    simp only [CoxeterSystem.leftInvSeq, List.map_cons, List.map_map,
      inclusion_simple]
    rw [← ih, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, MulAut.conj_apply, map_mul, map_inv,
      inclusion_simple]

theorem reflection_inclusion {t : (matrix (M := M) J).Group}
    (ht : (system (M := M) J).IsReflection t) :
    cs.IsReflection (inclusion cs J t) := by
  obtain ⟨w, i, rfl⟩ := ht
  exact ⟨inclusion cs J w, i.val, by simp only [map_mul, map_inv, inclusion_simple]⟩

theorem bruhatStep_inclusion_iff [Fintype J] (x y : (matrix (M := M) J).Group) :
    BruhatStep cs (inclusion cs J x) (inclusion cs J y) ↔
      BruhatStep (system (M := M) J) x y := by
  constructor
  · rintro ⟨hlen, t, ht, heq⟩
    obtain ⟨ω, hω, hprod⟩ := (system (M := M) J).exists_isReduced y
    have hi : cs.IsLeftInversion (inclusion cs J y) t := by
      refine ⟨ht, ?_⟩
      rw [heq, ← mul_assoc, ht.mul_self, one_mul]
      simpa only [heq] using hlen
    have hr := (reduced_map_iff cs J ω).2 hω
    have hw : cs.wordProd (ω.map Subtype.val) = inclusion cs J y := by
      rw [← inclusion_word, hprod]
    have hm := CoxeterSupport.mem_leftInvSeq_of_inversion cs hr (hw ▸ hi)
    rw [← leftInvSeq_inclusion] at hm
    obtain ⟨r, hr, hrt⟩ := List.mem_map.mp hm
    refine ⟨by simpa only [length_inclusion] using hlen,
      r, (system (M := M) J).isReflection_of_mem_leftInvSeq ω hr, ?_⟩
    apply inclusion_injective cs J
    simpa only [map_mul, hrt] using heq
  · rintro ⟨hlen, t, ht, heq⟩
    refine ⟨by simpa only [length_inclusion] using hlen,
      inclusion cs J t, reflection_inclusion cs J ht, ?_⟩
    rw [heq, map_mul]

end
end KLInvariance.StandardParabolic

namespace KLInvariance
universe u v u' v'
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}

/-- The graph reconstruction input in its source scope: the Coxeter system
can have infinitely many generators. The interval determines every reflection
edge without being supplied the reflection labels. -/
theorem diamondEdges_of_bruhatStep_general (cs : CoxeterSystem M W)
    {u b : W} {x y : Interval cs u b} (hxy : BruhatStep cs x.val y.val) :
    DiamondEdges x y := by
  classical
  obtain ⟨J, hJ, hwords⟩ := lower_ideal_finite_generator_support cs b
  let : Fintype J := hJ.fintype
  obtain ⟨ω, hω, hprod⟩ := hwords b (bruhat_refl cs b)
  obtain ⟨ν, rfl⟩ := StandardParabolic.lift_word J hω
  let bb := (StandardParabolic.system (M := M) J).wordProd ν
  have hb : StandardParabolic.inclusion cs J bb = b :=
    (StandardParabolic.inclusion_word cs J ν).trans hprod
  have hub : BruhatLE cs u b := (bruhat_trans cs x.property.1 x.property.2)
  obtain ⟨ub, hu⟩ := StandardParabolic.lower_range cs J bb (hb ▸ hub)
  subst u
  clear hprod
  subst b
  let e := StandardParabolic.intervalIso cs J ub bb
  let xx := e.symm x
  let yy := e.symm y
  have hx : StandardParabolic.inclusion cs J xx.val = x.val :=
    congrArg Subtype.val (e.apply_symm_apply x)
  have hy : StandardParabolic.inclusion cs J yy.val = y.val :=
    congrArg Subtype.val (e.apply_symm_apply y)
  have hh : BruhatStep (StandardParabolic.system (M := M) J) xx.val yy.val := by
    apply (StandardParabolic.bruhatStep_inclusion_iff cs J _ _).mp
    rwa [hx, hy]
  have hg := (diamondEdges_of_bruhatStep (StandardParabolic.system (M := M) J) hh).map e
  simpa only [xx, yy, e.apply_symm_apply] using hg

theorem diamondEdges_bruhatStep_general (cs : CoxeterSystem M W)
    {u b : W} {x y : Interval cs u b} (hxy : DiamondEdges x y) :
    BruhatStep cs x.val y.val := by
  classical
  obtain ⟨J, hJ, hwords⟩ := lower_ideal_finite_generator_support cs b
  let : Fintype J := hJ.fintype
  obtain ⟨ω, hω, hprod⟩ := hwords b (bruhat_refl cs b)
  obtain ⟨ν, rfl⟩ := StandardParabolic.lift_word J hω
  let bb := (StandardParabolic.system (M := M) J).wordProd ν
  have hb : StandardParabolic.inclusion cs J bb = b :=
    (StandardParabolic.inclusion_word cs J ν).trans hprod
  have hub : BruhatLE cs u b := (bruhat_trans cs x.property.1 x.property.2)
  obtain ⟨ub, hu⟩ := StandardParabolic.lower_range cs J bb (hb ▸ hub)
  subst u
  clear hprod
  subst b
  let e := StandardParabolic.intervalIso cs J ub bb
  let xx := e.symm x
  let yy := e.symm y
  have hx : StandardParabolic.inclusion cs J xx.val = x.val :=
    congrArg Subtype.val (e.apply_symm_apply x)
  have hy : StandardParabolic.inclusion cs J yy.val = y.val :=
    congrArg Subtype.val (e.apply_symm_apply y)
  have hh : DiamondEdges xx yy := hxy.map e.symm
  have hg := diamondEdges_bruhatStep (StandardParabolic.system (M := M) J) hh
  have hs := (StandardParabolic.bruhatStep_inclusion_iff cs J xx.val yy.val).mpr hg
  rwa [hx, hy] at hs

/-- Exact unlabelled directed graph invariance, also for arbitrary infinite
Coxeter systems. This is not yet KL polynomial invariance. -/
theorem intervalIso_bruhatStep_iff_general
    {I' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix I'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'} (e : Interval cs u b ≃o Interval cs' u' b')
    (x y : Interval cs u b) :
    BruhatStep cs' (e x).val (e y).val ↔ BruhatStep cs x.val y.val := by
  constructor
  · intro h
    exact diamondEdges_bruhatStep_general cs ((DiamondEdges.map_iff e).mp
      (diamondEdges_of_bruhatStep_general cs' h))
  · intro h
    exact diamondEdges_bruhatStep_general cs' ((diamondEdges_of_bruhatStep_general cs h).map e)

end KLInvariance

end


section


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

theorem graphRoot_mem {a₀ : W} {g h : planeSubgroup M cs P}
    (he : BruhatStep cs ((g : W) * a₀) ((h : W) * a₀)) :
    (graphRoot he).val ∈ P := by
  exact reflection_between_coset_mem M cs (a := a₀) g.property h.property (by group)
    (graphRoot_represents he)

include B

/-- The two labels on a composable coset path span the whole actual plane. -/
theorem graphRoot_path_plane {a₀ : W} {g h k : planeSubgroup M cs P}
    (he : BruhatStep cs ((g : W) * a₀) ((h : W) * a₀))
    (hf : BruhatStep cs ((h : W) * a₀) ((k : W) * a₀)) :
    rootPlane (graphRoot he) (graphRoot hf) = P := by
  exact (rootPlane_eq_of_mem B.left B.right (graphRoot he) (graphRoot hf)
    B.distinct (B.plane_eq.ge (graphRoot_mem he)) (B.plane_eq.ge (graphRoot_mem hf))
    (graphRoot_ne_of_path he hf)).trans B.plane_eq


theorem twoStep_mem_coset {a₀ : W} {g h k : planeSubgroup M cs P}
    (he : BruhatStep cs ((g : W) * a₀) ((h : W) * a₀))
    (hf : BruhatStep cs ((h : W) * a₀) ((k : W) * a₀))
    {z : W} (hez : BruhatStep cs ((g : W) * a₀) z)
    (hzf : BruhatStep cs z ((k : W) * a₀)) :
    z * a₀⁻¹ ∈ planeSubgroup M cs P := by
  by_cases hz : (h : W) * a₀ = z
  · rw [← hz, mul_inv_cancel_right]
    exact h.property
  have hplane := graphRoot_square_plane he hez hf hzf hz
  have hroot : (graphRoot hez).val ∈ P := by
    apply (hplane.symm.trans (B.graphRoot_path_plane he hf)).le
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have href : z * ((g : W) * a₀)⁻¹ ∈ planeSubgroup M cs P :=
    (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents hez)).mpr hroot
  convert (planeSubgroup M cs P).mul_mem href g.property using 1; group

/-- A relative rank-two interval has exactly its two ambient two-edge paths,
with no assumption that the two ambient and relative orders coincide. -/
theorem ambient_two_step_rank_two {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z * a₀))
    {g k : planeSubgroup M cs P} (hlen : B.system.length k = B.system.length g + 2) :
    ∃ a b : W, a ≠ b ∧ ∀ z : W,
      (BruhatStep cs ((g : W) * a₀) z ∧ BruhatStep cs z ((k : W) * a₀)) ↔
        z = a ∨ z = b := by
  obtain ⟨a,b,hab,hpaths⟩ := Dihedral.two_step_rank_two B.system hlen
  have ha := (hpaths a).mpr (Or.inl rfl)
  have he := (B.coset_step_iff hmin g a).mpr ha.1
  have hf := (B.coset_step_iff hmin a k).mpr ha.2
  refine ⟨(a : W)*a₀,(b : W)*a₀,?_,fun z => ?_⟩
  · intro heq
    exact hab (Subtype.ext (mul_right_cancel heq))
  constructor
  · intro hz
    let z' : planeSubgroup M cs P := ⟨z*a₀⁻¹,B.twoStep_mem_coset he hf hz.1 hz.2⟩
    have hz' : (z' : W)*a₀=z := by dsimp [z']; group
    have hp : BruhatStep B.system g z' ∧ BruhatStep B.system z' k := by
      constructor
      · exact (B.coset_step_iff hmin g z').mp (hz' ▸ hz.1)
      · exact (B.coset_step_iff hmin z' k).mp (hz' ▸ hz.2)
    rcases (hpaths z').mp hp with hza | hzb
    · exact Or.inl (hz'.symm.trans (congrArg (fun q : planeSubgroup M cs P => (q:W)*a₀) hza))
    · exact Or.inr (hz'.symm.trans (congrArg (fun q : planeSubgroup M cs P => (q:W)*a₀) hzb))
  · rintro (rfl | rfl)
    · exact ⟨he,hf⟩
    · have hb := (hpaths b).mpr (Or.inr rfl)
      exact ⟨(B.coset_step_iff hmin g b).mpr hb.1,
        (B.coset_step_iff hmin b k).mpr hb.2⟩

end PlaneBasis
end
end KLInvariance.TitsSpace

namespace KLInvariance.Dihedral
variable {G : Type*} [Group G] {N : CoxeterMatrix Bool}

/-- Exactly two intermediate vertices characterize relative rank two as soon
as one two-edge path exists. Used to rule out skipped ranks after transport. -/
theorem rank_two_of_two_step_bound (ds : CoxeterSystem N G) {x y a b : G}
    (ha : BruhatStep ds x a) (hay : BruhatStep ds a y)
    (hbound : ∀ z, BruhatStep ds x z → BruhatStep ds z y → z = a ∨ z = b) :
    ds.length y = ds.length x + 2 := by
  have hxa := (step_iff_odd ds x a).mp ha
  have hay' := (step_iff_odd ds a y).mp hay
  rw [Nat.odd_iff] at hxa hay'
  have heven : (ds.length y - ds.length x) % 2 = 0 := by omega
  by_contra hlen
  have hlarge : ds.length x + 3 < ds.length y := by omega
  obtain ⟨p,q,hpq,hlevel⟩ := two_elements_length ds
    (by omega : 0 < ds.length x+1) (w := y) (by omega)
  have hp := (hlevel p).mpr (Or.inl rfl)
  have hq := (hlevel q).mpr (Or.inr rfl)
  obtain ⟨r,s,hrs,hlevel'⟩ := two_elements_length ds
    (by omega : 0 < ds.length x+3) hlarge
  have hr := (hlevel' r).mpr (Or.inl rfl)
  have paths : ∀ z, ds.length z = ds.length x+1 ∨ ds.length z = ds.length x+3 →
      BruhatStep ds x z ∧ BruhatStep ds z y := by
    intro z hz
    rw [step_iff_odd,step_iff_odd,Nat.odd_iff,Nat.odd_iff]
    rcases hz with hz | hz <;> omega
  have pp := paths p (Or.inl hp)
  have pq := paths q (Or.inl hq)
  have pr := paths r (Or.inr hr)
  have hpr : p ≠ r := by intro he; rw [he] at hp; omega
  have hqr : q ≠ r := by intro he; rw [he] at hq; omega
  rcases hbound p pp.1 pp.2 with hp' | hp' <;>
    rcases hbound q pq.1 pq.2 with hq' | hq' <;>
    rcases hbound r pr.1 pr.2 with hr' | hr' <;> grind

end KLInvariance.Dihedral

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

theorem graphRoot_mem_of_coset {P : Submodule ℝ (I → ℝ)} {a₀ x y : W}
    (h : BruhatStep cs x y) (hx : x*a₀⁻¹ ∈ planeSubgroup M cs P)
    (hy : y*a₀⁻¹ ∈ planeSubgroup M cs P) : (graphRoot h).val ∈ P := by
  apply (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents h)).mp
  convert (planeSubgroup M cs P).mul_mem hy ((planeSubgroup M cs P).inv_mem hx) using 1
  group

theorem mem_coset_of_graphRoot {P : Submodule ℝ (I → ℝ)} {a₀ x y : W}
    (h : BruhatStep cs x y) (hx : x*a₀⁻¹ ∈ planeSubgroup M cs P)
    (hy : (graphRoot h).val ∈ P) : y*a₀⁻¹ ∈ planeSubgroup M cs P := by
  have hm := (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents h)).mpr hy
  convert (planeSubgroup M cs P).mul_mem hm hx using 1
  group

variable {D : Type*} [Group D] {N : CoxeterMatrix Bool} (ds : CoxeterSystem N D)
  {l r : D}

/-- The image of a full relative dihedral interval lies in one maximal plane
coset. This is derived just from the directed graph and distinct vertices. -/
theorem dihedral_image_in_plane
    (f : Interval ds l r → W) (hinj : Function.Injective f)
    (hgraph : ∀ a b : Interval ds l r,
      BruhatStep ds a.val b.val → BruhatStep cs (f a) (f b))
    (hlr : BruhatLE ds l r) (hrank : ds.length l + 2 ≤ ds.length r) :
    ∃ a b : PositiveRoot M cs, a ≠ b ∧
      ∀ z : Interval ds l r,
        f z * (f ⟨l,bruhat_refl ds l,hlr⟩)⁻¹ ∈ planeSubgroup M cs (rootPlane a b) := by
  let lo : Interval ds l r := ⟨l,bruhat_refl ds l,hlr⟩
  let hi : Interval ds l r := ⟨r,hlr,bruhat_refl ds r⟩
  obtain ⟨a,b,hab,ha,hb⟩ := Dihedral.two_interval_elements_length ds lo hi
    (n := ds.length l+1) (by dsimp [lo]; omega) (by dsimp [hi]; omega)
  have cover : ∀ p q : Interval ds l r, ds.length q.val = ds.length p.val+1 →
      BruhatStep cs (f p) (f q) := by
    intro p q hlen
    apply hgraph
    rw [Dihedral.step_iff_odd,Nat.odd_iff]
    omega
  have hla := cover lo a ha
  have hlb := cover lo b hb
  have hrootne := graphRoot_ne_of_same_source hla hlb (fun h => hab (hinj h))
  let P := rootPlane (graphRoot hla) (graphRoot hlb)
  refine ⟨graphRoot hla,graphRoot hlb,hrootne,?_⟩
  change ∀ z : Interval ds l r, f z * (f lo)⁻¹ ∈ planeSubgroup M cs P
  have hlo : f lo * (f lo)⁻¹ ∈ planeSubgroup M cs P := by simp
  have hat : f a * (f lo)⁻¹ ∈ planeSubgroup M cs P := by
    exact mem_coset_of_graphRoot hla hlo (Submodule.subset_span (Set.mem_insert _ _))
  have hbt : f b * (f lo)⁻¹ ∈ planeSubgroup M cs P := by
    exact mem_coset_of_graphRoot hlb hlo
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  intro z
  suffices ∀ n, ∀ z : Interval ds l r, ds.length z.val = n →
      f z * (f lo)⁻¹ ∈ planeSubgroup M cs P from this _ z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z hz
    have hzmin := length_le_of_bruhat ds z.property.1
    by_cases hzlo : z = lo
    · simpa only [hzlo] using hlo
    have hzgt : ds.length l < ds.length z.val :=
      length_lt_of_bruhat_ne ds z.property.1 (fun h => hzlo (Subtype.ext h.symm))
    by_cases hzone : ds.length z.val = ds.length l+1
    · obtain ⟨p,q,hpq,hlev⟩ := Dihedral.two_elements_length ds
        (by omega : 0 < ds.length l+1) (w := r) (by omega)
      have ap := (hlev a.val).mp ha
      have bp := (hlev b.val).mp hb
      have zp := (hlev z.val).mp hzone
      have habval : a.val ≠ b.val := fun h => hab (Subtype.ext h)
      have hza : z = a ∨ z = b := by
        apply (show z.val = a.val ∨ z.val = b.val → z = a ∨ z = b from
          fun h => h.elim (fun h => Or.inl (Subtype.ext h)) (fun h => Or.inr (Subtype.ext h)))
        grind
      rcases hza with rfl | rfl <;> assumption
    have htwo : ds.length l+2 ≤ ds.length z.val := by omega
    have hexp : ∃ p : Interval ds l r, ds.length p.val+2=ds.length z.val := by
      by_cases he : ds.length z.val = ds.length l+2
      · exact ⟨lo,he.symm⟩
      · obtain ⟨p,q,_,hp,_⟩ := Dihedral.two_interval_elements_length ds lo z
          (n := ds.length z.val-2) (by dsimp [lo]; omega) (by omega)
        exact ⟨p,by omega⟩
    obtain ⟨p,hp⟩ := hexp
    obtain ⟨q,s,hqs,hq,hs⟩ := Dihedral.two_interval_elements_length ds lo z
      (n := ds.length z.val-1) (by dsimp [lo]; omega) (by omega)
    have hp' := ih (ds.length p.val) (by omega) p rfl
    have hq' := ih (ds.length q.val) (by omega) q rfl
    have hs' := ih (ds.length s.val) (by omega) s rfl
    have hpq := cover p q (by omega)
    have hps := cover p s (by omega)
    have hqz := cover q z (by omega)
    have hsz := cover s z (by omega)
    have hplane : rootPlane (graphRoot hpq) (graphRoot hps) = P :=
      rootPlane_eq_of_mem _ _ _ _ hrootne (graphRoot_mem_of_coset hpq hp' hq')
        (graphRoot_mem_of_coset hps hp' hs')
        (graphRoot_ne_of_same_source hpq hps (fun h => hqs (hinj h)))
    have hsquare := graphRoot_square_plane hpq hps hqz hsz (fun h => hqs (hinj h))
    apply mem_coset_of_graphRoot hqz hq'
    apply (hsquare.trans hplane).le
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

end
end KLInvariance.TitsSpace

namespace KLInvariance.Dihedral
universe u₁ u₂
variable {D : Type u₁} [Group D] {N : CoxeterMatrix Bool} (ds : CoxeterSystem N D)
  {l r : D}

theorem exists_interval_length (hlr : BruhatLE ds l r) {n : ℕ}
    (hnl : ds.length l ≤ n) (hnr : n ≤ ds.length r) :
    ∃ z : Interval ds l r, ds.length z.val = n := by
  by_cases hl : n = ds.length l
  · exact ⟨⟨l,bruhat_refl ds l,hlr⟩,hl.symm⟩
  by_cases hr : n = ds.length r
  · exact ⟨⟨r,hlr,bruhat_refl ds r⟩,hr.symm⟩
  obtain ⟨a,b,_,ha,_⟩ := two_interval_elements_length ds
    (⟨l,bruhat_refl ds l,hlr⟩ : Interval ds l r)
    (⟨r,hlr,bruhat_refl ds r⟩ : Interval ds l r)
    (n := n) (by dsimp; omega) (by dsimp; omega)
  exact ⟨a,ha⟩

variable {D' : Type u₂} [Group D'] {N' : CoxeterMatrix Bool}
  (ds' : CoxeterSystem N' D')

theorem map_cover_length
    (f : Interval ds l r → D')
    (hgraph : ∀ x y : Interval ds l r, BruhatStep ds x.val y.val →
      BruhatStep ds' (f x) (f y))
    (htwo : ∀ x y : Interval ds l r, ds.length y.val = ds.length x.val+2 →
      ds'.length (f y) = ds'.length (f x)+2)
    (hlr : BruhatLE ds l r) (hrank : ds.length l+2 ≤ ds.length r)
    {x y : Interval ds l r} (hxy : ds.length y.val = ds.length x.val+1) :
    ds'.length (f y) = ds'.length (f x)+1 := by
  have hstep : ∀ p q : Interval ds l r, ds.length q.val = ds.length p.val+1 →
      ds'.length (f p) < ds'.length (f q) := by
    intro p q hpq
    apply (hgraph p q ?_).1
    rw [step_iff_odd,Nat.odd_iff]
    omega
  have hxy' := hstep x y hxy
  have hyr := length_le_of_bruhat ds y.property.2
  by_cases hy : ds.length y.val < ds.length r
  · obtain ⟨z,hz⟩ := exists_interval_length ds hlr
      (n := ds.length y.val+1)
      (by have := length_le_of_bruhat ds y.property.1; omega) (by omega)
    have hyz := hstep y z hz
    have hxz := htwo x z (by omega)
    omega
  · obtain ⟨z,hz⟩ := exists_interval_length ds hlr
      (n := ds.length x.val-1) (by omega) (by omega)
    have hzx := hstep z x (by omega)
    have hzy := htwo z y (by omega)
    omega

/-- A directed dihedral-interval graph injection which does not stretch any
rank-two interval preserves all relative ranks. -/
theorem map_length_affine
    (f : Interval ds l r → D')
    (hgraph : ∀ x y : Interval ds l r, BruhatStep ds x.val y.val →
      BruhatStep ds' (f x) (f y))
    (htwo : ∀ x y : Interval ds l r, ds.length y.val = ds.length x.val+2 →
      ds'.length (f y) = ds'.length (f x)+2)
    (hlr : BruhatLE ds l r) (hrank : ds.length l+2 ≤ ds.length r)
    (z : Interval ds l r) :
    ds'.length (f z) + ds.length l =
      ds'.length (f ⟨l,bruhat_refl ds l,hlr⟩) + ds.length z.val := by
  let lo : Interval ds l r := ⟨l,bruhat_refl ds l,hlr⟩
  change ds'.length (f z)+ds.length l=ds'.length (f lo)+ds.length z.val
  suffices ∀ n, ∀ z : Interval ds l r, ds.length z.val=n →
      ds'.length (f z)+ds.length l=ds'.length (f lo)+ds.length z.val from this _ z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z hz
    by_cases he : z=lo
    · simp [he,lo]
    have hlt : ds.length l < ds.length z.val :=
      length_lt_of_bruhat_ne ds z.property.1 (fun h => he (Subtype.ext h.symm))
    obtain ⟨p,hp⟩ := exists_interval_length ds hlr (n := ds.length z.val-1)
      (by omega) (by have := length_le_of_bruhat ds z.property.2; omega)
    have ihp := ih (ds.length p.val) (by omega) p rfl
    have hc := map_cover_length ds ds' f hgraph htwo hlr hrank (x := p) (y := z)
      (by omega)
    omega

/-- Once relative covers are recovered, the image exhausts rather than merely
embeds in the target dihedral interval. -/
theorem range_eq_interval_of_rank_two
    (f : Interval ds l r → D') (hinj : Function.Injective f)
    (hgraph : ∀ x y : Interval ds l r, BruhatStep ds x.val y.val →
      BruhatStep ds' (f x) (f y))
    (htwo : ∀ x y : Interval ds l r, ds.length y.val = ds.length x.val+2 →
      ds'.length (f y) = ds'.length (f x)+2)
    (hlr : BruhatLE ds l r) (hrank : ds.length l+2 ≤ ds.length r) :
    Set.range f = {z | BruhatLE ds' (f ⟨l,bruhat_refl ds l,hlr⟩) z ∧
      BruhatLE ds' z (f ⟨r,hlr,bruhat_refl ds r⟩)} := by
  let lo : Interval ds l r := ⟨l,bruhat_refl ds l,hlr⟩
  let hi : Interval ds l r := ⟨r,hlr,bruhat_refl ds r⟩
  have hlen (z : Interval ds l r) : ds'.length (f z)+ds.length l =
      ds'.length (f lo)+ds.length z.val :=
    map_length_affine ds ds' f hgraph htwo hlr hrank z
  have hhi : ds'.length (f hi)+ds.length l=ds'.length (f lo)+ds.length r := hlen hi
  have horder (x y : Interval ds l r) :
      BruhatLE ds' (f x) (f y) ↔ x ≤ y := by
    change BruhatLE ds' (f x) (f y) ↔ BruhatLE ds x.val y.val
    rw [bruhat_iff_length_lt_or_eq,bruhat_iff_length_lt_or_eq]
    have hx := hlen x
    have hy := hlen y
    constructor
    · rintro (h | h)
      · left; omega
      · exact Or.inr (congrArg Subtype.val (hinj h))
    · rintro (h | h)
      · left; omega
      · exact Or.inr (congrArg f (Subtype.ext h))
  apply Set.ext
  intro z
  change (∃ x, f x=z) ↔ BruhatLE ds' (f lo) z ∧ BruhatLE ds' z (f hi)
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨(horder lo x).mpr x.property.1,(horder x hi).mpr x.property.2⟩
  · intro hz
    by_cases hlo : z=f lo
    · exact ⟨lo,hlo.symm⟩
    by_cases htop : z=f hi
    · exact ⟨hi,htop.symm⟩
    have hzlo := length_lt_of_bruhat_ne ds' hz.1 (Ne.symm hlo)
    have hzhi := length_lt_of_bruhat_ne ds' hz.2 htop
    have hnlo : ds.length l < ds.length l+(ds'.length z-ds'.length (f lo)) := by omega
    have hnhi : ds.length l+(ds'.length z-ds'.length (f lo)) < ds.length r := by omega
    obtain ⟨a,b,hab,ha,hb⟩ := two_interval_elements_length ds lo hi hnlo hnhi
    have hfa : ds'.length (f a)=ds'.length z := by have := hlen a; omega
    have hfb : ds'.length (f b)=ds'.length z := by have := hlen b; omega
    obtain ⟨p,q,hpq,helements⟩ := two_elements_length ds' (by omega : 0<ds'.length z) hzhi
    have hp := (helements (f a)).mp hfa
    have hq := (helements (f b)).mp hfb
    have hr := (helements z).mp rfl
    have hab' : f a ≠ f b := fun h => hab (hinj h)
    have he : z=f a ∨ z=f b := by grind
    rcases he with he | he
    · exact ⟨a,he.symm⟩
    · exact ⟨b,he.symm⟩

end KLInvariance.Dihedral

namespace KLInvariance
universe u v u' v'
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
  {I' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix I'}
  {cs : CoxeterSystem M W} {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}

/-- An interval graph isomorphism preserves the exact two-edge intermediate
set, including ambient intermediates not specified as interval data. -/
theorem intervalIso_twoStep_iff
    (e : Interval cs u b ≃o Interval cs' u' b') (x y a c : Interval cs u b)
    (hpaths : ∀ z : W, (BruhatStep cs x.val z ∧ BruhatStep cs z y.val) ↔
      z=a.val ∨ z=c.val) (z : W') :
    (BruhatStep cs' (e x).val z ∧ BruhatStep cs' z (e y).val) ↔
      z=(e a).val ∨ z=(e c).val := by
  constructor
  · intro hz
    let z' : Interval cs' u' b' := ⟨z,
      bruhat_trans cs' (e x).property.1 (Relation.ReflTransGen.single hz.1),
      bruhat_trans cs' (Relation.ReflTransGen.single hz.2) (e y).property.2⟩
    have hz₁ : BruhatStep cs x.val (e.symm z').val := by
      apply (intervalIso_bruhatStep_iff_general cs cs' e x (e.symm z')).mp
      simpa only [e.apply_symm_apply] using hz.1
    have hz₂ : BruhatStep cs (e.symm z').val y.val := by
      apply (intervalIso_bruhatStep_iff_general cs cs' e (e.symm z') y).mp
      simpa only [e.apply_symm_apply] using hz.2
    rcases (hpaths (e.symm z').val).mp ⟨hz₁,hz₂⟩ with ha | hc
    · have he : e.symm z'=a := Subtype.ext ha
      have he' : z'=e a := by rw [← he,e.apply_symm_apply]
      exact Or.inl (congrArg Subtype.val he')
    · have he : e.symm z'=c := Subtype.ext hc
      have he' : z'=e c := by rw [← he,e.apply_symm_apply]
      exact Or.inr (congrArg Subtype.val he')
  · rintro (rfl | rfl)
    · have h := (hpaths a.val).mpr (Or.inl rfl)
      exact ⟨(intervalIso_bruhatStep_iff_general cs cs' e x a).mpr h.1,
        (intervalIso_bruhatStep_iff_general cs cs' e a y).mpr h.2⟩
    · have h := (hpaths c.val).mpr (Or.inr rfl)
      exact ⟨(intervalIso_bruhatStep_iff_general cs cs' e x c).mpr h.1,
        (intervalIso_bruhatStep_iff_general cs cs' e c y).mpr h.2⟩

end KLInvariance

namespace KLInvariance.TitsSpace.PlaneBasis
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

def cosetIntervalMap {a₀ u b : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P}
    (hlo : BruhatLE cs u ((g : W)*a₀)) (hhi : BruhatLE cs ((k : W)*a₀) b) :
    Interval B.system g k ↪ Interval cs u b where
  toFun z := ⟨(z.val : W)*a₀,bruhat_trans cs hlo (B.coset_bruhat hmin z.property.1),
    bruhat_trans cs (B.coset_bruhat hmin z.property.2) hhi⟩
  inj' := by
    intro x y he
    exact Subtype.ext (Subtype.ext (mul_right_cancel (congrArg Subtype.val he)))

theorem twoStep_interval_iff {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (x y : Interval B.system g k)
    (hlen : B.system.length y.val=B.system.length x.val+2) :
    ∃ a b : Interval B.system g k, a ≠ b ∧ ∀ z : W,
      (BruhatStep cs ((x.val : W)*a₀) z ∧ BruhatStep cs z ((y.val : W)*a₀)) ↔
        z=(a.val : W)*a₀ ∨ z=(b.val : W)*a₀ := by
  obtain ⟨a,b,hab,hpaths⟩ := Dihedral.two_step_rank_two B.system hlen
  have ha := (hpaths a).mpr (Or.inl rfl)
  have hb := (hpaths b).mpr (Or.inr rfl)
  let ai : Interval B.system g k := ⟨a,
    bruhat_trans B.system x.property.1 (Relation.ReflTransGen.single ha.1),
    bruhat_trans B.system (Relation.ReflTransGen.single ha.2) y.property.2⟩
  let bi : Interval B.system g k := ⟨b,
    bruhat_trans B.system x.property.1 (Relation.ReflTransGen.single hb.1),
    bruhat_trans B.system (Relation.ReflTransGen.single hb.2) y.property.2⟩
  have he := (B.coset_step_iff hmin x.val a).mpr ha.1
  have hf := (B.coset_step_iff hmin a y.val).mpr ha.2
  refine ⟨ai,bi,fun h => hab (congrArg Subtype.val h),fun z => ?_⟩
  constructor
  · intro hz
    let z' : planeSubgroup M cs P := ⟨z*a₀⁻¹,B.twoStep_mem_coset he hf hz.1 hz.2⟩
    have hz' : (z' : W)*a₀=z := by dsimp [z']; group
    have hp : BruhatStep B.system x.val z' ∧ BruhatStep B.system z' y.val := by
      constructor
      · exact (B.coset_step_iff hmin x.val z').mp (hz' ▸ hz.1)
      · exact (B.coset_step_iff hmin z' y.val).mp (hz' ▸ hz.2)
    rcases (hpaths z').mp hp with hza | hzb
    · exact Or.inl (hz'.symm.trans (congrArg (fun q : planeSubgroup M cs P => (q:W)*a₀) hza))
    · exact Or.inr (hz'.symm.trans (congrArg (fun q : planeSubgroup M cs P => (q:W)*a₀) hzb))
  · rintro (rfl | rfl)
    · exact ⟨he,hf⟩
    · exact ⟨(B.coset_step_iff hmin x.val b).mpr hb.1,
        (B.coset_step_iff hmin b y.val).mpr hb.2⟩

end
end KLInvariance.TitsSpace.PlaneBasis

namespace KLInvariance.TitsSpace.PlaneBasis
open Module
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section


theorem transport_interval {a₀ u b : W} {u' b' : W'}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (hgk : BruhatLE B.system g k)
    (hrank : B.system.length g+2 ≤ B.system.length k)
    (hlo : BruhatLE cs u ((g : W)*a₀)) (hhi : BruhatLE cs ((k : W)*a₀) b)
    (e : Interval cs u b ≃o Interval cs' u' b') :
    ∃ (P' : Submodule ℝ (I' → ℝ)) (B' : PlaneBasis (M := M') (cs := cs') P')
      (a' : W') (F : Interval B.system g k → planeSubgroup M' cs' P'),
      (∀ z ∈ planeSubgroup M' cs' P', cs'.length a' ≤ cs'.length (z*a')) ∧
      Function.Injective F ∧
      (∀ z, (F z : W')*a' = (e (B.cosetIntervalMap hmin hlo hhi z)).val) ∧
      (∀ x y, BruhatLE B'.system (F x) (F y) ↔ x ≤ y) ∧
      (∀ x y, BruhatStep B'.system (F x) (F y) ↔ BruhatStep B.system x.val y.val) ∧
      (∀ z, B'.system.length (F z)+B.system.length g =
        B'.system.length (F ⟨g,bruhat_refl B.system g,hgk⟩)+B.system.length z.val) ∧
      Set.range F = {z | BruhatLE B'.system (F ⟨g,bruhat_refl B.system g,hgk⟩) z ∧
        BruhatLE B'.system z (F ⟨k,hgk,bruhat_refl B.system k⟩)} := by
  let inc := B.cosetIntervalMap hmin hlo hhi
  let f : Interval B.system g k → W' := fun z => (e (inc z)).val
  let lo : Interval B.system g k := ⟨g,bruhat_refl B.system g,hgk⟩
  have hinj : Function.Injective f := by
    intro x y h
    exact inc.injective (e.injective (Subtype.ext h))
  have hgraph (x y : Interval B.system g k) (h : BruhatStep B.system x.val y.val) :
      BruhatStep cs' (f x) (f y) := by
    exact (intervalIso_bruhatStep_iff_general cs cs' e (inc x) (inc y)).mpr
      ((B.coset_step_iff hmin x.val y.val).mpr h)
  obtain ⟨α,β,hαβ,hplane⟩ := dihedral_image_in_plane B.system f hinj hgraph hgk hrank
  let P' := rootPlane α β
  obtain ⟨B'⟩ := nonempty_planeBasis α β hαβ
  obtain ⟨a',g₀,hg₀,hg₀a,hmin'⟩ := planeCoset_exists_minimal M' cs' P' (f lo)
  have hmem (z : Interval B.system g k) : f z*a'⁻¹ ∈ planeSubgroup M' cs' P' := by
    convert (planeSubgroup M' cs' P').mul_mem (hplane z) hg₀ using 1
    change f z*a'⁻¹=f z*(f lo)⁻¹*g₀
    rw [hg₀a]
    group
  let F : Interval B.system g k → planeSubgroup M' cs' P' := fun z => ⟨f z*a'⁻¹,hmem z⟩
  have hF (z : Interval B.system g k) : (F z : W')*a'=f z := by
    dsimp [F]; group
  have hFinj : Function.Injective F := by
    intro x y h
    apply hinj
    rw [← hF x,← hF y,h]
  have hFgraph (x y : Interval B.system g k) (h : BruhatStep B.system x.val y.val) :
      BruhatStep B'.system (F x) (F y) := by
    apply (B'.coset_step_iff hmin' (F x) (F y)).mp
    rw [hF x,hF y]
    exact hgraph x y h
  have htwo (x y : Interval B.system g k)
      (hlen : B.system.length y.val=B.system.length x.val+2) :
      B'.system.length (F y)=B'.system.length (F x)+2 := by
    obtain ⟨a,c,hac,hpaths⟩ := B.twoStep_interval_iff hmin x y hlen
    have hpaths' (z : W') : (BruhatStep cs' (f x) z ∧ BruhatStep cs' z (f y)) ↔
        z=f a ∨ z=f c := intervalIso_twoStep_iff e (inc x) (inc y) (inc a) (inc c) hpaths z
    have hpa := (hpaths' (f a)).mpr (Or.inl rfl)
    have hxa : BruhatStep B'.system (F x) (F a) := by
      apply (B'.coset_step_iff hmin' (F x) (F a)).mp
      simpa only [hF] using hpa.1
    have hay : BruhatStep B'.system (F a) (F y) := by
      apply (B'.coset_step_iff hmin' (F a) (F y)).mp
      simpa only [hF] using hpa.2
    apply Dihedral.rank_two_of_two_step_bound B'.system hxa hay (b := F c)
    intro z hxz hzy
    have hp₁ := (B'.coset_step_iff hmin' (F x) z).mpr hxz
    have hp₂ := (B'.coset_step_iff hmin' z (F y)).mpr hzy
    rw [hF x] at hp₁
    rw [hF y] at hp₂
    rcases (hpaths' ((z : W')*a')).mp ⟨hp₁,hp₂⟩ with he | he
    · exact Or.inl (Subtype.ext (mul_right_cancel (he.trans (hF a).symm)))
    · exact Or.inr (Subtype.ext (mul_right_cancel (he.trans (hF c).symm)))
  have hlen := Dihedral.map_length_affine B.system B'.system F hFgraph htwo hgk hrank
  have horder (x y : Interval B.system g k) : BruhatLE B'.system (F x) (F y) ↔ x ≤ y := by
    change BruhatLE B'.system (F x) (F y) ↔ BruhatLE B.system x.val y.val
    rw [Dihedral.bruhat_iff_length_lt_or_eq,Dihedral.bruhat_iff_length_lt_or_eq]
    have hx := hlen x
    have hy := hlen y
    constructor
    · rintro (h | h)
      · left; omega
      · exact Or.inr (congrArg Subtype.val (hFinj h))
    · rintro (h | h)
      · left; omega
      · exact Or.inr (congrArg F (Subtype.ext h))
  refine ⟨P',B',a',F,hmin',hFinj,hF,horder,?_,hlen,?_⟩
  · intro x y
    rw [Dihedral.step_iff_odd,Dihedral.step_iff_odd,Nat.odd_iff,Nat.odd_iff]
    have hx := hlen x
    have hy := hlen y
    omega
  · exact Dihedral.range_eq_interval_of_rank_two B.system B'.system F hFinj
      hFgraph htwo hgk hrank

end
end KLInvariance.TitsSpace.PlaneBasis

end


section


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

theorem inverted_of_positive_combination (w : W) (a b c : PositiveRoot M cs)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hc : c.val = r • a.val + s • b.val)
    (ha : rootInverted w a) (hb : rootInverted w b) :
    rootInverted w c := by
  intro i
  rw [hc, map_add, map_smul, map_smul]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hr (ha i))
    (mul_nonpos_of_nonneg_of_nonpos hs (hb i))

/-- Incoming graph labels are actual inversions at their upper vertex. -/
theorem graphRoot_inverted_target {x y : W} (h : BruhatStep cs x y) :
    rootInverted y (graphRoot h) := by
  apply ((graphRoot_represents h).inversion_iff (graphRoot h).property.2 y).mpr
  refine ⟨h.label_reflection, ?_⟩
  have he : (y*x⁻¹)*y=x := by
    calc
      (y*x⁻¹)*y = (y*x⁻¹)*((y*x⁻¹)*x) := by group
      _ = x := by rw [← mul_assoc,h.label_reflection.mul_self,one_mul]
  simpa only [he] using h.1

/-- Outgoing graph labels are actual noninversions at their lower vertex. -/
theorem graphRoot_not_inverted_source {x y : W} (h : BruhatStep cs x y) :
    ¬ rootInverted x (graphRoot h) := by
  intro hi
  have hh := ((graphRoot_represents h).inversion_iff (graphRoot h).property.2 x).mp hi
  have he : (y*x⁻¹)*x=y := by group
  have hh' := hh.2
  rw [he] at hh'
  exact lt_asymm h.1 hh'

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- In a plane with its first simple root inverted, every noninverted root
is later than every inverted root. This uses convexity, not a signed-index
formula for a particular realization. -/
theorem slope_lt_of_inverted_left (w : W) (hl : rootInverted w B.left)
    (a b : PositiveRoot M cs) (haP : a.val ∈ P) (hbP : b.val ∈ P)
    (ha : rootInverted w a) (hb : ¬ rootInverted w b) :
    geometricSlope a < geometricSlope b := by
  by_contra h
  have hba : geometricSlope b < geometricSlope a :=
    lt_of_le_of_ne (le_of_not_gt h) (fun he => hb (geometricSlope_injective he ▸ ha))
  have hlb : geometricSlope B.left < geometricSlope b :=
    lt_of_le_of_ne (B.left_min b hbP) (fun he => hb (geometricSlope_injective he ▸ hl))
  have heq : rootPlane B.left a = P :=
    rootPlane_eq_of_mem B.left B.right B.left a B.distinct
      (Submodule.subset_span (Set.mem_insert _ _))
      (B.plane_eq.ge haP) (fun he => by rw [he] at hlb; exact (lt_asymm hlb hba)) |>.trans B.plane_eq
  obtain ⟨r,s,hr,hs,hc⟩ := positive_combination_of_slope_between B.left a b
    (heq.symm ▸ hbP) hlb hba
  exact hb (inverted_of_positive_combination w B.left a b hr.le hs.le hc hl ha)

/-- The other angular cut, when the last simple root is inverted. -/
theorem slope_lt_of_inverted_right (w : W) (hr : rootInverted w B.right)
    (a b : PositiveRoot M cs) (haP : a.val ∈ P) (hbP : b.val ∈ P)
    (ha : rootInverted w a) (hb : ¬ rootInverted w b) :
    geometricSlope b < geometricSlope a := by
  by_contra h
  have hab : geometricSlope a < geometricSlope b :=
    lt_of_le_of_ne (le_of_not_gt h) (fun he => hb (geometricSlope_injective he ▸ ha))
  have hbr : geometricSlope b < geometricSlope B.right :=
    lt_of_le_of_ne (B.right_max b hbP) (fun he => hb (geometricSlope_injective he ▸ hr))
  have har : a ≠ B.right := by
    intro he
    rw [he] at hab
    exact lt_asymm hbr hab
  have heq : rootPlane a B.right = P :=
    (rootPlane_eq_of_mem B.left B.right a B.right B.distinct
      (B.plane_eq.ge haP) (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      har).trans B.plane_eq
  obtain ⟨r,s,hrr,hss,hc⟩ := positive_combination_of_slope_between a B.right b
    (heq.symm ▸ hbP) hab hbr
  exact hb (inverted_of_positive_combination w a B.right b hrr.le hss.le hc ha hr)

/-- In the mixed-sign case the angular cut is determined by the first
canonical simple root. In particular the comparison of consecutive path
labels depends only on their middle vertex. -/
theorem slope_lt_iff_inverted_left (w : W)
    (a b : PositiveRoot M cs) (haP : a.val ∈ P) (hbP : b.val ∈ P)
    (ha : rootInverted w a) (hb : ¬ rootInverted w b) :
    geometricSlope a < geometricSlope b ↔ rootInverted w B.left := by
  constructor
  · intro hab
    by_contra hl
    have hr : rootInverted w B.right := by
      by_contra hr
      obtain ⟨r,s,hrr,hss,he⟩ := B.positive_cone a haP
      exact noninverted_of_positive_combination w B.left B.right a hrr hss he hl hr ha
    exact lt_asymm hab (B.slope_lt_of_inverted_right w hr a b haP hbP ha hb)
  · intro hl
    exact B.slope_lt_of_inverted_left w hl a b haP hbP ha hb

/-- The exact middle-vertex test for two ascending graph arrows with both
labels in this root plane. -/
theorem consecutive_slopes_iff {x y z : W}
    (hxy : BruhatStep cs x y) (hyz : BruhatStep cs y z)
    (ha : (graphRoot hxy).val ∈ P) (hb : (graphRoot hyz).val ∈ P) :
    geometricSlope (graphRoot hxy) < geometricSlope (graphRoot hyz) ↔
      rootInverted y B.left :=
  B.slope_lt_iff_inverted_left y _ _ ha hb
    (graphRoot_inverted_target hxy) (graphRoot_not_inverted_source hyz)

end PlaneBasis
end
end KLInvariance.TitsSpace

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

/-- The genuine diagram automorphism of an arbitrary rank-two Coxeter system,
including the infinite one. -/
def swapHom (cs : CoxeterSystem M W) : W →* W :=
  cs.lift ⟨fun i => cs.simple (!i), by
    intro i j
    have he : M i j = M (!i) (!j) := by
      cases i <;> cases j
      · simp
      · exact M.symmetric _ _
      · exact M.symmetric _ _
      · simp
    rw [he]
    exact cs.simple_mul_simple_pow _ _⟩

@[simp] theorem swapHom_simple (cs : CoxeterSystem M W) (i : Bool) :
    swapHom cs (cs.simple i) = cs.simple (!i) := cs.lift_apply_simple _ i

@[simp] theorem swapHom_involutive (cs : CoxeterSystem M W) :
    Function.Involutive (swapHom cs) := by
  intro w
  apply cs.simple_induction w
  · intro i
    simp
  · simp
  · intro a b ha hb
    simp only [map_mul,ha,hb]

def swap (cs : CoxeterSystem M W) : W ≃* W where
  toFun := swapHom cs
  invFun := swapHom cs
  left_inv := swapHom_involutive cs
  right_inv := swapHom_involutive cs
  map_mul' := map_mul (swapHom cs)

@[simp] theorem swap_simple (cs : CoxeterSystem M W) (i : Bool) :
    swap cs (cs.simple i) = cs.simple (!i) := swapHom_simple cs i

@[simp] theorem swap_swap (cs : CoxeterSystem M W) (w : W) :
    swap cs (swap cs w) = w := swapHom_involutive cs w

theorem swap_wordProd (cs : CoxeterSystem M W) (ω : List Bool) :
    swap cs (cs.wordProd ω) = cs.wordProd (ω.map Bool.not) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    simp only [cs.wordProd_cons, map_mul, swap_simple, List.map_cons, ih]

@[simp] theorem length_swap (cs : CoxeterSystem M W) (w : W) :
    cs.length (swap cs w) = cs.length w := by
  have hle (z : W) : cs.length (swap cs z) ≤ cs.length z := by
    obtain ⟨ω,hω,rfl⟩ := cs.exists_isReduced z
    rw [swap_wordProd, hω.eq]
    simpa using cs.length_wordProd_le (ω.map Bool.not)
  exact le_antisymm (hle w) (by simpa using hle (swap cs w))

@[simp] theorem descent_swap (cs : CoxeterSystem M W) (w : W) (i : Bool) :
    cs.IsLeftDescent (swap cs w) i ↔ cs.IsLeftDescent w (!i) := by
  unfold CoxeterSystem.IsLeftDescent
  rw [length_swap, ← Bool.not_not i, ← swap_simple, ← map_mul, length_swap]
  simp

/-- A nonzero length below an existing greater length has exactly one left
simple descent. This is not asserted for a finite dihedral longest element. -/
theorem unique_leftDescent (cs : CoxeterSystem M W) {w z : W}
    (hw : 0 < cs.length w) (hz : cs.length w < cs.length z) :
    ∃! i : Bool, cs.IsLeftDescent w i := by
  obtain ⟨i,hi⟩ := cs.exists_leftDescent_of_ne_one (w := w) (by
    intro he
    rw [he,cs.length_one] at hw
    omega)
  refine ⟨i,hi,?_⟩
  intro j hj
  by_contra hji
  have hj' : j = !i := by cases i <;> cases j <;> simp_all
  have he : cs.wordProd (alt i (cs.length w)) =
      cs.wordProd (alt (!i) (cs.length w)) := by
    rw [← eq_alt_of_descent cs i hi, ← hj', ← eq_alt_of_descent cs j hj]
  obtain ⟨a,b,hab,hab'⟩ := two_elements_length cs hw hz
  have all_eq (v : W) (hv : cs.length v = cs.length w) : v=w := by
    obtain ⟨k,hk⟩ := exists_alt cs v
    rw [hv] at hk
    have hki : k=i ∨ k=(!i) := by cases k <;> cases i <;> simp
    rcases hki with hki | hki
    · rw [hki] at hk
      exact hk.trans (eq_alt_of_descent cs i hi).symm
    · rw [hki] at hk
      exact hk.trans (he.symm.trans (eq_alt_of_descent cs i hi).symm)
  exact hab ((all_eq a ((hab' a).mpr (.inl rfl))).trans
    (all_eq b ((hab' b).mpr (.inr rfl))).symm)

/-- Internally, the diagram involution interchanges the two unique-descent
vertices of each rank. -/
theorem descent_swap_false_iff_not (cs : CoxeterSystem M W) {w z : W}
    (hw : 0 < cs.length w) (hz : cs.length w < cs.length z) :
    cs.IsLeftDescent (swap cs w) false ↔ ¬ cs.IsLeftDescent w false := by
  rw [descent_swap]
  obtain ⟨i,hi,hu⟩ := unique_leftDescent cs hw hz
  cases i
  · constructor
    · intro h
      have hh := hu true h
      contradiction
    · exact fun h => (h hi).elim
  · constructor
    · intro _ h
      have hh := hu false h
      contradiction
    · exact fun _ => hi

end
end KLInvariance.Dihedral

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- The ambient sign of a canonical plane root in a minimal coset is the
intrinsic simple-descent sign, with the original left labels. -/
theorem simpleRoot_inverted_coset_iff {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (w : planeSubgroup M cs P) (i : Bool) :
    rootInverted ((w : W)*a₀) (B.simpleRoot i) ↔ B.system.IsLeftDescent w i := by
  change (∀ k, action M cs ((w : W)*a₀)⁻¹ (B.simpleRoot i).val k ≤ 0) ↔ _
  rw [root_inversion_coset_iff hmin w.property (B.simpleRoot i).property.1
    (B.simpleRoot_mem i)]
  have hr : Represents M cs (B.system.simple i : W) (B.simpleRoot i).val := by
    rw [B.system_simple]
    exact rootReflection_represents M cs _
  rw [B.inversion_iff hr (B.simpleRoot_mem i) (B.simpleRoot i).property.2 w]
  exact B.system.isLeftInversion_simple_iff_isLeftDescent w i

/-- Geometric label of an intrinsic graph edge, taken in the actual ambient
root plane rather than an abstract alternate representation. -/
def edgeRoot {x y : planeSubgroup M cs P} (h : BruhatStep B.system x y) :
    PositiveRoot M cs := graphRoot ((B.bruhatStep_iff x y).mpr h)

theorem edgeRoot_plane {x y : planeSubgroup M cs P} (h : BruhatStep B.system x y) :
    (B.edgeRoot h).val ∈ P := by
  apply (Represents.planeSubgroup_mem_iff M cs (graphRoot_represents
    ((B.bruhatStep_iff x y).mpr h))).mp
  exact (planeSubgroup M cs P).mul_mem y.property
    ((planeSubgroup M cs P).inv_mem x.property)

/-- In the intrinsic system, the middle-vertex test uses its actual left
simple generator; it therefore applies to any induced dihedral realization. -/
theorem edgeRoot_slopes_iff {x y z : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hyz : BruhatStep B.system y z) :
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hyz) ↔
      B.system.IsLeftDescent y false := by
  unfold edgeRoot
  rw [B.consecutive_slopes_iff ((B.bruhatStep_iff x y).mpr hxy)
    ((B.bruhatStep_iff y z).mpr hyz) (B.edgeRoot_plane hxy) (B.edgeRoot_plane hyz)]
  have hmin : ∀ z ∈ planeSubgroup M cs P, cs.length (1:W) ≤ cs.length (z*1) :=
    fun z _ => by simp
  simpa only [mul_one, simpleRoot, Bool.false_eq_true, ↓reduceIte] using
    B.simpleRoot_inverted_coset_iff hmin y false

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Geometric orders adapted to a fixed upper vertex. These are honest
ratios of linear functionals, with a strictly positive denominator. They
will be used only as a permissible choice of the source's schedule. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def simplePositive (i : I) : PositiveRoot M cs :=
  ⟨root i, ⟨1,i,by simp⟩, root_nonneg i⟩

@[simp] theorem simplePositive_val (i : I) :
    (simplePositive (M := M) (cs := cs) i).val = root i := rfl

@[simp] theorem rootRef_simplePositive (i : I) :
    rootRef (simplePositive (M := M) (cs := cs) i) = cs.simple i := by
  exact (rootReflection_represents M cs _).reflection_unique ⟨1,i,by simp,by simp⟩

theorem simplePositive_injective : Function.Injective (simplePositive (M := M) (cs := cs)) := by
  intro i j hij
  have he := congrArg (fun a : PositiveRoot M cs => a.val i) hij
  by_contra hne
  simp [simplePositive, root, hne] at he

theorem coordinate_sum (a : I → ℝ) : ∑ i, a i • root i = a := by
  ext j
  simp [root, Pi.single_apply, Finset.sum_apply]

theorem dual_coordinate_sum (h : Module.Dual ℝ (I → ℝ)) (a : I → ℝ) :
    h a = ∑ i, a i * h (root i) := by
  conv_lhs => rw [← coordinate_sum a]
  simp only [map_sum,map_smul,smul_eq_mul]

def PositiveFunctional (h : Module.Dual ℝ (I → ℝ)) : Prop := ∀ i, 0 < h (root i)

theorem PositiveFunctional.root_pos {h : Module.Dual ℝ (I → ℝ)}
    (hh : PositiveFunctional h) (a : PositiveRoot M cs) : 0 < h a.val := by
  rw [dual_coordinate_sum]
  obtain ⟨i,hi⟩ : ∃ i, a.val i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact a.property.1.ne_zero (funext hn)
  exact Finset.sum_pos' (fun j _ => mul_nonneg (a.property.2 j) (hh j).le)
    ⟨i,Finset.mem_univ _,mul_pos (lt_of_le_of_ne' (a.property.2 i) hi) (hh i)⟩

theorem height_positive : PositiveFunctional (height (I := I)) := by
  intro i
  simp [height,root]

/-- Both functionals are actual dual vectors; the root order is not a
label-carrying addition to the interval isomorphism. -/
structure RatioOrder where
  denominator : Module.Dual ℝ (I → ℝ)
  numerator : Module.Dual ℝ (I → ℝ)
  positive : PositiveFunctional denominator
  generic : Function.Injective (fun a : PositiveRoot M cs => numerator a.val / denominator a.val)

namespace RatioOrder
variable (O : RatioOrder (M := M) (cs := cs))

def slope (a : PositiveRoot M cs) : ℝ := O.numerator a.val / O.denominator a.val

theorem denominator_pos (a : PositiveRoot M cs) : 0 < O.denominator a.val :=
  O.positive.root_pos a

theorem slope_injective : Function.Injective O.slope := O.generic

/-- The cut at zero is the genuine inversion set of the upper vertex. -/
def Adapted (y : W) : Prop := ∀ a : PositiveRoot M cs,
  (O.slope a < 0 ↔ rootInverted y a) ∧ O.slope a ≠ 0

theorem simple_lower_bound (i : I)
    (hi : ∀ j, O.slope (simplePositive i) ≤ O.slope (simplePositive j))
    (a : PositiveRoot M cs) : O.slope (simplePositive i) ≤ O.slope a := by
  change O.slope (simplePositive i) ≤ O.numerator a.val / O.denominator a.val
  rw [le_div_iff₀ (O.denominator_pos a)]
  rw [dual_coordinate_sum O.numerator a.val, dual_coordinate_sum O.denominator a.val,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hj := (le_div_iff₀ (O.positive j)).mp (hi j)
  change O.slope (simplePositive i) * O.denominator (root j) ≤ O.numerator (root j) at hj
  nlinarith [mul_nonneg (a.property.2 j) (sub_nonneg.mpr hj)]

theorem exists_least_simple [Nonempty I] : ∃ i : I,
    ∀ a : PositiveRoot M cs, O.slope (simplePositive i) ≤ O.slope a := by
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image (Finset.univ : Finset I)
    (fun i => O.slope (simplePositive i)) Finset.univ_nonempty
  exact ⟨i, O.simple_lower_bound i (fun j => hi j (Finset.mem_univ j))⟩

theorem least_simple_descent {y : W} (hy : y ≠ 1) (ha : O.Adapted y) :
    ∃ i : I, cs.IsLeftDescent y i ∧
      O.slope (simplePositive i) < 0 ∧
      ∀ a : PositiveRoot M cs, O.slope (simplePositive i) ≤ O.slope a := by
  obtain ⟨j,hj⟩ := cs.exists_leftDescent_of_ne_one hy
  let : Nonempty I := ⟨j⟩
  obtain ⟨i,hi⟩ := O.exists_least_simple
  have hjr : rootInverted y (simplePositive (M := M) (cs := cs) j) := by
    apply ((rootReflection_represents M cs _).inversion_iff (simplePositive j).property.2 y).mpr
    simpa only [rootRef_simplePositive] using (show cs.IsLeftInversion y (cs.simple j) from
      ⟨cs.isReflection_simple j,hj⟩)
  have hi0 := lt_of_le_of_lt (hi (simplePositive j)) ((ha _).1.mpr hjr)
  refine ⟨i,?_,hi0,hi⟩
  have hir := ((rootReflection_represents M cs _).inversion_iff
    (simplePositive i).property.2 y).mp ((ha _).1.mp hi0)
  simpa only [rootRef_simplePositive, CoxeterSystem.IsLeftDescent] using hir.2


/-- A functional in the chamber indexed by y has exactly Inv(y) as its
negative roots. This is stronger data used only to construct the order. -/
def Chamber (y : W) : Prop := ∀ i, 0 < O.numerator (action M cs y (root i))

theorem adapted_of_chamber {y : W} (hc : O.Chamber y) : O.Adapted y := by
  let f : Module.Dual ℝ (I → ℝ) := O.numerator.comp (action M cs y).toLinearMap
  have hf : PositiveFunctional f := hc
  intro a
  have he (v : I → ℝ) : f (action M cs y⁻¹ v) = O.numerator v := by
    change O.numerator (action M cs y (action M cs y⁻¹ v)) = _
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  by_cases ha : rootInverted y a
  · have hv := hf.root_pos (positiveAction y⁻¹ a)
    rw [positiveAction_eq_of_nonpos _ _ ha, map_neg, he] at hv
    have hn : O.slope a < 0 := div_neg_of_neg_of_pos (by linarith) (O.denominator_pos a)
    exact ⟨iff_of_true hn ha, hn.ne⟩
  · have hp := (not_rootInverted_iff y a).mp ha
    have hv := hf.root_pos (positiveAction y⁻¹ a)
    rw [positiveAction_eq_of_nonneg _ _ hp, he] at hv
    have hn : 0 < O.slope a := div_pos hv (O.denominator_pos a)
    exact ⟨iff_of_false (not_lt.mpr hn.le) ha, hn.ne'⟩

end RatioOrder

/-- The generic functional can be chosen in any prescribed Coxeter chamber,
not just outside the countably many equality hyperplanes. The explicit
polynomial perturbation makes both requirements simultaneous. -/
theorem exists_ratioOrder_chamber_height (y : W) :
    ∃ O : RatioOrder (M := M) (cs := cs), O.Chamber y ∧ O.denominator=height := by
  classical
  let := countable_Positiveroot M cs
  let f₀ : Module.Dual ℝ (I → ℝ) := height.comp (action M cs y⁻¹).toLinearMap
  let f : ℝ → Module.Dual ℝ (I → ℝ) := fun t =>
    f₀ + t • ReflectionSchedules.momentFunctional t
  have hf (t : ℝ) (v : I → ℝ) : f t v = f₀ v +
      t * (ReflectionSchedules.coordinatePolynomial v).eval t := by
    simp [f,ReflectionSchedules.coordinatePolynomial_eval]
  let U : Set ℝ := {t | ∀ i, 0 < f t (action M cs y (root i))}
  have hu : IsOpen U := by
    change IsOpen {t | ∀ i, 0 < f t (action M cs y (root i))}
    rw [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_lt continuous_const
    simp only [hf]
    exact continuous_const.add (continuous_id.mul (Polynomial.continuous _))
  have h0 : 0 ∈ U := by
    intro i
    simp only [f,zero_smul,add_zero]
    change 0 < height (action M cs y⁻¹ (action M cs y (root i)))
    rw [← LinearEquiv.mul_apply,← map_mul,inv_mul_cancel,map_one]
    exact height_positive i
  let P := {p : PositiveRoot M cs × PositiveRoot M cs // p.1 ≠ p.2}
  let v : P → (I → ℝ) := fun p => normalizedRoot p.val.1 - normalizedRoot p.val.2
  let d : P → Polynomial ℝ := fun p => Polynomial.C (f₀ (v p)) +
    Polynomial.X * ReflectionSchedules.coordinatePolynomial (v p)
  have hd : ∀ p, d p ≠ 0 := by
    intro p hp
    have hz := congrArg (fun q : Polynomial ℝ => q.eval 0) hp
    have hz' : f₀ (v p) = 0 := by simpa [d] using hz
    have hq : ReflectionSchedules.coordinatePolynomial (v p) = 0 := by
      simpa only [d,hz',Polynomial.C_0,zero_add,mul_eq_zero,Polynomial.X_ne_zero,false_or] using hp
    have hv : v p = 0 := ReflectionSchedules.coordinatePolynomial_injective (by simpa [ReflectionSchedules.coordinatePolynomial] using hq)
    exact p.property (normalizedRoot_injective (sub_eq_zero.mp hv))
  let bad : Set ℝ := ⋃ p : P, {t | (d p).IsRoot t}
  have hbad : bad.Countable := Set.countable_iUnion
    (fun p => (Polynomial.finite_setOfPred_isRoot (hd p)).countable)
  obtain ⟨t,htU,ht⟩ := (hbad.dense_compl ℝ).inter_open_nonempty U hu ⟨0,h0⟩
  have hinj : Function.Injective (fun a : PositiveRoot M cs => f t a.val / height a.val) := by
    intro a b heq
    by_contra hab
    apply ht
    apply Set.mem_iUnion.mpr
    refine ⟨⟨(a,b),hab⟩,?_⟩
    change (d ⟨(a,b),hab⟩).eval t = 0
    dsimp only [d]
    rw [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X,← hf]
    change f t (normalizedRoot a - normalizedRoot b) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    simpa only [normalizedRoot,map_smul,smul_eq_mul,div_eq_mul_inv,mul_comm] using heq
  exact ⟨⟨height,f t,height_positive,hinj⟩,htU,rfl⟩

theorem exists_ratioOrder_chamber (y : W) :
    ∃ O : RatioOrder (M := M) (cs := cs), O.Chamber y := by
  obtain ⟨O,hO,_⟩ := exists_ratioOrder_chamber_height (M := M) (cs := cs) y
  exact ⟨O,hO⟩

@[simp] theorem positiveAction_simplePositive (i : I) :
    positiveAction (cs.simple i) (simplePositive (M := M) (cs := cs) i) = simplePositive i := by
  apply Subtype.ext
  rw [positiveAction_eq_of_nonpos]
  · simp only [simplePositive_val,action_simple_root,neg_neg]
  · simpa only [simplePositive_val,action_simple_root,Pi.neg_apply,neg_nonpos] using root_nonneg i

theorem simple_action_nonneg (i : I) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) : ∀ k, 0 ≤ action M cs (cs.simple i) a.val k := by
  apply a.property.1.act (cs.simple i) |>.sign.resolve_right
  intro hn
  exact ha (Subtype.ext (a.property.1.eq_simple_of_nonpos a.property.2 i hn))

theorem simple_positiveAction_val (i : I) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) :
    (positiveAction (cs.simple i) a).val = action M cs (cs.simple i) a.val :=
  positiveAction_eq_of_nonneg _ _ (simple_action_nonneg i a ha)

theorem simple_positiveAction_ne (i : I) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) : positiveAction (cs.simple i) a ≠ simplePositive i := by
  intro he
  apply ha
  exact (positiveActionEquiv (cs.simple i)).injective (he.trans (positiveAction_simplePositive i).symm)

theorem exists_uniform_pos_lt (v : I → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε < v i := by
  have aux (s : Finset I) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε < v i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨ε,hε,hlt⟩ := ih
      refine ⟨min ε (v a / 2),lt_min hε (half_pos (hv a)),?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl|hi
      · exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self (hv i))
      · exact lt_of_le_of_lt (min_le_left _ _) (hlt i hi)
  obtain ⟨ε,hε,hlt⟩ := aux Finset.univ
  exact ⟨ε,hε,fun i => hlt i (Finset.mem_univ i)⟩

namespace RatioOrder
variable (O : RatioOrder (M := M) (cs := cs))

def turnNumerator (i : I) : Module.Dual ℝ (I → ℝ) :=
  O.numerator.comp (action M cs (cs.simple i)).toLinearMap

def turnDenominator (i : I) (k : ℝ) : Module.Dual ℝ (I → ℝ) :=
  (O.numerator - k • O.denominator).comp (action M cs (cs.simple i)).toLinearMap

theorem exists_turn_parameter (i : I) (hi0 : O.slope (simplePositive i) < 0)
    (hi : ∀ a : PositiveRoot M cs, O.slope (simplePositive i) ≤ O.slope a) :
    ∃ k : ℝ, k < 0 ∧ O.slope (simplePositive i) < k ∧
      PositiveFunctional (O.turnDenominator i k) := by
  let c := O.slope (simplePositive i)
  let v : I → ℝ := fun j => if j=i then -c else
    O.slope (positiveAction (cs.simple i) (simplePositive j)) - c
  have hv : ∀ j, 0 < v j := by
    intro j
    by_cases hj : j=i
    · simp only [v,ite_eq_left hj]
      exact neg_pos.mpr hi0
    · simp only [v,ite_eq_right hj]
      apply sub_pos.mpr
      apply lt_of_le_of_ne (hi _)
      intro he
      exact simple_positiveAction_ne i (simplePositive j)
        (fun hh => hj (simplePositive_injective hh)) (O.slope_injective he.symm)
  obtain ⟨ε,hε,hεv⟩ := exists_uniform_pos_lt v hv
  have hεc : ε < -c := by simpa only [v,ite_eq_left rfl] using hεv i
  refine ⟨c+ε,by linarith,by dsimp [c]; linarith,?_⟩
  intro j
  change 0 < O.numerator (action M cs (cs.simple i) (root j)) -
    (c+ε)*O.denominator (action M cs (cs.simple i) (root j))
  by_cases hj : j=i
  · subst j
    rw [action_simple_root,map_neg,map_neg]
    have hc : c * O.denominator (root i) = O.numerator (root i) := by
      exact div_mul_cancel₀ _ (O.positive i).ne'
    nlinarith [mul_pos hε (O.positive i)]
  · let a := positiveAction (cs.simple i) (simplePositive (M := M) (cs := cs) j)
    have ha : a.val = action M cs (cs.simple i) (root j) :=
      simple_positiveAction_val i (simplePositive j) (fun hh => hj (simplePositive_injective hh))
    rw [← ha]
    have hvj : ε < O.slope a - c := by simpa only [v,ite_eq_right hj] using hεv j
    have hlt : c+ε < O.slope a := by linarith
    exact sub_pos.mpr ((lt_div_iff₀ (O.denominator_pos a)).mp hlt)

theorem turn_ratio_injective (i : I) (k : ℝ) (hk : k ≠ 0)
    (hp : PositiveFunctional (O.turnDenominator i k)) :
    Function.Injective (fun a : PositiveRoot M cs =>
      O.turnNumerator i a.val / O.turnDenominator i k a.val) := by
  intro a b hab
  have hh (a : PositiveRoot M cs) : O.denominator (action M cs (cs.simple i) a.val) ≠ 0 := by
    rcases (a.property.1.act (cs.simple i)).sign with hpos|hneg
    · have h := O.denominator_pos (positiveAction (cs.simple i) a)
      rw [positiveAction_eq_of_nonneg _ _ hpos] at h
      exact h.ne'
    · have h := O.denominator_pos (positiveAction (cs.simple i) a)
      rw [positiveAction_eq_of_nonpos _ _ hneg,map_neg] at h
      exact (neg_pos.mp h).ne
  have hc := (div_eq_div_iff (hp.root_pos a).ne' (hp.root_pos b).ne').mp hab
  change O.numerator (action M cs (cs.simple i) a.val) *
      (O.numerator (action M cs (cs.simple i) b.val) -
        k*O.denominator (action M cs (cs.simple i) b.val)) =
    O.numerator (action M cs (cs.simple i) b.val) *
      (O.numerator (action M cs (cs.simple i) a.val) -
        k*O.denominator (action M cs (cs.simple i) a.val)) at hc
  have hcross : O.numerator (action M cs (cs.simple i) a.val) *
      O.denominator (action M cs (cs.simple i) b.val) =
    O.numerator (action M cs (cs.simple i) b.val) *
      O.denominator (action M cs (cs.simple i) a.val) := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show k * (O.numerator (action M cs (cs.simple i) a.val) *
      O.denominator (action M cs (cs.simple i) b.val) -
        O.numerator (action M cs (cs.simple i) b.val) *
      O.denominator (action M cs (cs.simple i) a.val)) = 0 by nlinarith [hc])).resolve_left hk
  have he := (div_eq_div_iff (hh a) (hh b)).mpr hcross
  have hval (a : PositiveRoot M cs) :
      O.numerator (action M cs (cs.simple i) a.val) /
          O.denominator (action M cs (cs.simple i) a.val) =
        O.slope (positiveAction (cs.simple i) a) := by
    unfold slope
    rcases (a.property.1.act (cs.simple i)).sign with hpos|hneg
    · rw [positiveAction_eq_of_nonneg _ _ hpos]
    · rw [positiveAction_eq_of_nonpos _ _ hneg,map_neg,map_neg,neg_div_neg_eq]
  rw [hval a,hval b] at he
  exact (positiveActionEquiv (cs.simple i)).injective (O.slope_injective he)

def turn (i : I) (k : ℝ) (hk : k ≠ 0)
    (hp : PositiveFunctional (O.turnDenominator i k)) : RatioOrder (M := M) (cs := cs) :=
  ⟨O.turnDenominator i k,O.turnNumerator i,hp,O.turn_ratio_injective i k hk hp⟩


theorem turn_chamber (i : I) (k : ℝ) (hk : k ≠ 0)
    (hp : PositiveFunctional (O.turnDenominator i k)) {y : W} (hy : O.Chamber y) :
    (O.turn i k hk hp).Chamber (cs.simple i * y) := by
  intro j
  change 0 < O.numerator (action M cs (cs.simple i)
    (action M cs (cs.simple i * y) (root j)))
  rw [← LinearEquiv.mul_apply,← map_mul,cs.simple_mul_simple_cancel_left]
  exact hy j

theorem turn_simple_greatest (i : I) (k : ℝ) (hk : k < 0)
    (hp : PositiveFunctional (O.turnDenominator i k)) (a : PositiveRoot M cs)
    (ha : a ≠ simplePositive i) :
    (O.turn i k hk.ne hp).slope a < (O.turn i k hk.ne hp).slope (simplePositive i) := by
  have hlt : (O.turn i k hk.ne hp).slope a < 1 := by
    apply (div_lt_iff₀ (hp.root_pos a)).mpr
    change O.numerator (action M cs (cs.simple i) a.val) <
      1 * (O.numerator (action M cs (cs.simple i) a.val) -
        k * O.denominator (action M cs (cs.simple i) a.val))
    have hap := O.denominator_pos (positiveAction (cs.simple i) a)
    rw [simple_positiveAction_val i a ha] at hap
    nlinarith [mul_neg_of_neg_of_pos hk hap]
  have hgt : 1 < (O.turn i k hk.ne hp).slope (simplePositive i) := by
    apply (lt_div_iff₀ (hp.root_pos (simplePositive i))).mpr
    change 1 * (O.numerator (action M cs (cs.simple i) (root i)) -
       k * O.denominator (action M cs (cs.simple i) (root i))) <
      O.numerator (action M cs (cs.simple i) (root i))
    rw [action_simple_root,map_neg,map_neg]
    nlinarith [mul_neg_of_neg_of_pos hk (O.positive i)]
  exact hlt.trans hgt

theorem turn_slope_lt_iff (i : I) (k : ℝ) (hk : k < 0)
    (hp : PositiveFunctional (O.turnDenominator i k))
    (a b : PositiveRoot M cs) (ha : a ≠ simplePositive i) (hb : b ≠ simplePositive i) :
    (O.turn i k hk.ne hp).slope (positiveAction (cs.simple i) a) <
      (O.turn i k hk.ne hp).slope (positiveAction (cs.simple i) b) ↔ O.slope a < O.slope b := by
  have hact (a : PositiveRoot M cs) (ha : a ≠ simplePositive i) :
      action M cs (cs.simple i) (positiveAction (cs.simple i) a).val = a.val := by
    rw [simple_positiveAction_val i a ha,← LinearEquiv.mul_apply,← map_mul,
      (cs.isReflection_simple i).mul_self,map_one]
    rfl
  have haD := hp.root_pos (positiveAction (cs.simple i) a)
  have hbD := hp.root_pos (positiveAction (cs.simple i) b)
  change 0 < O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) -
    k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) at haD
  change 0 < O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) -
    k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) at hbD
  rw [hact a ha] at haD
  rw [hact b hb] at hbD
  change O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) /
    (O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val) -
      k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) a).val)) <
    O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) /
    (O.numerator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val) -
      k * O.denominator (action M cs (cs.simple i) (positiveAction (cs.simple i) b).val)) ↔
    O.numerator a.val / O.denominator a.val < O.numerator b.val / O.denominator b.val
  rw [hact a ha,hact b hb,div_lt_div_iff₀ haD hbD,
    div_lt_div_iff₀ (O.denominator_pos a) (O.denominator_pos b)]
  constructor
  · intro h
    by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg hk.le (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith
  · intro h
    have := mul_neg_of_neg_of_pos hk (sub_pos.mpr h)
    nlinarith

/-- The actual geometric rotation needed for the Hecke recursion. It moves
the least simple root to last and preserves all other root comparisons. -/
theorem exists_rotation {y : W} (hy : y ≠ 1) (hc : O.Chamber y) :
    ∃ (i : I) (O' : RatioOrder (M := M) (cs := cs)),
      cs.IsLeftDescent y i ∧ O'.Chamber (cs.simple i * y) ∧
      (∀ a : PositiveRoot M cs, a ≠ simplePositive i →
        O.slope (simplePositive i) < O.slope a ∧ O'.slope a < O'.slope (simplePositive i)) ∧
      (∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
        (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
          O.slope a < O.slope b)) := by
  obtain ⟨i,hi,hi0,hmin⟩ := O.least_simple_descent hy (O.adapted_of_chamber hc)
  obtain ⟨k,hk,_,hpos⟩ := O.exists_turn_parameter i hi0 hmin
  refine ⟨i,O.turn i k hk.ne hpos,hi,O.turn_chamber i k hk.ne hpos hc,?_,?_⟩
  · intro a ha
    exact ⟨lt_of_le_of_ne (hmin a) (fun he => ha (O.slope_injective he).symm),
      O.turn_simple_greatest i k hk hpos a ha⟩
  · exact O.turn_slope_lt_iff i k hk hpos

end RatioOrder

end
end KLInvariance.TitsSpace

end


section

/-! Rank-two path reversal in the actual induced root plane, for every finite
full interval. This is a required Dyer wall-crossing relation, not the Dyer
identification itself. -/
namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Switch the two vertices at every strictly internal rank, leaving all
other ranks fixed. The diagram involution supplies the intrinsic switch. -/
def rankFlip (cs : CoxeterSystem M W) (L H : ℕ) (w : W) : W :=
  if L < cs.length w ∧ cs.length w < H then swap cs w else w

@[simp] theorem length_rankFlip (cs : CoxeterSystem M W) (L H : ℕ) (w : W) :
    cs.length (rankFlip cs L H w) = cs.length w := by
  unfold rankFlip
  split <;> simp

@[simp] theorem rankFlip_involutive (cs : CoxeterSystem M W) (L H : ℕ) :
    Function.Involutive (rankFlip cs L H) := by
  intro w
  unfold rankFlip
  split <;> simp_all

@[simp] theorem rankFlip_lower (cs : CoxeterSystem M W) (x y : W) :
    rankFlip cs (cs.length x) (cs.length y) x = x := by simp [rankFlip]

@[simp] theorem rankFlip_upper (cs : CoxeterSystem M W) (x y : W) :
    rankFlip cs (cs.length x) (cs.length y) y = y := by simp [rankFlip]

@[simp] theorem rankFlip_bruhat_iff (cs : CoxeterSystem M W) (L H : ℕ) (x y : W) :
    BruhatLE cs (rankFlip cs L H x) (rankFlip cs L H y) ↔ BruhatLE cs x y := by
  simp only [bruhat_iff_length_lt_or_eq, length_rankFlip,
    (rankFlip_involutive cs L H).injective.eq_iff]

@[simp] theorem rankFlip_step_iff (cs : CoxeterSystem M W) (L H : ℕ) (x y : W) :
    BruhatStep cs (rankFlip cs L H x) (rankFlip cs L H y) ↔ BruhatStep cs x y := by
  simp only [step_iff_odd, length_rankFlip]

/-- An automorphism of the unlabelled full dihedral interval, fixing its ends.
It need not arise from a Coxeter-system automorphism at those ends. -/
def intervalFlip (cs : CoxeterSystem M W) (lo hi : W) :
    Interval cs lo hi ≃o Interval cs lo hi where
  toFun x := ⟨rankFlip cs (cs.length lo) (cs.length hi) x.val, by
    constructor
    · simpa only [rankFlip_lower] using
        (rankFlip_bruhat_iff cs (cs.length lo) (cs.length hi) lo x.val).mpr x.property.1
    · simpa only [rankFlip_upper] using
        (rankFlip_bruhat_iff cs (cs.length lo) (cs.length hi) x.val hi).mpr x.property.2⟩
  invFun x := ⟨rankFlip cs (cs.length lo) (cs.length hi) x.val, by
    constructor
    · simpa only [rankFlip_lower] using
        (rankFlip_bruhat_iff cs (cs.length lo) (cs.length hi) lo x.val).mpr x.property.1
    · simpa only [rankFlip_upper] using
        (rankFlip_bruhat_iff cs (cs.length lo) (cs.length hi) x.val hi).mpr x.property.2⟩
  left_inv x := Subtype.ext (rankFlip_involutive cs _ _ x.val)
  right_inv x := Subtype.ext (rankFlip_involutive cs _ _ x.val)
  map_rel_iff' := rankFlip_bruhat_iff cs _ _ _ _

@[simp] theorem intervalFlip_val (cs : CoxeterSystem M W) (lo hi : W)
    (x : Interval cs lo hi) :
    (intervalFlip cs lo hi x).val = rankFlip cs (cs.length lo) (cs.length hi) x.val := rfl

@[simp] theorem intervalFlip_involutive (cs : CoxeterSystem M W) (lo hi : W) :
    Function.Involutive (intervalFlip cs lo hi) :=
  fun x => Subtype.ext (rankFlip_involutive cs _ _ x.val)

def edgeFlip (cs : CoxeterSystem M W) (lo hi : W) :
    BruhatGraph.Edge cs lo hi ≃ BruhatGraph.Edge cs lo hi where
  toFun e := ⟨(intervalFlip cs lo hi e.val.1, intervalFlip cs lo hi e.val.2),
    (rankFlip_step_iff cs _ _ _ _).mpr e.property⟩
  invFun e := ⟨(intervalFlip cs lo hi e.val.1, intervalFlip cs lo hi e.val.2),
    (rankFlip_step_iff cs _ _ _ _).mpr e.property⟩
  left_inv e := Subtype.ext (Prod.ext
    (intervalFlip_involutive cs lo hi e.val.1)
    (intervalFlip_involutive cs lo hi e.val.2))
  right_inv e := Subtype.ext (Prod.ext
    (intervalFlip_involutive cs lo hi e.val.1)
    (intervalFlip_involutive cs lo hi e.val.2))

@[simp] theorem edgeFlip_source (cs : CoxeterSystem M W) (lo hi : W)
    (e : BruhatGraph.Edge cs lo hi) :
    BruhatGraph.source cs lo hi (edgeFlip cs lo hi e) =
      intervalFlip cs lo hi (BruhatGraph.source cs lo hi e) := rfl

@[simp] theorem edgeFlip_target (cs : CoxeterSystem M W) (lo hi : W)
    (e : BruhatGraph.Edge cs lo hi) :
    BruhatGraph.target cs lo hi (edgeFlip cs lo hi e) =
      intervalFlip cs lo hi (BruhatGraph.target cs lo hi e) := rfl

@[simp] theorem edgeFlip_involutive (cs : CoxeterSystem M W) (lo hi : W) :
    Function.Involutive (edgeFlip cs lo hi) := by
  intro e
  apply Subtype.ext
  change (intervalFlip cs lo hi (intervalFlip cs lo hi e.val.1),
    intervalFlip cs lo hi (intervalFlip cs lo hi e.val.2)) = e.val
  exact Prod.ext (intervalFlip_involutive cs lo hi e.val.1)
    (intervalFlip_involutive cs lo hi e.val.2)

end
end KLInvariance.Dihedral

namespace KLInvariance.SchedulePaths
variable {V E V' E' : Type*} (source target : E → V) (source' target' : E' → V')

/-- Relabelling graph vertices and edges preserves the actual path predicate. -/
theorem IsPath.map {x y : V} {p : List E}
    (hp : IsPath source target x y p) (f : V → V') (g : E → E')
    (hs : ∀ e, source' (g e) = f (source e))
    (ht : ∀ e, target' (g e) = f (target e)) :
    IsPath source' target' (f x) (f y) (p.map g) := by
  induction p generalizing x with
  | nil => exact congrArg f hp
  | cons e p ih =>
    exact ⟨(hs e).trans (congrArg f hp.1), ht e ▸ ih hp.2⟩

/-- Every adjacent pair in a genuine path is composable. -/
theorem IsPath.isChain {x y : V} {p : List E} (hp : IsPath source target x y p) :
    p.IsChain (fun e f => target e = source f) := by
  induction p generalizing x with
  | nil => exact .nil
  | cons e p ih =>
    cases p with
    | nil => exact .singleton e
    | cons f p =>
      apply List.isChain_cons_cons.mpr
      exact ⟨hp.2.1.symm, ih hp.2⟩

/-- A path's adjacent comparisons suffice for a transitive label order. The
statement allows the comparison to change under an edge map, provided the
local relation is checked only on composable edges. -/
theorem IsPath.pairwise_map_of_local {Λ Λ' : Type*} [LinearOrder Λ] [LinearOrder Λ']
    {x y : V} {p : List E} (hp : IsPath source target x y p)
    (label : E → Λ) (label' : E' → Λ') (g : E → E')
    (hlocal : ∀ e f, target e = source f →
      label e < label f → label' (g e) < label' (g f))
    (horder : p.Pairwise (fun e f => label e < label f)) :
    (p.map g).Pairwise (fun e f => label' e < label' f) := by
  rw [← List.isChain_iff_pairwise] at horder ⊢
  rw [List.isChain_map]
  induction p generalizing x with
  | nil => exact .nil
  | cons e p ih =>
    cases p with
    | nil => exact .singleton e
    | cons f p =>
      rw [List.isChain_cons_cons] at horder ⊢
      exact ⟨hlocal e f hp.2.1.symm horder.1, ih hp.2 horder.2⟩

end KLInvariance.SchedulePaths

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
open Dihedral BruhatGraph
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem edgeRoot_ne_of_path {x y z : planeSubgroup M cs P}
    (hxy : BruhatStep B.system x y) (hyz : BruhatStep B.system y z) :
    B.edgeRoot hxy ≠ B.edgeRoot hyz :=
  graphRoot_ne_of_path ((B.bruhatStep_iff x y).mpr hxy) ((B.bruhatStep_iff y z).mpr hyz)

/-- At every internal vertex, the cut switches side under the path involution.
This is the local relation behind rank-two path-product reversal. -/
theorem edgeRoot_slopes_rankFlip {x y z top : planeSubgroup M cs P} {L : ℕ}
    (hxy : BruhatStep B.system x y) (hyz : BruhatStep B.system y z)
    (hL : L < B.system.length y) (hH : B.system.length y < B.system.length top) :
    let hx := (rankFlip_step_iff B.system L (B.system.length top) x y).mpr hxy
    let hz := (rankFlip_step_iff B.system L (B.system.length top) y z).mpr hyz
    geometricSlope (B.edgeRoot hxy) < geometricSlope (B.edgeRoot hyz) ↔
      geometricSlope (B.edgeRoot hz) < geometricSlope (B.edgeRoot hx) := by
  dsimp only
  let hx := (rankFlip_step_iff B.system L (B.system.length top) x y).mpr hxy
  let hz := (rankFlip_step_iff B.system L (B.system.length top) y z).mpr hyz
  have hsign : B.system.IsLeftDescent
      (rankFlip B.system L (B.system.length top) y) false ↔
      ¬ B.system.IsLeftDescent y false := by
    rw [rankFlip,ite_eq_left ⟨hL,hH⟩]
    exact descent_swap_false_iff_not B.system (by omega) hH
  have hne : geometricSlope (B.edgeRoot hx) ≠ geometricSlope (B.edgeRoot hz) :=
    fun he => B.edgeRoot_ne_of_path hx hz (geometricSlope_injective he)
  rw [B.edgeRoot_slopes_iff]
  constructor
  · intro hi
    have hn : ¬ geometricSlope (B.edgeRoot hx) < geometricSlope (B.edgeRoot hz) := by
      rw [B.edgeRoot_slopes_iff,hsign]
      exact not_not.mpr hi
    exact lt_of_le_of_ne (le_of_not_gt hn) hne.symm
  · intro hi
    by_contra hn
    have hlt := (B.edgeRoot_slopes_iff hx hz).mpr (hsign.mpr hn)
    exact lt_asymm hlt hi

/-- Restriction of the actual geometric root slope to a full plane interval. -/
def intervalEdgeSlope (lo hi : planeSubgroup M cs P) (e : Edge B.system lo hi) : ℝ :=
  geometricSlope (B.edgeRoot e.property)

/-- The global edge map reverses the comparison for every composable pair.
No statement is asserted for disjoint edge labels, which can share ties. -/
theorem intervalEdgeSlope_flip {lo hi : planeSubgroup M cs P}
    (e f : Edge B.system lo hi)
    (hjoin : target B.system lo hi e = source B.system lo hi f) :
    B.intervalEdgeSlope lo hi e < B.intervalEdgeSlope lo hi f ↔
      B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi f) <
        B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi e) := by
  rcases e with ⟨⟨ex,ey⟩,he⟩
  rcases f with ⟨⟨fx,fy⟩,hf⟩
  change ey = fx at hjoin
  subst fx
  have hl : B.system.length lo < B.system.length ey.val :=
    lt_of_le_of_lt (length_le_of_bruhat B.system ex.property.1) he.1
  have hh : B.system.length ey.val < B.system.length hi :=
    lt_of_lt_of_le hf.1 (length_le_of_bruhat B.system fy.property.2)
  exact B.edgeRoot_slopes_rankFlip he hf hl hh

end PlaneBasis
end
end KLInvariance.TitsSpace

namespace KLInvariance.SchedulePaths
open scoped BigOperators
variable {V E R : Type*} (source target : E → V)
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The finite set of genuine directed paths selected by an edge schedule. -/
def subpaths (schedule : List E) (x y : V) : Finset (List E) :=
  schedule.sublists'.toFinset.filter (IsPath source target x y)

@[simp] theorem mem_subpaths (schedule : List E) (x y : V) (p : List E) :
    p ∈ subpaths source target schedule x y ↔
      p.Sublist schedule ∧ IsPath source target x y p := by
  simp [subpaths, List.mem_sublists']

variable [Semiring R]

theorem dispatch_eq_subpaths_sum (T : R) (schedule : List E) (hnd : schedule.Nodup)
    (x y : V) :
    dispatch source target T (fun z => if z=y then 1 else 0) schedule x =
      ∑ p ∈ subpaths source target schedule x y, T ^ p.length := by
  rw [entry_eq_weighted_paths, subpaths, Finset.sum_filter,
    List.sum_toFinset _ (List.nodup_sublists'.mpr hnd)]

/-- A length-preserving involution on the actual schedule-path sets proves
an operator-entry relation, with no Hecke polynomial used in the assumptions. -/
theorem dispatch_eq_of_path_involution (T : R) (schedule schedule' : List E)
    (hnd : schedule.Nodup) (hnd' : schedule'.Nodup) (x y : V) (g : E → E)
    (hg : Function.Involutive g)
    (hforward : ∀ p ∈ subpaths source target schedule x y,
      p.map g ∈ subpaths source target schedule' x y)
    (hbackward : ∀ p ∈ subpaths source target schedule' x y,
      p.map g ∈ subpaths source target schedule x y) :
    dispatch source target T (fun z => if z=y then 1 else 0) schedule x =
      dispatch source target T (fun z => if z=y then 1 else 0) schedule' x := by
  rw [dispatch_eq_subpaths_sum source target T schedule hnd,
    dispatch_eq_subpaths_sum source target T schedule' hnd']
  exact Finset.sum_nbij' (List.map g) (List.map g) hforward hbackward
    (fun p _ => List.map_involutive_iff.mpr hg p)
    (fun p _ => List.map_involutive_iff.mpr hg p) (fun p _ => by simp)

end
end KLInvariance.SchedulePaths

namespace KLInvariance.SchedulePaths
variable {V E : Type*} (source target : E → V)
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Sorted full schedules select precisely their strictly monotone paths;
an actual graph map satisfying the adjacent comparison test transports them. -/
theorem subpaths_map_of_sorted (label label' : E → ℝ)
    (schedule schedule' : List E) (x y : V)
    (hs : schedule.Pairwise (fun e f => label f ≤ label e))
    (hs' : schedule'.Pairwise (fun e f => label' f ≤ label' e))
    (hfull' : ∀ e, e ∈ schedule')
    (hties : ∀ e f, label e = label f → target e ≠ source f)
    (f : V → V) (g : E → E)
    (hsource : ∀ e, source (g e) = f (source e))
    (htarget : ∀ e, target (g e) = f (target e))
    (hx : f x=x) (hy : f y=y)
    (hlocal : ∀ e f, target e=source f → label f<label e → label' (g f)<label' (g e))
    (p : List E) (hp : p ∈ subpaths source target schedule x y) :
    p.map g ∈ subpaths source target schedule' x y := by
  obtain ⟨hsub,hp⟩ := (mem_subpaths source target schedule x y p).mp hp
  have hstrict := decreasing_of_schedule_path source target label hties hp (hs.sublist hsub)
  have horder := hp.pairwise_map_of_local source target
    (Λ := OrderDual ℝ) (Λ' := OrderDual ℝ)
    (fun e => (label e : OrderDual ℝ)) (fun e => (label' e : OrderDual ℝ)) g hlocal hstrict
  have hp' := hp.map source target source target f g hsource htarget
  rw [hx,hy] at hp'
  exact (mem_subpaths source target schedule' x y (p.map g)).mpr
    ⟨sublist_of_decreasing_subset label' horder hs' (fun _ _ => hfull' _), hp'⟩

end
end KLInvariance.SchedulePaths

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
open Dihedral BruhatGraph SchedulePaths
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem intervalEdgeSlope_ties {lo hi : planeSubgroup M cs P}
    (e f : Edge B.system lo hi) (heq : B.intervalEdgeSlope lo hi e = B.intervalEdgeSlope lo hi f) :
    target B.system lo hi e ≠ source B.system lo hi f := by
  intro hjoin
  rcases e with ⟨⟨ex,ey⟩,he⟩
  rcases f with ⟨⟨fx,fy⟩,hf⟩
  change ey = fx at hjoin
  subst fx
  exact B.edgeRoot_ne_of_path he hf (geometricSlope_injective heq)

theorem intervalEdgeSlope_flip_reverse {lo hi : planeSubgroup M cs P}
    (e f : Edge B.system lo hi)
    (hjoin : target B.system lo hi e = source B.system lo hi f) :
    B.intervalEdgeSlope lo hi f < B.intervalEdgeSlope lo hi e ↔
      B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi e) <
        B.intervalEdgeSlope lo hi (edgeFlip B.system lo hi f) := by
  have hj : target B.system lo hi (edgeFlip B.system lo hi e) =
      source B.system lo hi (edgeFlip B.system lo hi f) := by
    simpa only [edgeFlip_source,edgeFlip_target] using congrArg (intervalFlip B.system lo hi) hjoin
  simpa only [edgeFlip_involutive B.system lo hi e, edgeFlip_involutive B.system lo hi f] using
    (B.intervalEdgeSlope_flip (edgeFlip B.system lo hi e) (edgeFlip B.system lo hi f) hj).symm

/-- Rank-two reversal of the genuine path-product entry between the two
ends of any full interval. The order is the actual induced angular order. -/
theorem dispatch_reverse_endpoints {R : Type*} [Semiring R]
    {lo hi : planeSubgroup M cs P} (hlohi : BruhatLE B.system lo hi)
    (schedule : List (Edge B.system lo hi)) (hnd : schedule.Nodup)
    (hfull : ∀ e, e ∈ schedule)
    (hs : schedule.Pairwise (fun e f => B.intervalEdgeSlope lo hi f ≤ B.intervalEdgeSlope lo hi e))
    (T : R) :
    let x : Interval B.system lo hi := ⟨lo,bruhat_refl B.system lo,hlohi⟩
    let y : Interval B.system lo hi := ⟨hi,hlohi,bruhat_refl B.system hi⟩
    dispatch (source B.system lo hi) (target B.system lo hi) T
      (fun z => if z=y then 1 else 0) schedule x =
    dispatch (source B.system lo hi) (target B.system lo hi) T
      (fun z => if z=y then 1 else 0) schedule.reverse x := by
  dsimp only
  let x : Interval B.system lo hi := ⟨lo,bruhat_refl B.system lo,hlohi⟩
  let y : Interval B.system lo hi := ⟨hi,hlohi,bruhat_refl B.system hi⟩
  have hx : intervalFlip B.system lo hi x=x := Subtype.ext (rankFlip_lower B.system lo hi)
  have hy : intervalFlip B.system lo hi y=y := Subtype.ext (rankFlip_upper B.system lo hi)
  have hrs : schedule.reverse.Pairwise
      (fun e f => -B.intervalEdgeSlope lo hi f ≤ -B.intervalEdgeSlope lo hi e) := by
    rw [List.pairwise_reverse]
    exact hs.imp (fun h => neg_le_neg h)
  have hrfull : ∀ e, e ∈ schedule.reverse := fun e => List.mem_reverse.mpr (hfull e)
  apply dispatch_eq_of_path_involution _ _ T schedule schedule.reverse hnd (List.nodup_reverse.mpr hnd) x y
    (edgeFlip B.system lo hi) (edgeFlip_involutive B.system lo hi)
  · apply subpaths_map_of_sorted _ _ (B.intervalEdgeSlope lo hi)
      (fun e => -B.intervalEdgeSlope lo hi e) schedule schedule.reverse x y hs hrs hrfull
      (B.intervalEdgeSlope_ties) (intervalFlip B.system lo hi) (edgeFlip B.system lo hi)
      (edgeFlip_source B.system lo hi) (edgeFlip_target B.system lo hi) hx hy
    intro e f hj hlt
    exact neg_lt_neg ((B.intervalEdgeSlope_flip_reverse e f hj).mp hlt)
  · apply subpaths_map_of_sorted _ _ (fun e => -B.intervalEdgeSlope lo hi e)
      (B.intervalEdgeSlope lo hi) schedule.reverse schedule x y hrs hs hfull
      (fun e f he => B.intervalEdgeSlope_ties e f (neg_injective he))
      (intervalFlip B.system lo hi) (edgeFlip B.system lo hi)
      (edgeFlip_source B.system lo hi) (edgeFlip_target B.system lo hi) hx hy
    intro e f hj hlt
    exact (B.intervalEdgeSlope_flip e f hj).mp (neg_lt_neg_iff.mp hlt)

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Genuine Dyer identification for geometric orders adapted to a fixed top.
The path values below are defined from actual reflection edges; equality with
`Hecke.rTilde` will be proved by its genuine simple-descent recurrence. -/
namespace KLInvariance.AdaptedDyer
open TitsSpace SchedulePaths
open scoped BigOperators
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Edge := {e : W × W // BruhatStep cs e.1 e.2}
def source (e : Edge cs) : W := e.val.1
def target (e : Edge cs) : W := e.val.2
def rootLabel (e : Edge cs) : PositiveRoot M cs := graphRoot e.property

@[simp] theorem rootRef_rootLabel (e : Edge cs) :
    rootRef (rootLabel cs e) = target cs e * (source cs e)⁻¹ := by
  exact congrArg Subtype.val ((positiveRootEquiv M cs).left_inv
    ⟨e.val.2 * e.val.1⁻¹,e.property.label_reflection⟩)

theorem target_eq_root (e : Edge cs) :
    target cs e = rootRef (rootLabel cs e) * source cs e := by
  rw [rootRef_rootLabel]
  group

theorem rootLabel_ne_of_join (e f : Edge cs) (h : target cs e = source cs f) :
    rootLabel cs e ≠ rootLabel cs f := by
  rcases e with ⟨⟨x,y⟩,he⟩
  rcases f with ⟨⟨z,w⟩,hf⟩
  change y=z at h
  subst z
  exact graphRoot_ne_of_path he hf

variable {cs}
def score (O : RatioOrder (M := M) (cs := cs)) (e : Edge cs) : ℝ :=
  O.slope (rootLabel cs e)

theorem score_ties (O : RatioOrder (M := M) (cs := cs)) (e f : Edge cs)
    (h : score O e = score O f) : target cs e ≠ source cs f :=
  fun hj => rootLabel_ne_of_join cs e f hj (O.slope_injective h)

variable (cs)
def edgeFinset (b : W) : Finset (Edge cs) :=
  let P := ((lowerFinset cs b).product (lowerFinset cs b)).filter
    (fun e => BruhatStep cs e.1 e.2)
  P.attach.image (fun e => (⟨e.val,by
    exact (Finset.mem_filter.mp e.property).2⟩ : Edge cs))

omit [Fintype I] in
@[simp] theorem mem_edgeFinset (b : W) (e : Edge cs) :
    e ∈ edgeFinset cs b ↔ BruhatLE cs (target cs e) b := by
  unfold edgeFinset
  constructor
  · intro h
    obtain ⟨p,_,he⟩ := Finset.mem_image.mp h
    subst e
    exact (mem_lowerFinset cs b p.val.2).mp
      (Finset.mem_product.mp (Finset.mem_filter.mp p.property).1).2
  · intro h
    apply Finset.mem_image.mpr
    have hx : BruhatLE cs (source cs e) b := (show BruhatLE cs (source cs e) (target cs e) from .single e.property).trans h
    refine ⟨⟨e.val,Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(mem_lowerFinset cs b _).mpr hx,(mem_lowerFinset cs b _).mpr h⟩,e.property⟩⟩,
      Finset.mem_attach _ _,?_⟩
    rfl

variable {cs}
def schedule (O : RatioOrder (M := M) (cs := cs)) (b : W) : List (Edge cs) :=
  (edgeFinset cs b).toList.mergeSort (fun e f => score O e ≤ score O f)

@[simp] theorem mem_schedule (O : RatioOrder (M := M) (cs := cs)) (b : W) (e : Edge cs) :
    e ∈ schedule O b ↔ BruhatLE cs (target cs e) b := by
  simp [schedule]

theorem schedule_nodup (O : RatioOrder (M := M) (cs := cs)) (b : W) :
    (schedule O b).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem schedule_increasing (O : RatioOrder (M := M) (cs := cs)) (b : W) :
    (schedule O b).Pairwise (fun e f => score O e ≤ score O f) := by
  unfold schedule
  apply List.pairwise_mergeSort'

variable (cs)
omit [Fintype I] in
theorem path_le {x y : W} {p : List (Edge cs)}
    (hp : IsPath (source cs) (target cs) x y p) : BruhatLE cs x y := by
  induction p generalizing x with
  | nil => exact hp ▸ .refl
  | cons e p ih =>
    exact hp.1 ▸ (show BruhatLE cs (source cs e) (target cs e) from .single e.property).trans (ih hp.2)

omit [Fintype I] in
theorem path_targets_le {x y : W} {p : List (Edge cs)}
    (hp : IsPath (source cs) (target cs) x y p) :
    ∀ e ∈ p, BruhatLE cs (target cs e) y := by
  induction p generalizing x with
  | nil => simp
  | cons e p ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact path_le cs hp.2
    · exact ih hp.2 f hf

variable {cs}
def paths (O : RatioOrder (M := M) (cs := cs)) (x y : W) : Finset (List (Edge cs)) :=
  subpaths (source cs) (target cs) (schedule O y) x y

@[simp] theorem mem_paths (O : RatioOrder (M := M) (cs := cs)) (x y : W) (p : List (Edge cs)) :
    p ∈ paths O x y ↔ IsPath (source cs) (target cs) x y p ∧
      p.Pairwise (fun e f => score O e < score O f) := by
  rw [paths,mem_subpaths]
  constructor
  · rintro ⟨hsub,hp⟩
    refine ⟨hp,?_⟩
    exact decreasing_of_schedule_path (source cs) (target cs)
      (Λ := OrderDual ℝ) (fun e => (score O e : OrderDual ℝ))
      (fun e f h => score_ties O e f h) hp ((schedule_increasing O y).sublist hsub)
  · rintro ⟨hp,hord⟩
    refine ⟨?_,hp⟩
    apply sublist_of_decreasing_subset (Λ := OrderDual ℝ)
      (fun e => (score O e : OrderDual ℝ)) hord (schedule_increasing O y)
    intro e he
    exact (mem_schedule O y e).mpr (path_targets_le cs hp e he)

def polynomial (O : RatioOrder (M := M) (cs := cs)) (x y : W) : Polynomial ℤ :=
  ∑ p ∈ paths O x y, Polynomial.X ^ p.length

theorem polynomial_dispatch (O : RatioOrder (M := M) (cs := cs)) (x y : W) :
    polynomial O x y = dispatch (source cs) (target cs) Polynomial.X
      (fun z => if z=y then 1 else 0) (schedule O y) x :=
  (dispatch_eq_subpaths_sum _ _ _ _ (schedule_nodup O y) x y).symm


variable (cs)
theorem rootRef_injective : Function.Injective (rootRef (M := M) (cs := cs)) := by
  intro a b h
  apply (positiveRootEquiv M cs).symm.injective
  exact Subtype.ext h

theorem rootLabel_simple_iff (i : I) (e : Edge cs) :
    rootLabel cs e = simplePositive i ↔ target cs e = cs.simple i * source cs e := by
  constructor
  · intro h
    rw [target_eq_root cs e,h,rootRef_simplePositive]
  · intro h
    apply rootRef_injective cs
    rw [rootRef_rootLabel,rootRef_simplePositive,h]
    group

/-- On a non-simple-labelled edge this is actual left multiplication by s.
Simple-labelled edges are fixed merely to make the extension a total involution;
all path uses below exclude them before applying this map. -/
def rotateEdge (i : I) (e : Edge cs) : Edge cs :=
  if h : target cs e = cs.simple i * source cs e then e else
    ⟨(cs.simple i * source cs e,cs.simple i * target cs e),
      bruhatStep_simple_mul cs e.property i h⟩

theorem rotateEdge_val (i : I) (e : Edge cs) (h : rootLabel cs e ≠ simplePositive i) :
    (rotateEdge cs i e).val = (cs.simple i * source cs e,cs.simple i * target cs e) := by
  rw [rotateEdge,dite_eq_right (fun hh => h ((rootLabel_simple_iff cs i e).mpr hh))]

theorem rotateEdge_root (i : I) (e : Edge cs) (h : rootLabel cs e ≠ simplePositive i) :
    rootLabel cs (rotateEdge cs i e) = positiveAction (cs.simple i) (rootLabel cs e) := by
  apply rootRef_injective cs
  rw [rootRef_rootLabel]
  change (rotateEdge cs i e).val.2 * (rotateEdge cs i e).val.1⁻¹ =
    rootRef (positiveAction (cs.simple i) (rootLabel cs e))
  have hc : rootRef (positiveAction (cs.simple i) (rootLabel cs e)) =
      cs.simple i * rootRef (rootLabel cs e) * (cs.simple i)⁻¹ :=
    rootReflection_positiveAction _ _
  rw [rotateEdge_val cs i e h,hc,rootRef_rootLabel]
  group

theorem rotateEdge_nonsimple (i : I) (e : Edge cs) (h : rootLabel cs e ≠ simplePositive i) :
    rootLabel cs (rotateEdge cs i e) ≠ simplePositive i := by
  rw [rotateEdge_root cs i e h]
  exact simple_positiveAction_ne i _ h

@[simp] theorem rotateEdge_involutive (i : I) : Function.Involutive (rotateEdge cs i) := by
  intro e
  by_cases h : rootLabel cs e = simplePositive i
  · have he : rotateEdge cs i e = e := by
      rw [rotateEdge,dite_eq_left ((rootLabel_simple_iff cs i e).mp h)]
    rw [he,he]
  · apply Subtype.ext
    rw [rotateEdge_val cs i _ (rotateEdge_nonsimple cs i e h)]
    change (cs.simple i * (rotateEdge cs i e).val.1,
      cs.simple i * (rotateEdge cs i e).val.2) = e.val
    rw [rotateEdge_val cs i e h]
    simp only [cs.simple_mul_simple_cancel_left]
    rfl

omit [Fintype I] in
theorem path_map_of_mem {E E' V V' : Type*} (src tgt : E → V) (src' tgt' : E' → V')
    {p : List E} {x y : V} (hp : IsPath src tgt x y p) (f : V → V') (g : E → E')
    (hs : ∀ e ∈ p, src' (g e) = f (src e)) (ht : ∀ e ∈ p, tgt' (g e) = f (tgt e)) :
    IsPath src' tgt' (f x) (f y) (p.map g) := by
  induction p generalizing x with
  | nil => exact congrArg f hp
  | cons e p ih =>
    refine ⟨(hs e List.mem_cons_self).trans (congrArg f hp.1),?_⟩
    rw [ht e List.mem_cons_self]
    exact ih hp.2 (fun a ha => hs a (List.mem_cons_of_mem e ha))
      (fun a ha => ht a (List.mem_cons_of_mem e ha))

theorem path_rotate {x y : W} {p : List (Edge cs)} (i : I)
    (hp : IsPath (source cs) (target cs) x y p)
    (hn : ∀ e ∈ p, rootLabel cs e ≠ simplePositive i) :
    IsPath (source cs) (target cs) (cs.simple i*x) (cs.simple i*y) (p.map (rotateEdge cs i)) := by
  apply path_map_of_mem (source cs) (target cs) (source cs) (target cs)
    hp (fun z => cs.simple i*z) (rotateEdge cs i)
  · intro e he
    exact congrArg Prod.fst (rotateEdge_val cs i e (hn e he))
  · intro e he
    exact congrArg Prod.snd (rotateEdge_val cs i e (hn e he))


@[simp] theorem rotateEdge_twice (i : I) (e : Edge cs) :
    rotateEdge cs i (rotateEdge cs i e) = e := rotateEdge_involutive cs i e

variable {cs}
def Nonsimple (i : I) (p : List (Edge cs)) : Prop :=
  ∀ e ∈ p, rootLabel cs e ≠ simplePositive i

@[simp] theorem nonsimple_map (i : I) {p : List (Edge cs)} (hn : Nonsimple i p) :
    Nonsimple i (p.map (rotateEdge cs i)) := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  exact rotateEdge_nonsimple cs i f (hn f hf)

@[simp] theorem path_map_twice (i : I) (p : List (Edge cs)) :
    (p.map (rotateEdge cs i)).map (rotateEdge cs i) = p := by
  simp only [List.map_map,Function.comp_def,rotateEdge_twice]
  exact List.map_id p

theorem path_rotate_iff (i : I) {x y : W} {p : List (Edge cs)} (hn : Nonsimple i p) :
    IsPath (source cs) (target cs) (cs.simple i*x) (cs.simple i*y)
      (p.map (rotateEdge cs i)) ↔ IsPath (source cs) (target cs) x y p := by
  constructor
  · intro hp
    simpa only [cs.simple_mul_simple_cancel_left,path_map_twice] using
      path_rotate cs i hp (nonsimple_map i hn)
  · intro hp
    exact path_rotate cs i hp hn

theorem paths_rotate_iff (O O' : RatioOrder (M := M) (cs := cs)) (i : I)
    (hcmp : ∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
      (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
        O.slope a < O.slope b))
    {x y : W} {p : List (Edge cs)} (hn : Nonsimple i p) :
    p.map (rotateEdge cs i) ∈ paths O' (cs.simple i*x) (cs.simple i*y) ↔ p ∈ paths O x y := by
  rw [mem_paths,mem_paths,path_rotate_iff i hn,List.pairwise_map]
  apply and_congr_right
  intro _
  apply List.Pairwise.iff_of_mem
  intro e f he hf
  simpa only [score,rotateEdge_root cs i e (hn e he),rotateEdge_root cs i f (hn f hf)] using
    hcmp (rootLabel cs e) (rootLabel cs f) (hn e he) (hn f hf)

theorem nonsimple_of_greatest (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmax : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope a < O.slope (simplePositive i))
    {x y : W} (hy : ¬cs.length (cs.simple i*y) < cs.length y)
    {p : List (Edge cs)} (hp : p ∈ paths O x y) : Nonsimple i p := by
  rw [mem_paths] at hp
  rcases hp with ⟨hp,ho⟩
  induction p generalizing x with
  | nil => simp [Nonsimple]
  | cons e p ih =>
    have he : rootLabel cs e ≠ simplePositive i := by
      intro he
      cases p with
      | nil =>
        have hy' : target cs e = y := hp.2
        have hr := (rootLabel_simple_iff cs i e).mp he
        have hx' : source cs e = cs.simple i*y := by
          rw [← hy',hr,cs.simple_mul_simple_cancel_left]
        have hl := e.property.1
        change cs.length (source cs e) < cs.length (target cs e) at hl
        rw [hy',hx'] at hl
        exact hy hl
      | cons f p =>
        have hlt := (List.pairwise_cons.mp ho).1 f List.mem_cons_self
        have hle : score O f ≤ O.slope (simplePositive i) := by
          by_cases hf : rootLabel cs f = simplePositive i
          · exact le_of_eq (congrArg O.slope hf)
          · exact (hmax _ hf).le
        have hes : score O e = O.slope (simplePositive i) := congrArg O.slope he
        exact (not_lt_of_ge hle) (hes ▸ hlt)
    intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · exact he
    · exact ih hp.2 ho.tail f hf

theorem nonsimple_tail_of_least (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {e : Edge cs} {p : List (Edge cs)}
    (ho : (e::p).Pairwise (fun e f => score O e < score O f)) : Nonsimple i p := by
  intro f hf heq
  have hef := (List.pairwise_cons.mp ho).1 f hf
  have he : O.slope (simplePositive i) ≤ score O e := by
    by_cases he : rootLabel cs e = simplePositive i
    · exact le_of_eq (congrArg O.slope he).symm
    · exact (hmin _ he).le
  have hf' : score O f = O.slope (simplePositive i) := congrArg O.slope heq
  exact (not_lt_of_ge he) (hf' ▸ hef)

theorem nonsimple_of_least_descent (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length (cs.simple i*x) < cs.length x)
    {p : List (Edge cs)} (hp : p ∈ paths O x y) : Nonsimple i p := by
  obtain ⟨hp,ho⟩ := (mem_paths O x y p).mp hp
  cases p with
  | nil => simp [Nonsimple]
  | cons e p =>
    have he : rootLabel cs e ≠ simplePositive i := by
      intro he
      have hr := (rootLabel_simple_iff cs i e).mp he
      have hl := e.property.1
      change cs.length (source cs e) < cs.length (target cs e) at hl
      rw [hr,hp.1] at hl
      exact (lt_asymm hx hl)
    intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · exact he
    · exact nonsimple_tail_of_least O i hmin ho f hf

def nonsimplePaths (O : RatioOrder (M := M) (cs := cs)) (i : I) (x y : W) :
    Finset (List (Edge cs)) := (paths O x y).filter (Nonsimple i)

@[simp] theorem mem_nonsimplePaths (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (x y : W) (p : List (Edge cs)) :
    p ∈ nonsimplePaths O i x y ↔ p ∈ paths O x y ∧ Nonsimple i p := by
  simp [nonsimplePaths]

theorem sum_nonsimple_rotate (O O' : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmax : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O'.slope a < O'.slope (simplePositive i))
    (hcmp : ∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
      (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
        O.slope a < O.slope b))
    (x y : W) (hy : cs.length (cs.simple i*y) < cs.length y) :
    ∑ p ∈ nonsimplePaths O i x y, (Polynomial.X : Polynomial ℤ)^p.length =
      polynomial O' (cs.simple i*x) (cs.simple i*y) := by
  unfold polynomial
  have hasc : ¬cs.length (cs.simple i*(cs.simple i*y)) < cs.length (cs.simple i*y) := by
    rw [cs.simple_mul_simple_cancel_left]
    omega
  apply Finset.sum_bij (fun p _ => p.map (rotateEdge cs i))
  · intro p hp
    obtain ⟨hp,hn⟩ := (mem_nonsimplePaths O i x y p).mp hp
    exact (paths_rotate_iff O O' i hcmp hn).mpr hp
  · intro p hp q hq he
    have := congrArg (List.map (rotateEdge cs i)) he
    simpa only [path_map_twice] using this
  · intro q hq
    have hn := nonsimple_of_greatest O' i hmax hasc hq
    refine ⟨q.map (rotateEdge cs i),?_,path_map_twice i q⟩
    have hn' := nonsimple_map i hn
    apply (mem_nonsimplePaths O i x y _).mpr
    refine ⟨?_,hn'⟩
    apply (paths_rotate_iff O O' i hcmp hn').mp
    simpa only [path_map_twice] using hq
  · intro p hp
    simp only [List.length_map]


variable (cs)
def simpleEdge (i : I) (x : W) (hx : cs.length x < cs.length (cs.simple i*x)) : Edge cs :=
  ⟨(x,cs.simple i*x),hx,cs.simple i,cs.isReflection_simple i,rfl⟩

omit [Fintype I] in
@[simp] theorem simpleEdge_source (i : I) (x : W) (hx : cs.length x < cs.length (cs.simple i*x)) :
    source cs (simpleEdge cs i x hx) = x := rfl

omit [Fintype I] in
@[simp] theorem simpleEdge_target (i : I) (x : W) (hx : cs.length x < cs.length (cs.simple i*x)) :
    target cs (simpleEdge cs i x hx) = cs.simple i*x := rfl

@[simp] theorem simpleEdge_root (i : I) (x : W) (hx : cs.length x < cs.length (cs.simple i*x)) :
    rootLabel cs (simpleEdge cs i x hx) = simplePositive i :=
  (rootLabel_simple_iff cs i _).mpr rfl

variable {cs}
theorem cons_simple_mem (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length x < cs.length (cs.simple i*x))
    {p : List (Edge cs)} (hp : p ∈ nonsimplePaths O i (cs.simple i*x) y) :
    simpleEdge cs i x hx :: p ∈ paths O x y := by
  obtain ⟨hp,hn⟩ := (mem_nonsimplePaths O i _ _ _).mp hp
  obtain ⟨hp,ho⟩ := (mem_paths O _ _ _).mp hp
  apply (mem_paths O _ _ _).mpr
  refine ⟨⟨rfl,hp⟩,List.pairwise_cons.mpr ⟨?_,ho⟩⟩
  intro e he
  change O.slope (rootLabel cs (simpleEdge cs i x hx)) < O.slope (rootLabel cs e)
  rw [simpleEdge_root]
  exact hmin _ (hn e he)

theorem not_nonsimple_iff_cons (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length x < cs.length (cs.simple i*x)) (p : List (Edge cs)) :
    p ∈ (paths O x y).filter (fun p => ¬Nonsimple i p) ↔
      ∃ q ∈ nonsimplePaths O i (cs.simple i*x) y, p = simpleEdge cs i x hx :: q := by
  constructor
  · intro hp
    obtain ⟨hp,hn⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,ho⟩ := (mem_paths O _ _ _).mp hp
    cases p with
    | nil => exact (hn (by simp [Nonsimple])).elim
    | cons e p =>
      have hnp : Nonsimple i p := nonsimple_tail_of_least O i hmin ho
      have he : rootLabel cs e = simplePositive i := by
        by_contra he
        apply hn
        intro f hf
        rcases List.mem_cons.mp hf with rfl|hf
        · exact he
        · exact hnp f hf
      have heq : e = simpleEdge cs i x hx := by
        apply Subtype.ext
        apply Prod.ext
        · exact hp.1
        · change target cs e = cs.simple i*x
          rw [(rootLabel_simple_iff cs i e).mp he,hp.1]
      subst e
      refine ⟨p,(mem_nonsimplePaths O i _ _ _).mpr ⟨?_,hnp⟩,rfl⟩
      exact (mem_paths O _ _ _).mpr ⟨hp.2,ho.tail⟩
  · rintro ⟨q,hq,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨cons_simple_mem O i hmin hx hq,?_⟩
    intro hn
    exact hn _ List.mem_cons_self (simpleEdge_root cs i x hx)

theorem polynomial_split (O : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    {x y : W} (hx : cs.length x < cs.length (cs.simple i*x)) :
    polynomial O x y =
      (∑ p ∈ nonsimplePaths O i x y, (Polynomial.X : Polynomial ℤ)^p.length) +
      Polynomial.X * (∑ p ∈ nonsimplePaths O i (cs.simple i*x) y,
        (Polynomial.X : Polynomial ℤ)^p.length) := by
  unfold polynomial
  rw [← Finset.sum_filter_add_sum_filter_not (paths O x y) (Nonsimple i)]
  congr 1
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun p _ => simpleEdge cs i x hx :: p)
  · intro p hp
    exact (not_nonsimple_iff_cons O i hmin hx _).mpr ⟨p,hp,rfl⟩
  · intro p hp q hq he
    exact List.cons.inj he |>.2
  · intro q hq
    obtain ⟨p,hp,rfl⟩ := (not_nonsimple_iff_cons O i hmin hx q).mp hq
    exact ⟨p,hp,rfl⟩
  · intro p hp
    simp only [List.length_cons,pow_succ']

/-- The path expansion satisfies exactly the genuine normalized Hecke
recursion, because the chosen geometric order can be rotated at a descent. -/
theorem polynomial_recursion (O O' : RatioOrder (M := M) (cs := cs)) (i : I)
    (hmin : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O.slope (simplePositive i) < O.slope a)
    (hmax : ∀ a : PositiveRoot M cs, a ≠ simplePositive i →
      O'.slope a < O'.slope (simplePositive i))
    (hcmp : ∀ a b : PositiveRoot M cs, a ≠ simplePositive i → b ≠ simplePositive i →
      (O'.slope (positiveAction (cs.simple i) a) < O'.slope (positiveAction (cs.simple i) b) ↔
        O.slope a < O.slope b))
    (x y : W) (hy : cs.length (cs.simple i*y) < cs.length y) :
    polynomial O x y = if cs.length (cs.simple i*x) < cs.length x then
      polynomial O' (cs.simple i*x) (cs.simple i*y) else
      polynomial O' (cs.simple i*x) (cs.simple i*y) +
        Polynomial.X * polynomial O' x (cs.simple i*y) := by
  split_ifs with hx
  · have heq : nonsimplePaths O i x y = paths O x y := by
      ext p
      rw [mem_nonsimplePaths]
      exact and_iff_left_of_imp (nonsimple_of_least_descent O i hmin hx)
    rw [← sum_nonsimple_rotate O O' i hmax hcmp x y hy,heq]
    rfl
  · have ha : cs.length x < cs.length (cs.simple i*x) := by
      have := cs.length_simple_mul x i
      omega
    rw [polynomial_split O i hmin ha,
      sum_nonsimple_rotate O O' i hmax hcmp x y hy,
      sum_nonsimple_rotate O O' i hmax hcmp (cs.simple i*x) y hy,
      cs.simple_mul_simple_cancel_left]


@[simp] theorem paths_diagonal (O : RatioOrder (M := M) (cs := cs)) (x : W) :
    paths O x x = {[]} := by
  ext p
  rw [mem_paths,Finset.mem_singleton]
  cases p with
  | nil => simp [IsPath]
  | cons e p =>
    constructor
    · rintro ⟨hp,_⟩
      have hl := length_le_of_bruhat cs (path_le cs hp.2)
      have he := e.property.1
      change cs.length (source cs e) < cs.length (target cs e) at he
      rw [hp.1] at he
      omega
    · simp

@[simp] theorem polynomial_diagonal (O : RatioOrder (M := M) (cs := cs)) (x : W) :
    polynomial O x x = 1 := by
  simp [polynomial]

theorem polynomial_zero (O : RatioOrder (M := M) (cs := cs)) (x y : W)
    (h : ¬BruhatLE cs x y) : polynomial O x y = 0 := by
  have hp : paths O x y = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact h (path_le cs ((mem_paths O x y p).mp hp).1)
  simp [polynomial,hp]

/-- Dyer's increasing-path formula for a genuine generic geometric order
whose numerator is in the top chamber. The target is the Hecke-defined
normalized R-polynomial, not a renamed path polynomial. -/
theorem polynomial_eq_rTilde (O : RatioOrder (M := M) (cs := cs)) (x y : W)
    (hc : O.Chamber y) : polynomial O x y = Hecke.rTilde cs x y := by
  generalize hn : cs.length y = n
  induction n using Nat.strong_induction_on generalizing O x y with
  | h n ih =>
    by_cases hy : y=1
    · subst y
      by_cases hx : x=1
      · subst x
        rw [polynomial_diagonal,Hecke.rTilde_diagonal]
      · have hxy : ¬ BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          rw [cs.length_one] at hl
          exact hx (cs.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl))
        rw [polynomial_zero O x 1 hxy,Hecke.rTilde_zero cs x 1 hxy]
    · obtain ⟨i,O',hi,hc',hends,hcmp⟩ := O.exists_rotation hy hc
      have hi' : cs.length (cs.simple i*y) < n := hn ▸ hi
      have hsx := ih _ hi' O' (cs.simple i*x) (cs.simple i*y) hc' rfl
      have hx := ih _ hi' O' x (cs.simple i*y) hc' rfl
      rw [polynomial_recursion O O' i (fun a ha => (hends a ha).1)
        (fun a ha => (hends a ha).2) hcmp x y hi,
        Hecke.rTilde_recursion cs x y i hi,hsx,hx]

/-- An adapted geometric order exists for every top, without adding labels
or geometric data to the given interval isomorphism. -/
theorem exists_dyer_schedule (y : W) :
    ∃ O : RatioOrder (M := M) (cs := cs), O.Chamber y ∧
      ∀ x : W, polynomial O x y = Hecke.rTilde cs x y := by
  obtain ⟨O,hO⟩ := exists_ratioOrder_chamber (M := M) (cs := cs) y
  exact ⟨O,hO,fun x => polynomial_eq_rTilde O x y hO⟩

end
end KLInvariance.AdaptedDyer

end


section

/-! Finite edge-product algebra needed for geometric wall crossing. Every
operator is the actual `1 + T E_xy`; no R/KL identity is assumed here. -/

end

end OAI
