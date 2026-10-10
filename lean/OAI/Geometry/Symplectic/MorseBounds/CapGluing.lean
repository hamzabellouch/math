import OAI.Geometry.Symplectic.MorseBounds.LocalCorrection
import OAI.Geometry.Symplectic.MorseBounds.Composition
import OAI.Geometry.Symplectic.MorseBounds.Ambient

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.CapGluing
open scoped Manifold ContDiff Topology
open Set Filter
noncomputable section
local instance capGluingPropDecidable : (p : Prop) → Decidable p := Classical.propDecidable
variable {ι : Type*} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

def insert (e : ι → OpenPartialHomeomorph M N) (d : ℝ × N → N) (q : ℝ × M) : M :=
  if h : ∃ i, q.2 ∈ (e i).source then
    let i := Classical.choose h
    (e i).symm (d (q.1,e i q.2))
  else q.2

def zeroExtend (e : OpenPartialHomeomorph M N) (f : ℝ × N → ℝ) (q : ℝ × M) : ℝ :=
  if q.2 ∈ e.source then f (q.1,e q.2) else 0

def generator [Fintype ι] (e : ι → OpenPartialHomeomorph M N)
    (f : ℝ × N → ℝ) (q : ℝ × M) : ℝ := ∑ i, zeroExtend (e i) f q

variable {E F H G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [ChartedSpace H M] [ChartedSpace G N]

lemma source_index_unique (e : ι → OpenPartialHomeomorph M N)
    (hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source))
    {i j : ι} {x : M} (hi : x ∈ (e i).source) (hj : x ∈ (e j).source) : i = j := by
  by_contra hne
  exact Set.disjoint_left.mp (hdis hne) hi hj

lemma insert_in_source (e : ι → OpenPartialHomeomorph M N)
    (hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source))
    (d : ℝ × N → N) (t : ℝ) (i : ι) (x : M) (hx : x ∈ (e i).source) :
    insert e d (t,x) = (e i).symm (d (t,e i x)) := by
  have hex : ∃ j, x ∈ (e j).source := ⟨i,hx⟩
  have hj : Classical.choose hex = i :=
    source_index_unique e hdis (Classical.choose_spec hex) hx
  simp only [insert, dite_eq_left hex, hj]

lemma insert_outside (e : ι → OpenPartialHomeomorph M N) (d : ℝ × N → N)
    (t : ℝ) (x : M) (hx : ∀ i, x ∉ (e i).source) : insert e d (t,x) = x := by
  simp only [insert, not_exists.mpr hx, dite_false]

lemma coord_not_mem (e : OpenPartialHomeomorph M N) (C : Set N) {x : M}
    (hx : x ∈ e.source) (hnot : x ∉ e.symm '' C) : e x ∉ C := by
  intro hc
  exact hnot ⟨e x,hc,e.left_inv hx⟩

theorem zeroExtend_smooth [T2Space M] (e : OpenPartialHomeomorph M N)
    (he : ContMDiffOn I J ∞ e e.source) (C : Set N) (hC : IsCompact C)
    (hsub : C ⊆ e.target) (f : ℝ × N → ℝ)
    (hf : ContMDiff (𝓘(ℝ).prod J) 𝓘(ℝ) ∞ f)
    (hzero : ∀ t y, y ∉ C → f (t,y) = 0) :
    ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ (zeroExtend e f) := by
  intro q
  by_cases hx : q.2 ∈ e.source
  · have hc : ContMDiffAt (𝓘(ℝ).prod I) (𝓘(ℝ).prod J) ∞
        (fun p : ℝ × M => (p.1,e p.2)) q :=
      contMDiffAt_fst.prodMk (((he q.2 hx).contMDiffAt (e.open_source.mem_nhds hx)).comp q
        contMDiffAt_snd)
    apply ((hf (q.1,e q.2)).comp q hc).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.eventually (e.open_source.mem_nhds hx)] with p hp
    change (if p.2 ∈ e.source then f (p.1,e p.2) else 0) = f (p.1,e p.2)
    exact ite_eq_left hp
  · have hclosed : IsClosed (e.symm '' C) :=
      (hC.image_of_continuousOn (e.continuousOn_symm.mono hsub)).isClosed
    have hnot : q.2 ∉ e.symm '' C := by
      rintro ⟨y,hy,heq⟩
      exact hx (heq ▸ e.map_target (hsub hy))
    apply contMDiffAt_const.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.eventually (hclosed.isOpen_compl.mem_nhds hnot)]
      with p hp
    by_cases hm : p.2 ∈ e.source
    · simp only [zeroExtend, ite_eq_left hm]
      exact hzero _ _ (coord_not_mem e C hm hp)
    · simp only [zeroExtend, ite_eq_right hm]

lemma insert_off_support (e : ι → OpenPartialHomeomorph M N)
    (hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source))
    (C : Set N) (d : ℝ × N → N)
    (hid : ∀ t y, y ∉ C → d (t,y) = y) (t : ℝ) (x : M)
    (hx : ∀ i, x ∉ (e i).symm '' C) : insert e d (t,x) = x := by
  by_cases hm : ∃ i, x ∈ (e i).source
  · obtain ⟨i,hi⟩ := hm
    rw [insert_in_source e hdis _ _ i x hi,
      hid _ _ (coord_not_mem (e i) C hi (hx i)), (e i).left_inv hi]
  · exact insert_outside e d t x (not_exists.mp hm)

theorem insert_smooth [Finite ι] [T2Space M]
    (e : ι → OpenPartialHomeomorph M N)
    (hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source))
    (he : ∀ i, ContMDiffOn I J ∞ (e i) (e i).source)
    (hei : ∀ i, ContMDiffOn J I ∞ (e i).symm (e i).target)
    (C : Set N) (hC : IsCompact C) (hsub : ∀ i, C ⊆ (e i).target)
    (d : ℝ × N → N) (hd : ContMDiff (𝓘(ℝ).prod J) J ∞ d)
    (hid : ∀ t y, y ∉ C → d (t,y) = y)
    (hmap : ∀ t i, MapsTo (fun y => d (t,y)) (e i).target (e i).target) :
    ContMDiff (𝓘(ℝ).prod I) I ∞ (insert e d) := by
  intro q
  by_cases hx : ∃ i, q.2 ∈ (e i).source
  · obtain ⟨i,hi⟩ := hx
    have hc : ContMDiffAt (𝓘(ℝ).prod I) (𝓘(ℝ).prod J) ∞
        (fun p : ℝ × M => (p.1,e i p.2)) q :=
      contMDiffAt_fst.prodMk (((he i q.2 hi).contMDiffAt ((e i).open_source.mem_nhds hi)).comp q
        contMDiffAt_snd)
    have hm := hmap q.1 i ((e i).map_source hi)
    have hs := ((hei i _ hm).contMDiffAt ((e i).open_target.mem_nhds hm)).comp q
      ((hd (q.1,e i q.2)).comp q hc)
    apply hs.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.eventually ((e i).open_source.mem_nhds hi)]
      with p hp
    exact insert_in_source e hdis d p.1 i p.2 hp
  · let S : Set M := ⋃ i, (e i).symm '' C
    have hcomp : IsCompact S := isCompact_iUnion fun i =>
      hC.image_of_continuousOn ((e i).continuousOn_symm.mono (hsub i))
    have hnot : q.2 ∉ S := by
      rintro ⟨_, ⟨i,rfl⟩, y, hy, heq⟩
      exact hx ⟨i,heq ▸ (e i).map_target (hsub i hy)⟩
    apply contMDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.eventually
      (hcomp.isClosed.isOpen_compl.mem_nhds hnot)] with p hp
    apply insert_off_support e hdis C d hid p.1 p.2
    intro i hi
    exact hp (Set.mem_iUnion.mpr ⟨i,hi⟩)

theorem generator_smooth [Fintype ι] [T2Space M]
    (e : ι → OpenPartialHomeomorph M N)
    (he : ∀ i, ContMDiffOn I J ∞ (e i) (e i).source)
    (C : Set N) (hC : IsCompact C) (hsub : ∀ i, C ⊆ (e i).target)
    (f : ℝ × N → ℝ) (hf : ContMDiff (𝓘(ℝ).prod J) 𝓘(ℝ) ∞ f)
    (hzero : ∀ t y, y ∉ C → f (t,y) = 0) :
    ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ (generator e f) := by
  exact contMDiff_finsetSum fun i _ => zeroExtend_smooth (e i) (he i) C hC (hsub i) f hf hzero

lemma generator_in_source [Fintype ι]
    (e : ι → OpenPartialHomeomorph M N)
    (hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source))
    (f : ℝ × N → ℝ) (t : ℝ) (i : ι) (x : M) (hx : x ∈ (e i).source) :
    generator e f (t,x) = f (t,e i x) := by
  classical
  unfold generator
  rw [Finset.sum_eq_single i]
  · exact ite_eq_left hx
  · intro j _ hji
    have hj : x ∉ (e j).source := fun hj =>
      hji (source_index_unique e hdis hj hx)
    exact ite_eq_right hj
  · simp

lemma generator_outside [Fintype ι] (e : ι → OpenPartialHomeomorph M N)
    (f : ℝ × N → ℝ) (t : ℝ) (x : M) (hx : ∀ i, x ∉ (e i).source) :
    generator e f (t,x) = 0 := by
  exact Finset.sum_eq_zero fun i _ => ite_eq_right (hx i)

lemma insert_inverse (e : ι → OpenPartialHomeomorph M N)
    (hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source))
    (d d' : ℝ × N → N)
    (hmap : ∀ t i, MapsTo (fun y => d (t,y)) (e i).target (e i).target)
    (hinv : ∀ t y, d' (t,d (t,y)) = y) (t : ℝ) (x : M) :
    insert e d' (t,insert e d (t,x)) = x := by
  by_cases hx : ∃ i, x ∈ (e i).source
  · obtain ⟨i,hi⟩ := hx
    have hm := hmap t i ((e i).map_source hi)
    have hs := (e i).map_target hm
    rw [insert_in_source e hdis d t i x hi,
      insert_in_source e hdis d' t i _ hs, (e i).right_inv hm, hinv,
      (e i).left_inv hi]
  · have hn := not_exists.mp hx
    rw [insert_outside e d t x hn, insert_outside e d' t x hn]

theorem insert_diffeomorphism [Finite ι] [T2Space M]
    (e : ι → OpenPartialHomeomorph M N)
    (hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source))
    (he : ∀ i, ContMDiffOn I J ∞ (e i) (e i).source)
    (hei : ∀ i, ContMDiffOn J I ∞ (e i).symm (e i).target)
    (C : Set N) (hC : IsCompact C) (hsub : ∀ i, C ⊆ (e i).target)
    (d d' : ℝ × N → N)
    (hd : ContMDiff (𝓘(ℝ).prod J) J ∞ d)
    (hd' : ContMDiff (𝓘(ℝ).prod J) J ∞ d')
    (hid : ∀ t y, y ∉ C → d (t,y) = y)
    (hid' : ∀ t y, y ∉ C → d' (t,y) = y)
    (hmap : ∀ t i, MapsTo (fun y => d (t,y)) (e i).target (e i).target)
    (hmap' : ∀ t i, MapsTo (fun y => d' (t,y)) (e i).target (e i).target)
    (hinv : ∀ t y, d' (t,d (t,y)) = y)
    (hinv' : ∀ t y, d (t,d' (t,y)) = y) (t : ℝ) :
    ∃ a : M ≃ₘ⟮I,I⟯ M, (∀ x, a x = insert e d (t,x)) ∧
      (∀ x, a.symm x = insert e d' (t,x)) := by
  let a : M ≃ₘ⟮I,I⟯ M := {
    toFun := fun x => insert e d (t,x)
    invFun := fun x => insert e d' (t,x)
    left_inv := insert_inverse e hdis d d' hmap hinv t
    right_inv := insert_inverse e hdis d' d hmap' hinv' t
    contMDiff_toFun := (insert_smooth e hdis he hei C hC hsub d hd hid hmap).comp
      (contMDiff_const.prodMk contMDiff_id)
    contMDiff_invFun := (insert_smooth e hdis he hei C hC hsub d' hd' hid' hmap').comp
      (contMDiff_const.prodMk contMDiff_id) }
  exact ⟨a,fun _ => rfl,fun _ => rfl⟩

lemma inserted_in_source
    (e : ι → OpenPartialHomeomorph M N)
    (hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source))
    (d : ℝ × N → N) (g : M → M) (f : N → N)
    (hmap : ∀ i, MapsTo g (e i).source (e i).source)
    (heq : ∀ i x, x ∈ (e i).source → d (1,e i (g x)) = f (e i x))
    (i : ι) (x : M) (hx : x ∈ (e i).source) :
    insert e d (1,g x) = (e i).symm (f (e i x)) := by
  rw [insert_in_source e hdis d 1 i (g x) (hmap i hx), heq i x hx]

 theorem inserted_fixed_count [Finite ι]
    (e : ι → OpenPartialHomeomorph M N)
    (hdis : Pairwise (fun i j => Disjoint (e i).source (e j).source))
    (d : ℝ × N → N) (g : M → M) (f : N → N)
    (hmap : ∀ i, MapsTo g (e i).source (e i).source)
    (heq : ∀ i x, x ∈ (e i).source → d (1,e i (g x)) = f (e i x))
    (hfmap : ∀ i, MapsTo f (e i).target (e i).target)
    (hout : ∀ x, (∀ i, x ∉ (e i).source) → ∀ i, g x ∉ (e i).source)
    (hnofix : ∀ x, (∀ i, x ∉ (e i).source) → g x ≠ x)
    (hfixsub : ∀ i y, f y = y → y ∈ (e i).target)
    (hfinite : {y | f y = y}.Finite) :
    {x | insert e d (1,g x) = x}.Finite ∧
      {x | insert e d (1,g x) = x}.ncard =
        Nat.card ι * {y | f y = y}.ncard := by
  classical
  let A := {x | insert e d (1,g x) = x}
  let B := {y | f y = y}
  have hcover : ∀ x ∈ A, ∃ i, x ∈ (e i).source := by
    intro x hx
    by_contra hn
    have hno := not_exists.mp hn
    exact hnofix x hno ((insert_outside e d 1 (g x) (hout x hno)).symm.trans hx)
  have hlocal : ∀ i x, x ∈ (e i).source →
      (x ∈ A ↔ e i x ∈ B) := by
    intro i x hx
    change insert e d (1,g x) = x ↔ f (e i x) = e i x
    rw [inserted_in_source e hdis d g f hmap heq i x hx]
    constructor
    · intro h
      have hh := congrArg (e i) h
      rwa [(e i).right_inv (hfmap i ((e i).map_source hx))] at hh
    · intro h
      rw [h, (e i).left_inv hx]
  let j : A → ι := fun x => (hcover x x.property).choose
  have hj : ∀ x : A, x.val ∈ (e (j x)).source := fun x =>
    (hcover x x.property).choose_spec
  let a : A ≃ ι × B := {
    toFun := fun x => (j x, ⟨e (j x) x, (hlocal (j x) x (hj x)).mp x.property⟩)
    invFun := fun y => ⟨(e y.1).symm y.2,
      (hlocal y.1 _ ((e y.1).map_target (hfixsub y.1 y.2 y.2.property))).mpr (by
        simpa only [(e y.1).right_inv (hfixsub y.1 y.2 y.2.property)] using y.2.property)⟩
    left_inv := fun x => Subtype.ext ((e (j x)).left_inv (hj x))
    right_inv := by
      intro y
      dsimp
      have hindex : j ⟨(e y.1).symm y.2, by
          apply (hlocal y.1 _ ((e y.1).map_target (hfixsub y.1 y.2 y.2.property))).mpr
          simpa only [(e y.1).right_inv (hfixsub y.1 y.2 y.2.property)] using y.2.property⟩ = y.1 := by
        apply source_index_unique e hdis (hj _)
        exact (e y.1).map_target (hfixsub y.1 y.2 y.2.property)
      simp only [hindex, (e y.1).right_inv (hfixsub y.1 y.2 y.2.property)] }
  let : Finite B := hfinite
  let : Finite A := Finite.of_equiv (ι × B) a.symm
  refine ⟨Set.toFinite A, ?_⟩
  change Nat.card A = Nat.card ι * Nat.card B
  rw [Nat.card_congr a, Nat.card_prod]

end
end MorseArnold.CapGluing

end

end OAI
