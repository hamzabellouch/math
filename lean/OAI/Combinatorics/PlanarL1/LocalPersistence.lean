import OAI.Combinatorics.PlanarL1.MainPersistence
import OAI.Combinatorics.PlanarL1.ScaleHistory
import OAI.Combinatorics.PlanarL1.SecondaryGain

namespace OAI


section

namespace PlanarL1.Columns.Model.SecondaryCell
open PlanarL1.Interpolation
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (T : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root)) (old L : M.Point J root → ℝ) (ordinary : Bool)
lemma namedReplacement_eq_old_of_value (pc radius αo αh lo : ℝ)
    (α : Point.RadialTree.Noise (n := n)) (x : M.Point J root)
    (he : replacement T S old L ordinary pc radius αo αh lo α x=old x) :
    namedReplacement T S old L ordinary pc radius αo αh lo α x=⟨0,old x⟩ := by
  apply clippedNamed_eq_old_of_value rfl
  exact (namedReplacement_value T S old L ordinary pc radius αo αh lo α x).trans he

lemma namedReplacement_boundary_ball (hS : S.Nonempty) (hOld : LipschitzWith 5 old)
    (hL : LipschitzWith 1 L) (hζ : T.ζ = (1:ℝ)/10)
    {pc radius αo : ℝ} (hr : 0 ≤ radius) (hαo : αo ≤ radius/1000)
    (hδ : T.δ = (radius/1000)/8) {α : Point.RadialTree.Noise (n := n)} (hα : T.NoiseBounds α)
    (hord : ordinary = true → ∀ x, L x ≤ old x)
    (hadmit : ordinary = false → ∀ w ∈ S, ∀ x, dist w x = radius → pc-(65/100:ℝ)*radius ≤ old x)
    (αh lo : ℝ) (x y : M.Point J root) {ρ : ℝ}
    (hsmall : 18*ρ ≤ (199/1000:ℝ)*radius)
    (hy : dist x y ≤ ρ) (hout : radius ≤ seedDistance S y)
    (z : M.Point J root) (hz : dist x z ≤ ρ) (hin : seedDistance S z ≤ radius) :
    namedReplacement T S old L ordinary pc radius αo αh lo α z=⟨0,old z⟩ :=
  namedReplacement_eq_old_of_value T S old L ordinary pc radius αo αh lo α z
    (replacement_boundary_ball T S old L ordinary hS hOld hL hζ hr hαo hδ hα hord hadmit
      αh lo x y hsmall hy hout z hz hin)
end PlanarL1.Columns.Model.SecondaryCell

namespace PlanarL1.Columns.Model.BState
open MeasureTheory PlanarL1.Interpolation
open scoped NNReal
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {κ : ℝ} {lam : ℝ≥0}
  {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {S : BState M κ lam Ω μ}
namespace SecondaryBatch
variable (B : SecondaryBatch S)
lemma chosen_name (i : Fin (k+1)) (H : B.data.band) (a : B.NewIndex)
    (ha : B.chosen i H.val a) :
    (B.selected i H).name=familyName a.1 (a.2.val+1) := by
  obtain ⟨hb,_,he⟩ := ha
  exact congrArg NamedValue.name he
lemma newIndex_names_injective : Function.Injective (fun a : B.NewIndex => familyName a.1 (a.2.val+1)) := by
  intro a b hab
  obtain ⟨ha,hb⟩ := (familyName_inj a.1 b.1 (by omega) (by omega)).mp hab
  rcases a with ⟨a,i⟩
  rcases b with ⟨b,j⟩
  dsimp only at ha hb
  subst b
  have he : i=j := Fin.ext (by omega)
  subst j
  rfl
lemma chosen_iff_name (i : Fin (k+1)) (H : B.data.band) (a : B.NewIndex) :
    B.chosen i H.val a ↔ (B.selected i H).name=familyName a.1 (a.2.val+1) := by
  constructor
  · exact B.chosen_name i H a
  · intro he
    have hn : (B.selected i H).name≠0 := by rw [he]; exact familyName_ne_zero _ (by omega)
    obtain ⟨b,hb⟩ := B.exists_chosen i H hn
    have he' : b=a := B.newIndex_names_injective ((B.chosen_name i H b hb).symm.trans he)
    exact he' ▸ hb
lemma choose_eq_of_name {i j : Fin (k+1)} (H T : B.data.band)
    (hn : (B.selected i H).name=(B.selected j T).name) :
    B.choose i H.val=B.choose j T.val := by
  have he : B.chosen i H.val=B.chosen j T.val := by
    funext a
    exact propext ((B.chosen_iff_name i H a).trans (hn ▸ (B.chosen_iff_name j T a).symm))
  unfold choose
  simp only [he]
lemma choose_none_of_old_name {i : Fin (k+1)} {H : ℝ} (hne : S.name i H≠B.index) :
    B.choose i H=none := by
  have hn : ¬∃ a, B.chosen i H a := by
    rintro ⟨a,ha⟩
    exact hne (B.domain_name (B.mem_domain.mpr ⟨a.1,B.chosen_domain i H a ha⟩))
  exact dite_eq_right hn
end SecondaryBatch
namespace SecondaryLayer
variable (B : SecondaryLayer S)
lemma choose_eq {i j : Fin (k+1)} {H T : ℝ}
    (he : ∀ a, (B.batch a).choose i H=(B.batch a).choose j T) :
    B.choose i H=B.choose j T := by
  have h : B.chosen i H=B.chosen j T := by
    funext a
    simp only [chosen,he a.1]
  unfold choose
  simp only [h]
lemma name_eq [SFinite μ] {i j : Fin (k+1)} {H T : ℝ}
    (hold : S.name i H=S.name j T) (he : B.choose i H=B.choose j T) :
    B.apply.name i H=B.apply.name j T := by
  dsimp only [apply,BState.append,BState.lift]
  rw [he,hold]
lemma name_eq_of_selected [SFinite μ] {i j : Fin (k+1)} {H T : ℝ}
    (a : Fin (S.count+1)) (hH : H ∈ (B.batch a).data.band) (hT : T ∈ (B.batch a).data.band)
    (hi : S.name i H=a) (hj : S.name j T=a)
    (hn : ((B.batch a).selected i ⟨H,hH⟩).name=((B.batch a).selected j ⟨T,hT⟩).name) :
    B.apply.name i H=B.apply.name j T := by
  apply B.name_eq (hi.trans hj.symm)
  apply B.choose_eq
  intro b
  by_cases hb : b=a
  · subst b
    exact (B.batch a).choose_eq_of_name _ _ hn
  · rw [(B.batch b).choose_none_of_old_name (by simpa only [hi,B.same_index] using Ne.symm hb),
      (B.batch b).choose_none_of_old_name (by simpa only [hj,B.same_index] using Ne.symm hb)]
end SecondaryLayer
end PlanarL1.Columns.Model.BState

end



section

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters
variable {k : ℕ} {M : Model (k+1)} {q p L U : ℝ}
namespace Block
variable (b : Block (M := M) q p L U)
/-- At a doubly height-interior point, a narrow-band path can reach a seed
only in this very processed broad/component/narrow block. -/
lemma eq_of_path_small (d : Block (M := M) q p L U)
    (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))
    (e : M.Point (BandTrees.band broad d.lower) (BandTrees.root M broad d.lower d.1.2))
    (hc : c.height ∈ BandTrees.band narrow b.lower₂)
    (hd : c.height ∈ BandTrees.band narrow d.lower₂)
    {ρ τ : ℝ} (hρ : 0≤ρ) (hτ : 0≤τ)
    (hp : Tiling.Padded a₁ q c.height ρ)
    (hn : Tiling.Padded a₂ p c.height τ)
    (path : M.Path (BandTrees.band narrow d.lower₂) c.column e.column) : b=d := by
  have hNb : b.2.val.val=Tiling.index a₂ p c.height :=
    Tiling.unique_band_of_padded interpolationB.2.1 hτ hn (b.narrow_eq ▸ hc)
  have hNd : d.2.val.val=Tiling.index a₂ p c.height :=
    Tiling.unique_band_of_padded interpolationB.2.1 hτ hn (d.narrow_eq ▸ hd)
  have hBb : b.1.1.val=Tiling.index a₁ q c.height :=
    Tiling.unique_band_of_padded interpolationA.2.1 hρ hp (b.broad_eq ▸ c.inBand)
  have hBd : d.1.1.val=Tiling.index a₁ q c.height :=
    Tiling.unique_band_of_padded interpolationA.2.1 hρ hp (d.broad_eq ▸ d.sub hd)
  have hB : b.1.1=d.1.1 := Subtype.ext (hBb.trans hBd.symm)
  rcases b with ⟨⟨bi,bC⟩,bn⟩
  rcases d with ⟨⟨di,dC⟩,dn⟩
  dsimp only at hB
  subst di
  have hC : bC=dC := by
    have hr := c.reachable.trans ((path.widen (Block.sub ⟨⟨bi,dC⟩,dn⟩)).word.reachable.trans e.reachable.symm)
    have hm := SimpleGraph.ConnectedComponent.sound hr
    have hb : (M.activeGraph (BandTrees.band broad (MainFamily.lower q L U bi))).connectedComponentMk
        (BandTrees.root M broad (MainFamily.lower q L U bi) bC)=bC := BandTrees.root_mem _ _ _ _
    have hd' : (M.activeGraph (BandTrees.band broad (MainFamily.lower q L U bi))).connectedComponentMk
        (BandTrees.root M broad (MainFamily.lower q L U bi) dC)=dC := BandTrees.root_mem _ _ _ _
    exact hb.symm.trans (hm.trans hd')
  subst dC
  have hN : bn=dn := Subtype.ext (Subtype.ext (hNb.trans hNd.symm))
  subst dn
  rfl
end Block
end PlanarL1.Columns.Model.RetainedSelection

namespace PlanarL1.Columns.Model.RetainedSelection
open Parameters MeasureTheory
attribute [local instance] Classical.propDecidable
variable {k : ℕ} {M : Model (k+1)} {V Ω Ξ : Type*}
variable [Fintype V] [MeasurableSpace Ω] [MeasurableSpace Ξ]
variable {μ : Measure Ω} {ν : Measure Ξ}
variable (A : Ambient M) (SA : OrdinaryState M kappaA Ω μ)
variable (SB : BState M kappaB SecondaryGeometry.Group.lam Ξ ν)
variable (v : V → M.Point Set.univ A.root)
variable {L U : ℝ} (hv : ∀ x, (v x).height ∈ Set.Icc L U)
variable {q p : ℝ} {phaseD phaseG : MainFamily.BandComponent (M := M) q L U → ℝ}
variable (b : Block (M := M) q p L U)
variable (c : M.Point (BandTrees.band broad b.lower) (BandTrees.root M broad b.lower b.1.2))

variable (hc : c.height ∈ BandTrees.band narrow b.lower₂)
variable {ρ τ : ℝ} (hρ : 0≤ρ) (hτ : 0≤τ)
variable (hp : Tiling.Padded a₁ q c.height ρ) (hn : Tiling.Padded a₂ p c.height τ)
include hc hρ hτ hp hn

lemma touch_block_small {i : GroupIndex A SA SB v hv (p := p) (phaseD := phaseD) (phaseG := phaseG)}
    (h : Touch A SA SB v hv b c i) : i.1=b := by
  obtain ⟨w,_,path,_⟩ := h.2
  exact (b.eq_of_path_small i.1 c (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) i.1 w).point hc h.1 hρ hτ hp hn path).symm

noncomputable def localHit_small (i : Hits A SA SB v hv b c (phaseD := phaseD) (phaseG := phaseG)) :
    SurvivingGroups.Hits (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b) c := by
  have he := touch_block_small A SA SB v hv b c hc hρ hτ hp hn i.property
  rcases i with ⟨⟨d,j⟩,hi⟩
  dsimp only at he
  subst d
  exact ⟨j,hi.2⟩

lemma localHit_injective_small : Function.Injective
    (localHit_small A SA SB v hv b c hc hρ hτ hp hn (phaseD := phaseD) (phaseG := phaseG)) := by
  intro i j he
  have hi := touch_block_small A SA SB v hv b c hc hρ hτ hp hn i.property
  have hj := touch_block_small A SA SB v hv b c hc hρ hτ hp hn j.property
  rcases i with ⟨⟨d,i⟩,hi'⟩
  rcases j with ⟨⟨e,j⟩,hj'⟩
  dsimp only at hi hj
  subst d
  subst e
  have hraw : i=j := congrArg Subtype.val he
  subst j
  rfl

/-- Universal packing for the whole actual, finitely selected family. Both
old identifiers are derived by the local packing theorem, not assumed. -/
lemma touching_card_small : Fintype.card (Hits A SA SB v hv b c (phaseD := phaseD) (phaseG := phaseG))≤
    SurvivingGroups.packBound := by
  let := SurvivingGroups.instFintypeHits
    (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b) c
  have hb := SurvivingGroups.touching_card
    (localSeeds A SA SB v hv (phaseD := phaseD) (phaseG := phaseG) b) b.sub c hc
  apply le_trans _ hb
  exact Fintype.card_le_of_injective _ (localHit_injective_small A SA SB v hv b c hc hρ hτ hp hn)

lemma touching_finset_card_small :
    (Finset.univ.filter (Touch A SA SB v hv b c (phaseD := phaseD) (phaseG := phaseG))).card≤
      SurvivingGroups.packBound := by
  simpa only [Hits,Fintype.card_subtype] using touching_card_small A SA SB v hv b c hc hρ hτ hp hn

end PlanarL1.Columns.Model.RetainedSelection

end



section

namespace PlanarL1.FiniteRandom
attribute [local irreducible] prob
lemma prob_update_bound_pi {I : Type*} {D : I → Type*} [Fintype I] [DecidableEq I]
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)] (i : I) (P : (∀ i, D i) → Prop) {b : ℝ}
    (h : ∀ α, prob (fun r : D i => P (Function.update α i r)) ≤ b) : prob P≤b := by
  classical
  let e := (Equiv.piSplitAt i D).trans (Equiv.prodComm _ _)
  rw [←prob_equiv e.symm P]
  apply prob_prod_bound
  intro rest
  let α : ∀ i, D i := e.symm (rest, Classical.arbitrary (D i))
  have hu (r : D i) : e.symm (rest,r)=Function.update α i r := by
    funext j
    by_cases hj : j=i
    · subst j; simp [e,α,Equiv.piSplitAt]
    · simp [e,α,Equiv.piSplitAt,hj]
  simpa only [hu] using h α
end PlanarL1.FiniteRandom

namespace PlanarL1.Interpolation
attribute [local irreducible] FiniteRandom.prob
lemma familyAtomPair_probability_pi {X I : Type*} {D : I → Type*} {k : ℕ}
    [Fintype I] [DecidableEq I] [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (ι : Fin k → I) (hinj : Function.Injective ι)
    (old : X → ℝ) (A : ∀ g : Fin k, D (ι g) → ℕ → X → ℝ) (S : Fin k → Finset ℕ)
    (x : X) {t b : ℝ}
    (hpair : ∀ g i, i ∈ S g → ∀ j, j ∈ S g → i ≠ j →
      FiniteRandom.prob (fun ω => |A g ω i x-A g ω j x| ≤ t) ≤ b)
    (hconst : ∀ g i, i ∈ S g → i ≠ 0 → ∀ c : ℝ,
      FiniteRandom.prob (fun ω => |A g ω i x-c| ≤ t) ≤ b)
    (i j : ℕ) (hi : i ∈ familyNames S) (hj : j ∈ familyNames S) (hne : i ≠ j) :
    FiniteRandom.prob (fun ω : ∀ i, D i =>
      |familyAtom old (fun g => A g (ω (ι g))) i x-familyAtom old (fun g => A g (ω (ι g))) j x| ≤ t) ≤ b := by
  classical
  rcases mem_familyNames.mp hi with rfl | ⟨g,a,ha,rfl⟩
  · obtain ⟨h,c,hc,hcj⟩ := (mem_familyNames.mp hj).resolve_left (Ne.symm hne)
    subst j
    have hc0 : c ≠ 0 := by intro he; subst c; simp only [familyName_zero] at hne; exact hne rfl
    simp only [familyAtom_zero,familyAtom_name old _ h hc0]
    apply FiniteRandom.prob_update_bound_pi (ι h)
    intro ω
    simpa only [Function.update_self,abs_sub_comm] using hconst h c hc hc0 (old x)
  · rcases mem_familyNames.mp hj with rfl | ⟨h,c,hc,rfl⟩
    · have ha0 : a ≠ 0 := by intro he; subst a; simp only [familyName_zero] at hne; exact hne rfl
      simp only [familyAtom_name old _ g ha0,familyAtom_zero]
      apply FiniteRandom.prob_update_bound_pi (ι g)
      intro ω
      simpa only [Function.update_self] using hconst g a ha ha0 (old x)
    · by_cases ha0 : a=0
      · subst a
        have hc0 : c ≠ 0 := by intro he; subst c; simp only [familyName_zero] at hne; exact hne rfl
        simp only [familyName_zero,familyAtom_zero,familyAtom_name old _ h hc0]
        apply FiniteRandom.prob_update_bound_pi (ι h)
        intro ω
        simpa only [Function.update_self,abs_sub_comm] using hconst h c hc hc0 (old x)
      · by_cases hc0 : c=0
        · subst c
          simp only [familyName_zero,familyAtom_zero,familyAtom_name old _ g ha0]
          apply FiniteRandom.prob_update_bound_pi (ι g)
          intro ω
          simpa only [Function.update_self] using hconst g a ha ha0 (old x)
        · simp only [familyAtom_name old _ g ha0,familyAtom_name old _ h hc0]
          by_cases hgh : g=h
          · subst h
            have hac : a ≠ c := by intro he; subst c; exact hne rfl
            apply FiniteRandom.prob_update_bound_pi (ι g)
            intro ω
            simpa only [Function.update_self] using hpair g a ha c hc hac
          · apply FiniteRandom.prob_update_bound_pi (ι g)
            intro ω
            simpa only [Function.update_self,Function.update_of_ne (fun he => hgh (hinj he).symm)] using
              hconst g a ha ha0 (A h (ω (ι h)) c x)


lemma familyNames_card_sparse {k N : ℕ} (S : Fin k → Finset ℕ) (T : Finset (Fin k))
    (hS : ∀ g ∈ T, (S g).card≤N) (hout : ∀ g, g∉T → S g⊆{0}) :
    (familyNames S).card≤1+T.card*N := by
  classical
  have hsub : familyNames S⊆insert 0 (T.biUnion (fun g => (S g).image (familyName g))) := by
    intro i hi
    rcases mem_familyNames.mp hi with rfl | ⟨g,j,hj,rfl⟩
    · exact Finset.mem_insert_self _ _
    · by_cases hg : g∈T
      · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_image.mpr ⟨j,hj,rfl⟩⟩)
      · have hj0 : j=0 := Finset.mem_singleton.mp (hout g hg hj)
        rw [hj0,familyName_zero]
        exact Finset.mem_insert_self _ _
  calc
    _ ≤ (insert 0 (T.biUnion (fun g => (S g).image (familyName g)))).card := Finset.card_le_card hsub
    _ ≤ (T.biUnion (fun g => (S g).image (familyName g))).card+1 := Finset.card_insert_le _ _
    _ ≤ (∑ g∈T, ((S g).image (familyName g)).card)+1 := Nat.add_le_add_right Finset.card_biUnion_le 1
    _ ≤ (∑ _g∈T, N)+1 := Nat.add_le_add_right (Finset.sum_le_sum (fun g hg =>
      (Finset.card_image_le (s := S g) (f := familyName g)).trans (hS g hg))) 1
    _ = 1+T.card*N := by simp [Nat.add_comm]

lemma selection_near_tie_modulus {X : Type*} (F : X → NamedValue)
    (atom : ℕ → X → ℝ) (S : Finset ℕ) (x : X) (P : X → Prop) (hx : P x) {e : ℝ}
    (hF : ∀ z, P z → |(F x).value-(F z).value|≤e)
    (hA : ∀ i∈S, ∀ z, P z → |atom i z-atom i x|≤e)
    (hlist : ∀ z, P z → (F z).name∈S ∧ (F z).value=atom (F z).name z)
    (hbad : ∃ z, P z ∧ (F z).name≠(F x).name) :
    ∃ i∈S, ∃ j∈S, i≠j ∧ |atom i x-atom j x|≤2*e := by
  obtain ⟨z,hz,hn⟩ := hbad
  refine ⟨(F x).name,(hlist x hx).1,(F z).name,(hlist z hz).1,Ne.symm hn,?_⟩
  have hf := hF z hz
  have ha := hA (F z).name (hlist z hz).1 z hz
  rw [←(hlist z hz).2] at ha
  rw [←(hlist x hx).2]
  have ht := abs_sub_le (F x).value (F z).value (atom (F z).name x)
  linarith

lemma selection_probability_modulus {X Ω : Type*} [Fintype Ω]
    (F : Ω → X → NamedValue) (atom : Ω → ℕ → X → ℝ) (S : Finset ℕ)
    (x : X) (P : X → Prop) (hx : P x) {e b : ℝ} (hb : 0≤b)
    (hF : ∀ ω z, P z → |(F ω x).value-(F ω z).value|≤e)
    (hA : ∀ ω i, i∈S → ∀ z, P z → |atom ω i z-atom ω i x|≤e)
    (hlist : ∀ ω z, P z → (F ω z).name∈S ∧ (F ω z).value=atom ω (F ω z).name z)
    (hpair : ∀ i∈S, ∀ j∈S, i≠j →
      FiniteRandom.prob (fun ω => |atom ω i x-atom ω j x|≤2*e)≤b) :
    FiniteRandom.prob (fun ω => ∃ z, P z ∧ (F ω z).name≠(F ω x).name)≤S.card^2*b := by
  apply (FiniteRandom.prob_mono (fun ω h => selection_near_tie_modulus (F ω) (atom ω) S x P hx
    (hF ω) (hA ω) (hlist ω) h)).trans
  exact FiniteRandom.prob_pair_bound S _ hb hpair

lemma maxSelection_modulus {X : Type*} (old : X → NamedValue)
    (Fs : List (X → NamedValue)) (x z : X) {e : ℝ}
    (ho : |(old x).value-(old z).value|≤e)
    (hF : ∀ F∈Fs, |(F x).value-(F z).value|≤e) :
    |(maxSelection old Fs x).value-(maxSelection old Fs z).value|≤e := by
  induction Fs with
  | nil => exact ho
  | cons F Fs ih =>
    simp only [maxSelection,maxNamed_value]
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le (hF F (by simp))
      (ih (fun G hG => hF G (List.mem_cons_of_mem _ hG))))

lemma familySelection_modulus {X : Type*} {k : ℕ} (old : X → ℝ)
    (F : Fin k → X → NamedValue) (x z : X) {e : ℝ}
    (ho : |old x-old z|≤e) (hF : ∀ g, |(F g x).value-(F g z).value|≤e) :
    |(familySelection old F x).value-(familySelection old F z).value|≤e := by
  apply maxSelection_modulus _ _ _ _ ho
  intro G hG
  obtain ⟨g,rfl⟩ := List.mem_ofFn.mp hG
  exact hF g

lemma familyAtom_modulus {X : Type*} {k : ℕ} (old : X → ℝ)
    (A : Fin k → ℕ → X → ℝ) (x z : X) {e : ℝ}
    (ho : |old z-old x|≤e) (hA : ∀ g i, |A g i z-A g i x|≤e) (i : ℕ) :
    |familyAtom old A i z-familyAtom old A i x|≤e := by
  simp only [familyAtom]
  split_ifs with h h'
  · exact ho
  · exact hA _ _
  · exact ho

/-- Sparse, genuinely independent component samples in the literal maximum.
The full family numbering is retained even for groups irrelevant to the ball. -/
lemma familySelection_probability_sparse {X I : Type*} {D : I → Type*}
    [Fintype I] [DecidableEq I] [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    {k N B : ℕ} (ι : Fin k → I) (hinj : Function.Injective ι)
    (old : X → ℝ) (F : ∀ g : Fin k, D (ι g) → X → NamedValue)
    (A : ∀ g : Fin k, D (ι g) → ℕ → X → ℝ)
    (S : Fin k → Finset ℕ) (T : Finset (Fin k))
    (hcard : ∀ g∈T, (S g).card≤N) (hout : ∀ g, g∉T → S g⊆{0}) (hT : T.card≤B)
    (x : X) (P : X → Prop) (hx : P x) {e b : ℝ} (hb : 0≤b)
    (ho : ∀ z, P z → |old x-old z|≤e)
    (hF : ∀ g ω z, P z → |(F g ω x).value-(F g ω z).value|≤e)
    (hA : ∀ g ω i z, P z → |A g ω i z-A g ω i x|≤e)
    (hzero : ∀ g ω z, A g ω 0 z=old z)
    (hlist : ∀ g ω z, P z → (F g ω z).name∈S g ∧ (F g ω z).value=A g ω (F g ω z).name z)
    (hpair : ∀ g i, i∈S g → ∀ j, j∈S g → i≠j →
      FiniteRandom.prob (fun ω => |A g ω i x-A g ω j x|≤2*e)≤b)
    (hconst : ∀ g i, i∈S g → i≠0 → ∀ c : ℝ,
      FiniteRandom.prob (fun ω => |A g ω i x-c|≤2*e)≤b) :
    FiniteRandom.prob (fun ω : ∀ i, D i => ∃ z, P z ∧
      (familySelection old (fun g => F g (ω (ι g))) z).name≠
        (familySelection old (fun g => F g (ω (ι g))) x).name) ≤ (1+B*N : ℕ)^2*b := by
  have hp := selection_probability_modulus
    (fun ω : ∀ i, D i => familySelection old (fun g => F g (ω (ι g))))
    (fun ω => familyAtom old (fun g => A g (ω (ι g)))) (familyNames S) x P hx hb
    (fun ω z hz => familySelection_modulus old _ x z (ho z hz) (fun g => hF g _ z hz))
    (fun ω i _ z hz => familyAtom_modulus old _ x z ((abs_sub_comm _ _).trans_le (ho z hz))
      (fun g j => hA g _ j z hz) i)
    (fun ω z hz => familySelection_list old _ _ S (fun g y => hzero g _ y) z (fun g => hlist g _ z hz))
    (fun i hi j hj hij => familyAtomPair_probability_pi ι hinj old A S x hpair hconst i j hi hj hij)
  refine hp.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg (familyNames S).card) ?_ 2) hb)
  exact_mod_cast (familyNames_card_sparse S T hcard hout).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right N hT) 1)
end PlanarL1.Interpolation

end



section

namespace PlanarL1.Interpolation
/-- A local finite atom expansion, including its proved one-coordinate tests.
This is proof data for an actual named field, not a substitute for a chart. -/
structure LocalList {X W : Type*} [Fintype W] (old : X → ℝ)
    (F : W → X → NamedValue) (x : X) (e b : ℝ) where
  names : Finset ℕ
  atom : W → ℕ → X → ℝ
  zero : ∀ w z, atom w 0 z=old z
  selected : ∀ w z, (F w z).name∈names ∧ (F w z).value=atom w (F w z).name z
  field_variation : ∀ w z, |(F w x).value-(F w z).value|≤e
  atom_variation : ∀ w i z, |atom w i z-atom w i x|≤e
  pair_test : ∀ i∈names, ∀ j∈names, i≠j →
    FiniteRandom.prob (fun w => |atom w i x-atom w j x|≤2*e)≤b
  constant_test : ∀ i∈names, i≠0 → ∀ c : ℝ,
    FiniteRandom.prob (fun w => |atom w i x-c|≤2*e)≤b

noncomputable def oldLocalList {X W : Type*} [Fintype W] (old : X → ℝ)
    (x : X) {e b : ℝ} (ho : ∀ z, |old x-old z|≤e) :
    LocalList old (fun (_ : W) z => ⟨0,old z⟩) x e b where
  names := {0}
  atom _ _ z := old z
  zero _ _ := rfl
  selected _ _ := ⟨Finset.mem_singleton_self _,rfl⟩
  field_variation _ z := ho z
  atom_variation _ _ z := (abs_sub_comm _ _).trans_le (ho z)
  pair_test _i hi _j hj hn := False.elim (hn ((Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm))
  constant_test _i hi hn := False.elim (hn (Finset.mem_singleton.mp hi))

lemma LocalList.family_probability {X I : Type*} {D : I → Type*}
    [Fintype I] [DecidableEq I] [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    {k N B : ℕ} (ι : Fin k → I) (hinj : Function.Injective ι)
    (old : X → ℝ) (F : ∀ g : Fin k, D (ι g) → X → NamedValue)
    (x : X) {e b : ℝ} (hb : 0≤b) (ho : ∀ z, |old x-old z|≤e)
    (L : ∀ g, LocalList old (F g) x e b) (T : Finset (Fin k))
    (hc : ∀ g∈T, (L g).names.card≤N) (hout : ∀ g, g∉T → (L g).names⊆{0}) (hT : T.card≤B) :
    FiniteRandom.prob (fun w : ∀ i, D i => ∃ z,
      (familySelection old (fun g => F g (w (ι g))) z).name≠
        (familySelection old (fun g => F g (w (ι g))) x).name)≤(1+B*N : ℕ)^2*b := by
  simpa only [true_and] using familySelection_probability_sparse ι hinj old F
    (fun g => (L g).atom) (fun g => (L g).names) T hc hout hT x (fun _ => True) trivial hb
    (fun z _ => ho z) (fun g w z _ => (L g).field_variation w z)
    (fun g w i z _ => (L g).atom_variation w i z) (fun g => (L g).zero)
    (fun g w z _ => (L g).selected w z) (fun g => (L g).pair_test) (fun g => (L g).constant_test)
end PlanarL1.Interpolation

namespace PlanarL1.Columns.Model.SecondaryCell
open PlanarL1.Interpolation
open scoped NNReal
variable {n : ℕ} {M : Model n} {J : Set ℝ} {root : Fin n}
variable (R : Point.RadialTree (M := M) (J := J) (root := root))
variable (S : Finset (M.Point J root)) (old L : M.Point J root → ℝ)

/-- Literal secondary field has a bounded local atom expansion on any lifted
ball. The chosen radial node and the whole list precede all fresh offsets. -/
lemma sampled_local_list {X : Type*} (lift : X → M.Point J root) (x : X) {ρ : ℝ}
    (hρ : 0≤ρ) (hs : ρ≤R.radius) (hd : ∀ z, dist (lift x) (lift z)≤ρ)
    (ordinary : Bool) (hOld : LipschitzWith 5 old) (hL : LipschitzWith 1 L)
    (hζ : R.ζ=(1:ℝ)/10) (pc radius lo B : ℝ) (hB : 0 < B) (m : ℕ) (hm : 0 < m) :
    ∃ C : LocalList (fun z => old (lift z))
      (fun (w : Point.RadialTree.GridSample (n := n) R.depthCap m × Fin (m+1) × Fin (m+1)) z =>
        namedReplacement R S old L ordinary pc radius (B/m*w.2.1.val) (B/m*w.2.2.val) lo
          (R.gridNoise R.depthCap m w.1) (lift z)) x ((replacementConstant R : ℝ)*ρ)
      (((4*(replacementConstant R : ℝ)*ρ+R.q/m)/R.q)+(4*(replacementConstant R : ℝ)*ρ+B/m)/B),
      C.names.card≤6*(R.lookback+1)+3 := by
  classical
  obtain ⟨k,A,hlo,heq⟩ := R.common_formula (lift x) hρ hs
  have hk : k < R.depthCap := (R.depth_le_layerDepth (lift x) (hlo _ (by simpa using hρ))).trans_lt
    (R.layerDepth_lt_cap _)
  let atom := fun (w : Point.RadialTree.GridSample (n := n) R.depthCap m × Fin (m+1) × Fin (m+1))
    (i : ℕ) z => localAtom R S old L A pc radius (B/m*w.2.1.val) (B/m*w.2.2.val) lo
      (R.gridNoise R.depthCap m w.1) i (lift z)
  have ha (w : Point.RadialTree.GridSample (n := n) R.depthCap m × Fin (m+1) × Fin (m+1)) (i : ℕ) : LipschitzWith (replacementConstant R)
      (localAtom R S old L A pc radius (B/m*w.2.1.val) (B/m*w.2.2.val) lo
        (R.gridNoise R.depthCap m w.1) i) := localAtom_lipschitz R S old L hOld hL A _ _ _ _ _ _ i
  refine ⟨{ names := secondaryNames (R.recentNames A R.lookback)
            atom := atom
            zero := ?_
            selected := ?_
            field_variation := ?_
            atom_variation := ?_
            pair_test := ?_
            constant_test := ?_ }, ?_⟩
  · intro w z
    simp [atom,localAtom,secondaryAtom]
  · intro w z
    exact namedReplacement_local_list R S old L hζ A (lift x) hlo heq ordinary _ _ _ _ _ _
      (R.gridNoise_bounds _ _ hm _) (lift z) (hd z)
  · intro w z
    exact ((sampledReplacement_lipschitz R S old L ordinary hOld hL pc radius lo B _ m hm w).dist_le_mul
      (lift x) (lift z)).trans (mul_le_mul_of_nonneg_left (hd z) (NNReal.coe_nonneg _))
  · intro w i z
    have hh := (ha w i).dist_le_mul (lift z) (lift x)
    rw [Real.dist_eq,dist_comm (lift z)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hd z) (NNReal.coe_nonneg _))
  · intro i hi j hj hij
    simpa only [atom,show 2*(2*((replacementConstant R : ℝ)*ρ))=4*(replacementConstant R : ℝ)*ρ by ring] using
      localAtomPair_probability R S old L A (lift x) pc radius lo B hB _ m hk hm i j hi hj hij
        (show 0≤2*((replacementConstant R : ℝ)*ρ) by positivity)
  · intro i hi hi0 c
    simpa only [atom,show 2*(2*((replacementConstant R : ℝ)*ρ))=4*(replacementConstant R : ℝ)*ρ by ring] using
      localAtomConstant_probability R S old L A (lift x) pc radius lo B hB _ m hk hm i hi hi0 c
        (show 0≤2*((replacementConstant R : ℝ)*ρ) by positivity)
  · exact (secondaryNames_card _).trans (Nat.add_le_add_right (R.recentNames_card A R.lookback) 3)
end PlanarL1.Columns.Model.SecondaryCell

end

end OAI
