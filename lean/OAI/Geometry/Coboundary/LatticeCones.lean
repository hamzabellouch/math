import OAI.Geometry.Coboundary.ChamberCones
import OAI.GroupTheory.Congruence.ProStability
import OAI.Combinatorics.Coboundary.Skeleton

namespace OAI

/-!
Bounded-chamber and codistance attachments, lattice acyclicity, and uniform positive coset exactness.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}

theorem based_at (P : Submodule K[X] (PolynomialVectors.V K (M+2))) (hP : PolyBounded P)
    (D : FullChamber K (M+2) (by omega))
    (hroot : normalizedPolynomial (by omega) P hP ∈ D.face) :
    ∃ E : ResidueChamber (K := K) (N := M+2), ∃ hE : PolyBounded E.top,
      E.top = P ∧ face E hE (by omega) = D.face ∧ E.length = D.length ∧
      descentCore E hE = D.descentCore := by
  classical
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hroot
  obtain ⟨m,hm⟩ := normalizedPolynomial_spec (by omega) P hP
  let E := (D.polynomialChamber.reroot (by omega) j.val).scale m
  have hE : PolyBounded E.top := (reroot_bounded D.polynomialChamber (polyBounded_vertex _) (by omega) j.val).powerShift m
  refine ⟨E,hE,?_,?_,?_,?_⟩
  · apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K (M+2))
    change (powerShift (D.polynomialChamber.reroot (by omega) j.val).top m).map _ = _
    rw [powerShift_map_embedding,D.polynomialChamber.reroot_top (by omega) j.val j.isLt.le]
    change level (shift K (M+2)) ((D.stage j.castSucc).map _) m = _
    rw [D.stage_castSucc,polynomialLattice_map,hj]
    exact hm.symm
  · change face ((D.polynomialChamber.reroot (by omega) j.val).scale m) _ _ = _
    rw [scale_face _ (reroot_bounded D.polynomialChamber (polyBounded_vertex _) (by omega) j.val) m (by omega),
      reroot_face D.polynomialChamber (polyBounded_vertex _) j.val,full_face]
  · change ((D.polynomialChamber.reroot (by omega) j.val).scale m).length = _
    rw [ResidueChamber.scale_length,ResidueChamber.reroot_length]
    rfl
  · change descentCore ((D.polynomialChamber.reroot (by omega) j.val).scale m) _ = _
    rw [scale_descentCore _ (reroot_bounded D.polynomialChamber (polyBounded_vertex _) (by omega) j.val) m,
      reroot_descentCore D.polynomialChamber (polyBounded_vertex _) j.val,full_descentCore]

theorem normalization_core (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top) :
    ∃ E : FullChamber K (M+2) (by omega), E.face = face C hC (by omega) ∧
      E.length = C.length ∧ E.descentCore = descentCore C hC := by
  classical
  obtain ⟨E,hf,hl⟩ := normalization C hC
  have hroot : normalizedPolynomial (by omega) C.top hC ∈ E.face := by
    rw [hf]
    exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,by
      change normalizedPolynomial _ (C.stage 0) _ = _
      simp only [C.initial]⟩
  obtain ⟨R,hR,ht,hface,_,hcore⟩ := based_at C.top hC E hroot
  have he : R = C := eq_of_face_of_top R C hR hC (by omega) ht (hface.trans hf)
  exact ⟨E,hf,hl,he ▸ hcore.symm⟩
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors
variable {K : Type} [Field K] {M : ℕ}
variable (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top)
def RootInterval (D : Submodule K[X] (PolynomialVectors.V K (M+2))) : Prop :=
  powerShift C.top 1 ≤ D ∧ D ≤ C.top ∧ D ≠ powerShift C.top 1
noncomputable def normalizeModule (D : Submodule K[X] (PolynomialVectors.V K (M+2))) : Vertex K (M+2) := by
  classical
  exact if hD : PolyBounded D then normalizedPolynomial (by omega) D hD
  else normalizedPolynomial (by omega) C.top hC
lemma normalizeModule_of_bounded (D : Submodule K[X] (PolynomialVectors.V K (M+2))) (hD : PolyBounded D) :
    normalizeModule C hC D = normalizedPolynomial (by omega) D hD := by
  simp only [normalizeModule,dite_eq_left hD]
include hC in
lemma rootInterval_bounded {D : Submodule K[X] (PolynomialVectors.V K (M+2))}
    (hD : RootInterval C D) : PolyBounded D := (hC.powerShift 1).mono hD.1
lemma normalizeModule_stage (E : ResidueChamber (K := K) (N := M+2)) (hE : PolyBounded E.top)
    (r : Fin (M+2)) : normalizeModule C hC (E.stage r.castSucc) = vertex E hE (by omega) r := by
  exact normalizeModule_of_bounded C hC _ (stage_bounded E hE _)
lemma normalizeModule_initial : normalizeModule C hC C.top = vertex C hC (by omega) 0 := by
  rw [← C.initial]
  exact normalizeModule_stage C hC C hC 0
lemma normalizeModule_terminal : normalizeModule C hC (powerShift C.top 1) = vertex C hC (by omega) 0 := by
  rw [normalizeModule_of_bounded C hC _ (hC.powerShift 1),normalizedPolynomial_power]
  exact (normalizeModule_of_bounded C hC _ hC).symm.trans (normalizeModule_initial C hC)
lemma rootInterval_stage (E : ResidueChamber (K := K) (N := M+2)) (ht : E.top = C.top)
    (r : Fin (M+2)) : RootInterval C (E.stage r.castSucc) := by
  rw [RootInterval,← ht]
  exact ⟨E.lower _,E.profile_stage_le_top _,nonterminal_ne E r⟩
lemma normalizeModule_injective : Set.InjOn (normalizeModule C hC) (RootInterval C) := by
  intro D hD E hE he
  have hd := rootInterval_bounded C hC hD
  have hε := rootInterval_bounded C hC hE
  rw [normalizeModule_of_bounded C hC D hd,normalizeModule_of_bounded C hC E hε] at he
  apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K (M+2))
  apply homothetic_interval_eq (C.top.map (polynomialEmbedding K (M+2)))
  · exact Submodule.map_mono hD.2.1
  · exact Submodule.map_mono hE.2.1
  · change level (shift K (M+2)) (C.top.map _) 1 ≤ _
    rw [← powerShift_map_embedding]
    exact Submodule.map_mono hD.1
  · change level (shift K (M+2)) (C.top.map _) 1 ≤ _
    rw [← powerShift_map_embedding]
    exact Submodule.map_mono hE.1
  · intro hh
    apply hD.2.2
    apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K (M+2))
    rw [powerShift_map_embedding]
    exact hh
  · intro hh
    apply hE.2.2
    apply Submodule.map_injective_of_injective (polynomialEmbedding_injective K (M+2))
    rw [powerShift_map_embedding]
    exact hh
  · exact homothetic_trans _ (normalizedPolynomial_homothetic (by omega) D hd)
      (he ▸ homothetic_symm _ (normalizedPolynomial_homothetic (by omega) E hε))
noncomputable def liftModule (v : Vertex K (M+2)) : Submodule K[X] (PolynomialVectors.V K (M+2)) := by
  classical
  exact if h : ∃ D, RootInterval C D ∧ normalizeModule C hC D = v then h.choose else C.top
lemma liftModule_normalize {D : Submodule K[X] (PolynomialVectors.V K (M+2))} (hD : RootInterval C D) :
    liftModule C hC (normalizeModule C hC D) = D := by
  classical
  have hex : ∃ E, RootInterval C E ∧ normalizeModule C hC E = normalizeModule C hC D := ⟨D,hD,rfl⟩
  rw [liftModule,dite_eq_left hex]
  exact normalizeModule_injective C hC hex.choose_spec.1 hD hex.choose_spec.2
lemma liftModule_vertex (E : ResidueChamber (K := K) (N := M+2)) (hE : PolyBounded E.top)
    (ht : E.top = C.top) (r : Fin (M+2)) :
    liftModule C hC (vertex E hE (by omega) r) = E.stage r.castSucc := by
  rw [← normalizeModule_stage C hC E hE r]
  exact liftModule_normalize C hC (rootInterval_stage C E ht r)
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors AffineWindow
variable {K : Type} [Field K] {M L : ℕ}
variable (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top)
lemma normalizeModule_stage_succ (r : Fin (M+2)) :
    normalizeModule C hC (C.stage r.succ) = vertex C hC (by omega) (finRotate (M+2) r) := by
  by_cases hr : r.val < M+1
  · rw [finRotate_of_lt hr]
    exact normalizeModule_stage C hC C hC ⟨r.val+1,by omega⟩
  · have he : r = Fin.last (M+1) := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
    subst r
    rw [finRotate_last]
    change normalizeModule C hC (C.stage (Fin.last (M+2))) = _
    rw [C.terminal]
    exact normalizeModule_terminal C hC
lemma descentCore_card : (descentCore C hC).card = (descents (by omega) C.window).card := by
  classical
  apply Finset.card_image_of_injective
  exact (vertex_injective C hC (by omega)).comp (finRotate (M+2)).injective
lemma root_mem_core_iff : vertex C hC (by omega) 0 ∈ descentCore C hC ↔
    Fin.last (M+1) ∈ descents (by omega) C.window := by
  classical
  constructor
  · intro hh
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hh
    have hh := vertex_injective C hC (by omega) he
    have hr' : r = Fin.last (M+1) := (finRotate (M+2)).injective (hh.trans finRotate_last.symm)
    exact hr' ▸ hr
  · intro hh
    exact Finset.mem_image.mpr ⟨Fin.last (M+1),hh,by rw [finRotate_last]⟩
lemma fixedStages_image (c : Fin (L+1) → Fin (M+3))
    (hc : Set.range c = cutSet (by omega) C.window) :
    (C.fixedStages c).image (normalizeModule C hC) = insert (vertex C hC (by omega) 0) (descentCore C hC) := by
  classical
  have hmem (r : Fin (M+3)) : (∃ j, c j = r) ↔ r ∈ cutSet (by omega) C.window := by
    change r ∈ Set.range c ↔ _
    rw [hc]
    rfl
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
    have hr := (hmem (c j)).mp ⟨j,rfl⟩
    rcases Finset.mem_insert.mp hr with hz | hr
    · rw [hz,C.initial,normalizeModule_initial]
      exact Finset.mem_insert_self _ _
    · rcases Finset.mem_insert.mp hr with hz | hr
      · rw [hz,C.terminal,normalizeModule_terminal]
        exact Finset.mem_insert_self _ _
      · obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hr
        rw [← he,normalizeModule_stage_succ]
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r,hr,rfl⟩)
  · intro v hv
    rcases Finset.mem_insert.mp hv with he | hv
    · obtain ⟨j,hj⟩ := (hmem 0).mpr (Finset.mem_insert_self _ _)
      apply Finset.mem_image.mpr
      refine ⟨C.top,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,by rw [hj,C.initial]⟩,?_⟩
      exact (normalizeModule_initial C hC).trans he.symm
    · obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨j,hj⟩ := (hmem r.succ).mpr (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r,hr,rfl⟩)))
      exact Finset.mem_image.mpr ⟨C.stage r.succ,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,by rw [hj]⟩,
        normalizeModule_stage_succ C hC r⟩
lemma cut_rank_eq_core_card (c : Fin (L+1) ↪o Fin (M+3))
    (hc : Set.range c = cutSet (by omega) C.window)
    (hroot : vertex C hC (by omega) 0 ∈ descentCore C hC) : L = (descentCore C hC).card := by
  classical
  have hl := (root_mem_core_iff C hC).mp hroot
  have he : Finset.univ.image c = cutSet (by omega) C.window := by
    ext r
    simpa only [Finset.mem_image,Finset.mem_univ,true_and] using
      (show (∃ j, c j = r) ↔ r ∈ cutSet (by omega) C.window from by
        change r ∈ Set.range c ↔ _
        rw [hc]
        rfl)
  have hcard := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ c.injective,Finset.card_univ,Fintype.card_fin] at hcard
  have hn : Fin.last (M+2) ∈ (descents (by omega) C.window).image Fin.succ :=
    Finset.mem_image.mpr ⟨Fin.last (M+1),hl,rfl⟩
  have hz : (0 : Fin (M+3)) ∉ (descents (by omega) C.window).image Fin.succ := by simp
  rw [cutSet,Finset.insert_eq_of_mem hn,Finset.card_insert_of_notMem hz,
    Finset.card_image_of_injective _ (Fin.succ_injective _)] at hcard
  rw [descentCore_card]
  omega
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors AffineWindow
variable {K : Type} [Field K] {M L : ℕ}
variable (C E : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top) (hE : PolyBounded E.top)
lemma fixed_stages_of_core (ht : E.top = C.top)
    (c : Fin (L+1) → Fin (M+3)) (hc : Set.range c = cutSet (by omega) C.window)
    (hcore : descentCore C hC ⊆ face E hE (by omega)) : ∀ j, E.stage (c j) = C.stage (c j) := by
  intro j
  have hr : c j ∈ cutSet (by omega) C.window := by change c j ∈ (cutSet (by omega) C.window : Set _); rw [← hc]; exact Set.mem_range_self j
  rcases Finset.mem_insert.mp hr with hz | hr
  · rw [hz,E.initial,C.initial,ht]
  · rcases Finset.mem_insert.mp hr with hz | hr
    · rw [hz,E.terminal,C.terminal,ht]
    · obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hr
      rw [← he]
      by_cases hh : r.val < M+1
      · have hmem := hcore (Finset.mem_image.mpr ⟨r,hr,rfl⟩)
        rw [finRotate_of_lt hh] at hmem
        exact (shared_vertex_stage C E hC hE (by omega) ht.symm ⟨r.val+1,by omega⟩ hmem).symm
      · have heq : r.succ = Fin.last (M+2) := Fin.ext (by have := r.isLt; change r.val+1=M+2; omega)
        rw [heq,E.terminal,C.terminal,ht]
lemma core_eq_of_window_fixed (ht : E.top = C.top) (hw : E.window = C.window)
    (c : Fin (L+1) → Fin (M+3)) (hc : Set.range c = cutSet (by omega) C.window)
    (hfix : ∀ j, E.stage (c j) = C.stage (c j)) : descentCore E hE = descentCore C hC := by
  classical
  unfold descentCore
  rw [hw]
  apply Finset.image_congr
  intro r hr
  dsimp only
  by_cases hh : r.val < M+1
  · have hmem : r.succ ∈ cutSet (by omega) C.window :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r,hr,rfl⟩))
    change r.succ ∈ (cutSet (by omega) C.window : Set _) at hmem
    rw [← hc] at hmem
    obtain ⟨j,hj⟩ := hmem
    have hs : E.stage r.succ = C.stage r.succ := hj ▸ hfix j
    rw [finRotate_of_lt hh]
    change normalizedPolynomial _ (E.stage _) _ = normalizedPolynomial _ (C.stage _) _
    have hi : (⟨r.val+1,by omega⟩ : Fin (M+2)).castSucc = r.succ := Fin.ext rfl
    simp only [hi,hs]
  · have he : r = Fin.last (M+1) := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
    subst r
    rw [finRotate_last]
    change normalizedPolynomial _ (E.stage 0) _ = normalizedPolynomial _ (C.stage 0) _
    simp only [E.initial,C.initial,ht]
lemma fixedStages_top (c : Fin (L+1) → Fin (M+3)) (h0 : c 0 = 0) : C.top ∈ C.fixedStages c := by
  classical
  exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,by rw [h0,C.initial]⟩
lemma fixedStages_bottom (c : Fin (L+1) → Fin (M+3)) (hl : c (Fin.last L) = Fin.last (M+2)) :
    powerShift C.top 1 ∈ C.fixedStages c := by
  classical
  exact Finset.mem_image.mpr ⟨Fin.last L,Finset.mem_univ _,by rw [hl,C.terminal]⟩
lemma fixedStages_interval (c : Fin (L+1) → Fin (M+3)) {D : Submodule K[X] (PolynomialVectors.V K (M+2))}
    (hD : D ∈ C.fixedStages c) (hne : D ≠ powerShift C.top 1) : RootInterval C D := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
  exact ⟨C.lower _,C.profile_stage_le_top _,hne⟩
lemma core_has_fixed_representative (c : Fin (L+1) → Fin (M+3)) (h0 : c 0 = 0)
    (hc : Set.range c = cutSet (by omega) C.window) {v : Vertex K (M+2)}
    (hv : v ∈ descentCore C hC) :
    ∃ D ∈ C.fixedStages c, RootInterval C D ∧ normalizeModule C hC D = v := by
  classical
  have hh : v ∈ (C.fixedStages c).image (normalizeModule C hC) := by
    rw [fixedStages_image C hC c hc]
    exact Finset.mem_insert_of_mem hv
  obtain ⟨D,hD,hvD⟩ := Finset.mem_image.mp hh
  by_cases he : D = powerShift C.top 1
  · refine ⟨C.top,fixedStages_top C c h0,?_,?_⟩
    · have hh := rootInterval_stage C C rfl 0
      change RootInterval C (C.stage 0) at hh
      rwa [C.initial] at hh
    · rw [normalizeModule_initial]
      rwa [he,normalizeModule_terminal] at hvD
  · exact ⟨D,hD,fixedStages_interval C c hD he,hvD⟩
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices.BoundedChamber
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors AffineWindow InfiniteChains InfiniteChains.Cone InfiniteChains.Attachment
variable {K : Type} [Field K] {M L m : ℕ}
variable (C : ResidueChamber (K := K) (N := M+2)) (hC : PolyBounded C.top)
lemma lift_link_witness (hroot : vertex C hC (by omega) 0 ∈ descentCore C hC)
    (hlen : C.length = m+1) {s : Finset (Vertex K (M+2))}
    (hs : s ∈ codistanceLink m (descentCore C hC)) :
    ∃ E : ResidueChamber (K := K) (N := M+2), ∃ hE : PolyBounded E.top,
      E.top = C.top ∧ E.length = C.length ∧ descentCore E hE = descentCore C hC ∧
      s ⊆ face E hE (by omega) := by
  obtain ⟨hd,D,hD,hcore,hface⟩ := hs
  have hr : normalizedPolynomial (by omega) C.top hC ∈ D.face := by
    have hh := D.descentCore_subset (hcore ▸ hroot)
    simpa only [vertex,C.initial,Fin.castSucc_zero] using hh
  obtain ⟨E,hE,ht,hf,hl,hδ⟩ := based_at C.top hC D hr
  exact ⟨E,hE,ht,hl.trans (hD.trans hlen.symm),hδ.trans hcore,hf ▸ hface⟩
lemma normalized_link_lift (hroot : vertex C hC (by omega) 0 ∈ descentCore C hC)
    (hlen : C.length = m+1) (c : Fin (L+1) → Fin (M+3))
    (hc : Set.range c = (cutSet (by omega) C.window : Set _))
    {s : Finset (Vertex K (M+2))} (hs : s ∈ codistanceLink m (descentCore C hC)) :
    s.image (liftModule C hC) ∈ (C.rootedMinimumLink c).faces := by
  classical
  obtain ⟨E,hE,ht,hl,hcore,hface⟩ := lift_link_witness C hC hroot hlen hs
  have hfix := fixed_stages_of_core C E hC hE ht c hc (hcore ▸ descentCore_subset E hE)
  have hret {v} (hv : v ∈ s) : normalizeModule C hC (liftModule C hC v) = v := by
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp (hface hv)
    rw [liftModule_vertex C hC E hE ht,normalizeModule_stage]
  refine ⟨?_,E,ht,hl,hfix,?_⟩
  · apply Finset.disjoint_left.mpr
    intro D hD hfixed
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hD
    have hn : normalizeModule C hC (liftModule C hC v) ∈
        (C.fixedStages c).image (normalizeModule C hC) := Finset.mem_image_of_mem _ hfixed
    rw [fixedStages_image C hC c hc,Finset.insert_eq_of_mem hroot,hret hv] at hn
    exact Finset.disjoint_left.mp hs.1 hn hv
  · intro D hD
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp (hface hv)
    exact ⟨r.castSucc,(liftModule_vertex C hC E hE ht r).symm⟩
lemma rooted_link_interval (c : Fin (L+1) → Fin (M+3))
    (hlast : c (Fin.last L) = Fin.last (M+2))
    {s : Finset (Submodule K[X] (PolynomialVectors.V K (M+2)))}
    (hs : s ∈ (C.rootedMinimumLink c).faces) {D} (hD : D ∈ s) : RootInterval C D := by
  obtain ⟨hd,E,ht,_,_,hface⟩ := hs
  obtain ⟨r,rfl⟩ := hface D hD
  refine ⟨ht ▸ E.lower r,ht ▸ E.profile_stage_le_top r,?_⟩
  intro he
  exact Finset.disjoint_left.mp hd hD (he ▸ fixedStages_bottom C c hlast)
lemma normalized_link_map (hlen : C.length = m+1)
    (c : Fin (L+1) → Fin (M+3)) (hmono : StrictMono c) (h0 : c 0 = 0)
    (hlast : c (Fin.last L) = Fin.last (M+2))
    (hc : Set.range c = (cutSet (by omega) C.window : Set _))
    (hsorted : ∀ j : Fin L, (slice C.window (c j.castSucc) (c j.succ)).Pairwise (· ≤ ·))
    {s : Finset (Submodule K[X] (PolynomialVectors.V K (M+2)))}
    (hs : s ∈ (C.rootedMinimumLink c).faces) :
    s.image (normalizeModule C hC) ∈ codistanceLink m (descentCore C hC) := by
  classical
  obtain ⟨hd,E,ht,hl,hfix,hface⟩ := hs
  have hE : PolyBounded E.top := ht ▸ hC
  have hw := (C.fixed_stage_minimum_iff_window E (by omega) ht.symm c hmono.monotone h0 hlast
    (fun j => (hfix j).symm) hsorted).mp hl
  have hcore := core_eq_of_window_fixed C E hC hE ht hw c hc hfix
  obtain ⟨B,hBf,hBl,hBcore⟩ := normalization_core E hE
  refine ⟨?_,B,hBl.trans (hl.trans hlen),hBcore.trans hcore,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hv'
    obtain ⟨F,hF,hFI,hFn⟩ := core_has_fixed_representative C hC c h0 hc hv
    have hDI := rooted_link_interval C c hlast ⟨hd,E,ht,hl,hfix,hface⟩ hD
    have he := normalizeModule_injective C hC hFI hDI hFn
    exact Finset.disjoint_left.mp hd hD (he ▸ hF)
  · intro v hv
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨r,rfl⟩ := hface D hD
    have hr : r.val < M+2 := by
      by_contra hh
      have he : r = Fin.last (M+2) := Fin.ext (by have := r.isLt; simp only [Fin.val_last]; omega)
      have hn := (rooted_link_interval C c hlast ⟨hd,E,ht,hl,hfix,hface⟩ hD).2.2
      apply hn
      rw [he,E.terminal,ht]
    let t : Fin (M+2) := ⟨r.val,hr⟩
    have he : r = t.castSucc := Fin.ext rfl
    rw [he,normalizeModule_stage C hC E hE,hBf]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ t)
theorem codistanceLink_exact_of_rooted (hroot : vertex C hC (by omega) 0 ∈ descentCore C hC)
    (hlen : C.length = m+1)
    (c : Fin (L+1) → Fin (M+3)) (hmono : StrictMono c) (h0 : c 0 = 0)
    (hlast : c (Fin.last L) = Fin.last (M+2))
    (hc : Set.range c = (cutSet (by omega) C.window : Set _))
    (hsorted : ∀ j : Fin L, (slice C.window (c j.castSucc) (c j.succ)).Pairwise (· ≤ ·))
    (r : ℕ) (H : ExactIn (C.rootedMinimumLink c).faces r) :
    ExactIn (codistanceLink m (descentCore C hC)) r := by
  classical
  have hret (s) (hs : s ∈ codistanceLink m (descentCore C hC)) (v) (hv : v ∈ s) :
      normalizeModule C hC (liftModule C hC v) = v := by
    obtain ⟨E,hE,ht,_,_,hface⟩ := lift_link_witness C hC hroot hlen hs
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (hface hv)
    rw [liftModule_vertex C hC E hE ht,normalizeModule_stage]
  apply exactIn_retract (liftModule C hC) (normalizeModule C hC) _ _
    (fun _ hs => normalized_link_lift C hC hroot hlen c hc hs)
    (fun _ hs => normalized_link_map C hC hlen c hmono h0 hlast hc hsorted hs) ?_ ?_ hret r H
  · intro s hs v hv w hw hh
    rw [← hret s hs v hv,← hret s hs w hw,hh]
  · intro s hs D hD E hE he
    exact normalizeModule_injective C hC (rooted_link_interval C c hlast hs hD)
      (rooted_link_interval C c hlast hs hE) he
end CoboundaryExpanders.RationalLattices.BoundedChamber

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices PolynomialVectors AffineWindow InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone

theorem uniform_codistanceLink_exact (M : ℕ) :
    ∃ Q : ℕ, ∀ (K : Type) [Field K] [Fintype K], Q < Fintype.card K →
      ∀ (m : ℕ) (C : FullChamber K (M+2) (by omega)), C.length = m+1 →
      ∀ r < M+2-C.descentCore.card, ExactIn (codistanceLink m C.descentCore) r := by
  classical
  obtain ⟨Q,hQ⟩ := ResidueChamber.uniform_rootedMinimumLink_exact (M+2)
  refine ⟨Q,?_⟩
  intro K _ _ hq m C hlen r hr
  obtain ⟨v,hv⟩ := C.descentCore_nonempty (by omega)
  obtain ⟨E,hE,ht,hface,hl,hcore⟩ := BoundedChamber.based_at
    (polynomialLattice K (M+2) v) (polyBounded_vertex v) C
    (by rw [normalizedPolynomial_vertex]; exact C.descentCore_subset hv)
  have hroot : BoundedChamber.vertex E hE (by omega) 0 ∈ BoundedChamber.descentCore E hE := by
    rw [hcore]
    have he : BoundedChamber.vertex E hE (by omega) 0 = v := by
      change normalizedPolynomial _ (E.stage 0) _ = _
      simp only [E.initial,ht,normalizedPolynomial_vertex]
    rwa [he]
  obtain ⟨L,c,h0,hlast,hc⟩ := cuts_enumeration (by omega) E.window
  have hsort : ∀ j : Fin L, (slice E.window (c j.castSucc) (c j.succ)).Pairwise (· ≤ ·) := by
    apply slices_sorted_of_descents (by omega) E.window c
    intro a ha
    rw [hc]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
  have hL := BoundedChamber.cut_rank_eq_core_card E hE c hc hroot
  rw [hcore] at hL
  have hlenE : E.length = m+1 := hl.trans hlen
  rw [← hcore]
  apply BoundedChamber.codistanceLink_exact_of_rooted E hE hroot hlenE c c.strictMono h0 hlast hc hsort r
  exact hQ K E L c (by omega) c.strictMono h0 hlast hsort hq r (by omega)
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {M : ℕ}

theorem codistanceBlock_relative_of_link (m : ℕ) (C : FullChamber K (M+2) (by omega))
    (hlen : C.length = m+1) (r : ℕ)
    (H : C.descentCore.card ≤ r → ExactIn (codistanceLink m C.descentCore) (r-C.descentCore.card)) :
    RelativeExactIn (codistanceStage K (M+2) (by omega) m) (codistanceBlock m C.descentCore) r := by
  classical
  let A := C.descentCore
  let O : InfiniteChains.Complex (Vertex K (M+2)) := {
    faces := codistanceLink m A
    empty_mem := ⟨Finset.disjoint_empty_right _,C,hlen,rfl,Finset.empty_subset _⟩
    downward := by
      intro s t hs ht
      exact ⟨hs.1.mono_right ht,codistanceBlock_downward m A hs.2 ht⟩ }
  have hf (s) (hs : s ∈ codistanceBlock m A) : s.image (tagBy A) ∈ joinFaces A O := by
    constructor
    · rw [tagBy_left]; exact Finset.inter_subset_right
    · rw [tagBy_right]
      exact ⟨(by apply Finset.disjoint_left.mpr; intro v hv hv'; exact (Finset.mem_sdiff.mp hv').2 hv),codistanceBlock_downward m A hs Finset.sdiff_subset⟩
  have hg (s) (hs : s ∈ joinFaces A O) : s.image (Sum.elim id id) ∈ codistanceBlock m A := by
    rw [untag_image,codistanceBlock_join]
    exact ⟨s.toLeft,s.toRight,hs.1,hs.2,rfl⟩
  have hgi (s) (hs : s ∈ joinFaces A O) : Set.InjOn (Sum.elim id id) (s : Set (Vertex K (M+2) ⊕ Vertex K (M+2))) := by
    intro x hx y hy he
    rcases x with x|x <;> rcases y with y|y
    · exact congrArg Sum.inl he
    · change x = y at he
      exact (Finset.disjoint_left.mp hs.2.1 (hs.1 (Finset.mem_toLeft.mpr hx))
        (he.symm ▸ Finset.mem_toRight.mpr hy)).elim
    · change x = y at he
      exact (Finset.disjoint_left.mp hs.2.1 (hs.1 (Finset.mem_toLeft.mpr hy))
        (he ▸ Finset.mem_toRight.mpr hx)).elim
    · exact congrArg Sum.inr he
  apply relativeExactIn_retract (tagBy A) (Sum.elim id id)
    (codistanceStage K (M+2) (by omega) m) (codistanceBlock m A) (oldFaces A O) (joinFaces A O)
    (codistanceBlock_downward m A) hf hg ?_ ?_
    (fun _ _ => (tagBy_injective A).injOn) hgi (fun _ hs => hs.1)
    (fun _ _ v _ => untag_tagBy A v) r (relativeExactIn_join A O r H)
  · intro s hs
    refine ⟨hf s hs.2,?_⟩
    rw [tagBy_left]
    intro he
    have hn := (codistanceBlock_old_iff m A hs.2).mp hs.1
    apply hn
    rw [← he]
    exact Finset.inter_subset_left
  · intro s hs
    apply (codistanceBlock_old_iff m A (hg s hs.1)).mpr
    rw [untag_image]
    intro hA
    apply hs.2
    apply Finset.Subset.antisymm hs.1.1
    intro v hv
    rcases Finset.mem_union.mp (hA hv) with hh|hh
    · exact hh
    · exact (Finset.disjoint_left.mp hs.1.2.1 hv hh).elim
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable {K : Type} [Field K] {M : ℕ}
theorem codistanceStage_relative_of_links (m r : ℕ)
    (H : ∀ (C : FullChamber K (M+2) (by omega)), C.length = m+1 →
      C.descentCore.card ≤ r → ExactIn (codistanceLink m C.descentCore) (r-C.descentCore.card)) :
    RelativeExactIn (codistanceStage K (M+2) (by omega) m)
      (codistanceStage K (M+2) (by omega) (m+1)) r := by
  classical
  have hblocks (A : Finset (Vertex K (M+2))) :
      RelativeExactIn (codistanceStage K (M+2) (by omega) m) (codistanceBlock m A) r := by
    by_cases hex : ∃ C : FullChamber K (M+2) (by omega), C.length = m+1 ∧ C.descentCore = A
    · obtain ⟨C,hC,rfl⟩ := hex
      exact codistanceBlock_relative_of_link m C hC r (H C hC)
    · have he : codistanceBlock m A = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro s ⟨C,hC,hA,_⟩
        exact hex ⟨C,hC,hA⟩
      rw [he]
      exact relativeExactIn_empty _ _
  have hU := relativeExactIn_iUnion (codistanceStage K (M+2) (by omega) m)
    (codistanceBlock m) r (fun A => codistanceBlock_downward m A)
    (codistanceBlock_intersection m) hblocks
  rw [codistanceStage_successor]
  apply relativeExactIn_union _ _ _ r (codistanceStage_downward K (M+2) (by omega) m) ?_
    (fun _ hs => hs.1) (Join.relativeExactIn_self _ r) hU
  intro s t hs ht
  obtain ⟨A,hA⟩ := Set.mem_iUnion.mp hs
  exact Set.mem_iUnion.mpr ⟨A,codistanceBlock_downward m A hA ht⟩

theorem uniform_codistanceStage_zero_exact (M : ℕ) :
    ∃ Q : ℕ, ∀ (K : Type) [Field K] [Fintype K], Q < Fintype.card K →
      ∀ r < M, ExactIn (codistanceStage K (M+2) (by omega) 0) (r+1) := by
  obtain ⟨Q,hQ⟩ := uniform_codistanceLink_exact M
  refine ⟨Q,?_⟩
  intro K _ _ hq r hr
  apply exactIn_initial_of_filtration _ (codistanceStage_mono K (M+2) (by omega)) (r+1)
  · intro m
    apply codistanceStage_relative_of_links m (r+1+1)
    intro C hC hc
    exact hQ K hq m C hC _ (by omega)
  · rw [codistanceStage_exhaust]
    exact building_exact K (M+2) (by omega) r
end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)

lemma positive_power_equation (f h : K[X]) (a b : ℕ) (hf : f ≠ 0)
    (he : algebraMap K[X] (RatFunc K) h * uniformizer K ^ b =
      positive K f * uniformizer K ^ a) : b ≤ a := by
  by_contra hab
  obtain ⟨c,hc⟩ := Nat.exists_eq_add_of_lt (lt_of_not_ge hab)
  have hf0 : f = 0 := positive_zero_of_uniformizer_dvd K f (h*Polynomial.X^c) (by
    apply mul_right_cancel₀ (pow_ne_zero a (uniformizer_ne_zero K))
    rw [← he,hc]
    simp only [map_mul,map_pow,uniformizer]
    ring)
  exact hf hf0

lemma mem_level_cut (cut : Fin N) (a : ℕ) (v : V K N) :
    v ∈ level (shift K N) (cutLattice K N cut) a ↔
      ∀ i, ∃ f : K[X], algebraMap K[X] (RatFunc K) f *
        uniformizer K ^ (a + cutExponent N cut i) = v i := by
  classical
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (mem_level K N _ _ _).mp hv
    intro i
    obtain ⟨f,hf⟩ := hw i
    refine ⟨f,?_⟩
    simp only [Pi.smul_apply,Algebra.smul_def,map_pow]
    rw [← hf,pow_add]
    change _ = uniformizer K ^ a * _
    ring
  · intro hv
    choose f hf using hv
    let w : V K N := fun i => algebraMap K[X] (RatFunc K) (f i) * uniformizer K ^ cutExponent N cut i
    refine (mem_level K N _ _ _).mpr ⟨w,(fun i => ⟨f i,rfl⟩),?_⟩
    funext i
    simp only [Pi.smul_apply,Algebra.smul_def,map_pow]
    rw [← hf i,pow_add]
    change uniformizer K ^ a * _ = _
    dsimp only [w]
    ring

lemma positiveAction_cut_le_exponents
    (g : Matrix.SpecialLinearGroup (Fin N) K[X]) (c d : Fin N) (a b : ℕ)
    (hle : level (shift K N) (positiveAction K N g (cutLattice K N c)) a ≤
      level (shift K N) (cutLattice K N d) b) (i j : Fin N) (hg : g i j ≠ 0) :
    b + cutExponent N d i ≤ a + cutExponent N c j := by
  classical
  let v : V K N := Pi.single j (uniformizer K ^ cutExponent N c j)
  have hv : v ∈ cutLattice K N c := by
    intro k
    by_cases hk : k = j
    · subst k; exact ⟨1,by simp [v]⟩
    · exact ⟨0,by simp [v,hk]⟩
  have hv' : (Polynomial.X^a : K[X]) • positiveLinear K N g v ∈
      level (shift K N) (positiveAction K N g (cutLattice K N c)) a :=
    (mem_level K N _ _ _).mpr ⟨positiveLinear K N g v,
      (mem_positiveAction K N g _ _).mpr ⟨v,hv,rfl⟩,rfl⟩
  obtain ⟨f,hf⟩ := (mem_level_cut K N d b _).mp (hle hv') i
  apply positive_power_equation K (g i j) f _ _ hg
  convert hf using 1
  simp only [positiveLinear_apply,v,Matrix.mulVec_single,Pi.smul_apply,Algebra.smul_def,
    map_pow,positiveMatrix]
  change positive K (g i j) * uniformizer K ^ (a + cutExponent N c j) =
    uniformizer K ^ a * (positive K (g i j) * uniformizer K ^ cutExponent N c j)
  rw [pow_add]
  ring

lemma positiveAction_mul (g h : Matrix.SpecialLinearGroup (Fin N) K[X]) (A : LatticeSpace K N) :
    positiveAction K N (g*h) A = positiveAction K N g (positiveAction K N h A) := by
  ext v
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (mem_positiveAction K N _ _ _).mp hv
    exact (mem_positiveAction K N _ _ _).mpr ⟨positiveLinear K N h w,
      (mem_positiveAction K N _ _ _).mpr ⟨w,hw,rfl⟩,(positiveLinear_mul K N g h w).symm⟩
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (mem_positiveAction K N _ _ _).mp hv
    obtain ⟨z,hz,rfl⟩ := (mem_positiveAction K N _ _ _).mp hw
    exact (mem_positiveAction K N _ _ _).mpr ⟨z,hz,positiveLinear_mul K N g h z⟩

@[simp] lemma positiveAction_one (A : LatticeSpace K N) : positiveAction K N 1 A = A := by
  ext v
  simp only [mem_positiveAction,positiveLinear_one,exists_eq_right]

lemma actVertex_one (hN : 0 < N) (A : Vertex K N) : actVertex K N hN 1 A = A := by
  apply (homothetic_normalized_iff (shift K N) (standard K N) (shift_standard_le K N) _ _).mp
  apply homothetic_symm
  simpa only [positiveAction_one] using actVertex_homothetic K N hN 1 A

lemma actVertex_mul (hN : 0 < N) (g h : Matrix.SpecialLinearGroup (Fin N) K[X]) (A : Vertex K N) :
    actVertex K N hN (g*h) A = actVertex K N hN g (actVertex K N hN h A) := by
  apply (homothetic_normalized_iff (shift K N) (standard K N) (shift_standard_le K N) _ _).mp
  refine homothetic_trans _ (homothetic_symm _ (actVertex_homothetic K N hN (g*h) A)) ?_
  rw [positiveAction_mul]
  exact homothetic_trans _
    (homothetic_map _ _ (positiveAction_shift K N g) (actVertex_homothetic K N hN h A))
    (actVertex_homothetic K N hN g (actVertex K N hN h A))

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.Construction
open CoboundaryExpanders.RationalLattices CoboundaryExpanders.AffineLattices
variable (p n : ℕ) [Fact p.Prime]

lemma U_diagonal_ne_zero (g : Matrix.SpecialLinearGroup (Fin (n+1)) (R p))
    (hu : g ∈ U p (n+1)) (i : Fin (n+1)) : g i i ≠ 0 := by
  intro hz
  have he := hu i i le_rfl
  change Polynomial.eval 0 (g i i) = _ at he
  simp [hz] at he

lemma homothetic_cut_recognition (hn : 1 ≤ n) (g : Matrix.SpecialLinearGroup (Fin (n+1)) (R p))
    (hu : g ∈ U p (n+1)) (c d : Fin (n+1)) :
    Homothetic (shift (ZMod p) (n+1))
      (positiveAction (ZMod p) (n+1) g (cutLattice (ZMod p) (n+1) c)) (cutLattice (ZMod p) (n+1) d) ↔
      c = d ∧ g ∈ localGroup p n hn c := by
  constructor
  · rintro ⟨a,b,he⟩
    have hi : ∀ i, b + cutExponent (n+1) d i ≤ a + cutExponent (n+1) c i :=
      fun i => positiveAction_cut_le_exponents (ZMod p) (n+1) g c d a b he.le i i (U_diagonal_ne_zero p n g hu i)
    have he' : level (shift (ZMod p) (n+1))
        (positiveAction (ZMod p) (n+1) g⁻¹ (cutLattice (ZMod p) (n+1) d)) b =
        level (shift (ZMod p) (n+1)) (cutLattice (ZMod p) (n+1) c) a := by
      have hh := congrArg (positiveAction (ZMod p) (n+1) g⁻¹) he.symm
      rw [map_level _ _ (positiveAction_shift _ _ _),map_level _ _ (positiveAction_shift _ _ _),
        positiveAction_inv,OrderIso.symm_apply_apply] at hh
      simpa only [positiveAction_inv] using hh
    have hj : ∀ i, a + cutExponent (n+1) c i ≤ b + cutExponent (n+1) d i :=
      fun i => positiveAction_cut_le_exponents (ZMod p) (n+1) g⁻¹ d c b a he'.le i i
        (U_diagonal_ne_zero p n g⁻¹ ((U p (n+1)).inv_mem hu) i)
    have hab : a = b := by
      have h₁ := hi (Fin.last n)
      have h₂ := hj (Fin.last n)
      simp only [cutExponent,Fin.val_last,ite_eq_right (show ¬ n < d.val by omega),
        ite_eq_right (show ¬ n < c.val by omega),add_zero] at h₁ h₂
      omega
    subst b
    have hcd : c = d := by
      apply le_antisymm
      · by_contra h
        have hh := hi d
        simp only [cutExponent,lt_self_iff_false,ite_false,
          ite_eq_left (show d.val < c.val from lt_of_not_ge h)] at hh
        have hh' := hj d
        simp only [cutExponent,lt_self_iff_false,ite_false,
          ite_eq_left (show d.val < c.val from lt_of_not_ge h)] at hh'
        omega
      · by_contra h
        have hh := hi c
        simp only [cutExponent,lt_self_iff_false,ite_false,
          ite_eq_left (show c.val < d.val from lt_of_not_ge h)] at hh
        omega
    refine ⟨hcd,?_⟩
    subst d
    have heq := level_injective (shift (ZMod p) (n+1)) a he
    apply (preserves_cutLattice_iff_localGroup p n hn c g hu).mp
    intro v hv
    change positiveLinear (ZMod p) (n+1) g v ∈ _
    rw [← heq]
    exact (mem_positiveAction _ _ _ _ _).mpr ⟨v,hv,rfl⟩
  · rintro ⟨rfl,hg⟩
    have hle : positiveAction (ZMod p) (n+1) g (cutLattice (ZMod p) (n+1) c) ≤ cutLattice (ZMod p) (n+1) c := by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := (mem_positiveAction _ _ _ _ _).mp hv
      exact (preserves_cutLattice_iff_localGroup p n hn c g hu).mpr hg w hw
    have hge : cutLattice (ZMod p) (n+1) c ≤ positiveAction (ZMod p) (n+1) g (cutLattice (ZMod p) (n+1) c) := by
      have hle' : positiveAction (ZMod p) (n+1) g⁻¹ (cutLattice (ZMod p) (n+1) c) ≤ cutLattice (ZMod p) (n+1) c := by
        intro v hv
        obtain ⟨w,hw,rfl⟩ := (mem_positiveAction _ _ _ _ _).mp hv
        exact (preserves_cutLattice_iff_localGroup p n hn c g⁻¹ ((U p (n+1)).inv_mem hu)).mpr
          ((localGroup p n hn c).inv_mem hg) w hw
      simpa only [positiveAction_inv,OrderIso.apply_symm_apply] using (positiveAction (ZMod p) (n+1) g).monotone hle'
    exact ⟨0,0,le_antisymm hle hge⟩

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.Construction
open CoboundaryExpanders.RationalLattices CoboundaryExpanders.AffineLattices
variable (p n : ℕ) [Fact p.Prime]

lemma act_cut_eq_iff (hn : 1 ≤ n) (g h : U p (n+1)) (c d : Fin (n+1)) :
    actVertex (ZMod p) (n+1) (by omega) g.val (cutVertex (ZMod p) (n+1) c) =
    actVertex (ZMod p) (n+1) (by omega) h.val (cutVertex (ZMod p) (n+1) d) ↔
    c = d ∧ g⁻¹*h ∈ uLocalGroup p n hn c := by
  constructor
  · intro he
    have he' : cutVertex (ZMod p) (n+1) c =
        actVertex (ZMod p) (n+1) (by omega) (g.val⁻¹*h.val) (cutVertex (ZMod p) (n+1) d) := by
      have hh := congrArg (actVertex (ZMod p) (n+1) (by omega) g.val⁻¹) he
      simpa only [← actVertex_mul,inv_mul_cancel,actVertex_one] using hh
    have hh := actVertex_homothetic (ZMod p) (n+1) (by omega) (g.val⁻¹*h.val)
      (cutVertex (ZMod p) (n+1) d)
    rw [← he'] at hh
    obtain ⟨hdc,hh⟩ := (homothetic_cut_recognition p n hn (g.val⁻¹*h.val)
      ((U p (n+1)).mul_mem ((U p (n+1)).inv_mem g.property) h.property) d c).mp hh
    subst d
    exact ⟨rfl,hh⟩
  · rintro ⟨rfl,hgh⟩
    have hh := (homothetic_cut_recognition p n hn (g.val⁻¹*h.val)
      ((U p (n+1)).mul_mem ((U p (n+1)).inv_mem g.property) h.property) c c).mpr ⟨rfl,hgh⟩
    have hh' : actVertex (ZMod p) (n+1) (by omega) (g.val⁻¹*h.val)
        (cutVertex (ZMod p) (n+1) c) = cutVertex (ZMod p) (n+1) c := by
      apply (homothetic_normalized_iff _ _ (shift_standard_le (ZMod p) (n+1)) _ _).mp
      exact homothetic_trans _ (homothetic_symm _ (actVertex_homothetic _ _ _ _ _)) hh
    have hhh := congrArg (actVertex (ZMod p) (n+1) (by omega) g.val) hh'
    simpa only [← actVertex_mul,mul_inv_cancel_left] using hhh.symm

noncomputable def oppositionVertex (hn : 1 ≤ n) :
    TypedCosetFaces.Vertex (uLocalGroup p n hn) → RationalLattices.Vertex (ZMod p) (n+1) :=
  fun x => Quotient.lift (fun g : U p (n+1) =>
    actVertex (ZMod p) (n+1) (by omega) g.val (cutVertex (ZMod p) (n+1) x.1))
    (fun g h he => (act_cut_eq_iff p n hn g h x.1 x.1).mpr
      ⟨rfl,QuotientGroup.leftRel_apply.mp he⟩) x.2

@[simp] lemma oppositionVertex_mk (hn : 1 ≤ n) (g : U p (n+1)) (c : Fin (n+1)) :
    oppositionVertex p n hn (TypedCosetFaces.vertex (uLocalGroup p n hn) g c) =
      actVertex (ZMod p) (n+1) (by omega) g.val (cutVertex (ZMod p) (n+1) c) := rfl

lemma oppositionVertex_injective (hn : 1 ≤ n) : Function.Injective (oppositionVertex p n hn) := by
  rintro ⟨c,g⟩ ⟨d,h⟩ he
  induction g using Quotient.inductionOn with | h g =>
  induction h using Quotient.inductionOn with | h h =>
  obtain ⟨hcd,hgh⟩ := (act_cut_eq_iff p n hn g h c d).mp he
  subst d
  congr 1
  exact Quotient.sound (QuotientGroup.leftRel_apply.mpr hgh)

lemma oppositionVertex_face (hn : 1 ≤ n) (s : Finset (TypedCosetFaces.Vertex (uLocalGroup p n hn)))
    (hs : s ∈ (TypedCosetFaces.complex (uLocalGroup p n hn)).faces) :
    s.image (oppositionVertex p n hn) ∈ (building (ZMod p) (n+1)).faces := by
  obtain ⟨g,A,rfl⟩ := hs
  rw [TypedCosetFaces.face,Finset.image_image]
  change (A.image (fun c => actVertex (ZMod p) (n+1) (by omega) g.val (cutVertex (ZMod p) (n+1) c))) ∈ _
  change A.image (actVertex (ZMod p) (n+1) (by omega) g.val ∘ cutVertex (ZMod p) (n+1)) ∈ _
  rw [← Finset.image_image]
  apply actVertex_face
  apply (building (ZMod p) (n+1)).downward (baseChamber_face (ZMod p) (n+1))
  exact Finset.image_subset_image (Finset.subset_univ A)

def opposition : InfiniteChains.Complex (RationalLattices.Vertex (ZMod p) (n+1)) where
  faces := {s | ∃ g : U p (n+1), ∃ A : Finset (Fin (n+1)),
    A.image (fun c => actVertex (ZMod p) (n+1) (by omega) g.val (cutVertex (ZMod p) (n+1) c)) = s}
  empty_mem := ⟨1,∅,Finset.image_empty _⟩
  downward := by
    rintro s t ⟨g,A,rfl⟩ ht
    obtain ⟨B,hB,he⟩ := Finset.subset_image_iff.mp ht
    exact ⟨g,B,he⟩

lemma opposition_mem_image (hn : 1 ≤ n) (s : Finset (RationalLattices.Vertex (ZMod p) (n+1))) :
    s ∈ (opposition p n).faces ↔ ∃ t ∈ (TypedCosetFaces.complex (uLocalGroup p n hn)).faces,
      t.image (oppositionVertex p n hn) = s := by
  constructor
  · rintro ⟨g,A,rfl⟩
    exact ⟨TypedCosetFaces.face (uLocalGroup p n hn) g A,⟨g,A,rfl⟩,by
      rw [TypedCosetFaces.face,Finset.image_image]; rfl⟩
  · rintro ⟨t,⟨g,A,rfl⟩,rfl⟩
    exact ⟨g,A,by rw [TypedCosetFaces.face,Finset.image_image]; rfl⟩

lemma opposition_subcomplex (s : Finset (RationalLattices.Vertex (ZMod p) (n+1)))
    (hs : s ∈ (opposition p n).faces) : s ∈ (building (ZMod p) (n+1)).faces := by
  obtain ⟨g,A,rfl⟩ := hs
  change A.image (actVertex (ZMod p) (n+1) (by omega) g.val ∘ cutVertex (ZMod p) (n+1)) ∈ _
  rw [← Finset.image_image]
  apply actVertex_face
  exact (building (ZMod p) (n+1)).downward (baseChamber_face (ZMod p) (n+1))
    (Finset.image_subset_image (Finset.subset_univ A))

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.Construction
open RationalLattices InfiniteChains InfiniteChains.Attachment InfiniteChains.Cone
variable (p n : ℕ) [Fact p.Prime]
theorem opposition_faces_eq_codistance_zero :
    (opposition p n).faces = codistanceStage (ZMod p) (n+1) (by omega) 0 := by
  ext s
  rw [codistanceStage_zero,← common_orbit_iff_induced]
  constructor
  · rintro ⟨g,A,hA⟩
    refine ⟨g.val,?_,A,hA⟩
    have hg := g.property
    change ∀ i j : Fin (n+1), j ≤ i → Polynomial.eval 0 (g.val i j) = (1 : Matrix _ _ (ZMod p)) i j at hg
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hg
  · rintro ⟨g,hg,A,hA⟩
    have hu : g ∈ U p (n+1) := by
      change ∀ i j : Fin (n+1), j ≤ i → Polynomial.eval 0 (g i j) = (1 : Matrix _ _ (ZMod p)) i j
      simpa only [Polynomial.coeff_zero_eq_eval_zero] using hg
    exact ⟨⟨g,hu⟩,A,hA⟩

theorem uniform_infinite_coset_exact (n : ℕ) (hn : 2 ≤ n) :
    ∃ Q : ℕ, ∀ (p : ℕ) [Fact p.Prime], Q < p →
      ∀ r < n-1, ExactIn (TypedCosetFaces.complex (uLocalGroup p n (by omega))).faces (r+1) := by
  classical
  obtain ⟨k,rfl⟩ : ∃ k : ℕ, n = k+2 := ⟨n-2,by omega⟩
  obtain ⟨Q,hQ⟩ := uniform_codistanceStage_zero_exact (k+2-1)
  refine ⟨Q,?_⟩
  intro p _ hq r hr
  have hh := hQ (ZMod p) (by simpa only [ZMod.card] using hq) r hr
  rw [← opposition_faces_eq_codistance_zero] at hh
  have hk : 1 ≤ k+2 := by omega
  let : Nonempty (TypedCosetFaces.Vertex (uLocalGroup p (k+2) hk)) :=
    ⟨TypedCosetFaces.vertex (uLocalGroup p (k+2) hk) 1 0⟩
  apply exactIn_of_image (oppositionVertex p (k+2) hk) (oppositionVertex_injective p (k+2) hk)
    _ _ ?_ ?_ (r+1) hh
  · intro s hs
    exact (opposition_mem_image p (k+2) hk _).mpr ⟨s,hs,rfl⟩
  · intro s hs
    exact (opposition_mem_image p (k+2) hk s).mp hs

theorem uniform_infinite_coset_positive (n : ℕ) (hn : 2 ≤ n) :
    ∃ Q : ℕ, ∀ (p : ℕ) [Fact p.Prime], Q < p →
      ∀ j : ℕ, 0 < j → j < n-1 →
        (TypedCosetFaces.complex (uLocalGroup p n (by omega))).chainComplex.ExactAt j := by
  obtain ⟨Q,hQ⟩ := uniform_infinite_coset_exact n hn
  refine ⟨Q,?_⟩
  intro p _ hq j hj hjn
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact chainComplex_exactAt_of_exactIn _ r (hQ p hq (r+1) hjn)
end CoboundaryExpanders.Construction

end

noncomputable section


namespace CoboundaryExpanders
open Construction

theorem reduction_to_actual_integral_pro_stability
    (hstab : ∀ d : ℕ, 3 ≤ d → ∀ Q : ℕ,
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ Q < p ∧
        ∀ j : ℕ, 0 < j → j < d →
          IntegralProStability.ProIso p (2*d-1) j ∧
          IntegralProStability.ProIso p (2*d) j) : MainStatement := by
  apply reduction_to_positive_open_inputs
  intro d hd
  obtain ⟨Q₁,hQ₁⟩ := uniform_infinite_coset_positive (2*d) (by omega)
  obtain ⟨Q₂,hQ₂⟩ := actual_uniform_cosystolic (2*d) (by omega)
  obtain ⟨p,hp,ho,hQ,hs⟩ := hstab d hd (max Q₁ Q₂)
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨p,hp,ho,?_,?_,?_⟩
  · exact hQ₁ p (lt_of_le_of_lt (le_max_left _ _) hQ)
  · intro i hi hid
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by omega)
    have hprev : IntegralProStability.ProIso p (2*d-1) j ∧
        IntegralProStability.ProIso p (2*d) j := by
      by_cases hj : 0 < j
      · exact hs j hj (by omega)
      · have he : j = 0 := by omega
        subst j
        exact ⟨IntegralProStability.proIso_zero p _,IntegralProStability.proIso_zero p _⟩
    exact ⟨IntegralProStability.proZero_of_integral p (2*d-1) j hprev.1
        (hs (j+1) (by omega) hid).1,
      IntegralProStability.proZero_of_integral p (2*d) j hprev.2
        (hs (j+1) (by omega) hid).2⟩
  · exact hQ₂ p inferInstance (lt_of_le_of_lt (le_max_right _ _) hQ)
end CoboundaryExpanders

end

end OAI
