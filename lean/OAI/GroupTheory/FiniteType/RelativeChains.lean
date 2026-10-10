import Mathlib
import OAI.GroupTheory.FiniteType.SingularExcision

namespace OAI

noncomputable section
open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace RelativeChains
open Set CategoryTheory HomologicalComplex SingularChains
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma map_id (A : Set X) : map A A (ContinuousMap.id X) (fun _ h => h) = 𝟙 _ := by
  ext n c
  obtain ⟨c,rfl⟩ := projection_surjective A n c
  erw [map_projection]
  rw [SingularChains.map_id]
  rfl

lemma map_comp (A : Set X) (B : Set Y) (D : Set Z) (f : C(X,Y)) (g : C(Y,Z))
    (hf : MapsTo f A B) (hg : MapsTo g B D) :
    map A B f hf ≫ map B D g hg = map A D (g.comp f) (hg.comp hf) := by
  ext n c
  obtain ⟨c,rfl⟩ := projection_surjective A n c
  change (map B D g hg).f n ((map A B f hf).f n ((projection A).f n c)) = _
  simp only [map_projection,SingularChains.map_comp]
  rfl

lemma homeomorph_quasiIso (A : Set X) (B : Set Y) (e : X ≃ₜ Y) (he : ∀ x,x ∈ A ↔ e x ∈ B) :
    QuasiIso (map A B (e : C(X,Y)) (fun x hx => (he x).mp hx)) := by
  apply map_quasiIso
  · have eqr : restrictMap A B (e : C(X,Y)) (fun x hx => (he x).mp hx) = ((e.subtype he) : C(A,B)) := rfl
    rw [eqr]
    let := SingularChains.map_iso (e.subtype he)
    infer_instance
  · let := SingularChains.map_iso e
    infer_instance

lemma excision_map_quasiIso (A D : Set X) (B E : Set Y) (f : C(X,Y)) (hf : MapsTo f A B)
    (hD : IsClosed D) (hDA : D ⊆ interior A) (hE : IsClosed E) (hEB : E ⊆ interior B)
    (e : ↑(Dᶜ) ≃ₜ ↑(Eᶜ)) (he : ∀ x : ↑(Dᶜ),(e x).1 = f x.1)
    (hep : ∀ x : ↑(Dᶜ),x.1 ∈ A ↔ (e x).1 ∈ B) : QuasiIso (map A B f hf) := by
  let A' : Set ↑(Dᶜ) := (SingularSubspace.inclusionMap Dᶜ) ⁻¹' A
  let B' : Set ↑(Eᶜ) := (SingularSubspace.inclusionMap Eᶜ) ⁻¹' B
  let m := map A' B' (e : C(↑(Dᶜ),↑(Eᶜ))) (fun x hx => (hep x).mp hx)
  have hm : QuasiIso m := homeomorph_quasiIso A' B' e hep
  let := hm
  let := SingularExcision.excise_closed A D hD hDA
  let := SingularExcision.excise_closed B E hE hEB
  have comm : inclusion A Dᶜ ≫ map A B f hf = m ≫ inclusion B Eᶜ := by
    ext n c
    obtain ⟨c,rfl⟩ := projection_surjective A' n c
    change (map A B f hf).f n ((inclusion A Dᶜ).f n ((projection A').f n c)) =
      (inclusion B Eᶜ).f n (m.f n ((projection A').f n c))
    simp only [inclusion,m]
    have hemap : f.comp (SingularSubspace.inclusionMap Dᶜ) =
        (SingularSubspace.inclusionMap Eᶜ).comp (e : C(↑(Dᶜ),↑(Eᶜ))) := by
      apply ContinuousMap.ext
      intro x
      exact (he x).symm
    have h := congrArg (fun k : chains ↑(Dᶜ) ⟶ chains Y => k.f n c)
      (congrArg SingularChains.map hemap)
    simp only [SingularChains.map_comp] at h
    exact congrArg ((projection B).f n) h
  have : QuasiIso (inclusion A Dᶜ ≫ map A B f hf) := by rw [comm]; infer_instance
  exact quasiIso_of_comp_left (inclusion A Dᶜ) (map A B f hf)

lemma enlarge_quasiIso {A B : Set X} (h : A ⊆ B)
    (hh : QuasiIso (SingularChains.map (⟨Set.inclusion h,continuous_subtype_val.subtype_mk _⟩ : C(A,B)))) :
    QuasiIso (map A B (ContinuousMap.id X) h) := by
  apply map_quasiIso A B (ContinuousMap.id X) h hh
  rw [SingularChains.map_id]
  infer_instance

end RelativeChains

open Set Topology Metric

namespace CWExtension
section
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] {C : Set X} [CWComplex C]

abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Boundary (n : ℕ) := sphere (0 : Fin n → ℝ) 1

def charMap (n : ℕ) (i : RelCWComplex.cell C n) : C(Disk n,C) :=
  ⟨fun v => ⟨RelCWComplex.map n i v,
     RelCWComplex.closedCell_subset_complex n i ⟨v,v.2,rfl⟩⟩,
   (continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn n i)).subtype_mk _⟩

theorem isClosed_of_cells (S : Set C)
    (hS : ∀ n i, IsClosed (charMap n i ⁻¹' S)) : IsClosed S := by
  apply isClosed_induced_iff.mpr
  refine ⟨Subtype.val '' (S), ?_, ?_⟩
  · apply (CWComplex.closed C _ (by
      rintro _ ⟨x,hx,rfl⟩
      exact x.2)).mpr
    intro n i
    have hk : IsCompact (charMap n i ⁻¹' S) :=
      (hS n i).isCompact
    have he : (Subtype.val '' (S)) ∩ RelCWComplex.closedCell n i =
        (fun v : Disk n => RelCWComplex.map n i v) '' (charMap n i ⁻¹' S) := by
      ext x
      constructor
      · rintro ⟨⟨z,hz,hzx⟩,v,hv,hvx⟩
        refine ⟨⟨v,hv⟩,?_,hvx⟩
        have : charMap n i ⟨v,hv⟩ = z := Subtype.ext (hvx.trans hzx.symm)
        change charMap n i ⟨v,hv⟩ ∈ S
        rw [this]
        exact hz
      · rintro ⟨v,hv,rfl⟩
        exact ⟨⟨charMap n i v,hv,rfl⟩,v,v.2,rfl⟩
    rw [he]
    exact (hk.image (continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn n i))).isClosed
  · ext x
    simp

theorem continuous_of_cells (f : C → Y)
    (hf : ∀ n i, Continuous (f ∘ charMap n i)) : Continuous f := by
  apply continuous_iff_isClosed.mpr
  intro S hS
  exact isClosed_of_cells _ (fun n i => hS.preimage (hf n i))

end

section
open Set Topology Metric
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] {C : Set X} [CWComplex C]

abbrev Skel (C : Set X) [CWComplex C] (n : ℕ) :=
  (RelCWComplex.skeletonLT C (n : ℕ∞) : Set X)

def skelIncl (n : ℕ) : C(Skel C n,Skel C (n+1)) :=
  ⟨fun x => ⟨x,RelCWComplex.skeletonLT_mono (by exact_mod_cast Nat.le_succ n) x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

def charSkel (n : ℕ) (i : RelCWComplex.cell C n) : C(Disk n,Skel C (n+1)) :=
  ⟨fun v => ⟨RelCWComplex.map n i v,
      RelCWComplex.closedCell_subset_skeletonLT n i ⟨v,v.2,rfl⟩⟩,
    (continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn n i)).subtype_mk _⟩

def boundarySkel (n : ℕ) (i : RelCWComplex.cell C n) : C(Boundary n,Skel C n) :=
  ⟨fun v => ⟨RelCWComplex.map n i v,
      RelCWComplex.cellFrontier_subset_skeletonLT n i ⟨v,v.2,rfl⟩⟩,
    (continuousOn_iff_continuous_domRestrict.mp
      ((RelCWComplex.continuousOn n i).mono sphere_subset_closedBall)).subtype_mk _⟩

def stageQuot (n : ℕ) : C(Skel C n ⊕ (Σ _i : RelCWComplex.cell C n, Disk n),Skel C (n+1)) :=
  ⟨Sum.elim (skelIncl n) (fun z => charSkel n z.1 z.2),
    continuous_sum_dom.mpr ⟨(skelIncl n).continuous,continuous_sigma (fun i => (charSkel n i).continuous)⟩⟩

theorem stageQuot_surjective (n : ℕ) : Function.Surjective (stageQuot (C := C) n) := by
  intro x
  have hx := x.2
  change (x : X) ∈ (RelCWComplex.skeletonLT C ((n:ℕ∞)+1) : Set X) at hx
  rw [← RelCWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ] at hx
  rcases hx with hx | hx
  · exact ⟨Sum.inl ⟨x,hx⟩,rfl⟩
  · rcases mem_iUnion.mp hx with ⟨i,v,hv,hvx⟩
    exact ⟨Sum.inr ⟨i,⟨v,hv⟩⟩,Subtype.ext hvx⟩

theorem stageQuot_isQuotientMap (n : ℕ) : IsQuotientMap (stageQuot (C := C) n) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨stageQuot_surjective n, fun S => ⟨fun h => h.preimage (stageQuot n).continuous,?_⟩⟩
  intro hS
  apply isClosed_of_cells
  intro m i
  have hi : m < n+1 := by
    have := i.2
    simpa only [RelCWComplex.skeletonLT_I,mem_ofPred_eq,ENat.natCast_lt_natCast] using this
  by_cases hmn : m < n
  · let j : RelCWComplex.cell (Skel C n) m := ⟨i.1,by
      simpa only [RelCWComplex.skeletonLT_I,mem_ofPred_eq,ENat.natCast_lt_natCast] using hmn⟩
    have hc := hS.preimage (continuous_inl.comp (charMap m j).continuous)
    exact hc
  · have hmn : m = n := by omega
    subst m
    have hc := hS.preimage (continuous_inr.comp (continuous_sigmaMk (i := i.1)))
    exact hc

end

open Set Topology Metric
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] {C : Set X} [CWComplex C]

theorem boundary_of_mem_skel (n : ℕ) (i : RelCWComplex.cell C n) (v : Disk n)
    (hv : RelCWComplex.map n i v ∈ Skel C n) : (v : Fin n → ℝ) ∈ sphere 0 1 := by
  have hn : (v : Fin n → ℝ) ∉ ball 0 1 := by
    intro hb
    exact (RelCWComplex.disjoint_skeletonLT_openCell (C := C) (j := i) le_rfl).notMem_of_mem_left hv
      ⟨v,hb,rfl⟩
  rw [mem_sphere]
  exact le_antisymm v.2 (le_of_not_gt hn)

def stageData (n : ℕ) (f : C(Skel C n,Y))
    (g : ∀ _ : RelCWComplex.cell C n, C(Disk n,Y)) :
    C(Skel C n ⊕ (Σ _i : RelCWComplex.cell C n,Disk n),Y) :=
  ⟨Sum.elim f (fun z => g z.1 z.2),continuous_sum_dom.mpr
    ⟨f.continuous,continuous_sigma (fun i => (g i).continuous)⟩⟩

theorem stageData_factors (n : ℕ) (f : C(Skel C n,Y))
    (g : ∀ _ : RelCWComplex.cell C n, C(Disk n,Y))
    (hg : ∀ i (v : Boundary n),g i ⟨v,sphere_subset_closedBall v.2⟩ = f (boundarySkel n i v)) :
    Function.FactorsThrough (stageData n f g) (stageQuot n) := by
  intro a b hab
  have eqval := congrArg Subtype.val hab
  simp only [stageQuot,skelIncl,charSkel,ContinuousMap.coe_mk] at eqval
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg f (Subtype.ext eqval)
    | inr b =>
      change (a : X) = RelCWComplex.map n b.1 b.2 at eqval
      have hv : (b.2 : Fin n → ℝ) ∈ sphere 0 1 :=
        boundary_of_mem_skel n b.1 b.2 (eqval ▸ a.2)
      exact (congrArg f (Subtype.ext eqval)).trans (hg b.1 ⟨b.2,hv⟩).symm
  | inr a =>
    cases b with
    | inl b =>
      change RelCWComplex.map n a.1 a.2 = (b : X) at eqval
      have hv : (a.2 : Fin n → ℝ) ∈ sphere 0 1 :=
        boundary_of_mem_skel n a.1 a.2 (eqval.symm ▸ b.2)
      exact (hg a.1 ⟨a.2,hv⟩).trans (congrArg f (Subtype.ext eqval))
    | inr b =>
      change RelCWComplex.map n a.1 a.2 = RelCWComplex.map n b.1 b.2 at eqval
      by_cases ha : (a.2 : Fin n → ℝ) ∈ sphere 0 1
      · have hb : (b.2 : Fin n → ℝ) ∈ sphere 0 1 :=
          boundary_of_mem_skel n b.1 b.2 (eqval ▸
            RelCWComplex.cellFrontier_subset_skeletonLT n a.1 ⟨a.2,ha,rfl⟩)
        exact (hg a.1 ⟨a.2,ha⟩).trans
          ((congrArg f (Subtype.ext eqval)).trans (hg b.1 ⟨b.2,hb⟩).symm)
      · have ha' : (a.2 : Fin n → ℝ) ∈ ball 0 1 := lt_of_le_of_ne a.2.2 ha
        have hb : (b.2 : Fin n → ℝ) ∉ sphere 0 1 := by
          intro hb
          exact ha (boundary_of_mem_skel n a.1 a.2 (eqval.symm ▸
            RelCWComplex.cellFrontier_subset_skeletonLT n b.1 ⟨b.2,hb,rfl⟩))
        have hb' : (b.2 : Fin n → ℝ) ∈ ball 0 1 := lt_of_le_of_ne b.2.2 hb
        have hi : a.1 = b.1 := by
          by_contra hi
          exact (RelCWComplex.disjoint_openCell_of_ne (C := C) (by simp [hi] :
            (⟨n,a.1⟩ : Σ n,RelCWComplex.cell C n) ≠ ⟨n,b.1⟩)).notMem_of_mem_left
              ⟨a.2,ha',rfl⟩ ⟨b.2,hb',eqval.symm⟩
        rcases a with ⟨i,v⟩
        rcases b with ⟨j,w⟩
        dsimp at hi
        subst j
        have he : v = w := Subtype.ext ((RelCWComplex.map n i).injOn
          (by simpa [RelCWComplex.source_eq] using ha')
          (by simpa [RelCWComplex.source_eq] using hb') eqval)
        exact congrArg (g i) he

def extendSkel (n : ℕ) (f : C(Skel C n,Y))
    (g : ∀ _ : RelCWComplex.cell C n, C(Disk n,Y))
    (hg : ∀ i (v : Boundary n),g i ⟨v,sphere_subset_closedBall v.2⟩ = f (boundarySkel n i v)) :
    C(Skel C (n+1),Y) :=
  (stageQuot_isQuotientMap n).lift (stageData n f g) (stageData_factors n f g hg)

@[simp] theorem extendSkel_prior (n : ℕ) (f : C(Skel C n,Y))
    (g : ∀ _ : RelCWComplex.cell C n, C(Disk n,Y))
    (hg : ∀ i (v : Boundary n),g i ⟨v,sphere_subset_closedBall v.2⟩ = f (boundarySkel n i v))
    (x : Skel C n) : extendSkel n f g hg (skelIncl n x) = f x :=
  DFunLike.congr_fun ((stageQuot_isQuotientMap n).lift_comp (stageData n f g) (stageData_factors n f g hg)) (Sum.inl x)

@[simp] theorem extendSkel_disk (n : ℕ) (f : C(Skel C n,Y))
    (g : ∀ _ : RelCWComplex.cell C n, C(Disk n,Y))
    (hg : ∀ i (v : Boundary n),g i ⟨v,sphere_subset_closedBall v.2⟩ = f (boundarySkel n i v))
    (i : RelCWComplex.cell C n) (v : Disk n) : extendSkel n f g hg (charSkel n i v) = g i v :=
  DFunLike.congr_fun ((stageQuot_isQuotientMap n).lift_comp (stageData n f g) (stageData_factors n f g hg)) (Sum.inr (⟨i,v⟩ : Σ _j : RelCWComplex.cell C n,Disk n))

end CWExtension

end

end OAI
