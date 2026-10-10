import Mathlib

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

namespace CannonFaceIncidence
variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D]

def region (V : Set X) (π : V → D) (d : D) : Set X :=
  {x | ∃ h : x∈V, π ⟨x,h⟩=d}

def incident (V : Set X) (π : V → D) (x : X) : Set D :=
  {d | x∈closure (region V π d)}

omit [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D] in
lemma region_subset (V : Set X) (π : V → D) (d : D) : region V π d⊆V := by
  rintro x ⟨hx,_⟩
  exact hx

lemma region_isOpen {V : Set X} (hV : IsOpen V) {π : V → D} (hπ : Continuous π) (d : D) :
    IsOpen (region V π d) := by
  have he : region V π d=Subtype.val '' (π ⁻¹' {d}) := by
    ext x
    simp only [region,mem_ofPred_eq,mem_image,mem_preimage,mem_singleton_iff]
    constructor
    · rintro ⟨hx,he⟩
      exact ⟨⟨x,hx⟩,he,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x.property,hx⟩
  rw [he]
  exact hV.isOpenMap_subtype_val _ (hπ.isOpen_preimage _ (isOpen_discrete _))

lemma label_on_connected {V S : Set X} {π : V → D} (hπ : Continuous π)
    (hS : IsConnected S) (hSV : S⊆V) : ∃ d : D, S⊆region V π d := by
  let _ : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS.isPreconnected
  obtain ⟨x,hx⟩ := hS.nonempty
  let f : S → D := fun y => π ⟨y.val,hSV y.property⟩
  have hf : Continuous f := hπ.comp (by fun_prop)
  refine ⟨f ⟨x,hx⟩,fun y hy => ⟨hSV hy,?_⟩⟩
  exact (IsLocallyConstant.iff_continuous f).mpr hf |>.apply_eq_of_preconnectedSpace ⟨y,hy⟩ ⟨x,hx⟩

theorem sector_incidence {V W B : Set X} (hW : IsOpen W) (hBW : B⊆W)
    {π : V → D} (hπ : Continuous π) {ι : Type*} [Finite ι]
    (S : ι → Set X) (hS : ∀ i, IsConnected (S i))
    (hcover : W∩V=⋃ i, S i) (hclose : ∀ i, B⊆closure (S i)) :
    ∃ labels : ι → D, (∀ i, S i⊆region V π (labels i)) ∧
      ∀ x∈B, incident V π x=range labels := by
  classical
  have hSV (i : ι) : S i⊆V := by
    intro x hx
    exact (hcover.symm ▸ mem_iUnion_of_mem i hx).2
  choose labels hlabels using fun i => label_on_connected hπ (hS i) (hSV i)
  refine ⟨labels,hlabels,?_⟩
  intro x hx
  ext d
  constructor
  · intro hd
    by_contra hn
    have hnone : W∩region V π d=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro y ⟨hyW,hyR⟩
      have hyWV : y∈W∩V := ⟨hyW,region_subset V π d hyR⟩
      rw [hcover] at hyWV
      obtain ⟨i,hi⟩ := mem_iUnion.mp hyWV
      obtain ⟨hy,he⟩ := hlabels i hi
      obtain ⟨hy',he'⟩ := hyR
      apply hn
      exact ⟨i,he.symm.trans he'⟩
    have hm : (W∩region V π d).Nonempty :=
      (mem_closure_iff_nhds.mp hd) W (hW.mem_nhds (hBW hx))
    rw [hnone] at hm
    exact not_nonempty_empty hm
  · rintro ⟨i,rfl⟩
    exact closure_mono (hlabels i) (hclose i hx)

omit [TopologicalSpace D] [DiscreteTopology D] in

theorem incident_constant_on_preconnected {V A : Set X} {π : V → D}
    (hA : IsPreconnected A)
    (hloc : ∀ x∈A, ∃ W : Set X, IsOpen W ∧ x∈W ∧
      ∀ y∈A∩W, incident V π y=incident V π x) :
    ∀ x∈A, ∀ y∈A, incident V π x=incident V π y := by
  let _ : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp hA
  let f : A → Set D := fun x => incident V π x.val
  have hf : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_eventually_eq f).mpr
    intro x
    obtain ⟨W,hW,hxW,heq⟩ := hloc x.val x.property
    filter_upwards [(continuous_subtype_val.isOpen_preimage W hW).mem_nhds hxW] with y hy
    exact heq y.val ⟨y.property,hy⟩
  intro x hx y hy
  exact hf.apply_eq_of_preconnectedSpace ⟨x,hx⟩ ⟨y,hy⟩

end CannonFaceIncidence

namespace CannonFaceIncidence
open Set Metric Topology

def openBox (r : ℝ) : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo (-r) r
def halfBox (r : ℝ) (b : Bool) : Set (ℝ × ℝ) :=
  Ioo (-r) r ×ˢ (if b then Ioo 0 r else Ioo (-r) 0)

lemma openBox_eq_ball (r : ℝ) : openBox r=ball (0,0) r := by
  rw [←ball_prod_same,Real.ball_eq_Ioo]
  simp [openBox]

lemma halfBox_connected {r : ℝ} (hr : 0<r) (b : Bool) : IsConnected (halfBox r b) := by
  cases b
  · exact (isConnected_Ioo (by linarith : -r<r)).prod (isConnected_Ioo (neg_neg_of_pos hr))
  · exact (isConnected_Ioo (by linarith : -r<r)).prod (isConnected_Ioo hr)

lemma halfBox_closure {r : ℝ} (hr : 0<r) {p : ℝ × ℝ}
    (hp : p∈openBox r) (hp₂ : p.2=0) (b : Bool) : p∈closure (halfBox r b) := by
  have hrr : -r<r := by linarith
  cases b <;> simp only [halfBox,Bool.false_eq_true,↓reduceIte,closure_prod_eq]
  · rw [closure_Ioo hrr.ne,closure_Ioo (neg_neg_of_pos hr).ne]
    exact ⟨⟨hp.1.1.le,hp.1.2.le⟩,by rw [hp₂]; exact ⟨(neg_neg_of_pos hr).le,le_rfl⟩⟩
  · rw [closure_Ioo hrr.ne,closure_Ioo hr.ne]
    exact ⟨⟨hp.1.1.le,hp.1.2.le⟩,by rw [hp₂]; exact ⟨le_rfl,hr.le⟩⟩

variable {X D : Type*} [TopologicalSpace X] [TopologicalSpace D] [DiscreteTopology D]

theorem flat_chart_incidence {V W : Set X} {π : V → D} (hπ : Continuous π)
    (H : (ℝ × ℝ) ≃ₜ X) (hW : IsOpen W) (h₀ : H (0,0)∈W)
    (hflat : ∀ z∈W, z∈V ↔ (H.symm z).2≠0) :
    ∃ U : Set X, IsOpen U ∧ H (0,0)∈U ∧ U⊆W ∧
      ∃ labels : Bool → D, ∀ x∈U∩Vᶜ, incident V π x=range labels := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    ((hW.preimage H.continuous).mem_nhds h₀)
  let C := openBox r
  let U := H '' C
  have hCU : C⊆H ⁻¹' W := by rw [show C=openBox r from rfl,openBox_eq_ball]; exact hball
  have hUW : U⊆W := by rintro _ ⟨p,hp,rfl⟩; exact hCU hp
  have hU : IsOpen U := H.isOpenMap C (by rw [show C=openBox r from rfl,openBox_eq_ball]; exact isOpen_ball)
  have h₀U : H (0,0)∈U := ⟨(0,0),by rw [show C=openBox r from rfl,openBox_eq_ball]; exact mem_ball_self hr,rfl⟩
  let S : Bool → Set X := fun b => H '' halfBox r b
  have hSc (b : Bool) : IsConnected (S b) :=
    (halfBox_connected hr b).image H H.continuous.continuousOn
  have hcover : U∩V=⋃ b, S b := by
    ext x
    constructor
    · rintro ⟨⟨p,hp,rfl⟩,hpV⟩
      have hp₂ : p.2≠0 := by simpa using (hflat (H p) (hCU hp)).mp hpV
      rcases lt_or_gt_of_ne hp₂ with hl|hr'
      · exact mem_iUnion.mpr ⟨false,⟨p,⟨hp.1,hp.2.1,hl⟩,rfl⟩⟩
      · exact mem_iUnion.mpr ⟨true,⟨p,⟨hp.1,hr',hp.2.2⟩,rfl⟩⟩
    · intro hx
      obtain ⟨b,p,hp,rfl⟩ := mem_iUnion.mp hx
      have hpC : p∈C := by
        cases b
        · exact ⟨hp.1,hp.2.1,hp.2.2.trans hr⟩
        · exact ⟨hp.1,(neg_neg_of_pos hr).trans hp.2.1,hp.2.2⟩
      refine ⟨⟨p,hpC,rfl⟩,(hflat (H p) (hCU hpC)).mpr ?_⟩
      simp only [H.symm_apply_apply]
      cases b
      · exact hp.2.2.ne
      · exact hp.2.1.ne'
  have hclose (b : Bool) : U∩Vᶜ⊆closure (S b) := by
    rintro x ⟨⟨p,hp,hpx⟩,hxV⟩
    subst x
    have hp₂ : p.2=0 := by
      by_contra h
      apply hxV
      apply (hflat (H p) (hCU hp)).mpr
      simpa using h
    rw [show S b=H '' halfBox r b from rfl,←H.image_closure]
    exact ⟨p,halfBox_closure hr hp hp₂ b,rfl⟩
  obtain ⟨labels,_,hlabels⟩ := sector_incidence hU inter_subset_left hπ S hSc hcover hclose
  exact ⟨U,hU,h₀U,hUW,labels,hlabels⟩
end CannonFaceIncidence

end
end
end
end
end
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
