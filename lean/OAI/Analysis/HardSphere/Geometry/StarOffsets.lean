import Mathlib
import OAI.Analysis.HardSphere.Geometry.Vertex

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators Classical
namespace HardSphere.Lattice
variable {A : Type*} [AddCommGroup A]

lemma lower_ray_exterior (C : Finset Vertex) (x : Vertex) (i : Fin 3)
    (hx : ∀ c∈C, x i<c i) : x∈exterior C := by
  apply coordinateRay_exterior C x i (-1) (by norm_num)
  intro n hn
  have h := hx _ hn
  simp only [coordinateRay, ite_true, neg_one_mul] at h
  omega

theorem fill_subset_coordinateBox (C : Finset Vertex) : fill C⊆coordinateBox C := by
  intro x hx i
  change x∉exterior C at hx
  constructor
  · by_contra hn
    push Not at hn
    exact hx (lower_ray_exterior C x i hn)
  · by_contra hn
    push Not at hn
    exact hx (upper_ray_exterior C x i hn)

lemma exteriorShell_good (C : Finset Vertex) (B : Set Vertex)
    (hcomponent : ∀ c∈C, ∀ x∈B, starStep c x → x∈C) : exteriorShell C⊆Bᶜ := by
  rintro x ⟨hx, c,hc,hcx⟩ hxB
  exact hx.1 (hcomponent c hc x hxB hcx)

def starOffsets : Finset Vertex :=
  (Fintype.piFinset fun _ : Fin 3 ↦ Finset.Icc (-1 : ℤ) 1).erase 0

lemma starOffsets_card : starOffsets.card = 26 := by
  unfold starOffsets
  rw [Finset.card_erase_of_mem (by simp [Fintype.mem_piFinset]),
    Fintype.card_piFinset]
  norm_num [Fin.prod_univ_succ, Int.card_Icc]

lemma starStep_mem_offsets (c x : Vertex) (h : starStep c x) :
    x∈starOffsets.image (fun d ↦ c+d) := by
  refine Finset.mem_image.mpr ⟨x-c, ?_, by abel⟩
  rw [starOffsets, Finset.mem_erase]
  constructor
  · exact sub_ne_zero.mpr h.1.symm
  · rw [Fintype.mem_piFinset]
    intro i
    have hi := abs_le.mp (h.2 i)
    simp only [Finset.mem_Icc, Pi.sub_apply]
    constructor <;> omega

lemma exteriorShell_subset_offsets (C : Finset Vertex) :
    exteriorShell C ⊆ ↑(C.biUnion fun c ↦ starOffsets.image (fun d ↦ c+d)) := by
  rintro x ⟨_, c,hc,hcx⟩
  exact Finset.mem_biUnion.mpr ⟨c,hc,starStep_mem_offsets c x hcx⟩

lemma exteriorShell_finite (C : Finset Vertex) : (exteriorShell C).Finite :=
  (C.biUnion fun c ↦ starOffsets.image (fun d ↦ c+d)).finite_toSet.subset
    (exteriorShell_subset_offsets C)

theorem exteriorShell_card_le (C : Finset Vertex) :
    (exteriorShell C).ncard ≤ 26*C.card := by
  calc
    (exteriorShell C).ncard ≤
        (C.biUnion fun c ↦ starOffsets.image (fun d ↦ c+d)).card := by
      simpa only [Set.ncard_coe_finset] using
        Set.ncard_le_ncard (exteriorShell_subset_offsets C)
    _ ≤ ∑ c∈C, (starOffsets.image (fun d ↦ c+d)).card := Finset.card_biUnion_le
    _ ≤ ∑ _c∈C, 26 := by
      apply Finset.sum_le_sum
      intro c _
      exact (Finset.card_image_le).trans (le_of_eq starOffsets_card)
    _ = 26*C.card := by simp [Nat.mul_comm]

lemma withinReach_symm {D : Set Vertex} {e : Vertex → Vertex → Prop}
    (he : ∀ x y, e x y → e y x) {x y : Vertex} (h : withinReach e D x y) :
    withinReach e D y x := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact .refl
  | single h => exact .single ⟨h.2.1,h.1,he _ _ h.2.2⟩
  | trans _ _ ih₁ ih₂ => exact ih₂.trans ih₁

lemma withinReach_mono {D E : Set Vertex} {e : Vertex → Vertex → Prop}
    (hDE : D⊆E) {x y : Vertex} (h : withinReach e D x y) :
    withinReach e E x y := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact .refl
  | single h => exact .single ⟨hDE h.1,hDE h.2.1,h.2.2⟩
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma nearestStep_update (x : Vertex) (i : Fin 3) (k : ℤ) :
    nearestStep (Function.update x i k) (Function.update x i (k+1)) := by
  refine ⟨i,?_,?_⟩
  · simp
  · intro j hj
    simp [hj]

lemma withinReach_axis_le {D : Set Vertex} (x : Vertex) (i : Fin 3)
    (a b : ℤ) (hab : a≤b)
    (hD : ∀ k, a≤k → k≤b → Function.update x i k∈D) :
    withinReach nearestStep D (Function.update x i a) (Function.update x i b) := by
  have hpath : ∀ n : ℕ, (n:ℤ)≤b-a →
      withinReach nearestStep D (Function.update x i a) (Function.update x i (a+(n:ℤ))) := by
    intro n
    induction n with
    | zero => intro _; simp only [Nat.cast_zero,add_zero]; exact .refl
    | succ n ih =>
      intro hn
      have hn' : (n:ℤ)≤b-a := by omega
      have hprev := ih hn'
      have hu := hD (a+(n:ℤ)) (by omega) (by omega)
      have hv := hD (a+((n+1:ℕ):ℤ)) (by omega) (by omega)
      apply hprev.tail
      refine ⟨hu,hv,?_⟩
      convert nearestStep_update x i (a+(n:ℤ)) using 1; push_cast; abel_nf
  have hc : a+((b-a).toNat:ℤ)=b := by omega
  simpa only [hc] using hpath (b-a).toNat (by omega)

lemma withinReach_axis {D : Set Vertex} (x : Vertex) (i : Fin 3)
    (a b : ℤ)
    (hD : ∀ k, min a b≤k → k≤ max a b → Function.update x i k∈D) :
    withinReach nearestStep D (Function.update x i a) (Function.update x i b) := by
  rcases le_total a b with hab|hba
  · apply withinReach_axis_le x i a b hab
    simpa only [min_eq_left hab,max_eq_right hab] using hD
  · apply withinReach_symm (fun _ _ ↦ nearestStep_symm)
    apply withinReach_axis_le x i b a hba
    simpa only [min_eq_right hba,max_eq_left hba] using hD

def intervalBox (x y : Vertex) : Set Vertex :=
  {z | ∀ i, min (x i) (y i)≤z i ∧ z i≤ max (x i) (y i)}

def mixVertex (x y : Vertex) (n : ℕ) : Vertex := fun i ↦ if i.val<n then y i else x i

lemma mixVertex_zero (x y : Vertex) : mixVertex x y 0=x := by ext i; simp [mixVertex]
lemma mixVertex_three (x y : Vertex) : mixVertex x y 3=y := by
  ext i
  simp only [mixVertex,ite_eq_left i.isLt]
lemma mixVertex_box (x y : Vertex) (n : ℕ) : mixVertex x y n∈intervalBox x y := by
  intro i
  by_cases hi : i.val<n <;> simp [mixVertex,hi]
lemma mixVertex_succ (x y : Vertex) (n : ℕ) (hn : n<3) :
    mixVertex x y (n+1)=Function.update (mixVertex x y n) ⟨n,hn⟩ (y ⟨n,hn⟩) := by
  ext i
  by_cases hi : i=⟨n,hn⟩
  · subst i; simp [mixVertex]
  · have hin : i.val≠n := fun h ↦ hi (Fin.ext h)
    have hlt : (i.val<n+1) ↔ (i.val<n) := by omega
    simp only [Function.update_of_ne hi,mixVertex,hlt]

theorem intervalBox_reach (x y : Vertex) : withinReach nearestStep (intervalBox x y) x y := by
  have hpath : ∀ n : ℕ, n≤3 → withinReach nearestStep (intervalBox x y) x (mixVertex x y n) := by
    intro n
    induction n with
    | zero => intro _; rw [mixVertex_zero]; exact .refl
    | succ n ih =>
      intro hn
      have hn' : n<3 := by omega
      let i : Fin 3 := ⟨n,hn'⟩
      have hprev := ih (by omega)
      rw [mixVertex_succ x y n hn']
      apply hprev.trans
      have hold : mixVertex x y n i=x i := by simp [mixVertex,i]
      have haxis := withinReach_axis (D := intervalBox x y) (mixVertex x y n) i (x i) (y i) ?_
      · simpa only [withinReach,← hold,Function.update_eq_self,i] using haxis
      · intro k hk₁ hk₂ j
        by_cases hj : j=i
        · subst j
          simpa using And.intro hk₁ hk₂
        · rw [Function.update_of_ne hj]
          exact mixVertex_box x y n j
  simpa only [mixVertex_three] using hpath 3 (by omega)

lemma box_reach {D : Set Vertex} (x y : Vertex) (hD : intervalBox x y⊆D) :
    withinReach nearestStep D x y := withinReach_mono hD (intervalBox_reach x y)

lemma withinReach_end {D : Set Vertex} {e : Vertex → Vertex → Prop} {x y : Vertex}
    (hx : x∈D) (h : withinReach e D x y) : y∈D := by
  rcases h.cases_tail with he|⟨z,_,hzy⟩
  · exact he ▸ hx
  · exact hzy.2.1

lemma withinReach_invariant {D E : Set Vertex} {e : Vertex → Vertex → Prop}
    (hclosed : ∀ u∈E, ∀ v∈D, e u v → v∈E)
    {x y : Vertex} (hx : x∈E) (h : withinReach e D x y) : withinReach e E x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head h' _ ih =>
    have hv := hclosed _ hx _ h'.2.1 h'.2.2
    exact (ih hv).head ⟨hx,hv,h'.2.2⟩

lemma avoidingReach_symm (C : Finset Vertex) {x y : Vertex}
    (h : avoidingReach C x y) : avoidingReach C y x :=
  withinReach_symm (D := (↑C)ᶜ) (fun _ _ ↦ nearestStep_symm) h

lemma exterior_of_reach (C : Finset Vertex) {x y : Vertex}
    (hx : x∈exterior C) (hxy : avoidingReach C x y) : y∈exterior C := by
  have hy : y∉C := withinReach_end (D := (↑C)ᶜ) hx.1 hxy
  refine ⟨hy,hx.2.mono ?_⟩
  intro z hz
  exact (avoidingReach_symm C hxy).trans hz

def integerBox (M : ℤ) : Finset Vertex :=
  Fintype.piFinset fun _ : Fin 3 ↦ Finset.Icc (-M) M

lemma mem_integerBox (M : ℤ) (x : Vertex) : x∈integerBox M ↔ ∀ i, |x i|≤M := by
  simp only [integerBox,Fintype.mem_piFinset,Finset.mem_Icc,abs_le]

lemma finite_coordinate_bound (C : Finset Vertex) :
    ∃ M : ℤ, 0≤M ∧ ∀ c∈C, ∀ i, |c i|≤M := by
  let s : Finset ℤ := C.biUnion (fun c ↦ Finset.univ.image (fun i : Fin 3 ↦ |c i|))
  obtain ⟨M,hM⟩ := s.finite_toSet.exists_le
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro c hc i
  apply (hM _ ?_).trans (le_max_left M 0)
  exact Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩

lemma outside_box_reach (C : Finset Vertex) (M : ℤ) (hM : 0≤M)
    (hC : ∀ c∈C, ∀ i, |c i|≤M) (x : Vertex) (hx : x∉integerBox M) :
    avoidingReach C x (fun _ ↦ M+1) := by
  have hex : ∃ i, M < |x i| := by
    by_contra hn
    push Not at hn
    exact hx ((mem_integerBox M x).mpr hn)
  obtain ⟨i,hi⟩ := hex
  let r : Vertex := fun _ ↦ M+1
  let z : Vertex := Function.update r i (x i)
  have hxz : withinReach nearestStep ((↑C : Set Vertex)ᶜ) x z := by
    apply box_reach
    intro u hu huc
    have hui := hu i
    have hzi : z i=x i := by simp [z]
    rw [hzi,min_self,max_self] at hui
    have hueq : u i=x i := le_antisymm hui.2 hui.1
    have hbound := hC u huc i
    rw [hueq] at hbound
    omega
  have hzr : withinReach nearestStep ((↑C : Set Vertex)ᶜ) z r := by
    obtain ⟨j,hj⟩ : ∃ j : Fin 3, j≠i := exists_ne i
    apply box_reach
    intro u hu huc
    have huj := hu j
    have hzj : z j=M+1 := by simp [z,r,Function.update_of_ne hj]
    change min (z j) (M+1)≤u j ∧ u j≤ max (z j) (M+1) at huj
    rw [hzj,min_self,max_self] at huj
    have hueq : u j=M+1 := le_antisymm huj.2 huj.1
    have hbound := hC u huc j
    rw [hueq,abs_of_nonneg (by omega : 0≤M+1)] at hbound
    omega
  exact hxz.trans hzr

lemma exterior_reach_anchor (C : Finset Vertex) (M : ℤ) (hM : 0≤M)
    (hC : ∀ c∈C, ∀ i, |c i|≤M) {x : Vertex} (hx : x∈exterior C) :
    avoidingReach C x (fun _ ↦ M+1) := by
  obtain ⟨y,hxy,hy⟩ := hx.2.exists_notMem_finset (integerBox M)
  exact hxy.trans (outside_box_reach C M hM hC y hy)

theorem exterior_avoidingReach (C : Finset Vertex) {x y : Vertex}
    (hx : x∈exterior C) (hy : y∈exterior C) : avoidingReach C x y := by
  obtain ⟨M,hM,hC⟩ := finite_coordinate_bound C
  exact (exterior_reach_anchor C M hM hC hx).trans
    (avoidingReach_symm C (exterior_reach_anchor C M hM hC hy))

theorem exterior_NNConnected (C : Finset Vertex) : NNConnected (exterior C) := by
  intro x hx y hy
  apply withinReach_invariant (D := (↑C)ᶜ) _ hx (exterior_avoidingReach C hx hy)
  intro u hu v hv huv
  exact exterior_of_reach C hu (.single ⟨hu.1,hv,huv⟩)

def doubleVertex (x : Vertex) : Vertex := fun i ↦ 2*x i

def thickCube (c : Vertex) : Set Vertex := {z | ∀ i, |z i-2*c i|≤1}

def thicken (C : Finset Vertex) : Finset Vertex :=
  C.biUnion fun c ↦ Fintype.piFinset fun i : Fin 3 ↦ Finset.Icc (2*c i-1) (2*c i+1)

lemma mem_thicken (C : Finset Vertex) (z : Vertex) :
    z∈thicken C ↔ ∃ c∈C, z∈thickCube c := by
  simp only [thicken,Finset.mem_biUnion,Fintype.mem_piFinset,Finset.mem_Icc]
  constructor
  · rintro ⟨c,hc,hz⟩
    refine ⟨c,hc,fun i ↦ abs_le.mpr ?_⟩
    have h := hz i
    constructor <;> omega
  · rintro ⟨c,hc,hz⟩
    refine ⟨c,hc,fun i ↦ ?_⟩
    have h := abs_le.mp (hz i)
    constructor <;> omega

lemma double_mem_cube (c : Vertex) : doubleVertex c∈thickCube c := by
  intro i; simp [doubleVertex]

lemma thickCube_subset (C : Finset Vertex) {c : Vertex} (hc : c∈C) :
    thickCube c⊆(↑(thicken C) : Set Vertex) := fun z hz ↦ (mem_thicken C z).mpr ⟨c,hc,hz⟩

lemma thickCube_NNConnected (c : Vertex) : NNConnected (thickCube c) := by
  intro x hx y hy
  apply box_reach
  intro z hz i
  have hx' := abs_le.mp (hx i)
  have hy' := abs_le.mp (hy i)
  have hz' := hz i
  apply abs_le.mpr
  constructor <;> omega

lemma thicken_adjacent_centers (C : Finset Vertex) {c d : Vertex}
    (hc : c∈C) (hd : d∈C) (hcd : starStep c d) :
    withinReach nearestStep (↑(thicken C)) (doubleVertex c) (doubleVertex d) := by
  let m : Vertex := c+d
  have hmC : m∈thickCube c := by
    intro i
    change |c i+d i-2*c i|≤1
    rw [show c i+d i-2*c i=d i-c i by ring,abs_sub_comm]
    exact hcd.2 i
  have hmD : m∈thickCube d := by
    intro i
    change |c i+d i-2*d i|≤1
    rw [show c i+d i-2*d i=c i-d i by ring]
    exact hcd.2 i
  exact (withinReach_mono (thickCube_subset C hc)
    (thickCube_NNConnected c _ (double_mem_cube c) m hmC)).trans
    (withinReach_mono (thickCube_subset C hd)
      (thickCube_NNConnected d m hmD _ (double_mem_cube d)))

lemma thicken_star_reach (C : Finset Vertex) {c d : Vertex}
    (h : withinReach starStep (↑C) c d) :
    withinReach nearestStep (↑(thicken C)) (doubleVertex c) (doubleVertex d) := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact .refl
  | single h => exact thicken_adjacent_centers C h.1 h.2.1 h.2.2
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

lemma thicken_NNConnected (C : Finset Vertex) (hC : starConnected (↑C)) :
    NNConnected (↑(thicken C)) := by
  intro x hx y hy
  obtain ⟨c,hc,hcx⟩ := (mem_thicken C x).mp hx
  obtain ⟨d,hd,hdy⟩ := (mem_thicken C y).mp hy
  exact (withinReach_mono (thickCube_subset C hc)
    (thickCube_NNConnected c x hcx _ (double_mem_cube c))).trans
    ((thicken_star_reach C (hC c hc d hd)).trans
      (withinReach_mono (thickCube_subset C hd)
        (thickCube_NNConnected d _ (double_mem_cube d) y hdy)))

def complementComponent (A : Set Vertex) (r : Vertex) : Set Vertex :=
  {x | x∉A ∧ withinReach nearestStep Aᶜ r x}

lemma complementComponent_spec (A : Set Vertex) (r : Vertex) :
    NNComplementComponent A (complementComponent A r) := by
  have hclosed : ∀ x∈complementComponent A r, ∀ y, y∉A → nearestStep x y →
      y∈complementComponent A r := by
    intro x hx y hy hxy
    exact ⟨hy,hx.2.tail ⟨hx.1,hy,hxy⟩⟩
  refine ⟨Set.disjoint_left.mpr (fun _ ha hb ↦ hb.1 ha),?_,hclosed⟩
  intro x hx y hy
  apply withinReach_invariant (D := Aᶜ) (fun u hu v hv huv ↦ hclosed u hu v hv huv) hx
  exact (withinReach_symm (fun _ _ ↦ nearestStep_symm) hx.2).trans hy.2

lemma double_mem_thicken_iff (C : Finset Vertex) (x : Vertex) :
    doubleVertex x∈thicken C ↔ x∈C := by
  constructor
  · intro hx
    obtain ⟨c,hc,hcx⟩ := (mem_thicken C _).mp hx
    have he : x=c := by
      ext i
      have h := abs_le.mp (hcx i)
      dsimp [doubleVertex] at h
      omega
    exact he ▸ hc
  · intro hx
    exact (mem_thicken C _).mpr ⟨x,hx,double_mem_cube x⟩

lemma double_step (x : Vertex) (i : Fin 3) :
    doubleVertex (step x i)=step (step (doubleVertex x) i) i := by
  ext j
  by_cases hj : j=i
  · subst j
    simp only [doubleVertex,step_apply_same]
    ring
  · simp [doubleVertex,step,hj]

lemma splitPoint_not_thicken (C : Finset Vertex) (x : Vertex) (i : Fin 3)
    (hx : x∉C) (hy : step x i∉C) : step (doubleVertex x) i∉thicken C := by
  intro hm
  obtain ⟨c,hc,hcm⟩ := (mem_thicken C _).mp hm
  have hrest : ∀ j, j≠i → c j=x j := by
    intro j hj
    have h := abs_le.mp (hcm j)
    rw [step_apply_ne _ hj] at h
    dsimp [doubleVertex] at h
    omega
  have hi := abs_le.mp (hcm i)
  rw [step_apply_same] at hi
  dsimp [doubleVertex] at hi
  have hci : c i=x i ∨ c i=x i+1 := by omega
  rcases hci with hci|hci
  · have he : c=x := by
      ext j
      by_cases hj : j=i
      · subst j; exact hci
      · exact hrest j hj
    exact hx (he ▸ hc)
  · have he : c=step x i := by
      ext j
      by_cases hj : j=i
      · subst j; rw [step_apply_same]; exact hci
      · rw [step_apply_ne _ hj]; exact hrest j hj
    exact hy (he ▸ hc)

end HardSphere.Lattice
end
end
end
end

end OAI
