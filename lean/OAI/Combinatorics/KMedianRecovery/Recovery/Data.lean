import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.PhasesBounded

namespace OAI

namespace MetricKMedianRecovery.PhaseLeafGeometry
universe uD uX uY uC
variable {D : Type uD} {X : Type uX} {Y : Type uY} {C : Type uC}
variable [PseudoMetricSpace X]

structure Data (loc : D → X) (F B : Finset X) (U : ℝ) where
  root : X → X
  length : X → ℝ
  root_mem : ∀ b ∈ B, root b ∈ F
  nonneg : ∀ b ∈ B, 0 ≤ length b
  bound : ∀ b ∈ B, length b ≤ U
  client : ∀ b ∈ B, ∀ j, dist (loc j) b = length b + dist (loc j) (root b)
  regular : ∀ b ∈ B, ∀ i ∈ F, dist b i = length b + dist (root b) i
  copies : ∀ b ∈ B, ∀ c ∈ B, b ≠ c →
    dist b c = length b + dist (root b) (root c) + length c

noncomputable def empty (loc : D → X) (F : Finset X) (U : ℝ) : Data loc F ∅ U :=
  ⟨id,fun _ => 0,by simp,by simp,by simp,by simp,by simp,by simp⟩

noncomputable def mapRoot (e : X ↪ Y) (r : X → X) (y : Y) : Y  := by
  classical
  exact if h : ∃ x, e x = y then e (r (Classical.choose h)) else y
noncomputable def mapLength (e : X ↪ Y) (w : X → ℝ) (y : Y) : ℝ  := by
  classical
  exact if h : ∃ x, e x = y then w (Classical.choose h) else 0

omit [PseudoMetricSpace X] in
lemma mapRoot_apply (e : X ↪ Y) (r : X → X) (x : X) : mapRoot e r (e x) = e (r x) := by
  unfold mapRoot
  rw [dite_eq_left ⟨x,rfl⟩]
  have he := e.injective (Classical.choose_spec (show ∃ a, e a = e x from ⟨x,rfl⟩))
  rw [he]
omit [PseudoMetricSpace X] in
lemma mapLength_apply (e : X ↪ Y) (w : X → ℝ) (x : X) : mapLength e w (e x) = w x := by
  unfold mapLength
  rw [dite_eq_left ⟨x,rfl⟩]
  have he := e.injective (Classical.choose_spec (show ∃ a, e a = e x from ⟨x,rfl⟩))
  rw [he]

noncomputable def Data.map [PseudoMetricSpace Y] [DecidableEq Y]
    {loc : D → X} {F B : Finset X} {U : ℝ} (d : Data loc F B U)
    (e : X ↪ Y) (he : ∀ x y, dist (e x) (e y) = dist x y) :
    Data (fun j => e (loc j)) (F.image e) (B.image e) U := by
  refine ⟨mapRoot e d.root,mapLength e d.length,?_,?_,?_,?_,?_,?_⟩
  · intro b hb
    obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
    rw [mapRoot_apply]
    exact Finset.mem_image.mpr ⟨d.root b,d.root_mem b hb',rfl⟩
  · intro b hb
    obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
    rw [mapLength_apply]
    exact d.nonneg b hb'
  · intro b hb
    obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
    rw [mapLength_apply]
    exact d.bound b hb'
  · intro b hb j
    obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
    simpa only [mapRoot_apply,mapLength_apply,he] using d.client b hb' j
  · intro b hb i hi
    obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨i,hi',rfl⟩ := Finset.mem_image.mp hi
    simpa only [mapRoot_apply,mapLength_apply,he] using d.regular b hb' i hi'
  · intro b hb c hc hbc
    obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c,hc',rfl⟩ := Finset.mem_image.mp hc
    simpa only [mapRoot_apply,mapLength_apply,he] using d.copies b hb' c hc'
      (fun h => hbc (congrArg e h))

noncomputable def Data.attach [DecidableEq X] [DecidableEq C]
    {loc : D → X} {F B : Finset X} {U : ℝ} (d : Data loc F B U)
    (r : C → X) (w : C → ℝ) (hw : ∀ c, 0 ≤ w c) (A : Finset C)
    (hr : ∀ c ∈ A, r c ∈ F) (hU : ∀ c ∈ A, w c ≤ U) :
    letI : PseudoMetricSpace (X ⊕ C) := LeafMetric.attachedMetric r w hw
    Data (fun j => Sum.inl (loc j)) (F.image Sum.inl)
      (B.image Sum.inl ∪ A.image Sum.inr) U := by
  letI : PseudoMetricSpace (X ⊕ C) := LeafMetric.attachedMetric r w hw
  have old (x y : X) : dist (Sum.inl x : X ⊕ C) (Sum.inl y) = dist x y :=
    LeafMetric.original_distance r w x y
  have mix (x : X) (c : C) : dist (Sum.inl x : X ⊕ C) (Sum.inr c) = dist x (r c)+w c :=
    LeafMetric.copy_distance r w x c
  have new (c c' : C) (h : c ≠ c') :
      dist (Sum.inr c : X ⊕ C) (Sum.inr c') = w c+dist (r c) (r c')+w c' :=
    LeafMetric.copies_distance r w c c' h
  refine ⟨Sum.elim (fun x => Sum.inl (d.root x)) (fun c => Sum.inl (r c)),
    Sum.elim d.length w,?_,?_,?_,?_,?_,?_⟩
  · intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨d.root b,d.root_mem b hb',rfl⟩
    · obtain ⟨c,hc',rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨r c,hr c hc',rfl⟩
  · intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
      exact d.nonneg b hb'
    · obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hb
      exact hw c
  · intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
      exact d.bound b hb'
    · obtain ⟨c,hc',rfl⟩ := Finset.mem_image.mp hb
      exact hU c hc'
  · intro b hb j
    rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
      simpa only [Sum.elim_inl,old] using d.client b hb' j
    · obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hb
      simp only [Sum.elim_inr,old,mix,add_comm]
  · intro b hb i hi
    obtain ⟨i,hi',rfl⟩ := Finset.mem_image.mp hi
    rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
      simpa only [Sum.elim_inl,old] using d.regular b hb' i hi'
    · obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hb
      simp only [Sum.elim_inr,old,dist_comm (Sum.inr c : X ⊕ C),mix]
      rw [dist_comm i (r c),add_comm]
  · intro b hb c hc hbc
    rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
      rcases Finset.mem_union.mp hc with hc | hc
      · obtain ⟨c,hc',rfl⟩ := Finset.mem_image.mp hc
        simpa only [Sum.elim_inl,old] using d.copies b hb' c hc'
          (fun h => hbc (congrArg Sum.inl h))
      · obtain ⟨c,hc',rfl⟩ := Finset.mem_image.mp hc
        simp only [Sum.elim_inl,Sum.elim_inr,old,mix]
        rw [d.regular b hb' (r c) (hr c hc')]
    · obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hb
      rcases Finset.mem_union.mp hc with hc | hc
      · obtain ⟨c,hc',rfl⟩ := Finset.mem_image.mp hc
        simp only [Sum.elim_inl,Sum.elim_inr,old,dist_comm (Sum.inr b : X ⊕ C),mix]
        rw [d.regular c hc' (r b) (hr b hb'),dist_comm (d.root c) (r b)]
        ring
      · obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hc
        simpa only [Sum.elim_inr,old] using new b c
          (fun h => hbc (congrArg Sum.inr h))

end MetricKMedianRecovery.PhaseLeafGeometry

end OAI
