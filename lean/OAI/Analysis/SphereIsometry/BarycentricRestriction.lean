import OAI.Analysis.SphereIsometry.BarycentricFlags

namespace OAI

/-! # Embeddings of complexes and exact restriction under subdivision -/

noncomputable section

namespace Tingley.FiniteComplex

universe u v w z
variable {V : Type u} {W : Type v} [Fintype V] [Fintype W]
variable [DecidableEq V] [DecidableEq W]

structure Embedding (K : FiniteComplex V) (L : FiniteComplex W) where
  toEmbedding : V ↪ W
  map_mem_iff : ∀ s : Finset V, s.map toEmbedding ∈ L.faces ↔ s ∈ K.faces

namespace Embedding

variable {K : FiniteComplex V} {L : FiniteComplex W}

def full (e : V ↪ W) : Embedding (FiniteComplex.full : FiniteComplex V)
    (FiniteComplex.full : FiniteComplex W) where
  toEmbedding := e
  map_mem_iff := fun _ => by simp

def faceMap (e : Embedding K L) : FaceVertex K ↪ FaceVertex L where
  toFun s := ⟨s.val.map e.toEmbedding,
    (e.map_mem_iff s.val).mpr s.property.1, Finset.map_nonempty.mpr s.property.2⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    exact Finset.map_injective e.toEmbedding (congrArg Subtype.val h)

@[simp] theorem faceMap_val (e : Embedding K L) (s : FaceVertex K) :
    (e.faceMap s).val = s.val.map e.toEmbedding := rfl

def sd (e : Embedding K L) : Embedding K.sd L.sd where
  toEmbedding := e.faceMap
  map_mem_iff := by
    intro c
    rw [mem_sd_iff, mem_sd_iff]
    constructor
    · intro hc a ha b hb
      have h := hc (e.faceMap a) (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
        (e.faceMap b) (Finset.mem_map.mpr ⟨b, hb, rfl⟩)
      exact h.imp Finset.map_subset_map.mp Finset.map_subset_map.mp
    · intro hc a ha b hb
      obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨b', hb', rfl⟩ := Finset.mem_map.mp hb
      exact (hc a' ha' b' hb').imp Finset.map_subset_map.mpr Finset.map_subset_map.mpr

def preimage (e : Embedding K L) (s : Finset W) : Finset V :=
  Finset.univ.filter (fun v => e.toEmbedding v ∈ s)

@[simp] theorem mem_preimage (e : Embedding K L) {s : Finset W} {v : V} :
    v ∈ e.preimage s ↔ e.toEmbedding v ∈ s := by
  simp [preimage]

theorem map_preimage (e : Embedding K L) (s : Finset W)
    (hs : ∀ w ∈ s, ∃ v, e.toEmbedding v = w) :
    (e.preimage s).map e.toEmbedding = s := by
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact (e.mem_preimage).mp hv
  · intro hw
    obtain ⟨v, rfl⟩ := hs w hw
    exact Finset.mem_map.mpr ⟨v, e.mem_preimage.mpr hw, rfl⟩

theorem exists_face_preimage (e : Embedding K L) {s : Finset W} (hs : s ∈ L.faces)
    (hrange : ∀ w ∈ s, ∃ v, e.toEmbedding v = w) :
    ∃ t ∈ K.faces, t.map e.toEmbedding = s := by
  refine ⟨e.preimage s, ?_, e.map_preimage s hrange⟩
  apply (e.map_mem_iff _).mp
  rwa [e.map_preimage s hrange]

variable {I : Type w} {J : Type z} [DecidableEq I] [DecidableEq J]

theorem faceCarrier_map (e : Embedding K L) (i : I ↪ J)
    {cV : V → Finset I} {cW : W → Finset J}
    (h : ∀ v, cW (e.toEmbedding v) = (cV v).map i) (s : Finset V) :
    faceCarrier cW (s.map e.toEmbedding) = (faceCarrier cV s).map i := by
  ext j
  constructor
  · intro hj
    obtain ⟨w, hw, hj⟩ := mem_faceCarrier.mp hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    rw [h] at hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_map.mpr ⟨a, mem_faceCarrier.mpr ⟨v, hv, ha⟩, rfl⟩
  · intro hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hj
    obtain ⟨v, hv, ha⟩ := mem_faceCarrier.mp ha
    refine mem_faceCarrier.mpr ⟨e.toEmbedding v,
      Finset.mem_map.mpr ⟨v, hv, rfl⟩, ?_⟩
    rw [h]
    exact Finset.mem_map.mpr ⟨a, ha, rfl⟩

theorem sdCarrier_faceMap (e : Embedding K L) (i : I ↪ J)
    {cV : V → Finset I} {cW : W → Finset J}
    (h : ∀ v, cW (e.toEmbedding v) = (cV v).map i) (s : FaceVertex K) :
    L.sdCarrier cW (e.faceMap s) = (K.sdCarrier cV s).map i :=
  e.faceCarrier_map i h s.val

theorem faceMap_range_iff (e : Embedding K L) {cW : W → Finset J} {A : Finset J}
    (h : ∀ w, cW w ⊆ A ↔ ∃ v, e.toEmbedding v = w) (s : FaceVertex L) :
    L.sdCarrier cW s ⊆ A ↔ ∃ t : FaceVertex K, e.faceMap t = s := by
  constructor
  · intro hs
    have hvertices : ∀ w ∈ s.val, ∃ v, e.toEmbedding v = w := by
      intro w hw
      apply (h w).mp
      intro j hj
      exact hs (mem_faceCarrier.mpr ⟨w, hw, hj⟩)
    obtain ⟨t, ht, hts⟩ := e.exists_face_preimage s.property.1 hvertices
    have hne : t.Nonempty := by
      have : (t.map e.toEmbedding).Nonempty := hts.symm ▸ s.property.2
      exact Finset.map_nonempty.mp this
    refine ⟨⟨t, ht, hne⟩, ?_⟩
    exact Subtype.ext hts
  · rintro ⟨t, rfl⟩
    intro j hj
    obtain ⟨w, hw, hj⟩ := mem_faceCarrier.mp hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact (h _).mpr ⟨v, rfl⟩ hj

theorem face_range_iff (e : Embedding K L) {cW : W → Finset J} {A : Finset J}
    (h : ∀ w, cW w ⊆ A ↔ ∃ v, e.toEmbedding v = w) {s : Finset W}
    (hs : s ∈ L.faces) :
    faceCarrier cW s ⊆ A ↔ ∃ t ∈ K.faces, t.map e.toEmbedding = s := by
  constructor
  · intro hsub
    apply e.exists_face_preimage hs
    intro w hw
    apply (h w).mp
    intro j hj
    exact hsub (mem_faceCarrier.mpr ⟨w, hw, hj⟩)
  · rintro ⟨t, ht, rfl⟩
    intro j hj
    obtain ⟨w, hw, hj⟩ := mem_faceCarrier.mp hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact (h _).mpr ⟨v, rfl⟩ hj

end Embedding

end Tingley.FiniteComplex

end

end OAI
