import OAI.Analysis.SphereIsometry.SubdivisionData
import OAI.Analysis.SphereIsometry.BarycentricRestriction

namespace OAI

/-! # The exact original-face restriction of every concrete subdivision -/

noncomputable section

namespace Tingley

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def iterEmbedding (e : I ↪ J) : (k : ℕ) →
    FiniteComplex.Embedding (iterData I k).complex (iterData J k).complex
  | 0 => FiniteComplex.Embedding.full e
  | k + 1 => (iterEmbedding e k).sd

theorem iterEmbedding_carrier (e : I ↪ J) (k : ℕ)
    (v : (iterData I k).Vertex) :
    (iterData J k).carrier ((iterEmbedding e k).toEmbedding v) =
      ((iterData I k).carrier v).map e := by
  induction k with
  | zero =>
      change I at v
      change ({e v} : Finset J) = ({v} : Finset I).map e
      exact (Finset.map_singleton e v).symm
  | succ k ih =>
      exact (iterEmbedding e k).sdCarrier_faceMap e ih v

theorem iterEmbedding_range_iff (e : I ↪ J) (k : ℕ)
    (v : (iterData J k).Vertex) :
    (iterData J k).carrier v ⊆ Finset.univ.map e ↔
      ∃ w, (iterEmbedding e k).toEmbedding w = v := by
  induction k with
  | zero =>
      change J at v
      change ({v} : Finset J) ⊆ Finset.univ.map e ↔ ∃ w : I, e w = v
      simp only [Finset.singleton_subset_iff, Finset.mem_map,
        Finset.mem_univ, true_and]
  | succ k ih => exact (iterEmbedding e k).faceMap_range_iff ih v

theorem iterEmbedding_faceCarrier (e : I ↪ J) (k : ℕ)
    (s : Finset (iterData I k).Vertex) :
    FiniteComplex.faceCarrier (iterData J k).carrier
        (s.map (iterEmbedding e k).toEmbedding) =
      (FiniteComplex.faceCarrier (iterData I k).carrier s).map e :=
  (iterEmbedding e k).faceCarrier_map e (iterEmbedding_carrier e k) s

theorem iterEmbedding_face_range_iff (e : I ↪ J) (k : ℕ)
    {s : Finset (iterData J k).Vertex} (hs : s ∈ (iterData J k).complex.faces) :
    FiniteComplex.faceCarrier (iterData J k).carrier s ⊆ Finset.univ.map e ↔
      ∃ t ∈ (iterData I k).complex.faces, t.map (iterEmbedding e k).toEmbedding = s :=
  (iterEmbedding e k).face_range_iff (iterEmbedding_range_iff e k) hs

def lastFaceEmbedding (m k : ℕ) : IterVertex m k ↪ IterVertex (m + 1) k :=
  (iterEmbedding (Fin.castSuccEmb : Fin (m + 1) ↪ Fin ((m + 1) + 1)) k).toEmbedding

theorem lastFace_carrier (m k : ℕ) (v : IterVertex m k) :
    iterCarrier (m + 1) k (lastFaceEmbedding m k v) =
      (iterCarrier m k v).map Fin.castSuccEmb :=
  iterEmbedding_carrier Fin.castSuccEmb k v

theorem lastFace_faceCarrier (m k : ℕ) (s : Finset (IterVertex m k)) :
    faceCarrier (m + 1) k (s.map (lastFaceEmbedding m k)) =
      (faceCarrier m k s).map Fin.castSuccEmb :=
  iterEmbedding_faceCarrier Fin.castSuccEmb k s

theorem lastFace_range_iff (m k : ℕ) (v : IterVertex (m + 1) k) :
    Fin.last (m + 1) ∉ iterCarrier (m + 1) k v ↔
      ∃ w, lastFaceEmbedding m k w = v := by
  have h := iterEmbedding_range_iff
    (Fin.castSuccEmb : Fin (m + 1) ↪ Fin ((m + 1) + 1)) k v
  simpa only [iterCarrier, lastFaceEmbedding, Finset.map_eq_image,
    Fin.coe_castSuccEmb, Fin.image_castSucc, Finset.subset_compl_singleton] using h

theorem lastFace_mem_iff (m k : ℕ) (s : Finset (IterVertex m k)) :
    s.map (lastFaceEmbedding m k) ∈ iterComplex (m + 1) k ↔ s ∈ iterComplex m k :=
  (iterEmbedding Fin.castSuccEmb k).map_mem_iff s

theorem lastFace_face_range_iff {m k : ℕ} {s : Finset (IterVertex (m + 1) k)}
    (hs : s ∈ iterComplex (m + 1) k) :
    Fin.last (m + 1) ∉ faceCarrier (m + 1) k s ↔
      ∃ t ∈ iterComplex m k, t.map (lastFaceEmbedding m k) = s := by
  have h := iterEmbedding_face_range_iff
    (Fin.castSuccEmb : Fin (m + 1) ↪ Fin ((m + 1) + 1)) k hs
  simpa only [faceCarrier, iterCarrier, iterComplex, lastFaceEmbedding,
    Finset.map_eq_image, Fin.coe_castSuccEmb, Fin.image_castSucc,
    Finset.subset_compl_singleton] using h

theorem lastFace_map_top_mem (m k : ℕ) {s : Finset (IterVertex m k)}
    (hs : s ∈ topCells m k) :
    s.map (lastFaceEmbedding m k) ∈ codimFaces (m + 1) k := by
  obtain ⟨hsface, hscard⟩ := mem_topCells.mp hs
  exact mem_codimFaces.mpr ⟨(lastFace_mem_iff m k s).mpr hsface, by simpa using hscard⟩

theorem lastFace_top_image (m k : ℕ) :
    (topCells m k).map (Finset.mapEmbedding (lastFaceEmbedding m k)).toEmbedding =
      (codimFaces (m + 1) k).filter
        (fun s => Fin.last (m + 1) ∉ faceCarrier (m + 1) k s) := by
  ext s
  constructor
  · intro hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hs
    apply Finset.mem_filter.mpr
    refine ⟨lastFace_map_top_mem m k ht, ?_⟩
    change Fin.last (m + 1) ∉ faceCarrier (m + 1) k (t.map (lastFaceEmbedding m k))
    rw [lastFace_faceCarrier]
    simp only [Finset.mem_map, not_exists, not_and]
    intro i hi
    exact Fin.castSucc_ne_last i
  · intro hs
    obtain ⟨hscodim, hboundary⟩ := Finset.mem_filter.mp hs
    obtain ⟨hsface, hscard⟩ := mem_codimFaces.mp hscodim
    obtain ⟨t, htface, hts⟩ := (lastFace_face_range_iff hsface).mp hboundary
    apply Finset.mem_map.mpr
    refine ⟨t, mem_topCells.mpr ⟨htface, ?_⟩, hts⟩
    have hcard := congrArg Finset.card hts
    simpa [hscard] using hcard

end Tingley

end

end OAI
