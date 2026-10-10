import OAI.Analysis.NuclearUltrapower.SOSSemantics

namespace OAI

section

noncomputable section
namespace NuclearUltrapower.SOS

def genSet : Finset SL := (generators.map interpret).toFinset

theorem generators_det : ∀ m ∈ generators, (toMatrix m).det = 1 := by
  decide +kernel

theorem generators_inverse : ∀ m ∈ generators, matInv m ∈ generators := by
  decide +kernel

theorem genSet_inv {g : SL} (h : g ∈ genSet) : g⁻¹ ∈ genSet := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  exact ⟨matInv m, generators_inverse m hm, interpret_inv m (generators_det m hm)⟩

def GoodWord (n : ℕ) (m : Mat3) : Prop :=
  (toMatrix m).det = 1 ∧ ∃ w : List SL, w.prod = interpret m ∧ w.length ≤ n ∧
    ∀ s ∈ w, s ∈ genSet

theorem goodWord_one : GoodWord 0 matOne := by
  refine ⟨by rw [toMatrix_one, Matrix.det_one], [], ?_, by simp, by simp⟩
  simp only [List.prod_nil, interpret_one]

theorem goodWord_generator {m : Mat3} (hm : m ∈ generators) : GoodWord 1 m := by
  refine ⟨generators_det m hm, [interpret m], by simp, by simp, ?_⟩
  intro s hs
  have : s = interpret m := by simpa using hs
  subst s
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨m, hm, rfl⟩)

theorem goodWord_mul {n k : ℕ} {a b : Mat3} (ha : GoodWord n a) (hb : GoodWord k b) :
    GoodWord (n+k) (matMul a b) := by
  obtain ⟨had, wa, hwa, hla, hsa⟩ := ha
  obtain ⟨hbd, wb, hwb, hlb, hsb⟩ := hb
  refine ⟨by rw [toMatrix_mul, Matrix.det_mul, had, hbd, one_mul], wa ++ wb, ?_, ?_, ?_⟩
  · rw [List.prod_append, hwa, hwb, interpret_mul a b had hbd]
  · simp only [List.length_append]; omega
  · intro s hs
    exact (List.mem_append.mp hs).elim (hsa s) (hsb s)

theorem goodWord_mono {n k : ℕ} {a : Mat3} (ha : GoodWord n a) (h : n ≤ k) : GoodWord k a := by
  obtain ⟨had, w, hw, hl, hs⟩ := ha
  exact ⟨had, w, hw, hl.trans h, hs⟩

theorem goodWord_inv {n : ℕ} {a : Mat3} (ha : GoodWord n a) : GoodWord n (matInv a) := by
  obtain ⟨had, w, hw, hl, hs⟩ := ha
  refine ⟨by rw [toMatrix_inv, Matrix.det_adjugate, had, one_pow], w.reverse.map Inv.inv, ?_, ?_, ?_⟩
  · rw [List.map_reverse, ← List.prod_inv_reverse, hw, interpret_inv a had]
  · simpa using hl
  · intro s hmem
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hmem
    exact genSet_inv (hs g (List.mem_reverse.mp hg))

def matrixWord : List Mat3 → Mat3
  | [] => matOne
  | a::as => matMul a (matrixWord as)

theorem matrixWord_good (w : List Mat3) (hw : ∀ m ∈ w, m ∈ generators) :
    GoodWord w.length (matrixWord w) := by
  induction w with
  | nil => exact goodWord_one
  | cons a w ih =>
    have ha := goodWord_generator (hw a (by simp))
    have ht := ih (fun m hm => hw m (by simp [hm]))
    simpa only [List.length_cons, Nat.add_comm, matrixWord] using goodWord_mul ha ht

def generator0 : Mat3 := [1, -1, 0, 0, 1, 0, 0, 0, 1]
def generator1 : Mat3 := [1, 1, 0, 0, 1, 0, 0, 0, 1]
def generator2 : Mat3 := [1, 0, -1, 0, 1, 0, 0, 0, 1]
def generator3 : Mat3 := [1, 0, 1, 0, 1, 0, 0, 0, 1]
def generator4 : Mat3 := [1, 0, 0, -1, 1, 0, 0, 0, 1]
def generator5 : Mat3 := [1, 0, 0, 1, 1, 0, 0, 0, 1]
def generator6 : Mat3 := [1, 0, 0, 0, 1, -1, 0, 0, 1]
def generator7 : Mat3 := [1, 0, 0, 0, 1, 1, 0, 0, 1]
def generator8 : Mat3 := [1, 0, 0, 0, 1, 0, -1, 0, 1]
def generator9 : Mat3 := [1, 0, 0, 0, 1, 0, 1, 0, 1]
def generator10 : Mat3 := [1, 0, 0, 0, 1, 0, 0, -1, 1]
def generator11 : Mat3 := [1, 0, 0, 0, 1, 0, 0, 1, 1]
def basisWords : List (List Mat3) := [[generator0, generator5], [generator2, generator9], [generator3, generator8], [generator1, generator4], [generator0, generator0], [generator0, generator2], [generator2, generator11], [generator0, generator7], [generator4, generator0], [generator6, generator0], [generator0, generator8], [generator8, generator0], [generator0, generator10], [generator0], [generator0, generator11], [generator9, generator0], [generator0, generator9], [generator7, generator0], [generator5, generator0], [generator0, generator6], [generator3, generator10], [generator0, generator3], [generator2, generator2], [generator2, generator4], [generator4, generator2], [generator2, generator6], [generator8, generator2], [generator10, generator2], [generator2], [generator11, generator2], [generator9, generator2], [generator2, generator7], [generator5, generator2], [generator2, generator5], [generator4, generator4], [generator4, generator6], [generator6, generator9], [generator4, generator8], [generator11, generator4], [generator4, generator10], [generator4], [generator4, generator11], [generator10, generator4], [generator4, generator9], [generator7, generator8], [generator4, generator7], [generator6, generator11], [generator7, generator10], [generator6, generator6], [generator8, generator6], [generator10, generator6], [generator6], [generator11, generator6], [generator9, generator6], [generator8, generator8], [generator8, generator10], [generator8], [generator8, generator11], [generator10, generator10], [generator10], [], [generator11], [generator11, generator11], [generator9, generator10], [generator9], [generator9, generator11], [generator9, generator9], [generator8, generator7], [generator10, generator7], [generator7], [generator11, generator7], [generator9, generator7], [generator7, generator7], [generator6, generator10], [generator7, generator11], [generator6, generator8], [generator5, generator6], [generator10, generator5], [generator5, generator8], [generator5, generator10], [generator5], [generator5, generator11], [generator5, generator9], [generator11, generator5], [generator5, generator7], [generator7, generator9], [generator5, generator5], [generator4, generator3], [generator3, generator4], [generator3, generator6], [generator8, generator3], [generator10, generator3], [generator3], [generator11, generator3], [generator9, generator3], [generator3, generator7], [generator3, generator5], [generator5, generator3], [generator3, generator3], [generator1, generator6], [generator2, generator10], [generator1, generator2], [generator4, generator1], [generator6, generator1], [generator8, generator1], [generator1, generator8], [generator1, generator10], [generator1], [generator1, generator11], [generator1, generator9], [generator9, generator1], [generator7, generator1], [generator5, generator1], [generator1, generator3], [generator3, generator11], [generator1, generator7], [generator1, generator1], [generator0, generator4], [generator2, generator8], [generator3, generator9], [generator1, generator5]]
theorem basis_words : basisWords.map matrixWord = basis := by decide +kernel

theorem basisWords_length : ∀ w ∈ basisWords, w.length ≤ 2 := by decide +kernel

theorem basisWords_support : ∀ w ∈ basisWords, ∀ m ∈ w, m ∈ generators := by decide +kernel

theorem basis_good {m : Mat3} (hm : m ∈ basis) : GoodWord 2 m := by
  rw [← basis_words] at hm
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
  exact goodWord_mono (matrixWord_good w (basisWords_support w hw)) (basisWords_length w hw)

end NuclearUltrapower.SOS
end
end

section

noncomputable section
namespace NuclearUltrapower.SOS

/-- The subgroup generated by the elementary integer matrices. -/
def elementary : Subgroup SL := Subgroup.closure (genSet : Set SL)
abbrev E := elementary

def eInterpret (m : Mat3) : E := by
  classical
  exact if h : interpret m ∈ elementary then ⟨interpret m, h⟩ else 1

theorem goodWord_mem {n : ℕ} {m : Mat3} (h : GoodWord n m) : interpret m ∈ elementary := by
  obtain ⟨_, w, hw, _, hs⟩ := h
  rw [← hw]
  exact elementary.list_prod_mem (fun g hg => Subgroup.subset_closure (hs g hg))

theorem eInterpret_coe {n : ℕ} {m : Mat3} (h : GoodWord n m) :
    (eInterpret m : SL) = interpret m := by
  simp only [eInterpret, dite_eq_left (goodWord_mem h)]

@[simp] theorem eInterpret_one : eInterpret matOne = 1 := by
  apply Subtype.ext
  rw [eInterpret_coe goodWord_one, interpret_one]
  rfl

theorem eInterpret_mul {n k : ℕ} {a b : Mat3} (ha : GoodWord n a) (hb : GoodWord k b) :
    eInterpret (matMul a b) = eInterpret a * eInterpret b := by
  apply Subtype.ext
  change (eInterpret (matMul a b) : SL) = (eInterpret a : SL) * (eInterpret b : SL)
  rw [eInterpret_coe (goodWord_mul ha hb), eInterpret_coe ha, eInterpret_coe hb,
    interpret_mul a b ha.1 hb.1]

theorem eInterpret_inv {n : ℕ} {a : Mat3} (ha : GoodWord n a) :
    eInterpret (matInv a) = (eInterpret a)⁻¹ := by
  apply Subtype.ext
  change (eInterpret (matInv a) : SL) = (eInterpret a : SL)⁻¹
  rw [eInterpret_coe (goodWord_inv ha), eInterpret_coe ha, interpret_inv a ha.1]

def eGenSet : Finset E := (generators.map eInterpret).toFinset

theorem mem_eGenSet {g : E} : g ∈ eGenSet ↔ (g : SL) ∈ genSet := by
  constructor
  · intro h
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    rw [eInterpret_coe (goodWord_generator hm)]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨m,hm,rfl⟩)
  · intro h
    obtain ⟨m, hm, he⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    apply List.mem_toFinset.mpr
    refine List.mem_map.mpr ⟨m,hm,?_⟩
    apply Subtype.ext
    exact (eInterpret_coe (goodWord_generator hm)).trans he

theorem eGenSet_inv {g : E} (hg : g ∈ eGenSet) : g⁻¹ ∈ eGenSet :=
  mem_eGenSet.mpr (genSet_inv (mem_eGenSet.mp hg))

theorem eWord {n : ℕ} {m : Mat3} (h : GoodWord n m) :
    ∃ w : List E, w.prod = eInterpret m ∧ w.length ≤ n ∧ ∀ s ∈ w, s ∈ eGenSet := by
  obtain ⟨hd,w,hw,hlen,hmem⟩ := h
  let f (s : {s // s ∈ w}) : E := ⟨s.1, Subgroup.subset_closure (hmem _ s.2)⟩
  refine ⟨w.attach.map f, ?_, by simpa using hlen, ?_⟩
  · apply Subtype.ext
    change elementary.subtype ((w.attach.map f).prod) = (eInterpret m : SL)
    rw [map_list_prod, List.map_map]
    simp only [Function.comp_def]
    have he : w.attach.map (fun s => elementary.subtype (f s)) = w := by
      simpa only [f, Subgroup.coe_subtype, List.map_id_fun, id_eq] using
        (List.attach_map_val (l := w) (f := id))
    rw [he, hw, eInterpret_coe ⟨hd,w,hw,hlen,hmem⟩]
  · intro s hs
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hs
    exact mem_eGenSet.mpr (hmem _ t.2)

theorem eSet_generates : Subgroup.closure (eGenSet : Set E) = ⊤ := by
  apply top_unique
  intro g _
  let K := Subgroup.closure (eGenSet : Set E)
  have he : elementary ≤ K.map elementary.subtype := by
    apply (Subgroup.closure_le _).mpr
    intro s hs
    have hs' : s ∈ elementary := Subgroup.subset_closure hs
    exact ⟨⟨s,hs'⟩, Subgroup.subset_closure (mem_eGenSet.mpr hs), rfl⟩
  obtain ⟨k,hk,hkg⟩ := he g.2
  have : k = g := Subtype.ext hkg
  exact this ▸ hk

end NuclearUltrapower.SOS
end
end

end OAI
