import OAI.Geometry.HeilbronnTriangle.NormDecomposition

namespace OAI


noncomputable section

namespace Problem355.NormDecomposition

open scoped BigOperators

variable {ι : Type*} [LinearOrder ι]

abbrev IncreasingTriple (ι : Type*) [LinearOrder ι] :=
  {t : ι × ι × ι // t.1 < t.2.1 ∧ t.2.1 < t.2.2}

def tripleToSet (t : IncreasingTriple ι) : {s : Finset ι // s.card = 3} :=
  ⟨{t.val.1, t.val.2.1, t.val.2.2},
    Finset.card_eq_three.mpr ⟨_, _, _, ne_of_lt t.property.1,
      ne_of_lt (lt_trans t.property.1 t.property.2), ne_of_lt t.property.2, rfl⟩⟩

def tripleFromSet (s : {s : Finset ι // s.card = 3}) : IncreasingTriple ι :=
  ⟨(s.val.orderEmbOfFin s.property 0, s.val.orderEmbOfFin s.property 1,
      s.val.orderEmbOfFin s.property 2),
    (s.val.orderEmbOfFin s.property).strictMono (by decide),
    (s.val.orderEmbOfFin s.property).strictMono (by decide)⟩

private theorem triple_vector_strictMono (t : IncreasingTriple ι) :
    StrictMono (![t.val.1, t.val.2.1, t.val.2.2] : Fin 3 → ι) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  · exact t.property.1
  · exact t.property.2

@[simp] theorem tripleFromSet_tripleToSet (t : IncreasingTriple ι) :
    tripleFromSet (tripleToSet t) = t := by
  have h : (![t.val.1, t.val.2.1, t.val.2.2] : Fin 3 → ι) =
      (tripleToSet t).val.orderEmbOfFin (tripleToSet t).property := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      fin_cases i <;> simp [tripleToSet]
    · exact triple_vector_strictMono t
  apply Subtype.ext
  apply Prod.ext
  · exact (congrFun h 0).symm
  · apply Prod.ext
    · exact (congrFun h 1).symm
    · exact (congrFun h 2).symm

@[simp] theorem tripleToSet_tripleFromSet (s : {s : Finset ι // s.card = 3}) :
    tripleToSet (tripleFromSet s) = s := by
  apply Subtype.ext
  have h := Finset.image_orderEmbOfFin_univ s.val s.property
  simpa [tripleToSet, tripleFromSet, Fin.univ_succ] using h

def tripleSetEquiv : IncreasingTriple ι ≃ {s : Finset ι // s.card = 3} where
  toFun := tripleToSet
  invFun := tripleFromSet
  left_inv := tripleFromSet_tripleToSet
  right_inv := tripleToSet_tripleFromSet

variable [Fintype ι]

theorem card_increasingTriple :
    Fintype.card (IncreasingTriple ι) = Nat.choose (Fintype.card ι) 3 := by
  rw [Fintype.card_congr tripleSetEquiv, Fintype.card_finset_len]

def increasingTripleEquivFin :
    IncreasingTriple ι ≃ Fin (Nat.choose (Fintype.card ι) 3) :=
  Fintype.equivFinOfCardEq card_increasingTriple

variable {R : Type*} [CommRing R]

theorem increasingSum_eq_sum_triples (f : ι → ι → ι → R) :
    increasingSum f = ∑ t : IncreasingTriple ι, f t.val.1 t.val.2.1 t.val.2.2 := by
  unfold increasingSum
  simpa only [Finset.sum_filter, Fintype.sum_prod_type] using
    (Finset.sum_subtype
      (Finset.univ.filter (fun t : ι × ι × ι => t.1 < t.2.1 ∧ t.2.1 < t.2.2))
      (fun _ => by simp)
      (fun t : ι × ι × ι => f t.1 t.2.1 t.2.2))

theorem increasingSum_eq_sum_fin (f : ι → ι → ι → R) :
    increasingSum f = ∑ a : Fin (Nat.choose (Fintype.card ι) 3),
      let t := (increasingTripleEquivFin (ι := ι)).symm a
      f t.val.1 t.val.2.1 t.val.2.2 := by
  rw [increasingSum_eq_sum_triples]
  exact ((increasingTripleEquivFin (ι := ι)).symm.sum_comp
    (fun t : IncreasingTriple ι => f t.val.1 t.val.2.1 t.val.2.2)).symm

def decompositionRows {X : Type*} (c : ι → ι → ι → R) (m : ι → X → R)
    (a : Fin (Nat.choose (Fintype.card ι) 3)) : Fin 3 → X → R :=
  let t := (increasingTripleEquivFin (ι := ι)).symm a
  ![fun x => c t.val.1 t.val.2.1 t.val.2.2 * m t.val.1 x,
    m t.val.2.1, m t.val.2.2]

theorem alternating_sum_eq_sum_determinants {X : Type*}
    (c : ι → ι → ι → R) (m : ι → X → R)
    (h12 : ∀ i k, c i i k = 0) (h13 : ∀ i j, c i j i = 0)
    (h23 : ∀ i j, c i j j = 0)
    (hs12 : ∀ i j k, c j i k = -c i j k)
    (hs23 : ∀ i j k, c i k j = -c i j k) (x y z : X) :
    (∑ i, ∑ j, ∑ k, c i j k * m i x * m j y * m k z) =
      ∑ a : Fin (Nat.choose (Fintype.card ι) 3),
        Matrix.det !![
          decompositionRows c m a 0 x, decompositionRows c m a 0 y,
            decompositionRows c m a 0 z;
          decompositionRows c m a 1 x, decompositionRows c m a 1 y,
            decompositionRows c m a 1 z;
          decompositionRows c m a 2 x, decompositionRows c m a 2 y,
            decompositionRows c m a 2 z] := by
  rw [alternating_triple_sum c h12 h13 h23 hs12 hs23
    (fun i => m i x) (fun i => m i y) (fun i => m i z),
    increasingSum_eq_sum_fin]
  apply Finset.sum_congr rfl
  intro a _
  simp [decompositionRows, Matrix.det_fin_three]
  ring

end Problem355.NormDecomposition

end

end OAI
