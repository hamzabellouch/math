import Mathlib
import OAI.CategoryTheory.Thomason.SubdivisionPairing

namespace OAI

/-! Extension Anodyne. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma nonDegenerate_of_unique_face {X : SSet.{u}} {n : ℕ}
    (x : X.obj (op ⦋n⦌)) (hx : x ∈ X.nonDegenerate n)
    (y : X.obj (op ⦋n + 1⦌)) (j : Fin (n + 2)) (hj : X.δ j y = x)
    (hunique : ∀ i : Fin (n + 2), X.δ i y = x → i = j) :
    y ∈ X.nonDegenerate (n + 1) := by
  by_contra hy
  rw [← X.mem_degenerate_iff_notMem_nonDegenerate,
    X.degenerate_eq_iUnion_range_σ] at hy
  simp only [Set.mem_iUnion, Set.mem_range] at hy
  obtain ⟨i, z, rfl⟩ := hy
  have hm : X.map (SimplexCategory.δ j ≫ SimplexCategory.σ i).op z = x := by
    rw [op_comp, CategoryTheory.Functor.map_comp]
    exact hj
  have : Mono (SimplexCategory.δ j ≫ SimplexCategory.σ i) :=
    X.mono_of_nonDegenerate ⟨x, hx⟩ _ z hm
  have he : z = x := by
    rw [SimplexCategory.eq_id_of_mono (SimplexCategory.δ j ≫ SimplexCategory.σ i), op_id, CategoryTheory.Functor.map_id] at hm
    exact hm
  have h1 : X.δ i.castSucc (X.σ i z) = x := by
    rw [← CategoryTheory.comp_apply, SimplicialObject.δ_comp_σ_self]
    exact he
  have h2 : X.δ i.succ (X.σ i z) = x := by
    rw [← CategoryTheory.comp_apply, SimplicialObject.δ_comp_σ_succ]
    exact he
  have hh := (hunique i.castSucc h1).trans (hunique i.succ h2).symm
  exact (Fin.ne_of_lt i.castSucc_lt_succ) hh

lemma exPairSimplex_face_unique (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hk : exIndex X n x = k)
    (hpos : 0 < k.val) (hI : ¬ ExTypeI X n x) (i : Fin (n + 2))
    (hi : (SSet.ex.obj X).δ i (exPairSimplex X n k x) = x) : i = k.succ := by
  have hx : ExLevel X n (ordinalVertex n k) x := hk ▸ exIndex_level X n x
  by_cases hil : i ≤ k.castSucc
  · let j : Fin (n + 1) := ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
    have hjk : j.val + 1 = k.val := by dsimp [j]; omega
    have hlev := exPairSimplex_lowFace_level X n j k hjk i hil x hx
    rw [hi] at hlev
    have hh := (exIndex_le_iff X n x j).mpr hlev
    rw [hk] at hh
    have hval : k.val ≤ j.val := hh
    omega
  · by_contra hine
    have hgt : k.succ < i := by
      have h1 : k.val < i.val := lt_of_not_ge hil
      have h2 : i.val ≠ k.val + 1 := fun h => hine (Fin.ext h)
      change k.val + 1 < i.val
      omega
    cases n with
    | zero => have hk0 := k.isLt; omega
    | succ n =>
      cases k using Fin.lastCases with
      | last => have hi0 := i.isLt; have hgt0 : n + 2 < i.val := hgt; omega
      | cast k =>
        cases i using Fin.cases with
        | zero => exact (not_lt_of_ge (Fin.zero_le _) hgt).elim
        | succ i =>
          have hki : k.castSucc < i := by
            change k.val < i.val
            change k.val + 1 < i.val + 1 at hgt
            omega
          have he := exPairSimplex_highFace X n k i hki x
          apply hI
          exact ⟨k, (SSet.ex.obj X).δ i x, hk, he.symm.trans hi⟩

lemma exPairSimplex_nonDegenerate (X : SSet.{u}) (n : ℕ)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hx : ExTypeII X n x) :
    exPairSimplex X n (exIndex X n x) x ∈ (SSet.ex.obj X).nonDegenerate (n + 1) :=
  nonDegenerate_of_unique_face x hx.1 _ _ (exPairSimplex_face X n _ x)
    (exPairSimplex_face_unique X n _ x rfl hx.2.1 hx.2.2)

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma extraVertexMap_lowDegeneracy (n : ℕ) (i k : Fin (n + 1)) (hik : i ≤ k) :
    extraVertexMap.{u} (n + 1) k.succ ≫ SimplexCategory.sd.map (SimplexCategory.σ i) =
      SimplexCategory.sd.map (SimplexCategory.σ i.castSucc) ≫ extraVertexMap n k := by
  change PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ =
    PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  apply OrderHom.ext
  funext s
  exact extraVertex_lowDegeneracy n i k hik s

lemma extraVertexMap_highDegeneracy (n : ℕ) (i k : Fin (n + 1)) (hki : k < i) :
    extraVertexMap.{u} (n + 1) k.castSucc ≫ SimplexCategory.sd.map (SimplexCategory.σ i) =
      SimplexCategory.sd.map (SimplexCategory.σ i.succ) ≫ extraVertexMap n k := by
  change PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ =
    PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  apply OrderHom.ext
  funext s
  exact extraVertex_highDegeneracy n i k hki s

lemma exPairSimplex_lowDegeneracy (X : SSet.{u}) (n : ℕ) (i k : Fin (n + 1)) (hik : i ≤ k)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    exPairSimplex X (n + 1) k.succ ((SSet.ex.obj X).σ i x) =
      (SSet.ex.obj X).σ i.castSucc (exPairSimplex X n k x) := by
  apply ULift.ext
  change extraVertexMap (n + 1) k.succ ≫ (SimplexCategory.sd.map (SimplexCategory.σ i) ≫ x.down) =
    SimplexCategory.sd.map (SimplexCategory.σ i.castSucc) ≫ (extraVertexMap n k ≫ x.down)
  erw [← Category.assoc, extraVertexMap_lowDegeneracy n i k hik, Category.assoc]

lemma exPairSimplex_highDegeneracy (X : SSet.{u}) (n : ℕ) (i k : Fin (n + 1)) (hki : k < i)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    exPairSimplex X (n + 1) k.castSucc ((SSet.ex.obj X).σ i x) =
      (SSet.ex.obj X).σ i.succ (exPairSimplex X n k x) := by
  apply ULift.ext
  change extraVertexMap (n + 1) k.castSucc ≫ (SimplexCategory.sd.map (SimplexCategory.σ i) ≫ x.down) =
    SimplexCategory.sd.map (SimplexCategory.σ i.succ) ≫ (extraVertexMap n k ≫ x.down)
  erw [← Category.assoc, extraVertexMap_highDegeneracy n i k hki, Category.assoc]

lemma exLevel_highDegeneracy {X : SSet.{u}} {n : ℕ} (i k : Fin (n + 1)) (hki : k < i)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hx : ExLevel X n (ordinalVertex n k) x) :
    ExLevel X (n + 1) (ordinalVertex (n + 1) k.castSucc) ((SSet.ex.obj X).σ i x) := by
  apply exLevel_map_of _ _ (SimplexCategory.σ i) _ x hx
  intro a ha
  change k < i.predAbove a.down
  unfold Fin.predAbove
  split_ifs with h
  · change k.val < a.down.val - 1
    have h1 : k.val < i.val := hki
    have h2 : i.val < a.down.val := h
    omega
  · exact ha

lemma exIndex_degeneracy_ne_self (X : SSet.{u}) (n : ℕ) (i : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hpos : 0 < i.val) :
    exIndex X (n + 1) ((SSet.ex.obj X).σ i x) ≠ i.castSucc := by
  intro he
  let j : Fin (n + 1) := ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  have hji : j.succ = i.castSucc := Fin.ext (by dsimp [j]; omega)
  have hx : ExLevel X n (ordinalVertex n j) x := by
    have h := exLevel_lowFace j i.castSucc (by rw [hji]) ((SSet.ex.obj X).σ i x)
      (by rw [hji, ← he]; exact exIndex_level _ _ _)
    have hh : (SSet.ex.obj X).δ i.castSucc ((SSet.ex.obj X).σ i x) = x := by
      rw [← CategoryTheory.comp_apply, SimplicialObject.δ_comp_σ_self]
      rfl
    rwa [hh] at h
  have hji' : j < i := by change i.val - 1 < i.val; omega
  have hlev := exLevel_highDegeneracy i j hji' x hx
  have hh := (exIndex_le_iff _ _ _ _).mpr hlev
  rw [he] at hh
  have hh' : i.val ≤ j.val := hh
  have hj' : j.val < i.val := hji'
  omega

lemma exPairSimplex_reflects_nonDegenerate (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hk : exIndex X n x = k) (hp : 0 < k.val)
    (hx : exPairSimplex X n k x ∈ (SSet.ex.obj X).nonDegenerate (n + 1)) :
    x ∈ (SSet.ex.obj X).nonDegenerate n := by
  cases n with
  | zero => simp
  | succ n =>
    by_contra hdeg
    rw [← (SSet.ex.obj X).mem_degenerate_iff_notMem_nonDegenerate,
      (SSet.ex.obj X).degenerate_eq_iUnion_range_σ] at hdeg
    simp only [Set.mem_iUnion, Set.mem_range] at hdeg
    obtain ⟨i, y, rfl⟩ := hdeg
    by_cases hik : i.val < k.val
    · let j : Fin (n + 1) := ⟨k.val - 1, by have := k.isLt; omega⟩
      have hj : j.succ = k := Fin.ext (by dsimp [j]; omega)
      have hij : i ≤ j := by change i.val ≤ k.val - 1; omega
      rw [← hj, exPairSimplex_lowDegeneracy X n i j hij y] at hx
      exact hx ((SSet.ex.obj X).σ_mem_degenerate _ _)
    · have hki : k.val ≤ i.val := Nat.le_of_not_gt hik
      let j : Fin (n + 1) := ⟨k.val, lt_of_le_of_lt hki i.isLt⟩
      have hj : j.castSucc = k := Fin.ext rfl
      rcases lt_or_eq_of_le hki with hjlt | hjeq
      · rw [← hj, exPairSimplex_highDegeneracy X n i j hjlt y] at hx
        exact hx ((SSet.ex.obj X).σ_mem_degenerate _ _)
      · have hk' : k = i.castSucc := Fin.ext hjeq
        exact exIndex_degeneracy_ne_self X n i y (by rw [← hjeq]; exact hp) (hk.trans hk')

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma exPairSimplex_input_not_typeI (X : SSet.{u}) (n : ℕ)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌))
    (hx : exPairSimplex X n (exIndex X n x) x ∈ (SSet.ex.obj X).nonDegenerate (n + 1)) :
    ¬ ExTypeI X n x := by
  cases n with
  | zero => exact not_false
  | succ n =>
    rintro ⟨k, y, hk, rfl⟩
    rw [hk, exPairSimplex_twice] at hx
    exact hx ((SSet.ex.obj X).σ_mem_degenerate _ _)

lemma exTypeI_preimage_typeII (X : SSet.{u}) (n : ℕ)
    (x : (SSet.ex.obj X).obj (op ⦋n + 1⦌))
    (hx : x ∈ (SSet.ex.obj X).nonDegenerate (n + 1))
    (hp : 0 < (exIndex X (n + 1) x).val) (hI : ExTypeI X (n + 1) x) :
    ∃ y : (SSet.ex.obj X).obj (op ⦋n⦌), ExTypeII X n y ∧
      exPairSimplex X n (exIndex X n y) y = x := by
  obtain ⟨k, y, hk, rfl⟩ := hI
  have hyk := exTypeI_preimage_index X n k y hk
  have hpk : 0 < k.val := by simpa only [hk, Fin.val_castSucc] using hp
  refine ⟨y, ⟨exPairSimplex_reflects_nonDegenerate X n k y hyk hpk hx, ?_, ?_⟩, ?_⟩
  · rwa [hyk]
  · apply exPairSimplex_input_not_typeI
    rwa [hyk]
  · rw [hyk]

lemma exPairSimplex_injective (X : SSet.{u}) (n : ℕ)
    (x y : (SSet.ex.obj X).obj (op ⦋n⦌))
    (h : exPairSimplex X n (exIndex X n x) x =
      exPairSimplex X n (exIndex X n y) y) : x = y := by
  have hk : exIndex X n x = exIndex X n y := by
    have he := congrArg (exIndex X (n + 1)) h
    rw [exIndex_pair _ _ _ _ (exIndex_level _ _ _),
      exIndex_pair _ _ _ _ (exIndex_level _ _ _)] at he
    exact Fin.ext (congrArg (fun t : Fin (n + 2) => t.val) he)
  have he := congrArg (fun z => (SSet.ex.obj X).δ (exIndex X n x).succ z) h
  rw [exPairSimplex_face, hk, exPairSimplex_face] at he
  exact he

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

abbrev ExPairIndices (X : SSet.{u}) := Σ n : ℕ, {x : (SSet.ex.obj X).obj (op ⦋n⦌) // ExTypeII X n x}

lemma exIndex_pos_of_notMem (X : SSet.{u}) (n : ℕ)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌))
    (hx : x ∉ (SSet.Subcomplex.range (exComparison.app X)).obj (op ⦋n⦌)) :
    0 < (exIndex X n x).val := by
  apply Nat.pos_of_ne_zero
  intro h
  have he : exIndex X n x = 0 := Fin.ext h
  exact hx ((exIndex_zero_iff X n x).mp he)

lemma exIndex_notMem_of_pos (X : SSet.{u}) (n : ℕ)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hx : 0 < (exIndex X n x).val) :
    x ∉ (SSet.Subcomplex.range (exComparison.app X)).obj (op ⦋n⦌) := by
  intro h
  have he := (exIndex_zero_iff X n x).mpr h
  simp only [he, Fin.val_zero, lt_self_iff_false] at hx

noncomputable def exPairingCore (X : SSet.{u}) :
    (SSet.Subcomplex.range (exComparison.app X)).PairingCore where
  ι := ExPairIndices X
  dim s := s.1
  simplex s := exPairSimplex X s.1 (exIndex X s.1 s.2.1) s.2.1
  index s := (exIndex X s.1 s.2.1).succ
  nonDegenerate₁ s := exPairSimplex_nonDegenerate X s.1 s.2.1 s.2.2
  nonDegenerate₂ s := by rw [exPairSimplex_face]; exact s.2.2.1
  notMem₁ s := exIndex_notMem_of_pos X _ _ (by
    rw [exIndex_pair _ _ _ _ (exIndex_level _ _ _)]
    exact s.2.2.2.1)
  notMem₂ s := by
    rw [exPairSimplex_face]
    exact exIndex_notMem_of_pos X _ _ s.2.2.2.1
  injective_type₁' {s t} h := by
    obtain ⟨n, ⟨x, hx⟩⟩ := s
    obtain ⟨m, ⟨y, hy⟩⟩ := t
    have hnm : n = m := Nat.add_right_cancel (SSet.S.dim_eq_of_mk_eq h)
    subst m
    have he := exPairSimplex_injective X n x y ((SSet.S.ext_iff _ _).mp h)
    subst y
    rfl
  injective_type₂' {s t} h := by
    simp only [exPairSimplex_face] at h
    obtain ⟨n, ⟨x, hx⟩⟩ := s
    obtain ⟨m, ⟨y, hy⟩⟩ := t
    have hnm : n = m := SSet.S.dim_eq_of_mk_eq h
    subst m
    have he := (SSet.S.ext_iff _ _).mp h
    change x = y at he
    subst y
    rfl
  type₁_ne_type₂' s t h := by
    simp only [exPairSimplex_face] at h
    obtain ⟨n, ⟨x, hx⟩⟩ := s
    obtain ⟨m, ⟨y, hy⟩⟩ := t
    have hnm : n + 1 = m := SSet.S.dim_eq_of_mk_eq h
    subst m
    have he := (SSet.S.ext_iff _ _).mp h
    change exPairSimplex X n (exIndex X n x) x = y at he
    exact hy.2.2 (he ▸ exPairSimplex_typeI X n x)
  surjective' x := by
    obtain ⟨n, x, hnd, hn, rfl⟩ := x.mk_surjective
    have hp := exIndex_pos_of_notMem X n x hn
    by_cases hI : ExTypeI X n x
    · cases n with
      | zero => exact hI.elim
      | succ n =>
        obtain ⟨y, hy, he⟩ := exTypeI_preimage_typeII X n x hnd hp hI
        exact ⟨⟨n, ⟨y, hy⟩⟩, Or.inl (congrArg SSet.S.mk he.symm)⟩
    · refine ⟨⟨n, ⟨x, hnd, hp, hI⟩⟩, Or.inr ?_⟩
      simp only [exPairSimplex_face]
      rfl

instance exPairingCore_isProper (X : SSet.{u}) : (exPairingCore X).IsProper where
  isUniquelyCodimOneFace s := by
    apply (SSet.S.IsUniquelyCodimOneFace.iff _ _).mpr
    change ∃! i, (SSet.ex.obj X).δ i (exPairSimplex X s.1 (exIndex X s.1 s.2.1) s.2.1) =
      (SSet.ex.obj X).δ (exIndex X s.1 s.2.1).succ
        (exPairSimplex X s.1 (exIndex X s.1 s.2.1) s.2.1)
    rw [exPairSimplex_face]
    exact ⟨_, exPairSimplex_face X _ _ _,
      exPairSimplex_face_unique X _ _ _ rfl s.2.2.2.1 s.2.2.2.2⟩

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma exPairSimplex_other_face_index_lt (X : SSet.{u}) (n : ℕ)
    (y x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hy : ExTypeII X n y) (hx : ExTypeII X n x)
    (hxy : x ≠ y) (i : Fin (n + 2))
    (hi : (SSet.ex.obj X).δ i (exPairSimplex X n (exIndex X n y) y) = x) :
    exIndex X n x < exIndex X n y := by
  let k := exIndex X n y
  have hp : 0 < k.val := hy.2.1
  have hlev : ExLevel X n (ordinalVertex n k) y := exIndex_level _ _ _
  by_cases hil : i ≤ k.castSucc
  · let j : Fin (n + 1) := ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
    have hjk : j.val + 1 = k.val := by dsimp [j]; omega
    have h := exPairSimplex_lowFace_level X n j k hjk i hil y hlev
    rw [hi] at h
    apply lt_of_le_of_lt ((exIndex_le_iff X n x j).mpr h)
    change k.val - 1 < k.val
    omega
  · have hine : i ≠ k.succ := by
      intro he
      rw [he, exPairSimplex_face] at hi
      exact hxy hi.symm
    have hgt : k.succ < i := by
      have h1 : k.val < i.val := lt_of_not_ge hil
      have h2 : i.val ≠ k.val + 1 := fun h => hine (Fin.ext h)
      change k.val + 1 < i.val
      omega
    have hle : exIndex X n x ≤ k := by
      apply (exIndex_le_iff X n x k).mpr
      rw [← hi]
      exact exLevel_highFace k i _ ((exPairSimplex_level_iff X n k k le_rfl y).mpr hlev)
    apply lt_of_le_of_ne hle
    intro he
    cases n with
    | zero => have hk0 := k.isLt; omega
    | succ n =>
      cases hk : k using Fin.lastCases with
      | last =>
        have hgt0 : n + 2 < i.val := by
          rw [hk] at hgt
          exact hgt
        have hi0 := i.isLt
        omega
      | cast j =>
        cases i using Fin.cases with
        | zero => exact (not_lt_of_ge (Fin.zero_le _) hgt).elim
        | succ i =>
          have hji : j.castSucc < i := by
            rw [hk] at hgt
            change j.val + 1 < i.val + 1 at hgt
            change j.val < i.val
            omega
          apply hx.2.2
          refine ⟨j, (SSet.ex.obj X).δ i y, he.trans hk, ?_⟩
          change (SSet.ex.obj X).δ i.succ (exPairSimplex X (n + 1) k y) = x at hi
          rw [hk] at hi
          exact (exPairSimplex_highFace X n j i hji y).symm.trans hi

noncomputable def exPairRank (X : SSet.{u}) (s : ExPairIndices X) : ℕ :=
  s.1 * (s.1 + 1) + (exIndex X s.1 s.2.1).val

lemma exPairRank_decreases (X : SSet.{u}) (s t : ExPairIndices X)
    (h : (exPairingCore X).AncestralRel s t) : exPairRank X s < exPairRank X t := by
  have hd : s.1 < t.1 + 1 := SSet.N.dim_lt_of_lt h.2
  obtain ⟨n, ⟨x, hx⟩⟩ := s
  obtain ⟨m, ⟨y, hy⟩⟩ := t
  change n < m + 1 at hd
  rcases (Nat.lt_succ_iff.mp hd).lt_or_eq with hnm | hnm
  · have hn := (exIndex X n x).isLt
    have hm := (exIndex X m y).isLt
    change n * (n + 1) + (exIndex X n x).val < m * (m + 1) + (exIndex X m y).val
    nlinarith
  · subst m
    have hxy : x ≠ y := by
      intro he
      subst y
      exact h.1 rfl
    have hle := (SSet.N.le_iff_exists_mono).mp h.2.le
    obtain ⟨f, hf, he⟩ := hle
    change ⦋n⦌ ⟶ ⦋n + 1⦌ at f
    have : Mono f := hf
    obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
    change (SSet.ex.obj X).δ i (exPairSimplex X n (exIndex X n y) y) =
      (SSet.ex.obj X).δ (exIndex X n x).succ (exPairSimplex X n (exIndex X n x) x) at he
    rw [exPairSimplex_face] at he
    have hk := exPairSimplex_other_face_index_lt X n y x hy hx hxy i he
    exact Nat.add_lt_add_left hk _

instance exPairingCore_isRegular (X : SSet.{u}) : (exPairingCore X).IsRegular where
  wf := Subrelation.wf (fun {s t} h => exPairRank_decreases X s t h) (measure (exPairRank X)).wf

theorem exComparison_strongAnodyne (X : SSet.{u}) :
    SSet.strongAnodyneExtensions (exComparison.app X) :=
  ⟨inferInstance, (exPairingCore X).pairing, inferInstance⟩

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory

lemma exComparison_anodyne (X : SSet.{u}) : SSet.anodyneExtensions (exComparison.app X) :=
  SSet.strongAnodyneExtensions_le_anodyneExtensions _ (exComparison_strongAnodyne X)

theorem exComparison_weak (X : SSet.{u}) : simplicialWeakEquivalences (exComparison.app X) :=
  TopologicalHorn.anodyne_weak_equivalence _ (exComparison_anodyne X)

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory

theorem ex_map_weak_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    simplicialWeakEquivalences (SSet.ex.map f) ↔ simplicialWeakEquivalences f := by
  have he := exComparison.naturality f
  constructor
  · intro h
    exact simplicialWeakEquivalences.of_postcomp f (exComparison.app Y)
      (exComparison_weak Y) (he.symm ▸ simplicialWeakEquivalences.comp_mem _ _ (exComparison_weak X) h)
  · intro h
    exact simplicialWeakEquivalences.of_precomp (exComparison.app X) (SSet.ex.map f)
      (exComparison_weak X) (he ▸ simplicialWeakEquivalences.comp_mem _ _ h (exComparison_weak Y))

lemma exSquared_map_weak_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    simplicialWeakEquivalences ((SSet.ex ⋙ SSet.ex).map f) ↔ simplicialWeakEquivalences f := by
  change simplicialWeakEquivalences (SSet.ex.map (SSet.ex.map f)) ↔ _
  rw [ex_map_weak_iff, ex_map_weak_iff]

lemma thomasonWeak_iff_nerve {C D : OmegaCategory.{u}} (f : C ⟶ D) :
    simplicialWeakEquivalences (thomasonRight.map f) ↔
      simplicialWeakEquivalences (streetNerveFunctor.map f) :=
  exSquared_map_weak_iff _

lemma thomasonWeakFinite_iff_nerve {n : ℕ} {C D : OmegaCategory.NCategory.{u} n} (f : C ⟶ D) :
    simplicialWeakEquivalences ((thomasonRightFinite n).map f) ↔
      simplicialWeakEquivalences ((streetNerveFinite n).map f) :=
  exSquared_map_weak_iff _

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

variable {E : Type u} [PartialOrder E]

noncomputable def flagOldLast (A : Set E) (s : MeetingChains A) : A :=
  ⟨chainLast (chainIntersection A s).val,
    (chainIntersection A s).property _ (chainGreatest_mem _)⟩

lemma flagOldLast_mono (A : Set E) {s t : MeetingChains A} (h : s ≤ t) :
    flagOldLast A s ≤ flagOldLast A t :=
  chainLast.monotone ((chainIntersection A).monotone h)

lemma le_flagOldLast (A : Set E) (s : MeetingChains A) (a : E)
    (ha : a ∈ s.val.finset) (haA : a ∈ A) : a ≤ (flagOldLast A s).val := by
  classical
  apply le_chainGreatest
  exact Finset.mem_filter.mpr ⟨ha, haA⟩

lemma flagOldLast_of_old (A : Set E) (s : NonemptyFiniteChains E)
    (hs : ∀ a ∈ s.finset, a ∈ A) (hm : ∃ a ∈ s.finset, a ∈ A) :
    (flagOldLast A ⟨s, hm⟩).val = chainLast s := by
  classical
  change chainLast (chainIntersection A ⟨s, hm⟩).val = chainLast s
  congr 1
  apply NonemptyFiniteChains.ext
  exact Finset.filter_eq_self.mpr hs

noncomputable def conicalFlagRetraction (A : Set E) (p : A) (c : A →o A)
    (hc : ∀ a : A, a.val ≤ (c a).val) (hp : ∀ a : A, p ≤ c a) :
    NonemptyFiniteChains E →o A := by
  classical
  let old (s : NonemptyFiniteChains E) := ∀ a ∈ s.finset, a ∈ A
  let meet (s : NonemptyFiniteChains E) := ∃ a ∈ s.finset, a ∈ A
  let r (s : NonemptyFiniteChains E) : A :=
    if hs : old s then ⟨chainLast s, hs _ (chainGreatest_mem s)⟩
    else if hs : meet s then c (flagOldLast A ⟨s, hs⟩) else p
  refine ⟨r, fun s t hst => ?_⟩
  by_cases ht : old t
  · have hs : old s := fun a ha => ht a (hst ha)
    change r s ≤ r t
    dsimp [r]
    rw [dite_eq_left hs, dite_eq_left ht]
    exact chainLast.monotone hst
  · by_cases hs : old s
    · have htm : meet t := by
        obtain ⟨a, ha⟩ := s.nonempty
        exact ⟨a, hst ha, hs a ha⟩
      dsimp [r]
      rw [dite_eq_left hs, dite_eq_right ht, dite_eq_left htm]
      exact (le_flagOldLast A ⟨t, htm⟩ (chainLast s) (hst (chainGreatest_mem s))
        (hs _ (chainGreatest_mem s))).trans (hc _)
    · by_cases hsm : meet s
      · have htm : meet t := by
          obtain ⟨a, ha, haA⟩ := hsm
          exact ⟨a, hst ha, haA⟩
        dsimp [r]
        rw [dite_eq_right hs, dite_eq_right ht, dite_eq_left hsm, dite_eq_left htm]
        exact c.monotone (flagOldLast_mono A hst)
      · dsimp [r]
        rw [dite_eq_right hs, dite_eq_right ht, dite_eq_right hsm]
        split_ifs with htm
        · exact hp _
        · exact le_rfl

lemma conicalFlagRetraction_old (A : Set E) (p : A) (c : A →o A)
    (hc : ∀ a : A, a.val ≤ (c a).val) (hp : ∀ a : A, p ≤ c a)
    (s : NonemptyFiniteChains E) (hs : ∀ a ∈ s.finset, a ∈ A) :
    (conicalFlagRetraction A p c hc hp s).val = chainLast s := by
  classical
  simp only [conicalFlagRetraction, OrderHom.coe_mk, dite_eq_left hs]

lemma conicalFlagRetraction_map_old (A : Set E) (p : A) (c : A →o A)
    (hc : ∀ a : A, a.val ≤ (c a).val) (hp : ∀ a : A, p ≤ c a)
    (s : NonemptyFiniteChains A) :
    conicalFlagRetraction A p c hc hp (s.map (OrderHom.Subtype.val _)) = chainLast s := by
  apply Subtype.ext
  rw [conicalFlagRetraction_old]
  · exact chainGreatest_map s (OrderHom.Subtype.val _)
  · intro a ha
    obtain ⟨b, _, rfl⟩ := (s.mem_map_iff _ a).mp ha
    exact b.property

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

def HornFaces (n : ℕ) (k : Fin (n+1)) : Set (NonemptyFiniteChains (ULift.{u} (Fin (n+1)))) :=
  {s | ∃ a : Fin (n+1), a ≠ k ∧ ULift.up a ∉ s.finset}

noncomputable def hornFacePoint {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) : HornFaces.{u} n k := by
  classical
  refine ⟨⟨{ULift.up k}, by simp, by simp⟩, ?_⟩
  have hex : ∃ a : Fin (n+1), a ≠ k := by
    by_cases hk : k = 0
    · exact ⟨⟨1, by omega⟩, fun h => by have := congrArg Fin.val (h.trans hk); simp at this⟩
    · exact ⟨0, Ne.symm hk⟩
  obtain ⟨a, ha⟩ := hex
  exact ⟨a, ha, by simpa using ha⟩

noncomputable def hornFaceCone {n : ℕ} (k : Fin (n+1)) : HornFaces.{u} n k →o HornFaces.{u} n k where
  toFun s := ⟨⟨insert (ULift.up k) s.val.finset, by simp, by
    intro a b
    exact le_total a.val b.val⟩, by
    obtain ⟨a, hak, ha⟩ := s.property
    exact ⟨a, hak, by simpa using And.intro hak ha⟩⟩
  monotone' s t h := by
    intro a ha
    rcases Finset.mem_insert.mp ha with ha | ha
    · exact Finset.mem_insert.mpr (Or.inl ha)
    · exact Finset.mem_insert.mpr (Or.inr (h ha))

lemma le_hornFaceCone {n : ℕ} (k : Fin (n+1)) (s : HornFaces.{u} n k) :
    s.val ≤ (hornFaceCone k s).val := by
  intro a ha
  exact Finset.mem_insert_of_mem ha

lemma hornFacePoint_le_cone {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) (s : HornFaces.{u} n k) :
    hornFacePoint hn k ≤ hornFaceCone k s := by
  classical
  intro a ha
  have ha' : a = ULift.up k := by
    change a ∈ (hornFacePoint hn k).val.finset at ha
    simpa [hornFacePoint] using ha
  subst a
  exact Finset.mem_insert_self _ _

noncomputable def hornFlagRetraction {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1)) :
    NonemptyFiniteChains (NonemptyFiniteChains (ULift.{u} (Fin (n+1)))) →o HornFaces.{u} n k :=
  conicalFlagRetraction _ (hornFacePoint hn k) (hornFaceCone k)
    (le_hornFaceCone k) (hornFacePoint_le_cone hn k)

lemma hornFlagRetraction_old {n : ℕ} (hn : 1 ≤ n) (k : Fin (n+1))
    (s : NonemptyFiniteChains (HornFaces.{u} n k)) :
    hornFlagRetraction hn k (s.map (OrderHom.Subtype.val _)) = chainLast s :=
  conicalFlagRetraction_map_old _ _ _ _ _ _

lemma allowedChains_iff {E : Type u} [PartialOrder E] (K : (nerve E).Subcomplex)
    (c : NonemptyFiniteChains E) :
    (∃ s : (K : SSet).N, simplexChain (subcomplexN K s).simplex = c) ↔
      (chainSimplex c).simplex ∈ K.obj (op ⦋(chainSimplex c).dim⦌) := by
  constructor
  · rintro ⟨s, hs⟩
    have he : subcomplexN K s = chainSimplex c := by
      apply nerveNondegenerateChains.injective
      change simplexChain _ = simplexChain _
      rw [hs, simplexChain_chainSimplex]
    have hh : (subcomplexN K s).simplex ∈ K.obj (op ⦋(subcomplexN K s).dim⦌) := s.simplex.property
    exact he ▸ hh
  · intro h
    exact ⟨SSet.N.mk ⟨(chainSimplex c).simplex, h⟩
      ((K.mem_nonDegenerate_iff _).mpr (chainSimplex c).nonDegenerate),
      simplexChain_chainSimplex c⟩

lemma orderedSimplexSubcomplex_mem_iff {n d : ℕ}
    (K : (SSet.stdSimplex.{u}.obj ⦋n⦌).Subcomplex)
    (x : (nerve (ULift.{u} (Fin (n+1)))) _⦋d⦌) :
    x ∈ (orderedSimplexSubcomplex K).obj _ ↔
      (SSet.stdSimplex.isoNerve n).inv.app _ x ∈ K.obj _ := by
  constructor
  · rintro ⟨y, rfl⟩
    have he := congrArg (fun f => f.app (op ⦋d⦌) y.val) (SSet.stdSimplex.isoNerve.{u} n).hom_inv_id
    change (SSet.stdSimplex.isoNerve n).inv.app _
      ((SSet.stdSimplex.isoNerve n).hom.app _ y.val) = y.val at he
    change (SSet.stdSimplex.isoNerve n).inv.app _
      ((SSet.stdSimplex.isoNerve n).hom.app _ y.val) ∈ K.obj _
    rw [he]
    exact y.property
  · intro h
    refine ⟨⟨(SSet.stdSimplex.isoNerve n).inv.app _ x, h⟩, ?_⟩
    exact congrArg (fun f => f.app (op ⦋d⦌) x) (SSet.stdSimplex.isoNerve.{u} n).inv_hom_id

lemma hornFaces_allowed_iff {n : ℕ} (k : Fin (n+1))
    (c : NonemptyFiniteChains (ULift.{u} (Fin (n+1)))) :
    (∃ s : (orderedSimplexSubcomplex (SSet.horn n k) : SSet).N,
      simplexChain (subcomplexN _ s).simplex = c) ↔ c ∈ HornFaces n k := by
  rw [allowedChains_iff, orderedSimplexSubcomplex_mem_iff, SSet.mem_horn_iff_notMem_range]
  have hm (a : Fin (n+1)) :
      a ∈ Set.range ((SSet.stdSimplex.isoNerve n).inv.app _ (chainSimplex c).simplex) ↔
        ULift.up a ∈ c.finset := by
    conv_rhs => rw [← simplexChain_chainSimplex c, mem_simplexChain]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply ULift.ext
      exact hi
    · rintro ⟨i, hi⟩
      exact ⟨i, congrArg ULift.down hi⟩
  simp only [HornFaces, Set.mem_ofPred_eq, exists_prop, hm]

noncomputable def hornFacesIso {n : ℕ} (k : Fin (n+1)) :
    AllowedChains (orderedSimplexSubcomplex (SSet.horn.{u} n k)) ≃o HornFaces.{u} n k where
  toFun c := ⟨c.val, (hornFaces_allowed_iff k c.val).mp c.property⟩
  invFun c := ⟨c.val, (hornFaces_allowed_iff k c.val).mpr c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder Limits

variable {E : Type u} [PartialOrder E]

lemma simplexVertices_yoneda {n : ℕ} (x : (nerve E) _⦋n⦌) :
    simplexNerveIso.hom.app ⦋n⦌ ≫ nerveMap (simplexVertices x).monotone.functor =
      SSet.yonedaEquiv.symm x := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  rfl

lemma lastVertex_nerve :
    sdNerveMap ≫ nerveMap (chainLast (X := E)).monotone.functor =
      lastVertex.app (nerve E) := by
  apply (isColimitOfPreserves SSet.sd (nerve E).isColimitCoconeN').hom_ext
  intro s
  change SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫ (_ ≫ _) =
    SSet.sd.map (SSet.yonedaEquiv.symm s.simplex) ≫ _
  rw [← Category.assoc, sdNerveMap_fac, Category.assoc, lastVertex.naturality]
  rw [lastVertex_stdSimplex, Category.assoc]
  congr 1
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply nerve.ext_of_isThin
  funext j
  exact chainGreatest_map (x.obj j) (simplexVertices s.simplex)

lemma sdSubcomplex_lastVertex (K : (nerve E).Subcomplex) :
    SSet.sd.map K.ι ≫ sdNerveMap ≫ nerveMap chainLast.monotone.functor =
      lastVertex.app (K : SSet) ≫ K.ι := by
  rw [lastVertex_nerve]
  exact lastVertex.naturality K.ι

lemma sdTwiceSubcomplex_lastVertex (K : (nerve E).Subcomplex) :
    (sdTwiceSubcomplexIso K).hom ≫ nerveMap chainLast.monotone.functor =
      lastVertex.app (SSet.sd.obj (K : SSet)) ≫ (sdSubcomplexIso K).hom := by
  change (SSet.sd.map (sdSubcomplexMap K) ≫ sdNerveMap) ≫ _ = _
  rw [Category.assoc, lastVertex_nerve]
  exact lastVertex.naturality (sdSubcomplexMap K)

end Thomason.Subdivision

end

end OAI
