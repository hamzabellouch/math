import Mathlib
import OAI.CategoryTheory.Thomason.SubdivisionFaces

namespace OAI

/-! Subdivision Pairing. -/

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma chainLast_singletonChain {A : Type*} [PartialOrder A] (a : A) :
    chainLast (singletonChain a) = a :=
  Finset.mem_singleton.mp (chainGreatest_mem (singletonChain a))

lemma chainLast_chainUnionMap {A B : Type*} [PartialOrder A] [LinearOrder B]
    (f : A → NonemptyFiniteChains B) (g : A →o B)
    (hg : ∀ a, chainLast (f a) = g a) (s : NonemptyFiniteChains A) :
    chainLast (chainUnionMap f s) = g (chainLast s) := by
  apply le_antisymm
  · obtain ⟨a, ha, hb⟩ := (mem_chainUnionMap f s _).mp
      (chainGreatest_mem (chainUnionMap f s))
    exact (le_chainGreatest (f a) hb).trans ((hg a).le.trans (g.monotone (le_chainGreatest s ha)))
  · apply le_chainGreatest
    apply (mem_chainUnionMap f s _).mpr
    exact ⟨chainLast s, chainGreatest_mem s, hg (chainLast s) ▸ chainGreatest_mem (f (chainLast s))⟩

local instance subdivisionPairingExtraVertexLinearOrder (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))
local instance subdivisionPairingExtraVertexFintype (n : ℕ) : Fintype (OrdinalVertices.{u} n) :=
  inferInstanceAs (Fintype (ULift (Fin (n + 1))))

lemma mem_initialFlag (n : ℕ) (a b : OrdinalVertices.{u} n) :
    b ∈ (initialFlag ⦋n⦌ a).finset ↔ b ≤ a := by
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

noncomputable def collapseVertices (n : ℕ) (k : Fin (n + 1)) :
    OrdinalVertices.{u} (n + 1) →o OrdinalVertices.{u} n :=
  (SimplexCategory.toPartOrd.map (SimplexCategory.σ k)).hom

lemma collapseVertices_apply (n : ℕ) (k : Fin (n + 1)) (a : OrdinalVertices.{u} (n + 1)) :
    collapseVertices n k a = ordinalVertex n (k.predAbove a.down) := rfl

lemma face_collapse_le (n : ℕ) (k : Fin (n + 1)) (a : OrdinalVertices.{u} (n + 1)) :
    faceVertices n k.succ (collapseVertices n k a) ≤ a := by
  change k.succ.succAbove (k.predAbove a.down) ≤ a.down
  by_cases h : a.down = k.succ
  · rw [h, Fin.predAbove_succ_self, Fin.succAbove_succ_self]
    exact k.castSucc_le_succ
  · exact (Fin.succ_succAbove_predAbove h).le

lemma extraVertexFace_last (n : ℕ) (k : Fin (n + 1)) (a : OrdinalVertices.{u} (n + 1)) :
    chainLast (extraVertexFace n k a) = collapseVertices n k a := by
  classical
  unfold extraVertexFace
  split_ifs with h
  · erw [chainLast_initialFlag]
    apply ULift.ext
    change k = k.predAbove a.down
    rw [h, Fin.predAbove_succ_self]
  · exact chainLast_singletonChain _

lemma chainLast_extraVertex (n : ℕ) (k : Fin (n + 1)) (s : OrdinalChains.{u} (n + 1)) :
    chainLast (extraVertex n k s) = collapseVertices n k (chainLast s) :=
  chainLast_chainUnionMap _ _ (extraVertexFace_last n k) s

lemma extraVertex_initialFlag (n : ℕ) (k : Fin (n + 1)) (a : OrdinalVertices.{u} (n + 1)) :
    extraVertex n k (initialFlag ⦋n + 1⦌ a) = initialFlag ⦋n⦌ (collapseVertices n k a) := by
  apply NonemptyFiniteChains.ext
  ext b
  change b ∈ (chainUnionMap _ _).finset ↔ _
  erw [mem_chainUnionMap, mem_initialFlag]
  constructor
  · rintro ⟨c, hc, hb⟩
    have hbc := le_chainGreatest (extraVertexFace n k c) hb
    exact hbc.trans ((extraVertexFace_last n k c).le.trans ((collapseVertices n k).monotone ((mem_initialFlag _ _ _).mp hc)))
  · intro hb
    refine ⟨faceVertices n k.succ b, (mem_initialFlag _ _ _).mpr ?_, ?_⟩
    · exact ((faceVertices n k.succ).monotone hb).trans (face_collapse_le n k a)
    · erw [extraVertexFace_gap]
      exact (mem_singletonChain _ _).mpr rfl

lemma extraVertex_eq_initialFlag_of_last_inserted (n : ℕ) (k : Fin (n + 1))
    (s : OrdinalChains.{u} (n + 1)) (hs : chainLast s = ordinalVertex (n + 1) k.succ) :
    extraVertex n k s = initialFlag ⦋n⦌ (ordinalVertex n k) := by
  classical
  apply le_antisymm
  · apply (le_initialFlag _ _ _).mpr
    rw [chainLast_extraVertex, hs]
    change (ordinalVertex n (k.predAbove k.succ)) ≤ _
    rw [Fin.predAbove_succ_self]
  · intro b hb
    apply (mem_chainUnionMap _ _ _).mpr
    refine ⟨ordinalVertex (n + 1) k.succ, hs ▸ chainGreatest_mem s, ?_⟩
    change b ∈ (extraVertexFace n k (ordinalVertex (n + 1) k.succ)).finset
    have he : extraVertexFace n k (ordinalVertex (n + 1) k.succ) =
        initialFlag ⦋n⦌ (ordinalVertex n k) := ite_eq_left rfl
    exact he.symm ▸ hb

lemma predAbove_le_eq_of_castSucc_lt {n : ℕ} {j k : Fin (n + 1)} (hjk : j ≤ k)
    {i : Fin (n + 2)} (hij : j.castSucc < i) (hdi : k.predAbove i ≤ j) :
    i = k.succ ∧ j = k := by
  unfold Fin.predAbove at hdi
  split_ifs at hdi with h
  · have hi : i.val = k.val + 1 ∧ j.val = k.val := by
      simp only [Fin.le_iff_val_le_val, Fin.lt_def, Fin.val_castSucc,
        Fin.val_pred] at hdi hij hjk h
      omega
    exact ⟨Fin.ext hi.1, Fin.ext hi.2⟩
  · have : False := by
      simp only [Fin.le_iff_val_le_val, Fin.lt_def, Fin.val_castSucc,
        Fin.coe_castPred] at hdi hij
      omega
    exact this.elim

lemma extraVertex_partialLastVertex (n : ℕ) (j k : Fin (n + 1)) (hjk : j ≤ k)
    (s : OrdinalChains.{u} (n + 1)) :
    extraVertex n k (partialLastVertex (n + 1) (ordinalVertex (n + 1) j.castSucc) s) =
      partialLastVertex n (ordinalVertex n j) (extraVertex n k s) := by
  rw [partialLastVertex_apply, partialLastVertex_apply, chainLast_extraVertex]
  by_cases h : chainLast s ≤ ordinalVertex (n + 1) j.castSucc
  · rw [ite_eq_left h]
    have hc : collapseVertices n k (chainLast s) ≤ ordinalVertex n j := by
      have hd := (collapseVertices n k).monotone h
      change collapseVertices n k (chainLast s) ≤ ordinalVertex n (k.predAbove j.castSucc) at hd
      exact hd.trans (by rw [Fin.predAbove_castSucc_of_le _ _ hjk])
    rw [ite_eq_left hc]
  · rw [ite_eq_right h, extraVertex_initialFlag]
    by_cases hc : collapseVertices n k (chainLast s) ≤ ordinalVertex n j
    · rw [ite_eq_left hc]
      obtain ⟨hi, hjk'⟩ := predAbove_le_eq_of_castSucc_lt hjk (lt_of_not_ge h) hc
      subst j
      have hs : chainLast s = ordinalVertex (n + 1) k.succ := ULift.ext _ _ hi
      rw [extraVertex_eq_initialFlag_of_last_inserted n k s hs, hs]
      change initialFlag ⦋n⦌ (ordinalVertex n (k.predAbove k.succ)) = _
      rw [Fin.predAbove_succ_self]
    · rw [ite_eq_right hc]

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma extraVertexMap_partialLastMap (n : ℕ) (j k : Fin (n + 1)) (hjk : j ≤ k) :
    partialLastMap (n + 1) (ordinalVertex (n + 1) j.castSucc) ≫ extraVertexMap.{u} n k =
      extraVertexMap n k ≫ partialLastMap n (ordinalVertex n j) := by
  unfold partialLastMap extraVertexMap
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  apply OrderHom.ext
  funext s
  exact extraVertex_partialLastVertex n j k hjk s

lemma exPairSimplex_level_iff (X : SSet.{u}) (n : ℕ) (j k : Fin (n + 1)) (hjk : j ≤ k)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    ExLevel X (n + 1) (ordinalVertex (n + 1) j.castSucc) (exPairSimplex X n k x) ↔
      ExLevel X n (ordinalVertex n j) x := by
  change (partialLastMap _ _ ≫ (extraVertexMap n k ≫ x.down) = extraVertexMap n k ≫ x.down) ↔ _
  erw [← Category.assoc, extraVertexMap_partialLastMap n j k hjk, Category.assoc]
  constructor
  · intro h
    have hh := congrArg (SimplexCategory.sd.map (SimplexCategory.δ k.succ) ≫ ·) h
    change partialLastMap n (ordinalVertex n j) ≫ x.down = x.down
    simpa only [← Category.assoc, extraVertexMap_face, Category.id_comp] using hh
  · intro h
    erw [h]

lemma map_singletonChain {A B : Type*} [PartialOrder A] [PartialOrder B]
    (g : A →o B) (a : A) : (singletonChain a).map g = singletonChain (g a) := by
  apply NonemptyFiniteChains.ext
  ext b
  simp only [NonemptyFiniteChains.mem_map_iff, mem_singletonChain]
  exact ⟨fun ⟨a', h, e⟩ => h ▸ e.symm, fun h => ⟨a, rfl, h.symm⟩⟩

lemma map_chainUnionMap {A B C : Type*} [PartialOrder A] [LinearOrder B] [LinearOrder C]
    (f : A → NonemptyFiniteChains B) (g : B →o C) (s : NonemptyFiniteChains A) :
    (chainUnionMap f s).map g = chainUnionMap (fun a => (f a).map g) s := by
  apply NonemptyFiniteChains.ext
  ext c
  simp only [NonemptyFiniteChains.mem_map_iff, mem_chainUnionMap]
  exact ⟨fun ⟨b, ⟨a, ha, hb⟩, he⟩ => ⟨a, ha, b, hb, he⟩,
    fun ⟨a, ha, b, hb, he⟩ => ⟨b, ⟨a, ha, hb⟩, he⟩⟩

local instance subdivisionPairingFaceLinearOrder (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))
local instance subdivisionPairingFaceFintype (n : ℕ) : Fintype (OrdinalVertices.{u} n) :=
  inferInstanceAs (Fintype (ULift (Fin (n + 1))))

lemma faceVertices_of_lt (n : ℕ) (i : Fin (n + 2)) (a : OrdinalVertices.{u} n)
    (h : a.down.castSucc < i) :
    faceVertices n i a = ordinalVertex (n + 1) a.down.castSucc := by
  change ordinalVertex _ (i.succAbove a.down) = _
  rw [Fin.succAbove_of_castSucc_lt _ _ h]

lemma initialFlag_map_faceVertices (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (h : k.castSucc < i) :
    (initialFlag ⦋n⦌ (ordinalVertex n k)).map (faceVertices n i) =
      initialFlag ⦋n + 1⦌ (ordinalVertex (n + 1) k.castSucc) := by
  apply NonemptyFiniteChains.ext
  ext b
  rw [NonemptyFiniteChains.mem_map_iff, mem_initialFlag]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hak : a.down ≤ k := (mem_initialFlag _ _ _).mp ha
    rw [faceVertices_of_lt _ _ _ ((show a.down.castSucc ≤ k.castSucc from hak).trans_lt h)]
    exact hak
  · intro hb
    have hbn : b.down.val < n + 1 := lt_of_le_of_lt hb k.isLt
    let a := ordinalVertex n (⟨b.down.val, hbn⟩ : Fin (n + 1))
    refine ⟨a, (mem_initialFlag _ _ _).mpr hb, ?_⟩
    rw [faceVertices_of_lt _ _ _ (show a.down.castSucc < i from hb.trans_lt h)]
    rfl

lemma extraVertexFace_highFace (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (hki : k.castSucc < i) (a : OrdinalVertices.{u} (n + 1)) :
    extraVertexFace (n + 1) k.castSucc (faceVertices (n + 1) i.succ a) =
      (extraVertexFace n k a).map (faceVertices n i) := by
  classical
  by_cases ha : a.down = k.succ
  · have h : faceVertices (n + 1) i.succ a = ordinalVertex (n + 2) k.castSucc.succ := by
      rw [faceVertices_of_lt]
      · apply ULift.ext
        rw [ha]
        rfl
      · change a.down.val < i.val + 1
        rw [ha]
        exact Nat.succ_lt_succ hki
    rw [h]
    have hleft : extraVertexFace (n + 1) k.castSucc (ordinalVertex (n + 2) k.castSucc.succ) =
        initialFlag ⦋n + 1⦌ (ordinalVertex (n + 1) k.castSucc) := ite_eq_left rfl
    have hright : extraVertexFace n k a = initialFlag ⦋n⦌ (ordinalVertex n k) := ite_eq_left ha
    rw [hleft, hright, initialFlag_map_faceVertices n k i hki]
  · have hne : (faceVertices (n + 1) i.succ a).down ≠ k.castSucc.succ := by
      intro he
      have hh := (Fin.succAbove_right_injective (p := i.succ))
      apply ha
      apply hh
      calc
        i.succ.succAbove a.down = k.castSucc.succ := he
        _ = i.succ.succAbove k.succ := by
          rw [Fin.succAbove_of_castSucc_lt _ _ (show k.succ.castSucc < i.succ from Nat.succ_lt_succ hki)]
          rfl
    unfold extraVertexFace
    erw [ite_eq_right ha, ite_eq_right hne, map_singletonChain]
    congr 1
    have he := congrArg (fun f : ⦋n + 1⦌ ⟶ ⦋n + 1⦌ => f.toOrderHom a.down)
      (SimplexCategory.δ_comp_σ_of_gt hki)
    exact ULift.ext _ _ he

lemma extraVertex_highFace (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (hki : k.castSucc < i) (s : OrdinalChains.{u} (n + 1)) :
    extraVertex (n + 1) k.castSucc (s.map (faceVertices (n + 1) i.succ)) =
      (extraVertex n k s).map (faceVertices n i) := by
  change chainUnionMap _ _ = (chainUnionMap _ _).map _
  rw [chainUnionMap_map, map_chainUnionMap]
  congr 2
  funext a
  exact extraVertexFace_highFace n k i hki a

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

local instance subdivisionPairingChainLastLinearOrder (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))
local instance subdivisionPairingChainLastFintype (n : ℕ) : Fintype (OrdinalVertices.{u} n) :=
  inferInstanceAs (Fintype (ULift (Fin (n + 1))))

lemma chainLast_map {A B : Type*} [PartialOrder A] [PartialOrder B]
    (s : NonemptyFiniteChains A) (f : A →o B) :
    chainLast (s.map f) = f (chainLast s) := chainGreatest_map s f

lemma faceVertices_of_le (n : ℕ) (i : Fin (n + 2)) (a : OrdinalVertices.{u} n)
    (h : i ≤ a.down.castSucc) : faceVertices n i a = ordinalVertex (n + 1) a.down.succ := by
  change ordinalVertex _ (i.succAbove a.down) = _
  rw [Fin.succAbove_of_le_castSucc _ _ h]

lemma collapseVertices_succ_of_le (n : ℕ) (k a : Fin (n + 1)) (h : k ≤ a) :
    collapseVertices n k (ordinalVertex (n + 1) a.succ) = ordinalVertex n a := by
  change ordinalVertex n (k.predAbove a.succ) = _
  rw [Fin.predAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr h), Fin.pred_succ]

lemma extraVertex_lowFace_saturated (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (hik : i ≤ k.castSucc) (s : OrdinalChains.{u} n) (hs : ordinalVertex n k ≤ chainLast s) :
    partialLastVertex n (ordinalVertex n k) (extraVertex n k (s.map (faceVertices n i))) =
      initialFlag ⦋n⦌ (chainLast s) := by
  have hface : chainLast (s.map (faceVertices n i)) =
      ordinalVertex (n + 1) (chainLast s).down.succ := by
    rw [chainLast_map, faceVertices_of_le _ _ _ (hik.trans hs)]
  have hlast : chainLast (extraVertex n k (s.map (faceVertices n i))) = chainLast s := by
    rw [chainLast_extraVertex, hface, collapseVertices_succ_of_le n k _ hs]
    rfl
  by_cases he : chainLast s = ordinalVertex n k
  · have hinput : chainLast (s.map (faceVertices n i)) = ordinalVertex (n + 1) k.succ := by
      rw [hface, he]; rfl
    rw [extraVertex_eq_initialFlag_of_last_inserted n k _ hinput,
      partialLastVertex_initialFlag, he]
  · rw [partialLastVertex_apply, hlast, ite_eq_right (fun h => he (le_antisymm h hs))]

lemma extraVertex_lowFace_partialLastVertex (n : ℕ) (j k : Fin (n + 1))
    (hjk : j.val + 1 = k.val) (i : Fin (n + 2)) (hik : i ≤ k.castSucc)
    (s : OrdinalChains.{u} n) :
    partialLastVertex n (ordinalVertex n k)
      (extraVertex n k ((partialLastVertex n (ordinalVertex n j) s).map (faceVertices n i))) =
    partialLastVertex n (ordinalVertex n k) (extraVertex n k (s.map (faceVertices n i))) := by
  rw [partialLastVertex_apply n (ordinalVertex n j)]
  split_ifs with h
  · rfl
  · have hs : ordinalVertex n k ≤ chainLast s := by
      change k.val ≤ (chainLast s).down.val
      have hh : ¬ (chainLast s).down.val ≤ j.val := h
      omega
    rw [extraVertex_lowFace_saturated n k i hik s hs,
      extraVertex_lowFace_saturated n k i hik (initialFlag ⦋n⦌ (chainLast s))
        (by rw [chainLast_initialFlag]; exact hs), chainLast_initialFlag]

lemma extraVertexMap_lowFace_partialLastMap (n : ℕ) (j k : Fin (n + 1))
    (hjk : j.val + 1 = k.val) (i : Fin (n + 2)) (hik : i ≤ k.castSucc) :
    partialLastMap n (ordinalVertex n j) ≫ SimplexCategory.sd.map (SimplexCategory.δ i) ≫
      extraVertexMap.{u} n k ≫ partialLastMap n (ordinalVertex n k) =
    SimplexCategory.sd.map (SimplexCategory.δ i) ≫ extraVertexMap n k ≫
      partialLastMap n (ordinalVertex n k) := by
  change PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ ≫
    PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ =
    PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _
  repeat' erw [← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  apply OrderHom.ext
  funext s
  exact extraVertex_lowFace_partialLastVertex n j k hjk i hik s

lemma exPairSimplex_lowFace_level (X : SSet.{u}) (n : ℕ) (j k : Fin (n + 1))
    (hjk : j.val + 1 = k.val) (i : Fin (n + 2)) (hik : i ≤ k.castSucc)
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hx : ExLevel X n (ordinalVertex n k) x) :
    ExLevel X n (ordinalVertex n j) ((SSet.ex.obj X).δ i (exPairSimplex X n k x)) := by
  change partialLastMap n (ordinalVertex n j) ≫
    (SimplexCategory.sd.map (SimplexCategory.δ i) ≫ (extraVertexMap n k ≫ x.down)) =
    SimplexCategory.sd.map (SimplexCategory.δ i) ≫ (extraVertexMap n k ≫ x.down)
  have he := congrArg (· ≫ x.down) (extraVertexMap_lowFace_partialLastMap n j k hjk i hik)
  change partialLastMap n (ordinalVertex n k) ≫ x.down = x.down at hx
  simpa only [Category.assoc, hx] using he

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

local instance subdivisionPairingAbsorptionLinearOrder (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))
local instance subdivisionPairingAbsorptionFintype (n : ℕ) : Fintype (OrdinalVertices.{u} n) :=
  inferInstanceAs (Fintype (ULift (Fin (n + 1))))

lemma partialLastVertex_map_absorb (n m : ℕ) (j : OrdinalVertices.{u} n)
    (k : OrdinalVertices.{u} m) (f : OrdinalVertices.{u} n →o OrdinalVertices.{u} m)
    (hf : ∀ a, j < a → k < f a) (s : OrdinalChains.{u} n) :
    partialLastVertex m k ((partialLastVertex n j s).map f) =
      partialLastVertex m k (s.map f) := by
  rw [partialLastVertex_apply n j]
  split_ifs with h
  · rfl
  · have hh := hf (chainLast s) (lt_of_not_ge h)
    rw [partialLastVertex_apply, partialLastVertex_apply, chainLast_map,
      chainLast_map, chainLast_initialFlag, ite_eq_right hh.not_ge, ite_eq_right hh.not_ge]

lemma partialLastMap_sd_absorb {n m : ℕ} (j : OrdinalVertices.{u} n)
    (k : OrdinalVertices.{u} m) (f : ⦋n⦌ ⟶ ⦋m⦌)
    (hf : ∀ a, j < a → k < (SimplexCategory.toPartOrd.map f).hom a) :
    partialLastMap n j ≫ SimplexCategory.sd.map f ≫ partialLastMap m k =
      SimplexCategory.sd.map f ≫ partialLastMap m k := by
  change PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ ≫
    PartOrd.nerveFunctor.map _ = PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _
  repeat' erw [← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  apply OrderHom.ext
  funext s
  exact partialLastVertex_map_absorb n m j k _ hf s

lemma exLevel_map_of {X : SSet.{u}} {n m : ℕ} (j : OrdinalVertices.{u} n)
    (k : OrdinalVertices.{u} m) (f : ⦋n⦌ ⟶ ⦋m⦌)
    (hf : ∀ a, j < a → k < (SimplexCategory.toPartOrd.map f).hom a)
    (x : (SSet.ex.obj X).obj (op ⦋m⦌)) (hx : ExLevel X m k x) :
    ExLevel X n j ((SSet.ex.obj X).map f.op x) := by
  change partialLastMap _ _ ≫ (SimplexCategory.sd.map f ≫ x.down) = SimplexCategory.sd.map f ≫ x.down
  have he := congrArg (· ≫ x.down) (partialLastMap_sd_absorb j k f hf)
  change partialLastMap m k ≫ x.down = x.down at hx
  simpa only [Category.assoc, hx] using he

lemma exLevel_highFace {X : SSet.{u}} {n : ℕ} (k : Fin (n + 1)) (i : Fin (n + 2))
    (x : (SSet.ex.obj X).obj (op ⦋n + 1⦌))
    (hx : ExLevel X (n + 1) (ordinalVertex (n + 1) k.castSucc) x) :
    ExLevel X n (ordinalVertex n k) ((SSet.ex.obj X).δ i x) := by
  apply exLevel_map_of _ _ (SimplexCategory.δ i) _ x hx
  intro a ha
  change k.castSucc < i.succAbove a.down
  unfold Fin.succAbove
  split_ifs
  · exact ha
  · exact (show k.castSucc < a.down.castSucc from ha).trans_le a.down.castSucc_le_succ

lemma exLevel_lowFace {X : SSet.{u}} {n : ℕ} (j : Fin (n + 1)) (i : Fin (n + 2))
    (hi : i ≤ j.succ) (x : (SSet.ex.obj X).obj (op ⦋n + 1⦌))
    (hx : ExLevel X (n + 1) (ordinalVertex (n + 1) j.succ) x) :
    ExLevel X n (ordinalVertex n j) ((SSet.ex.obj X).δ i x) := by
  apply exLevel_map_of _ _ (SimplexCategory.δ i) _ x hx
  intro a ha
  change j.succ < i.succAbove a.down
  rw [Fin.succAbove_of_le_castSucc _ _ (hi.trans (show j.succ ≤ a.down.castSucc from ha))]
  exact Fin.succ_lt_succ_iff.mpr ha

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma extraVertexMap_highFace (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (hki : k.castSucc < i) :
    SimplexCategory.sd.map (SimplexCategory.δ i.succ) ≫ extraVertexMap.{u} (n + 1) k.castSucc =
    extraVertexMap n k ≫ SimplexCategory.sd.map (SimplexCategory.δ i) := by
  change PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ =
      PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  apply OrderHom.ext
  funext s
  exact extraVertex_highFace n k i hki s

lemma exPairSimplex_highFace (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1)) (i : Fin (n + 2))
    (hki : k.castSucc < i) (x : (SSet.ex.obj X).obj (op ⦋n + 1⦌)) :
    (SSet.ex.obj X).δ i.succ (exPairSimplex X (n + 1) k.castSucc x) =
      exPairSimplex X n k ((SSet.ex.obj X).δ i x) := by
  apply ULift.ext
  change SimplexCategory.sd.map (SimplexCategory.δ i.succ) ≫ (extraVertexMap (n + 1) k.castSucc ≫ x.down) =
    extraVertexMap n k ≫ (SimplexCategory.sd.map (SimplexCategory.δ i) ≫ x.down)
  erw [← Category.assoc, extraVertexMap_highFace n k i hki, Category.assoc]

lemma chainUnionMap_comp {A B C : Type*} [PartialOrder A] [LinearOrder B] [LinearOrder C]
    (f : B → NonemptyFiniteChains C) (g : A → NonemptyFiniteChains B)
    (s : NonemptyFiniteChains A) :
    chainUnionMap f (chainUnionMap g s) = chainUnionMap (fun a => chainUnionMap f (g a)) s := by
  apply NonemptyFiniteChains.ext
  ext c
  simp only [mem_chainUnionMap]
  exact ⟨fun ⟨b, ⟨a, ha, hb⟩, hc⟩ => ⟨a, ha, b, hb, hc⟩,
    fun ⟨a, ha, b, hb, hc⟩ => ⟨b, ⟨a, ha, hb⟩, hc⟩⟩

lemma chainUnionMap_on_singleton {A B : Type*} [PartialOrder A] [LinearOrder B]
    (f : A → NonemptyFiniteChains B) (a : A) : chainUnionMap f (singletonChain a) = f a := by
  apply NonemptyFiniteChains.ext
  ext b
  simp only [mem_chainUnionMap, mem_singletonChain]
  exact ⟨fun ⟨a', ha, hb⟩ => ha ▸ hb, fun hb => ⟨a, rfl, hb⟩⟩

local instance subdivisionPairingChainUnionLinearOrder (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))
local instance subdivisionPairingChainUnionFintype (n : ℕ) : Fintype (OrdinalVertices.{u} n) :=
  inferInstanceAs (Fintype (ULift (Fin (n + 1))))

lemma predAbove_castSucc_eq_succ {n : ℕ} (k : Fin (n + 1)) (a : Fin (n + 3))
    (ha : a ≠ k.castSucc.succ) : k.castSucc.predAbove a = k.succ.predAbove a := by
  apply Fin.ext
  unfold Fin.predAbove
  split_ifs with h1 h2 h3
  · rfl
  · have hv : a.val = k.val + 1 := by
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h1 h2
      omega
    exact (ha (Fin.ext hv)).elim
  · have : False := by
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h1 h3
      omega
    exact this.elim
  · rfl

lemma extraVertexFace_twice (n : ℕ) (k : Fin (n + 1)) (a : OrdinalVertices.{u} (n + 2)) :
    extraVertex n k (extraVertexFace (n + 1) k.castSucc a) =
      extraVertexFace n k (collapseVertices (n + 1) k.succ a) := by
  classical
  by_cases ha : a.down = k.castSucc.succ
  · have hleft : extraVertexFace (n + 1) k.castSucc a =
        initialFlag ⦋n + 1⦌ (ordinalVertex (n + 1) k.castSucc) := ite_eq_left ha
    rw [hleft, extraVertex_initialFlag]
    have hcl : collapseVertices n k (ordinalVertex (n + 1) k.castSucc) = ordinalVertex n k := by
      change ordinalVertex n (k.predAbove k.castSucc) = _
      rw [Fin.predAbove_castSucc_self]
    have hcr : collapseVertices (n + 1) k.succ a = ordinalVertex (n + 1) k.succ := by
      change ordinalVertex (n + 1) (k.succ.predAbove a.down) = _
      rw [ha]
      change ordinalVertex (n + 1) (k.succ.predAbove k.succ.castSucc) = _
      rw [Fin.predAbove_castSucc_self]
    rw [hcl, hcr]
    exact (ite_eq_left rfl).symm
  · have hh : extraVertexFace (n + 1) k.castSucc a =
        singletonChain (collapseVertices (n + 1) k.castSucc a) := ite_eq_right ha
    rw [hh]
    change chainUnionMap _ (singletonChain _) = _
    rw [chainUnionMap_on_singleton]
    congr 1
    exact ULift.ext _ _ (predAbove_castSucc_eq_succ k a.down ha)

lemma extraVertex_twice (n : ℕ) (k : Fin (n + 1)) (s : OrdinalChains.{u} (n + 2)) :
    extraVertex n k (extraVertex (n + 1) k.castSucc s) =
      extraVertex n k (s.map (collapseVertices (n + 1) k.succ)) := by
  change chainUnionMap _ (chainUnionMap _ _) = chainUnionMap _ _
  rw [chainUnionMap_comp, chainUnionMap_map]
  congr 2
  funext a
  exact extraVertexFace_twice n k a

lemma extraVertexMap_twice (n : ℕ) (k : Fin (n + 1)) :
    extraVertexMap.{u} (n + 1) k.castSucc ≫ extraVertexMap n k =
      SimplexCategory.sd.map (SimplexCategory.σ k.succ) ≫ extraVertexMap n k := by
  change PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _ =
      PartOrd.nerveFunctor.map _ ≫ PartOrd.nerveFunctor.map _
  erw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  apply PartOrd.hom_ext
  apply OrderHom.ext
  funext s
  exact extraVertex_twice n k s

lemma exPairSimplex_twice (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    exPairSimplex X (n + 1) k.castSucc (exPairSimplex X n k x) =
      (SSet.ex.obj X).σ k.succ (exPairSimplex X n k x) := by
  apply ULift.ext
  change extraVertexMap (n + 1) k.castSucc ≫ (extraVertexMap n k ≫ x.down) =
    SimplexCategory.sd.map (SimplexCategory.σ k.succ) ≫ (extraVertexMap n k ≫ x.down)
  erw [← Category.assoc, extraVertexMap_twice, Category.assoc]

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

local instance subdivisionPairingCollapseLinearOrder (n : ℕ) : LinearOrder (OrdinalVertices.{u} n) :=
  inferInstanceAs (LinearOrder (ULift (Fin (n + 1))))
local instance subdivisionPairingCollapseFintype (n : ℕ) : Fintype (OrdinalVertices.{u} n) :=
  inferInstanceAs (Fintype (ULift (Fin (n + 1))))

lemma collapseVertices_face (n : ℕ) (i : Fin (n + 1)) (a : OrdinalVertices.{u} n) :
    collapseVertices n i (faceVertices n i.succ a) = a :=
  ULift.ext _ _ (predAbove_succ_succAbove i a.down)

lemma initialFlag_map_collapseVertices (n : ℕ) (i : Fin (n + 1))
    (a : OrdinalVertices.{u} (n + 1)) :
    (initialFlag ⦋n + 1⦌ a).map (collapseVertices n i) =
      initialFlag ⦋n⦌ (collapseVertices n i a) := by
  apply NonemptyFiniteChains.ext
  ext b
  rw [NonemptyFiniteChains.mem_map_iff, mem_initialFlag]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact (collapseVertices n i).monotone ((mem_initialFlag _ _ _).mp hc)
  · intro hb
    refine ⟨faceVertices n i.succ b, (mem_initialFlag _ _ _).mpr ?_, collapseVertices_face n i b⟩
    exact ((faceVertices n i.succ).monotone hb).trans (face_collapse_le n i a)

lemma predAbove_eq_succ_low_iff {n : ℕ} (i k : Fin (n + 1)) (hik : i ≤ k)
    (a : Fin (n + 3)) : i.castSucc.predAbove a = k.succ ↔ a = k.succ.succ := by
  constructor
  · intro h
    apply Fin.ext
    have hh := congrArg Fin.val h
    unfold Fin.predAbove at hh
    split_ifs at hh with he
    · simp only [Fin.val_pred, Fin.val_succ] at hh
      have ha := a.isLt
      have hi := i.isLt
      have hhik : i.val ≤ k.val := hik
      simp only [Fin.lt_def, Fin.val_castSucc] at he
      change a.val = k.val + 1 + 1
      omega
    · simp only [Fin.coe_castPred, Fin.val_succ] at hh
      have hhik : i.val ≤ k.val := hik
      simp only [Fin.lt_def, Fin.val_castSucc] at he
      omega
  · intro h
    rw [h, Fin.predAbove_of_castSucc_lt, Fin.pred_succ]
    exact Fin.castSucc_lt_succ_iff.mpr (show i.castSucc ≤ k.succ from (show i.castSucc ≤ k.castSucc from hik).trans k.castSucc_le_succ)

lemma predAbove_eq_succ_high_iff {n : ℕ} (i k : Fin (n + 1)) (hki : k < i)
    (a : Fin (n + 3)) : i.succ.predAbove a = k.succ ↔ a = k.castSucc.succ := by
  constructor
  · intro h
    apply Fin.ext
    have hh := congrArg Fin.val h
    unfold Fin.predAbove at hh
    split_ifs at hh with he
    · simp only [Fin.val_pred, Fin.val_succ] at hh
      have hki' : k.val < i.val := hki
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at he
      change a.val = k.val + 1
      omega
    · simpa only [Fin.coe_castPred, Fin.val_succ, Fin.val_castSucc] using hh
  · intro h
    rw [h]
    change i.succ.predAbove k.succ.castSucc = k.succ
    exact Fin.predAbove_castSucc_of_le _ _ (Fin.succ_le_succ_iff.mpr hki.le)

lemma extraVertexFace_lowDegeneracy (n : ℕ) (i k : Fin (n + 1)) (hik : i ≤ k)
    (a : OrdinalVertices.{u} (n + 2)) :
    (extraVertexFace (n + 1) k.succ a).map (collapseVertices n i) =
      extraVertexFace n k (collapseVertices (n + 1) i.castSucc a) := by
  classical
  by_cases ha : a.down = k.succ.succ
  · have hl : extraVertexFace (n + 1) k.succ a =
        initialFlag ⦋n + 1⦌ (ordinalVertex (n + 1) k.succ) := ite_eq_left ha
    have hr : extraVertexFace n k (collapseVertices (n + 1) i.castSucc a) =
        initialFlag ⦋n⦌ (ordinalVertex n k) :=
      ite_eq_left ((predAbove_eq_succ_low_iff i k hik a.down).mpr ha)
    rw [hl, hr, initialFlag_map_collapseVertices, collapseVertices_succ_of_le n i k hik]
  · have hb := (predAbove_eq_succ_low_iff i k hik a.down).not.mpr ha
    unfold extraVertexFace
    erw [ite_eq_right ha, ite_eq_right hb, map_singletonChain]
    congr 1
    have h := congrArg (fun f : ⦋n + 2⦌ ⟶ ⦋n⦌ => f.toOrderHom a.down)
      (SimplexCategory.σ_comp_σ hik)
    exact ULift.ext _ _ h.symm

lemma extraVertexFace_highDegeneracy (n : ℕ) (i k : Fin (n + 1)) (hki : k < i)
    (a : OrdinalVertices.{u} (n + 2)) :
    (extraVertexFace (n + 1) k.castSucc a).map (collapseVertices n i) =
      extraVertexFace n k (collapseVertices (n + 1) i.succ a) := by
  classical
  by_cases ha : a.down = k.castSucc.succ
  · have hl : extraVertexFace (n + 1) k.castSucc a =
        initialFlag ⦋n + 1⦌ (ordinalVertex (n + 1) k.castSucc) := ite_eq_left ha
    have hr : extraVertexFace n k (collapseVertices (n + 1) i.succ a) =
        initialFlag ⦋n⦌ (ordinalVertex n k) :=
      ite_eq_left ((predAbove_eq_succ_high_iff i k hki a.down).mpr ha)
    rw [hl, hr, initialFlag_map_collapseVertices]
    congr 1
    change ordinalVertex n (i.predAbove k.castSucc) = _
    rw [Fin.predAbove_castSucc_of_le _ _ hki.le]
  · have hb := (predAbove_eq_succ_high_iff i k hki a.down).not.mpr ha
    unfold extraVertexFace
    erw [ite_eq_right ha, ite_eq_right hb, map_singletonChain]
    congr 1
    have h := congrArg (fun f : ⦋n + 2⦌ ⟶ ⦋n⦌ => f.toOrderHom a.down)
      (SimplexCategory.σ_comp_σ hki.le)
    exact ULift.ext _ _ h

lemma extraVertex_lowDegeneracy (n : ℕ) (i k : Fin (n + 1)) (hik : i ≤ k)
    (s : OrdinalChains.{u} (n + 2)) :
    (extraVertex (n + 1) k.succ s).map (collapseVertices n i) =
      extraVertex n k (s.map (collapseVertices (n + 1) i.castSucc)) := by
  change (chainUnionMap _ _).map _ = chainUnionMap _ _
  rw [map_chainUnionMap, chainUnionMap_map]
  congr 2
  funext a
  exact extraVertexFace_lowDegeneracy n i k hik a

lemma extraVertex_highDegeneracy (n : ℕ) (i k : Fin (n + 1)) (hki : k < i)
    (s : OrdinalChains.{u} (n + 2)) :
    (extraVertex (n + 1) k.castSucc s).map (collapseVertices n i) =
      extraVertex n k (s.map (collapseVertices (n + 1) i.succ)) := by
  change (chainUnionMap _ _).map _ = chainUnionMap _ _
  rw [map_chainUnionMap, chainUnionMap_map]
  congr 2
  funext a
  exact extraVertexFace_highDegeneracy n i k hki a

end Thomason.Subdivision

end

noncomputable section
universe u v w z


namespace Thomason.Subdivision

open CategoryTheory Simplicial Opposite PartialOrder

lemma exLevel_exists_nat (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    ∃ k : ℕ, ∃ h : k < n + 1, ExLevel X n (ordinalVertex n ⟨k, h⟩) x :=
  ⟨n, Nat.lt_succ_self n, exLevel_top X n x⟩

noncomputable def exIndex (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) : Fin (n + 1) := by
  classical
  exact ⟨Nat.find (exLevel_exists_nat X n x), (Nat.find_spec (exLevel_exists_nat X n x)).choose⟩

lemma exIndex_level (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    ExLevel X n (ordinalVertex n (exIndex X n x)) x := by
  classical
  exact (Nat.find_spec (exLevel_exists_nat X n x)).choose_spec

lemma exIndex_le_iff (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (k : Fin (n + 1)) :
    exIndex X n x ≤ k ↔ ExLevel X n (ordinalVertex n k) x := by
  classical
  constructor
  · intro h
    exact (exIndex_level X n x).mono h
  · intro h
    exact Nat.find_min' (exLevel_exists_nat X n x) ⟨k.isLt, h⟩

lemma exIndex_zero_iff (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    exIndex X n x = 0 ↔ x ∈ Set.range ((exComparison.app X).app (op ⦋n⦌)) := by
  rw [← exLevel_zero_iff, ← exIndex_le_iff]
  exact ⟨fun h => h.le, fun h => le_antisymm h (Fin.zero_le _)⟩

lemma exIndex_pair (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌)) (hx : ExLevel X n (ordinalVertex n k) x) :
    exIndex X (n + 1) (exPairSimplex X n k x) = (exIndex X n x).castSucc := by
  have hxk := (exIndex_le_iff X n x k).mpr hx
  have hk : exIndex X (n + 1) (exPairSimplex X n k x) ≤ k.castSucc :=
    (exIndex_le_iff _ _ _ _).mpr ((exPairSimplex_level_iff X n k k le_rfl x).mpr hx)
  let l : Fin (n + 1) := ⟨(exIndex X (n + 1) (exPairSimplex X n k x)).val,
    lt_of_le_of_lt hk k.isLt⟩
  have hl : exIndex X (n + 1) (exPairSimplex X n k x) = l.castSucc := Fin.ext rfl
  apply Fin.ext
  apply le_antisymm
  · exact (exIndex_le_iff _ _ _ _).mpr
      ((exPairSimplex_level_iff X n (exIndex X n x) k hxk x).mpr (exIndex_level X n x))
  · have hlev : ExLevel X (n + 1) (ordinalVertex (n + 1) l.castSucc) (exPairSimplex X n k x) := by
      rw [← hl]
      exact exIndex_level _ _ _
    exact (exIndex_le_iff X n x l).mpr
      ((exPairSimplex_level_iff X n l k (show l ≤ k from hk) x).mp hlev)

def ExTypeI (X : SSet.{u}) : (n : ℕ) → (SSet.ex.obj X).obj (op ⦋n⦌) → Prop := fun n => match n with
  | 0 => fun _ => False
  | n + 1 => fun x => ∃ k : Fin (n + 1), ∃ y : (SSet.ex.obj X).obj (op ⦋n⦌),
      exIndex X (n + 1) x = k.castSucc ∧ exPairSimplex X n k y = x

def ExTypeII (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) : Prop :=
  x ∈ (SSet.ex.obj X).nonDegenerate n ∧ 0 < (exIndex X n x).val ∧ ¬ ExTypeI X n x

lemma exPairSimplex_typeI (X : SSet.{u}) (n : ℕ) (x : (SSet.ex.obj X).obj (op ⦋n⦌)) :
    ExTypeI X (n + 1) (exPairSimplex X n (exIndex X n x) x) :=
  ⟨exIndex X n x, x, exIndex_pair X n _ x (exIndex_level X n x), rfl⟩

lemma exTypeI_preimage_index (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (x : (SSet.ex.obj X).obj (op ⦋n⦌))
    (h : exIndex X (n + 1) (exPairSimplex X n k x) = k.castSucc) :
    exIndex X n x = k := by
  have hx : ExLevel X n (ordinalVertex n k) x := by
    apply (exPairSimplex_level_iff X n k k le_rfl x).mp
    rw [← h]
    exact exIndex_level _ _ _
  have he := (exIndex_pair X n k x hx).symm.trans h
  exact Fin.ext (congrArg (fun t : Fin (n + 2) => t.val) he)

end Thomason.Subdivision

end

end OAI
