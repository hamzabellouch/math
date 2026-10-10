import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.LeibmanSquare01
import OAI.Combinatorics.SumProduct.Alignment.PairTail03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped commutatorElement

end
 

 
section
noncomputable section
namespace LeibmanSquare
open CubeFaces RationalLattice
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Filtration G) (h0 : H.level 0 = ⊤) (h1 : H.level 1 = ⊤)
variable [∀ i, (H.level i).Normal]

include h1 in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma first_eq_pairTail : level H h0 1 = PairTail.square (H.level 2) := by
  ext x
  change (x.1 ∈ H.level 1 ∧ x.2 ∈ H.level 1 ∧ x.1⁻¹*x.2 ∈ H.level (1+1)) ↔ _
  simp only [h1,Subgroup.mem_top,true_and]
  rfl

def firstPairEquiv : level H h0 1 ≃* PairTail.square (H.level 2) :=
  MulEquiv.subgroupCongr (first_eq_pairTail H h0 h1)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] lemma firstPairEquiv_val (x : level H h0 1) :
    (firstPairEquiv H h0 h1 x).val = x.val := rfl

omit [IsTopologicalGroup G] in
lemma firstPairEquiv_continuous : Continuous (firstPairEquiv H h0 h1) :=
  continuous_subtype_val.subtype_mk _
omit [IsTopologicalGroup G] in
lemma firstPairEquiv_symm_continuous : Continuous (firstPairEquiv H h0 h1).symm :=
  continuous_subtype_val.subtype_mk _

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma restricted_map_pairLevel (i : ℕ) :
    ((restricted H h0).level i).map (firstPairEquiv H h0 h1).toMonoidHom =
      PairTail.pairLevel (H.level 2) (H.level (max 1 i)) (H.level (max 1 i+1)) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨hy.1,hy.2.2⟩
  · rintro ⟨hx,hxy⟩
    change x.val.1 ∈ H.level (max 1 i) at hx
    refine ⟨(firstPairEquiv H h0 h1).symm x,?_,(firstPairEquiv H h0 h1).apply_symm_apply x⟩
    change x.val.1 ∈ H.level (max 1 i) ∧ x.val.2 ∈ H.level (max 1 i) ∧
      x.val.1⁻¹*x.val.2 ∈ H.level (max 1 i+1)
    refine ⟨hx,?_,hxy⟩
    have hh := (H.level (max 1 i)).mul_mem hx (H.antitone (by omega) hxy)
    simpa using hh

variable (s : ℕ) (hs0 : 1 ≤ s) (hs : H.level (s+1) = ⊥)

include hs0 hs in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma last_map_diagonal :
    ((restricted H h0).level s).map (firstPairEquiv H h0 h1).toMonoidHom =
      PairTail.diagonal (H.level 2) (H.level s) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (y : G × G) ∈ level H h0 (max 1 s) at hy
    rw [max_eq_right hs0] at hy
    have hh := (last_level H h0 s hs y.val).mp hy
    exact ⟨hh.1,hh.2.symm⟩
  · rintro ⟨hx,he⟩
    refine ⟨(firstPairEquiv H h0 h1).symm x,?_,(firstPairEquiv H h0 h1).apply_symm_apply x⟩
    change x.val ∈ level H h0 (max 1 s)
    rw [max_eq_right hs0,last_level H h0 s hs]
    exact ⟨hx,he.symm⟩

include h1 hs in
omit [TopologicalSpace G] [IsTopologicalGroup G] [∀ levelIndex, (H.level levelIndex).Normal] in
lemma last_central_ambient : H.level s ≤ Subgroup.center G := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : y ∈ H.level 1 := by rw [h1]; trivial
  have hh := H.commutator_le s 1 (Subgroup.commutator_mem_commutator hx hy)
  rw [hs,Subgroup.mem_bot] at hh
  exact (commutatorElement_eq_one_iff_commute.mp hh).eq.symm

variable [((restricted H h0).level s).Normal]
variable [(PairTail.diagonal (H.level 2) (H.level s)).Normal]

 

def reducedPairEquiv :
    ((level H h0 1) ⧸ (restricted H h0).level s) ≃*
      (PairTail.square (H.level 2) ⧸ PairTail.diagonal (H.level 2) (H.level s)) :=
  QuotientGroup.congr _ _ (firstPairEquiv H h0 h1) (last_map_diagonal H h0 h1 s hs0 hs)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] lemma reducedPairEquiv_mk (x : level H h0 1) :
    reducedPairEquiv H h0 h1 s hs0 hs (QuotientGroup.mk x) =
      QuotientGroup.mk (firstPairEquiv H h0 h1 x) := rfl

omit [IsTopologicalGroup G] in
lemma reducedPairEquiv_continuous : Continuous (reducedPairEquiv H h0 h1 s hs0 hs) := by
  rw [(QuotientGroup.isQuotientMap_mk ((restricted H h0).level s)).continuous_iff]
  change Continuous (fun x => QuotientGroup.mk (firstPairEquiv H h0 h1 x))
  exact QuotientGroup.continuous_mk.comp (firstPairEquiv_continuous H h0 h1)

omit [IsTopologicalGroup G] in
lemma reducedPairEquiv_symm_continuous : Continuous (reducedPairEquiv H h0 h1 s hs0 hs).symm := by
  rw [(QuotientGroup.isQuotientMap_mk (PairTail.diagonal (H.level 2) (H.level s))).continuous_iff]
  change Continuous (fun x => QuotientGroup.mk ((firstPairEquiv H h0 h1).symm x))
  exact QuotientGroup.continuous_mk.comp (firstPairEquiv_symm_continuous H h0 h1)

def reducedPairHomeomorph :
    ((level H h0 1) ⧸ (restricted H h0).level s) ≃ₜ
      (PairTail.square (H.level 2) ⧸ PairTail.diagonal (H.level 2) (H.level s)) where
  toEquiv := (reducedPairEquiv H h0 h1 s hs0 hs).toEquiv
  continuous_toFun := reducedPairEquiv_continuous H h0 h1 s hs0 hs
  continuous_invFun := reducedPairEquiv_symm_continuous H h0 h1 s hs0 hs

end LeibmanSquare
end
end
 

 
section
noncomputable section
namespace RationalLattice
variable {G K : Type*} [Group G] [Group K] [TopologicalSpace G] [TopologicalSpace K] {n : ℕ}

def pullCoordinates (c : RealCoordinates K n) (e : G ≃* K)
    (hc : Continuous e) (hci : Continuous e.symm) : RealCoordinates G n where
  coord := ({toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hci} : G ≃ₜ K).trans c.coord
  one_coord i := by change c.coord (e 1) i = 0; rw [map_one,c.one_coord]
  correction := c.correction
  mul_coord g h i := by
    change c.coord (e (g*h)) i = _
    rw [map_mul]
    exact c.mul_coord _ _ _
end RationalLattice

namespace LeibmanSquare
open CubeFaces RationalLattice PairTail
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Filtration G) (h0 : H.level 0 = ⊤) (h1 : H.level 1 = ⊤)
variable [∀ i, (H.level i).Normal]
variable (s : ℕ) (hs0 : 1 ≤ s) (hs : H.level (s+1) = ⊥)
variable [((restricted H h0).level s).Normal]
variable [(PairTail.diagonal (H.level 2) (H.level s)).Normal]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma squareLattice_map (Γ : Subgroup G) :
    ((Γ.prod Γ).comap (level H h0 1).subtype).map (firstPairEquiv H h0 h1).toMonoidHom =
      PairTail.squareLattice (H.level 2) Γ := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨(firstPairEquiv H h0 h1).symm x,hx,(firstPairEquiv H h0 h1).apply_symm_apply x⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma reducedLattice_map (Γ : Subgroup G) :
    (((Γ.prod Γ).comap (level H h0 1).subtype).map
      (QuotientGroup.mk' ((restricted H h0).level s))).map
        (reducedPairEquiv H h0 h1 s hs0 hs).toMonoidHom =
      PairTail.reducedLattice (H.level 2) (H.level s) Γ := by
  rw [Subgroup.map_map]
  have he : (reducedPairEquiv H h0 h1 s hs0 hs).toMonoidHom.comp
      (QuotientGroup.mk' ((restricted H h0).level s)) =
      (QuotientGroup.mk' (PairTail.diagonal (H.level 2) (H.level s))).comp
        (firstPairEquiv H h0 h1).toMonoidHom := by ext x; rfl
  rw [he,← Subgroup.map_map,squareLattice_map]
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma reducedLevel_map (i : ℕ) :
    (((restricted H h0).level i).map (QuotientGroup.mk' ((restricted H h0).level s))).map
        (reducedPairEquiv H h0 h1 s hs0 hs).toMonoidHom =
      PairTail.reducedLevel (H.level 2) (H.level s)
        (H.level (max 1 i)) (H.level (max 1 i+1)) := by
  rw [Subgroup.map_map]
  have he : (reducedPairEquiv H h0 h1 s hs0 hs).toMonoidHom.comp
      (QuotientGroup.mk' ((restricted H h0).level s)) =
      (QuotientGroup.mk' (PairTail.diagonal (H.level 2) (H.level s))).comp
        (firstPairEquiv H h0 h1).toMonoidHom := by ext x; rfl
  rw [he,← Subgroup.map_map,restricted_map_pairLevel]
  rfl

variable {t d r : ℕ} (c : RealCoordinates G (t+d))
variable (h2 : ∀ g : G, g ∈ H.level 2 ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i = 0)
variable (hr : r ≤ t+d)
variable (hS : ∀ g : G, g ∈ H.level s ↔ ∀ i : Fin (t+d), i.val < r → c.coord g i = 0)

 

def sourceReducedCoordinates : RealCoordinates
    ((level H h0 1) ⧸ (restricted H h0).level s) (r+d) :=
  pullCoordinates (PairTail.reducedCoordinates c (H.level 2) h2 hr (H.level s) hS
    (last_central_ambient H h1 s hs))
    (reducedPairEquiv H h0 h1 s hs0 hs)
    (reducedPairEquiv_continuous H h0 h1 s hs0 hs)
    (reducedPairEquiv_symm_continuous H h0 h1 s hs0 hs)

lemma sourceReduced_integer_lattice (Γ : Subgroup G)
    (hΓ : ∀ g : G, g ∈ Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i = z)
    (x : (level H h0 1) ⧸ (restricted H h0).level s) :
    x ∈ ((Γ.prod Γ).comap (level H h0 1).subtype).map
      (QuotientGroup.mk' ((restricted H h0).level s)) ↔
      ∀ i, ∃ z : ℤ, (sourceReducedCoordinates H h0 h1 s hs0 hs c h2 hr hS).coord x i = z := by
  have hm : x ∈ ((Γ.prod Γ).comap (level H h0 1).subtype).map
      (QuotientGroup.mk' ((restricted H h0).level s)) ↔
      reducedPairEquiv H h0 h1 s hs0 hs x ∈ PairTail.reducedLattice (H.level 2) (H.level s) Γ := by
    rw [← reducedLattice_map H h0 h1 s hs0 hs Γ]
    constructor
    · intro hx; exact ⟨x,hx,rfl⟩
    · rintro ⟨y,hy,he⟩
      have hh : y = x := (reducedPairEquiv H h0 h1 s hs0 hs).injective he
      exact hh ▸ hy
  rw [hm,PairTail.reducedLattice_iff c (H.level 2) h2 hr (H.level s) hS
    (last_central_ambient H h1 s hs) Γ hΓ]
  rfl

end LeibmanSquare
end
end
 

 
section
noncomputable section
namespace MalcevSubspaceQuotient
open RationalLattice MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (N : Subgroup G) [N.Normal] (I : Set (Fin n))
variable (hN : ∀ g : G, g ∈ N ↔ ∀ i ∈ I, c.coord g i = 0)

def mask (x : Fin n → ℝ) (i : Fin n) : ℝ := by
  classical
  exact if i∈I then x i else 0

def strip (g : G) : G := c.coord.symm (mask I (c.coord g))

include hN in
omit [IsTopologicalGroup G] [N.Normal] in
lemma axis_mem {i : Fin n} (hi : i∉I) (t : ℝ) : axis c i t ∈ N := by
  apply (hN _).mpr
  intro j hj
  have hji : j≠i := by intro he; exact hi (he ▸ hj)
  simp [hji]

include hsk in
omit [IsTopologicalGroup G] in
lemma mk_coordinates (x : Fin n → ℝ) :
    (QuotientGroup.mk (c.coord.symm x) : G ⧸ N) =
      (List.ofFn (fun i => QuotientGroup.mk (axis c i (x i)) : Fin n → G ⧸ N)).prod := by
  conv_lhs => rw [hsk.ordered (c.coord.symm x)]
  change (QuotientGroup.mk' N) (List.ofFn _ |>.prod) = _
  rw [map_list_prod,List.map_ofFn]
  simp only [Homeomorph.apply_symm_apply]
  rfl

include hN hsk in
omit [IsTopologicalGroup G] in
lemma mk_strip (g : G) : (QuotientGroup.mk (strip c I g) : G ⧸ N)=QuotientGroup.mk g := by
  have hg : (QuotientGroup.mk g : G ⧸ N) = QuotientGroup.mk (c.coord.symm (c.coord g)) := by simp
  rw [hg,strip,mk_coordinates c hsk N,mk_coordinates c hsk N]
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  by_cases hi : i∈I
  · simp [mask,hi]
  · simp only [mask,ite_eq_right hi,axis_zero,QuotientGroup.mk_one]
    exact ((QuotientGroup.eq_one_iff _).mpr (axis_mem c N I hN hi _)).symm

include hN in
omit [IsTopologicalGroup G] [N.Normal] in
lemma strip_unique (g h : G)
    (hg : ∀ i∉I, c.coord g i=0) (hh : ∀ i∉I, c.coord h i=0)
    (he : (QuotientGroup.mk g : G ⧸ N)=QuotientGroup.mk h) : g=h := by
  have hn := (hN _).mp (QuotientGroup.eq.mp he)
  apply c.coord.injective
  funext i
  suffices hf : ∀ k : ℕ, ∀ hk : k<n, c.coord g ⟨k,hk⟩=c.coord h ⟨k,hk⟩ from hf i.val i.isLt
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    let j : Fin n := ⟨k,hk⟩
    by_cases hj : j∈I
    · have hpre : ∀ u : Fin n, u.val<k → c.coord g u=c.coord h u := by
        intro u hu
        exact ih u.val hu u.isLt
      have hd := (MalcevPrefixQuotient.prefix_eq_iff c (Nat.le_of_lt hk) g h).mp hpre
      have hm := coord_mul_of_right_zero c g (g⁻¹*h) j (by intro u hu; exact hd u hu)
      rw [mul_inv_cancel_left,hn j hj,add_zero] at hm
      exact hm.symm
    · exact (hg j hj).trans (hh j hj).symm

include hN hsk in
 

omit [IsTopologicalGroup G] in
theorem eq_coset_iff (g h : G) :
    (QuotientGroup.mk g : G ⧸ N)=QuotientGroup.mk h ↔
      ∀ i∈I, c.coord g i=c.coord h i := by
  classical
  constructor
  · intro he
    have he' : strip c I g=strip c I h := by
      apply strip_unique c N I hN
      · intro i hi; simp [strip,mask,hi]
      · intro i hi; simp [strip,mask,hi]
      · rw [mk_strip c hsk N I hN,mk_strip c hsk N I hN,he]
    intro i hi
    have hf := congrArg (fun a => c.coord a i) he'
    simpa [strip,mask,hi] using hf
  · intro he
    have he' : strip c I g=strip c I h := by
      unfold strip
      congr 1
      funext i
      by_cases hi : i∈I
      · simpa [mask,hi] using he i hi
      · simp [mask,hi]
    rw [← mk_strip c hsk N I hN g,← mk_strip c hsk N I hN h,he']

end MalcevSubspaceQuotient

end
end
end
end
end

end OAI
