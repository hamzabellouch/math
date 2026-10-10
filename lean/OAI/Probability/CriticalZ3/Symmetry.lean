import OAI.Probability.CriticalZ3.ProductCylinder

namespace OAI

open MeasureTheory ProbabilityTheory Classical

namespace CriticalZ3
open Classical

noncomputable def internalSites (D : Set Vertex) (hD : D.Finite) : Finset Vertex := hD.toFinset
noncomputable def internalBonds (D : Set Vertex) (hD : D.Finite) : Finset Bond :=
  (hD.toFinset ×ˢ Finset.univ).filter (fun e => step e.1 e.2 ∈ D)

theorem mem_internalBonds {D : Set Vertex} {hD : D.Finite} {e : Bond} :
    e ∈ internalBonds D hD ↔ e.1 ∈ D ∧ step e.1 e.2 ∈ D := by
  simp [internalBonds]

theorem bondWithin_congr {D : Set Vertex} {hD : D.Finite} {ω ω' : BondConfig}
    (hω : ∀ e ∈ internalBonds D hD, ω' e = ω e) :
    Within D (BondOpen ω') = Within D (BondOpen ω) := by
  funext x y
  apply propext
  by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
  · simp only [Within,hx,hy,true_and,BondOpen]
    apply or_congr
    · apply exists_congr
      intro i
      by_cases he : y = step x i
      · rw [hω (x,i) (mem_internalBonds.mpr ⟨hx,he ▸ hy⟩)]
      · simp [he]
    · apply exists_congr
      intro i
      by_cases he : x = step y i
      · rw [hω (y,i) (mem_internalBonds.mpr ⟨hy,he ▸ hx⟩)]
      · simp [he]
  all_goals simp [Within,hx,hy]

theorem siteWithin_congr {D : Set Vertex} {hD : D.Finite} {ω ω' : SiteConfig}
    (hω : ∀ x ∈ hD.toFinset, ω' x = ω x) :
    Within D (SiteOpen ω') = Within D (SiteOpen ω) := by
  funext x y
  apply propext
  by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
  · simp only [Within,hx,hy,true_and,SiteOpen,hω x (hD.mem_toFinset.mpr hx),
      hω y (hD.mem_toFinset.mpr hy)]
  all_goals simp [Within,hx,hy]

theorem bondSeedReaches_determined (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    ∀ ω ω', (∀ e ∈ internalBonds (cube c n) (cube_finite c n), ω' e = ω e) →
      (ω' ∈ bondSeedReaches c m n T ↔ ω ∈ bondSeedReaches c m n T) := by
  intro ω ω' hω
  simp only [bondSeedReaches,Set.mem_ofPred_eq,bondWithin_congr hω]

theorem siteSeedReaches_determined (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (T : Set Vertex) :
    ∀ ω ω', (∀ e ∈ (cube_finite c n).toFinset, ω' e = ω e) →
      (ω' ∈ siteSeedReaches c m n T ↔ ω ∈ siteSeedReaches c m n T) := by
  intro ω ω' hω
  simp only [siteSeedReaches,Set.mem_ofPred_eq,siteWithin_congr hω]
  apply exists_congr
  intro x
  by_cases hx : x ∈ cube c m
  · simp only [hx,true_and,hω x ((cube_finite c n).mem_toFinset.mpr (cube_mono c hmn hx))]
  · simp only [hx,false_and]

theorem bondOpen_mono {ω ω' : BondConfig} (h : ω ≤ ω') {x y : Vertex}
    (hxy : BondOpen ω x y) : BondOpen ω' x y := by
  rcases hxy with ⟨i,hi,hw⟩ | ⟨i,hi,hw⟩
  · exact Or.inl ⟨i,hi,Bool.eq_true_of_true_le (hw ▸ h (x,i))⟩
  · exact Or.inr ⟨i,hi,Bool.eq_true_of_true_le (hw ▸ h (y,i))⟩

theorem siteOpen_mono {ω ω' : SiteConfig} (h : ω ≤ ω') {x y : Vertex}
    (hxy : SiteOpen ω x y) : SiteOpen ω' x y :=
  ⟨hxy.1,Bool.eq_true_of_true_le (hxy.2.1 ▸ h x),Bool.eq_true_of_true_le (hxy.2.2 ▸ h y)⟩

theorem bondSeedReaches_mono (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    Monotone (fun ω => ω ∈ bondSeedReaches c m n T) := by
  rintro ω ω' h ⟨x,hx,y,hy,hp⟩
  refine ⟨x,hx,y,hy,Relation.ReflTransGen.mono ?_ x y hp⟩
  intro a b h'
  exact ⟨h'.1,h'.2.1,bondOpen_mono h h'.2.2⟩

theorem siteSeedReaches_mono (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    Monotone (fun ω => ω ∈ siteSeedReaches c m n T) := by
  rintro ω ω' h ⟨x,hx,hω,y,hy,hp⟩
  refine ⟨x,hx,Bool.eq_true_of_true_le (hω ▸ h x),y,hy,Relation.ReflTransGen.mono ?_ x y hp⟩
  intro a b h'
  exact ⟨h'.1,h'.2.1,siteOpen_mono h h'.2.2⟩

end CriticalZ3

namespace CriticalZ3
open Classical

structure SignedSymmetry where
  perm : Equiv.Perm (Fin 3)
  signs : Fin 3 → Bool
  shift : Vertex

namespace SignedSymmetry

def vertex (S : SignedSymmetry) : Vertex ≃ Vertex where
  toFun x := fun i => S.shift i + if S.signs i then x (S.perm i) else -x (S.perm i)
  invFun y := fun i => if S.signs (S.perm.symm i) then
    y (S.perm.symm i)-S.shift (S.perm.symm i) else -(y (S.perm.symm i)-S.shift (S.perm.symm i))
  left_inv x := by
    funext i
    simp only [Equiv.apply_symm_apply]
    cases S.signs (S.perm.symm i) <;> simp
  right_inv y := by
    funext i
    simp only [Equiv.symm_apply_apply]
    cases S.signs i <;> simp

def edgeShift (S : SignedSymmetry) (k : Fin 3) : Vertex :=
  fun i => if S.signs (S.perm.symm k) then 0 else if S.perm.symm k = i then -1 else 0

def bond (S : SignedSymmetry) : Bond ≃ Bond :=
  (Equiv.prodComm _ _).trans
    ((Equiv.prodCongrRight (fun k => S.vertex.trans (Equiv.addRight (S.edgeShift k)))).trans
    ((Equiv.prodCongr S.perm.symm (Equiv.refl _)).trans (Equiv.prodComm _ _)))

theorem bond_apply (S : SignedSymmetry) (e : Bond) :
    S.bond e = (S.vertex e.1+S.edgeShift e.2,S.perm.symm e.2) := rfl

theorem edge_spec (S : SignedSymmetry) (e : Bond) :
    (S.vertex e.1 = (S.bond e).1 ∧ S.vertex (step e.1 e.2) = step (S.bond e).1 (S.bond e).2) ∨
    (S.vertex e.1 = step (S.bond e).1 (S.bond e).2 ∧ S.vertex (step e.1 e.2) = (S.bond e).1) := by
  have hi (i : Fin 3) : (e.2 = S.perm i) ↔ (S.perm.symm e.2 = i) := by
    constructor
    · intro h; rw [h,Equiv.symm_apply_apply]
    · intro h; rw [←h,Equiv.apply_symm_apply]
  by_cases hs : S.signs (S.perm.symm e.2) = true
  · left
    constructor
    · funext i
      simp [bond_apply,edgeShift,hs]
    · funext i
      by_cases he : S.perm.symm e.2 = i
      · have hsi : S.signs i = true := he ▸ hs
        simp [bond_apply,vertex,edgeShift,step,hsi,hi,he]
        ; ring
      · simp [bond_apply,vertex,edgeShift,step,hs,hi,he]
  · right
    constructor
    · funext i
      by_cases he : S.perm.symm e.2 = i
      · have hsi : S.signs i ≠ true := he ▸ hs
        simp [bond_apply,vertex,edgeShift,step,hsi,he]
      · simp [bond_apply,vertex,edgeShift,step,hs,he]
    · funext i
      by_cases he : S.perm.symm e.2 = i
      · have hsi : S.signs i ≠ true := he ▸ hs
        simp [bond_apply,vertex,edgeShift,step,hsi,hi,he]
        ; ring
      · simp [bond_apply,vertex,edgeShift,step,hs,hi,he]

def Endpoints (e : Bond) (x y : Vertex) : Prop :=
  (x = e.1 ∧ y = step e.1 e.2) ∨ (y = e.1 ∧ x = step e.1 e.2)

theorem endpoints_map (S : SignedSymmetry) (e : Bond) (x y : Vertex) :
    Endpoints (S.bond e) (S.vertex x) (S.vertex y) ↔ Endpoints e x y := by
  rcases S.edge_spec e with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · unfold Endpoints
    rw [←h₂,←h₁]
    simp only [Equiv.apply_eq_iff_eq]
  · unfold Endpoints
    rw [←h₁,←h₂]
    simp only [Equiv.apply_eq_iff_eq]
    tauto

theorem bondOpen_iff (ω : BondConfig) (x y : Vertex) :
    BondOpen ω x y ↔ ∃ e, ω e = true ∧ Endpoints e x y := by
  constructor
  · rintro (⟨i,h,hω⟩ | ⟨i,h,hω⟩)
    · exact ⟨(x,i),hω,Or.inl ⟨rfl,h⟩⟩
    · exact ⟨(y,i),hω,Or.inr ⟨rfl,h⟩⟩
  · rintro ⟨⟨z,i⟩,hω,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact Or.inl ⟨i,rfl,hω⟩
    · exact Or.inr ⟨i,rfl,hω⟩

theorem bondOpen_map (S : SignedSymmetry) (ω : BondConfig) (x y : Vertex) :
    BondOpen (fun e => ω (S.bond e)) x y ↔ BondOpen ω (S.vertex x) (S.vertex y) := by
  simp_rw [bondOpen_iff]
  constructor
  · rintro ⟨e,he,hxy⟩
    exact ⟨S.bond e,he,(S.endpoints_map e x y).mpr hxy⟩
  · rintro ⟨e,he,hxy⟩
    refine ⟨S.bond.symm e,by simpa using he,?_⟩
    apply (S.endpoints_map (S.bond.symm e) x y).mp
    simpa using hxy

theorem neighbor_map (S : SignedSymmetry) (x y : Vertex) :
    NearestNeighbor x y ↔ NearestNeighbor (S.vertex x) (S.vertex y) := by
  have he (x y : Vertex) : NearestNeighbor x y ↔ BondOpen (fun _ => true) x y := by
    simp only [NearestNeighbor,BondOpen,and_true]
    rw [exists_or]
  simpa only [he] using S.bondOpen_map (fun _ => true) x y

theorem siteOpen_map (S : SignedSymmetry) (ω : SiteConfig) (x y : Vertex) :
    SiteOpen (fun e => ω (S.vertex e)) x y ↔ SiteOpen ω (S.vertex x) (S.vertex y) := by
  simp only [SiteOpen,←S.neighbor_map]

theorem cube_map (S : SignedSymmetry) (c x : Vertex) (n : ℕ) :
    x ∈ cube c n ↔ S.vertex x ∈ cube (S.vertex c) n := by
  simp only [mem_cube]
  have he (i : Fin 3) :
      (S.vertex c i - (n:ℤ) ≤ S.vertex x i ∧ S.vertex x i ≤ S.vertex c i + (n:ℤ)) ↔
      (c (S.perm i)-(n:ℤ) ≤ x (S.perm i) ∧ x (S.perm i) ≤ c (S.perm i)+(n:ℤ)) := by
    dsimp [vertex]
    cases S.signs i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  simp_rw [he]
  constructor
  · intro h i; exact h _
  · intro h i; simpa only [Equiv.apply_symm_apply] using h (S.perm.symm i)

end SignedSymmetry
end CriticalZ3

end OAI
