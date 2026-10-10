import Mathlib
import OAI.Combinatorics.StripMass.VacuumClosure

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

namespace Pairing

lemma mapRestrict_eq_of_supported {n m : ℕ} (f : Fin n ↪o Fin m) (p : Pairing m)
    (hp : ∀ i, p.Occupied i → ∃ j, f j=i) : (p.restrict f).map f=p := by
  apply ext_adj
  intro i j
  rw [map_adj]
  constructor
  · rintro ⟨a,b,hab,rfl,rfl⟩
    exact (restrict_adj f p a b).mp hab
  · intro hij
    obtain ⟨a,rfl⟩ := hp i ⟨j,hij⟩
    obtain ⟨b,rfl⟩ := hp j ⟨f a,adj_symm hij⟩
    exact ⟨a,b,(restrict_adj f p a b).mpr hij,rfl,rfl⟩

lemma mapRestrict_omit {n : ℕ} (a : Fin (n+1)) (p : Pairing (n+1))
    (hp : ¬p.Occupied a) : (p.restrict (Fin.succAboveOrderEmb a)).map
      (Fin.succAboveOrderEmb a)=p := by
  apply mapRestrict_eq_of_supported
  intro i hi
  have hia : i ≠ a := fun he => hp (he ▸ hi)
  exact Fin.exists_succAbove_eq hia

lemma join_map {n m : ℕ} (f : Fin n ↪o Fin m) (p q : Pairing n) (i j : Fin m) :
    join (p.map f) (q.map f) i j ↔ ∃ a b, join p q a b ∧ f a=i ∧ f b=j := by
  simp only [join,map_adj]
  constructor
  · rintro (⟨a,b,h,rfl,rfl⟩|⟨a,b,h,rfl,rfl⟩)
    · exact ⟨a,b,Or.inl h,rfl,rfl⟩
    · exact ⟨a,b,Or.inr h,rfl,rfl⟩
  · rintro ⟨a,b,h,rfl,rfl⟩
    exact h.elim (fun hh => Or.inl ⟨a,b,hh,rfl,rfl⟩)
      (fun hh => Or.inr ⟨a,b,hh,rfl,rfl⟩)

lemma join_map_reach {n m : ℕ} (f : Fin n ↪o Fin m) (p q : Pairing n) (i j : Fin n) :
    Relation.ReflTransGen (join (p.map f) (q.map f)) (f i) (f j) ↔
      Relation.ReflTransGen (join p q) i j := by
  constructor
  · intro hh
    have h : ∀ {y}, Relation.ReflTransGen (join (p.map f) (q.map f)) (f i) y →
        ∃ k, f k=y ∧ Relation.ReflTransGen (join p q) i k := by
      intro y hy
      induction hy with
      | refl => exact ⟨i,rfl,.refl⟩
      | @tail y z hy hyz ih =>
        obtain ⟨k,hk,hpath⟩ := ih
        obtain ⟨a,b,hab,ha,hb⟩ := (join_map f p q y z).mp hyz
        have hka : k=a := f.injective (hk.trans ha.symm)
        subst k
        exact ⟨b,hb,hpath.tail hab⟩
    obtain ⟨k,hk,hpath⟩ := h hh
    exact f.injective hk ▸ hpath
  · intro hh
    exact Graph.map_reach f (fun a b hab => .single
      ((join_map f p q (f a) (f b)).mpr ⟨a,b,hab,rfl,rfl⟩)) hh

lemma gluesAt_map {n m : ℕ} (f : Fin n ↪o Fin m) (root : Fin n) (p q : Pairing n) :
    GluesAt (f root) (p.map f) (q.map f) ↔ GluesAt root p q := by
  constructor
  · rintro ⟨hp,ho,hd⟩
    refine ⟨(map_occupied f p root).mp hp,?_,?_⟩
    · intro i
      simpa only [map_occupied] using ho (f i)
    · intro i j hij
      apply (join_map_reach f p q i root).mp
      exact hd (f i) (f j) ((join_map f p q _ _).mpr ⟨i,j,hij,rfl,rfl⟩)
  · rintro ⟨hp,ho,hd⟩
    refine ⟨(map_occupied f p root).mpr hp,?_,?_⟩
    · intro i
      constructor
      · rintro ⟨j,hij⟩
        obtain ⟨a,b,hab,rfl,rfl⟩ := (map_adj f p i j).mp hij
        exact (map_occupied f q a).mpr ((ho a).mp ⟨b,hab⟩)
      · rintro ⟨j,hij⟩
        obtain ⟨a,b,hab,rfl,rfl⟩ := (map_adj f q i j).mp hij
        exact (map_occupied f p a).mpr ((ho a).mpr ⟨b,hab⟩)
    · intro i j hij
      obtain ⟨a,b,hab,rfl,rfl⟩ := (join_map f p q i j).mp hij
      exact (join_map_reach f p q a root).mpr (hd a b hab)

lemma gluesAt_map_supported {n m : ℕ} (f : Fin n ↪o Fin m) (root : Fin n)
    (p : Pairing m) (q : Pairing n) (h : GluesAt (f root) p (q.map f)) :
    ∃ r : Pairing n, r.map f=p := by
  refine ⟨p.restrict f,mapRestrict_eq_of_supported f p ?_⟩
  intro i hi
  obtain ⟨j,hij⟩ := (h.2.1 i).mp hi
  obtain ⟨a,b,_,ha,_⟩ := (map_adj f q i j).mp hij
  exact ⟨a,ha⟩

end Pairing

 

theorem functionMatrix_glue_adjoint {K : Type*} [CommRing K] {n m : ℕ}
    (f : Fin n ↪o Fin m) (root : Fin n) :
    (glueMatrix (f root) : Matrix _ _ K) * functionMatrix (Pairing.map f) =
      functionMatrix (Pairing.map f) * glueMatrix root := by
  ext q p
  refine (mul_functionMatrix (Pairing.map f) (glueMatrix (K:=K) (f root)) q p).trans ?_
  by_cases h : ∃ r : Pairing n, r.map f=q
  · obtain ⟨r,rfl⟩ := h
    refine Eq.trans ?_ (functionMatrix_mul_apply (Pairing.map f) (Pairing.map_injective f)
      (glueMatrix (K:=K) root) r p).symm
    simp only [glueMatrix,Pairing.gluesAt_map]
  · refine Eq.trans ?_ (functionMatrix_mul_outside (Pairing.map f) (glueMatrix (K:=K) root) q p h).symm
    apply ite_eq_right
    exact fun hh => h (Pairing.gluesAt_map_supported f root q p hh)

 

lemma functionMatrix_transpose_mul_self {K P Q : Type*} [CommRing K] [Fintype P]
    [Fintype Q] [DecidableEq P] (f : P → Q) (hf : Function.Injective f) :
    (functionMatrix (K:=K) f).transpose * functionMatrix (K:=K) f = 1 := by
  ext p q
  rw [mul_functionMatrix (K:=K)]
  simp [Matrix.transpose_apply,functionMatrix,optionMatrix,hf.eq_iff,Matrix.one_apply]

 

lemma localR_vacant_right {K : Type*} [CommRing K] {n : ℕ} (a : Position n)
    (w : Weights K) (p q : Pairing n) (hp : ¬p.Occupied a.right)
    (hq : ¬q.Occupied a.right) :
    localR a w q p = if p=q then (if p.Occupied a.left then w.A else 1) else 0 := by
  have hne : a.right ≠ a.left := by
    intro he
    have h := a.adjacent
    have he' := congrArg Fin.val he
    omega
  simp only [localR,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  by_cases ha : p.Occupied a.left
  · rw [Finset.sum_eq_single .vertical₀]
    · simp [Weights.tile,optionMatrix,Pairing.tileStep,ha,hp]
    · intro t _ ht
      have ho (htb : t.Occupied 3) : p.tileStep a.left a.right a.adjacent t ≠ some q := by
        intro he
        have hh := (p.tileStep_support a.left a.right a.adjacent t q he a.right).mpr
          (by simp [Pairing.stepSupport,hne,htb])
        exact hq hh
      cases t <;> try simp_all [Weights.tile,optionMatrix,Pairing.tileStep]
      intro he
      exact (ho (by unfold Tile.Occupied Tile.Adj Tile.edges; decide) he).elim
    · simp
  · rw [Finset.sum_eq_single .vacant]
    · simp [Weights.tile,optionMatrix,Pairing.tileStep,ha,hp]
    · intro t _ ht
      have ho (htb : t.Occupied 3) : p.tileStep a.left a.right a.adjacent t ≠ some q := by
        intro he
        have hh := (p.tileStep_support a.left a.right a.adjacent t q he a.right).mpr
          (by simp [Pairing.stepSupport,hne,htb])
        exact hq hh
      cases t <;> try simp_all [Weights.tile,optionMatrix,Pairing.tileStep]
      intro he
      exact (ho (by unfold Tile.Occupied Tile.Adj Tile.edges; decide) he).elim
    · simp

 

def splitProjection {K : Type*} [CommRing K] {n m : ℕ}
    (f : Fin n ↪o Fin m) (a : Position m) (w : Weights K) :
    Matrix (Pairing n) (Pairing m) K :=
  (functionMatrix (K:=K) (Pairing.map f)).transpose * localR a w

theorem splitProjection_glue_adjoint {K : Type*} [CommRing K] {n m : ℕ}
    (f : Fin n ↪o Fin m) (a : Position m) (w : Weights K) (root : Fin n)
    (ha : f root ≠ a.left) (hb : f root ≠ a.right) :
    (glueMatrix (K:=K) (f root)) *
        (localR a w * functionMatrix (K:=K) (Pairing.map f)) =
      (splitProjection f a w).transpose * glueMatrix root := by
  let E := functionMatrix (K:=K) (Pairing.map f)
  let L := localR a w
  have ht : (splitProjection f a w).transpose = L.transpose * E := by
    simpa only [splitProjection,Matrix.transpose_transpose] using (Matrix.transpose_mul E.transpose L)
  calc
    _ = (glueMatrix (f root) * L) * E := (Matrix.mul_assoc _ _ _).symm
    _ = (L.transpose * glueMatrix (f root)) * E :=
      congrArg (fun M => M * E) (localR_glue_adjoint a (f root) ha hb w)
    _ = L.transpose * (glueMatrix (f root) * E) := Matrix.mul_assoc _ _ _
    _ = L.transpose * (E * glueMatrix root) :=
      congrArg (fun M => L.transpose * M) (functionMatrix_glue_adjoint f root)
    _ = (L.transpose * E) * glueMatrix root := (Matrix.mul_assoc _ _ _).symm
    _ = _ := congrArg (fun M => M * glueMatrix root) ht.symm

lemma transpose_functionMatrix_mul_apply {K P Q R : Type*} [CommRing K]
    [Fintype Q] (f : P → Q) (M : Matrix Q R K) (p : P) (r : R) :
    ((functionMatrix (K:=K) f).transpose * M) p r = M (f p) r := by
  simpa only [functionMatrix,Function.comp_apply,Option.elim_some] using
    transpose_optionMatrix_mul_apply M (some ∘ f) p r

lemma vacant_restriction_localR {K : Type*} [CommRing K] {n : ℕ}
    (a : Position (n+1)) (w : Weights K) (p q : Pairing n) :
    ((functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb a.right))).transpose *
      localR a w * functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb a.right))) q p =
      if p=q then
        (if (p.map (Fin.succAboveOrderEmb a.right)).Occupied a.left then w.A else 1) else 0 := by
  rw [mul_functionMatrix,transpose_functionMatrix_mul_apply,
    localR_vacant_right a w _ _ (p.map_not_occupied_omit a.right) (q.map_not_occupied_omit a.right)]
  simp only [(Pairing.map_injective _).eq_iff]

lemma vacant_restriction_localR_mulVec {K : Type*} [CommRing K] {n : ℕ}
    (a : Position (n+1)) (w : Weights K) (v : Pairing n → K) (p : Pairing n) :
    (((functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb a.right))).transpose *
      localR a w * functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb a.right))).mulVec v) p =
      (if (p.map (Fin.succAboveOrderEmb a.right)).Occupied a.left then w.A else 1) * v p := by
  simp only [Matrix.mulVec,dotProduct,vacant_restriction_localR]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp [hq]
  · simp

 

theorem splitMap_injective {K : Type*} [Field K] {n : ℕ}
    (a : Position (n+1)) (w : Weights K) (hA : w.A≠0) :
    Function.Injective
      (localR a w * functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb a.right))).mulVec := by
  intro v z hvz
  funext p
  have hh := congrArg (fun U =>
    ((functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb a.right))).transpose).mulVec U p) hvz
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,←Matrix.mul_assoc,
    vacant_restriction_localR_mulVec,vacant_restriction_localR_mulVec] at hh
  exact mul_left_cancel₀ (by split_ifs <;> first | exact hA | exact one_ne_zero) hh

lemma mergeMap_injective {n m : ℕ} (r : ℕ) (hr : r+2≤n+1) :
    Function.Injective (mergeMap (m:=m) r hr).mulVec := by
  apply splitMap_injective
  exact div_ne_zero (constF_phase_ne_zero m)
    (eighthRoot_two_add_one_ne_zero (constF_phase_eight m))

 

 


lemma sum_tiles {K : Type*} [AddCommMonoid K] (f : Tile → K) :
    ∑ t, f t = f .vacant + f .vertical₀ + f .vertical₁ + f .diagonal₀ +
      f .diagonal₁ + f .cap + f .cup + f .verticalPair + f .capCup := by
  change (∑ t ∈ ({.vacant,.vertical₀,.vertical₁,.diagonal₀,.diagonal₁,.cap,.cup,
    .verticalPair,.capCup} : Finset Tile), f t) = _
  simp [add_assoc]

lemma mul_localR_apply {K Q : Type*} [CommRing K] {n : ℕ}
    (M : Matrix Q (Pairing n) K) (a : Position n) (w : Weights K)
    (q : Q) (p : Pairing n) :
    (M * localR a w) q p = ∑ t : Tile,
      w.tile t * (p.tileStep a.left a.right a.adjacent t).elim 0 (M q) := by
  simp only [localR,Matrix.mul_sum,Matrix.mul_smul,Matrix.sum_apply,Matrix.smul_apply,
    smul_eq_mul,mul_optionMatrix_apply]

lemma localR_apply {K : Type*} [CommRing K] {n : ℕ}
    (a : Position n) (w : Weights K) (q p : Pairing n) :
    localR a w q p = ∑ t : Tile,
      w.tile t * (p.tileStep a.left a.right a.adjacent t).elim 0
        (fun r => if r=q then 1 else 0) := by
  have h := mul_localR_apply (1 : Matrix (Pairing n) (Pairing n) K) a w q p
  have h1 : (1 : Matrix (Pairing n) (Pairing n) K) q = (fun r => if r=q then 1 else 0) := by
    funext r
    simp [Matrix.one_apply,eq_comm]
  rw [h1,Matrix.one_mul] at h
  exact h

namespace Pairing
lemma mapOccupied_equiv_occupied {n : ℕ} (p : Pairing n) (f : Equiv.Perm (Fin n))
    (hf : ∀ i j, p.Occupied i → p.Occupied j → (f i < f j ↔ i < j)) (i : Fin n) :
    (p.mapOccupied f.toEmbedding hf).Occupied i ↔ p.Occupied (f.symm i) := by
  simp only [Occupied,mapOccupied_equiv_adj]
  constructor
  · rintro ⟨j,h⟩
    exact ⟨f.symm j,h⟩
  · rintro ⟨j,h⟩
    exact ⟨f j,by simpa using h⟩

@[simp] lemma moveIntoVacancy_occupied {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (hb : ¬p.Occupied b) (i : Fin n) :
    (p.moveIntoVacancy a b hab hb).Occupied i ↔ p.Occupied (Equiv.swap a b i) :=
  mapOccupied_equiv_occupied p (Equiv.swap a b) _ i

@[simp] lemma moveIntoLowerVacancy_occupied {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (ha : ¬p.Occupied a) (i : Fin n) :
    (p.moveIntoLowerVacancy a b hab ha).Occupied i ↔ p.Occupied (Equiv.swap a b i) :=
  mapOccupied_equiv_occupied p (Equiv.swap a b) _ i

@[simp] lemma insertCup_occupied {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (ha : ¬p.Occupied a) (hb : ¬p.Occupied b) (i : Fin n) :
    (p.insertCup a b hab ha hb).Occupied i ↔ i=a ∨ i=b ∨ p.Occupied i := by
  simp [Occupied,insertCup_adj,exists_or]

lemma moveIntoLowerVacancy_inverse {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (ha : ¬p.Occupied a)
    (h : ¬(p.moveIntoLowerVacancy a b hab ha).Occupied b) :
    (p.moveIntoLowerVacancy a b hab ha).moveIntoVacancy a b hab h = p := by
  apply ext_adj
  intro i j
  simp only [moveIntoVacancy_adj,moveIntoLowerVacancy_adj,Equiv.swap_apply_self]
end Pairing

 

def vacantProjection {K : Type*} [Zero K] [One K] {n : ℕ} (b : Fin n) :
    Matrix (Pairing n) (Pairing n) K := Matrix.diagonal (fun p => if p.Occupied b then 0 else 1)

lemma mul_vacantProjection_apply {K Q : Type*} [CommRing K] {n : ℕ}
    (M : Matrix Q (Pairing n) K) (b : Fin n) (q : Q) (p : Pairing n) :
    (M * vacantProjection (K:=K) b) q p = if p.Occupied b then 0 else M q p := by
  rw [vacantProjection,Matrix.mul_diagonal]
  by_cases hp : p.Occupied b <;> simp [hp]

lemma functionMatrix_mul_transpose_omit {K : Type*} [CommRing K] {n : ℕ}
    (b : Fin (n+1)) :
    functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb b)) *
      (functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb b))).transpose =
    vacantProjection (K:=K) b := by
  ext q p
  by_cases hp : p.Occupied b
  · rw [Matrix.mul_apply]
    have hz : (vacantProjection (K:=K) b) q p=0 := by
      by_cases he : q=p <;> simp [vacantProjection,he,hp]
    rw [hz]
    apply Finset.sum_eq_zero
    intro r _
    have hne : r.map (Fin.succAboveOrderEmb b) ≠ p := fun he =>
      r.map_not_occupied_omit b (he.symm ▸ hp)
    simp [Matrix.transpose_apply,functionMatrix,optionMatrix,hne]
  · have he := Pairing.mapRestrict_omit b p hp
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (p.restrict (Fin.succAboveOrderEmb b))]
    · by_cases hqp : q=p
      · subst q
        simp [Matrix.transpose_apply,functionMatrix,optionMatrix,he,vacantProjection,hp]
      · simp [Matrix.transpose_apply,functionMatrix,optionMatrix,he,vacantProjection,hqp,Ne.symm hqp]
    · intro r _ hr
      have hn : r.map (Fin.succAboveOrderEmb b) ≠ p := by
        intro h
        exact hr ((Pairing.map_injective _).eq_iff.mp (h.trans he.symm))
      simp [Matrix.transpose_apply,functionMatrix,optionMatrix,hn]
    · simp

 

theorem localR_factor_merge {K : Type*} [CommRing K] {n : ℕ}
    (a : Position n) (r : K) :
    localR a ⟨r,r,r,0,0⟩ * vacantProjection (K:=K) a.right * localR a ⟨r,r,r,0,0⟩ =
      localR a ⟨r^2,r^2,r,0,r^2⟩ := by
  ext q p
  rw [mul_localR_apply,localR_apply]
  simp only [sum_tiles,Weights.tile]
  by_cases ha : p.Occupied a.left
  · by_cases hb : p.Occupied a.right
    · by_cases hn : p.Adj a.left a.right
      · simp [Pairing.tileStep,ha,hb,hn]
      · let s := p.capRemove a.left a.right a.adjacent ha hb hn
        have hsa : ¬s.Occupied a.left := (p.capRemove_vacant _ _ _ ha hb hn).1
        have hsb : ¬s.Occupied a.right := (p.capRemove_vacant _ _ _ ha hb hn).2
        simp only [Pairing.tileStep,ha,hb,hn,not_true_eq_false,and_false,
          and_true,ite_true,ite_false,dite_true,dite_false,Option.elim_none,
          Option.elim_some,zero_mul,mul_zero,add_zero,zero_add]
        change r * ((localR a ⟨r,r,r,0,0⟩ * vacantProjection (K:=K) a.right) q s) = _
        rw [mul_vacantProjection_apply,ite_eq_right hsb,localR_apply]
        simp only [sum_tiles,Weights.tile,Pairing.tileStep,hsa,hsb,not_false_eq_true,
          and_self,and_false,false_and,ite_true,ite_false,dite_true,dite_false,Option.elim_none,
          Option.elim_some,mul_zero,add_zero,one_mul]
        ring
    · simp only [Pairing.tileStep,ha,hb,not_true_eq_false,not_false_eq_true,and_self,
        and_false,false_and,ite_true,ite_false,dite_true,dite_false,Option.elim_none,
        Option.elim_some,mul_zero,add_zero,zero_add]
      simp only [mul_vacantProjection_apply,Pairing.moveIntoVacancy_occupied,
        Equiv.swap_apply_right,ha,hb,ite_true,ite_false,mul_zero,add_zero]
      rw [localR_apply]
      simp only [sum_tiles,Weights.tile,Pairing.tileStep,ha,hb,not_true_eq_false,
        not_false_eq_true,and_self,and_false,false_and,ite_true,ite_false,dite_true,dite_false,
        Option.elim_none,Option.elim_some,mul_zero,add_zero,zero_add]
      ring
  · by_cases hb : p.Occupied a.right
    · let s := p.moveIntoLowerVacancy a.left a.right a.adjacent ha
      have hsa : s.Occupied a.left := by simp [s,hb]
      have hsb : ¬s.Occupied a.right := by simp [s,ha]
      simp only [Pairing.tileStep,ha,hb,not_true_eq_false,not_false_eq_true,and_self,
        and_false,false_and,ite_true,ite_false,dite_true,dite_false,Option.elim_none,
        Option.elim_some,mul_zero,add_zero,zero_add]
      change r * ((localR a (⟨r,r,r,0,0⟩ : Weights K) * vacantProjection (K:=K) a.right) q p) +
        r * ((localR a (⟨r,r,r,0,0⟩ : Weights K) * vacantProjection (K:=K) a.right) q s) = _
      rw [mul_vacantProjection_apply,ite_eq_left hb,mul_zero,zero_add,
        mul_vacantProjection_apply,ite_eq_right hsb,localR_apply]
      simp only [sum_tiles,Weights.tile,Pairing.tileStep,hsa,hsb,not_true_eq_false,
        not_false_eq_true,and_self,and_false,false_and,ite_true,ite_false,dite_true,dite_false,
        Option.elim_none,Option.elim_some,mul_zero,add_zero,zero_add]
      rw [Pairing.moveIntoLowerVacancy_inverse p a.left a.right a.adjacent ha hsb]
      ring
    · simp only [Pairing.tileStep,ha,hb,not_false_eq_true,and_self,and_false,false_and,
        ite_true,ite_false,dite_true,dite_false,Option.elim_none,Option.elim_some,
        mul_zero,add_zero,one_mul]
      simp only [mul_vacantProjection_apply,Pairing.insertCup_occupied,hb,
        or_true,true_or,ite_true,ite_false,mul_zero,add_zero]
      rw [localR_apply]
      simp only [sum_tiles,Weights.tile,Pairing.tileStep,ha,hb,not_false_eq_true,
        and_self,and_false,false_and,ite_true,ite_false,dite_true,dite_false,
        Option.elim_none,Option.elim_some,mul_zero,add_zero,one_mul]

 

 


lemma sin_lambda_eq_c : Real.sin lambda = c := by
  rw [← Real.cos_pi_div_two_sub]
  congr 1
  unfold lambda
  ring

lemma sin_three_lambda_eq_C : Real.sin (3*lambda) = C := by
  rw [← Real.cos_pi_div_two_sub]
  congr 1
  unfold lambda
  ring

lemma sin_four_lambda_eq_one : Real.sin (4*lambda)=1 := by
  rw [show 4*lambda=Real.pi/2 by unfold lambda; ring,Real.sin_pi_div_two]

lemma C_ne_zero : C≠0 := by
  rw [←sin_three_lambda_eq_C]
  exact ne_of_gt sin_three_lambda_pos

lemma d_mul_c_div_C : d*c/C=rho^2 := by
  have hr := rho_eq_two_c_d
  have hC := rho_eq_inv_two_C
  calc
    d*c/C = (rho/2)/C := by rw [hr]; ring
    _ = rho*(1/(2*C)) := by ring
    _ = rho^2 := by rw [←hC]; ring

lemma d_sq_div_C : d^2/C=rho := by
  rw [d_sq,rho_eq_inv_two_C]
  ring

lemma torusL_phase_two (n : ℕ) : torusL (constF n phase ^ 2)=constF n C := by
  rw [torusL,←pow_add,←pow_add]
  norm_num only [Nat.reduceAdd]
  rw [torusSin_phase_pow,torusSin_phase_pow]
  simp only [Nat.cast_ofNat,sin_four_lambda_eq_one,sin_five_lambda_eq,sin_three_lambda_eq_C]
  simp only [Complex.ofReal_one,constF,map_one,one_mul]

 

lemma torusWeights_phase_two (n : ℕ) :
    torusWeights (constF n phase^2) =
      (⟨(constF n rho)^2,(constF n rho)^2,constF n rho,0,(constF n rho)^2⟩ :
        Weights (SpectralField n)) := by
  have hq := constF_phase_ne_zero n
  have hq32 : constF n phase^3/constF n phase^2=constF n phase := by field_simp
  have hq21 : constF n phase^2/constF n phase=constF n phase := by field_simp
  have hs1 : torusSin (constF n phase)=constF n c := by
    have h := torusSin_phase_pow n 1
    simpa only [pow_one,Nat.cast_one,one_mul,sin_lambda_eq_c] using h
  have he : constF n d*constF n c/constF n C=(constF n rho)^2 := by
    have h := congrArg (fun x : ℝ => constF n (x:ℂ)) d_mul_c_div_C
    simpa only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
      constF,map_div₀,map_mul,map_pow] using h
  have hu : constF n d*constF n d/constF n C=constF n rho := by
    have h := congrArg (fun x : ℝ => constF n (x:ℂ)) d_sq_div_C
    simpa only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_mul,constF,
      map_div₀,map_pow,map_mul,pow_two] using h
  unfold torusWeights
  simp only [hq32,hq21,div_self (pow_ne_zero 2 hq),torusSin_one,torusSin_phase_pow,
    Nat.cast_ofNat,sin_two_lambda_eq_d,hs1,torusL_phase_two,mul_zero,zero_div,he,hu,
    mul_comm (constF n c) (constF n d)]

 

def mergeProjection {n m : ℕ} (r : ℕ) (hr : r+2≤n+1) :
    Matrix (Pairing n) (Pairing (n+1)) (SpectralField m) :=
  splitProjection (Fin.succAboveOrderEmb ⟨r+1,by omega⟩)
    (PartialColumn.rowPosition r hr) (mergeWeights (constF m phase))

 

theorem mergeMap_mul_projection {n m : ℕ} (r : ℕ) (hr : r+2≤n+1) :
    mergeMap (m:=m) r hr * mergeProjection r hr =
      localR (PartialColumn.rowPosition r hr) (torusWeights (constF m phase^2)) := by
  unfold mergeMap mergeProjection splitProjection
  let E := functionMatrix (K:=SpectralField m)
    (Pairing.map (Fin.succAboveOrderEmb (⟨r+1,by omega⟩ : Fin (n+1))))
  let S := localR (PartialColumn.rowPosition r hr) (mergeWeights (constF m phase))
  calc
    _ = S * (E * (E.transpose * S)) := Matrix.mul_assoc _ _ _
    _ = S * ((E * E.transpose) * S) :=
      congrArg (fun M => S * M) (Matrix.mul_assoc E E.transpose S).symm
    _ = (S * (E * E.transpose)) * S := (Matrix.mul_assoc _ _ _).symm
    _ = (S * vacantProjection (K:=SpectralField m) (⟨r+1,by omega⟩ : Fin (n+1))) * S :=
      congrArg (fun M => (S * M) * S) (functionMatrix_mul_transpose_omit _)
    _ = _ := by
      dsimp only [S]
      rw [mergeWeights_source_constant,torusWeights_phase_two]
      exact localR_factor_merge (PartialColumn.rowPosition r hr) (constF m rho)

 

 


lemma functionMatrix_vacantProjection {K : Type*} [CommRing K] {n m : ℕ}
    (f : Fin n ↪o Fin m) (i : Fin n) :
    functionMatrix (K:=K) (Pairing.map f) * vacantProjection (K:=K) i =
      vacantProjection (K:=K) (f i) * functionMatrix (K:=K) (Pairing.map f) := by
  ext q p
  simp only [vacantProjection,Matrix.mul_diagonal,Matrix.diagonal_mul]
  by_cases h : p.map f=q
  · subst q
    simp only [Pairing.map_occupied]
    ring
  · simp [functionMatrix,optionMatrix,h]

 
def twoVacancyInsertion {K : Type*} [CommRing K] {n : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    Matrix (Pairing (n+2)) (Pairing n) K :=
  functionMatrix (Pairing.map (Fin.succAboveOrderEmb (⟨r+1,by omega⟩ : Fin (n+2)))) *
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb (⟨r,by omega⟩ : Fin (n+1))))

lemma twoVacancyInsertion_mul_transpose {K : Type*} [CommRing K] {n : ℕ}
    (r : ℕ) (hr : r+2≤n+2) :
    twoVacancyInsertion (K:=K) r hr * (twoVacancyInsertion (K:=K) r hr).transpose =
      vacantProjection (K:=K) (PartialColumn.rowPosition r hr).left *
        vacantProjection (K:=K) (PartialColumn.rowPosition r hr).right := by
  let b : Fin (n+2) := ⟨r+1,by omega⟩
  let a : Fin (n+1) := ⟨r,by omega⟩
  have hab : b.succAbove a = (PartialColumn.rowPosition r hr).left := by
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · change r<r+1; omega
  unfold twoVacancyInsertion
  let B := functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb b))
  let A := functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb a))
  calc
    _ = (B*A) * (A.transpose*B.transpose) :=
      congrArg (fun M => (B*A)*M) (Matrix.transpose_mul B A)
    _ = B * (A * (A.transpose * B.transpose)) := Matrix.mul_assoc _ _ _
    _ = B * ((A * A.transpose) * B.transpose) :=
      congrArg (fun M => B*M) (Matrix.mul_assoc A A.transpose B.transpose).symm
    _ = (B * (A * A.transpose)) * B.transpose := (Matrix.mul_assoc _ _ _).symm
    _ = (B * vacantProjection (K:=K) a) * B.transpose :=
      congrArg (fun M => (B*M)*B.transpose) (functionMatrix_mul_transpose_omit a)
    _ = (vacantProjection (K:=K) (b.succAbove a) * B) * B.transpose :=
      congrArg (fun M => M*B.transpose) (functionMatrix_vacantProjection (Fin.succAboveOrderEmb b) a)
    _ = vacantProjection (K:=K) (b.succAbove a) * (B*B.transpose) := Matrix.mul_assoc _ _ _
    _ = vacantProjection (K:=K) (b.succAbove a) * vacantProjection (K:=K) b :=
      congrArg (fun M => vacantProjection (K:=K) (b.succAbove a)*M) (functionMatrix_mul_transpose_omit b)
    _ = _ := by rw [hab]; rfl

 

lemma localR_factor_deletion {K : Type*} [CommRing K] {n : ℕ} (a : Position n) :
    localR a (deletionWeights : Weights K) * vacantProjection (K:=K) a.left *
      vacantProjection (K:=K) a.right * localR a (deletionWeights : Weights K) =
    localR a (deletionWeights : Weights K) := by
  ext q p
  rw [mul_localR_apply,localR_apply]
  simp only [sum_tiles,deletionWeights,Weights.tile]
  by_cases ha : p.Occupied a.left
  · by_cases hb : p.Occupied a.right
    · by_cases hn : p.Adj a.left a.right
      · simp [Pairing.tileStep,ha,hb,hn]
      · let s := p.capRemove a.left a.right a.adjacent ha hb hn
        have hsa : ¬s.Occupied a.left := (p.capRemove_vacant _ _ _ ha hb hn).1
        have hsb : ¬s.Occupied a.right := (p.capRemove_vacant _ _ _ ha hb hn).2
        simp only [Pairing.tileStep,ha,hb,hn,not_true_eq_false,and_false,
          and_true,ite_true,ite_false,dite_true,dite_false,Option.elim_none,
          Option.elim_some,zero_mul,mul_zero,add_zero,zero_add,one_mul]
        change ((localR a (⟨0,0,1,0,1⟩ : Weights K) * vacantProjection (K:=K) a.left *
          vacantProjection (K:=K) a.right) q s) +
          ((localR a (⟨0,0,1,0,1⟩ : Weights K) * vacantProjection (K:=K) a.left *
          vacantProjection (K:=K) a.right) q (s.insertCup a.left a.right a.adjacent hsa hsb)) = _
        simp only [mul_vacantProjection_apply,hsb,hsa,Pairing.insertCup_occupied,
          or_true,true_or,ite_true,ite_false,add_zero]
        rw [localR_apply]
        simp only [sum_tiles,Weights.tile,Pairing.tileStep,hsa,hsb,not_false_eq_true,
          and_self,and_false,false_and,ite_true,ite_false,dite_true,dite_false,Option.elim_none,
          Option.elim_some,mul_zero,add_zero,one_mul]
        rfl
    · simp [Pairing.tileStep,ha,hb]
  · by_cases hb : p.Occupied a.right
    · simp [Pairing.tileStep,ha,hb]
    · simp only [Pairing.tileStep,ha,hb,not_false_eq_true,and_self,and_false,false_and,
        ite_true,ite_false,dite_true,dite_false,Option.elim_none,Option.elim_some,
        mul_zero,add_zero,one_mul]
      simp only [mul_vacantProjection_apply,Pairing.insertCup_occupied,ha,hb,
        or_true,true_or,ite_true,ite_false,add_zero]
      rw [localR_apply]
      simp only [sum_tiles,Weights.tile,Pairing.tileStep,ha,hb,not_false_eq_true,
        and_self,and_false,false_and,ite_true,ite_false,dite_true,dite_false,
        Option.elim_none,Option.elim_some,mul_zero,add_zero,one_mul]

 
def deletionProjection {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    Matrix (Pairing n) (Pairing (n+2)) (SpectralField m) :=
  (twoVacancyInsertion (K:=SpectralField m) r hr).transpose *
    localR (PartialColumn.rowPosition r hr) deletionWeights

theorem deletionMap_mul_projection {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    deletionMap (m:=m) r hr * deletionProjection r hr =
      localR (PartialColumn.rowPosition r hr) (torusWeights (constF m phase^3)) := by
  let E := twoVacancyInsertion (K:=SpectralField m) r hr
  let S := localR (PartialColumn.rowPosition r hr) (deletionWeights : Weights (SpectralField m))
  change (S*E) * (E.transpose*S) = _
  calc
    _ = S * (E * (E.transpose * S)) := Matrix.mul_assoc _ _ _
    _ = S * ((E * E.transpose) * S) :=
      congrArg (fun M => S*M) (Matrix.mul_assoc E E.transpose S).symm
    _ = (S * (E * E.transpose)) * S := (Matrix.mul_assoc _ _ _).symm
    _ = (S * (vacantProjection (K:=SpectralField m) (PartialColumn.rowPosition r hr).left *
        vacantProjection (K:=SpectralField m) (PartialColumn.rowPosition r hr).right)) * S :=
      congrArg (fun M => (S*M)*S) (twoVacancyInsertion_mul_transpose r hr)
    _ = ((S * vacantProjection (K:=SpectralField m) (PartialColumn.rowPosition r hr).left) *
        vacantProjection (K:=SpectralField m) (PartialColumn.rowPosition r hr).right) * S :=
      congrArg (fun M => M*S) (Matrix.mul_assoc _ _ _).symm
    _ = _ := by
      dsimp only [S]
      rw [localR_factor_deletion,torusWeights_phase_three]

end
end CriticalStrip.Diagram

end OAI
