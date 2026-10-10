import Mathlib
import OAI.Combinatorics.StripMass.GraphPath
import OAI.Combinatorics.StripMass.RealEvaluation

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators Classical
open Finset Matrix

 
def angleScalar {n : ℕ} (u : Fin n → ℝ) : ℂ :=
  angleEvaluation u (polynomialVacuumVector n (empty n))

 

def angleVacuum {n : ℕ} (u : Fin n → ℝ) (p : Pairing n) : ℝ :=
  (angleEvaluation u (polynomialVacuumVector n p)/angleScalar u).re

def angleNorthSource {n : ℕ} (u : Fin n → ℝ) (p : SourcePairing n) : ℝ :=
  (angleEvaluation u (polynomialNorthSource n p)/angleScalar u).re

lemma rationalAt_angle_vacuum {n : ℕ} (u : Fin n → ℝ) (p : Pairing n) :
    RationalAt (angleEvaluation u).toRingHom (rationalVacuum n p)
      (angleEvaluation u (polynomialVacuumVector n p)) := by
  have h:=RationalAt.algebraMap (φ:=(angleEvaluation u).toRingHom) (F:=SpectralField n)
    (polynomialVacuumVector n p)
  rw [show algebraMap (Laurent n) (SpectralField n) (polynomialVacuumVector n p)=rationalVacuum n p from
    polynomialVacuumVector_eval n p] at h
  exact h

lemma rationalAt_angle_column {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) (p q : Pairing n) :
    RationalAt (angleEvaluation u).toRingHom (column (spectralWeights n) p q)
      (transfer u p q:ℂ) := by
  have hc:=rationalAt_column (spectralWeights n)
    (fun i=>(physicalWeights (3*lambda-u i)).map Complex.ofRealHom)
    (fun i t=>by simpa using rationalAt_angle_spectralWeights u hL i t) p q
  rw [←column_map] at hc
  exact hc

lemma angle_rawVacuum_stationary {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) :
    ((transfer u).map Complex.ofRealHom).mulVec (fun p=>angleEvaluation u (polynomialVacuumVector n p))=
      fun p=>angleEvaluation u (polynomialVacuumVector n p) := by
  funext p
  have hm:=RationalAt.mulVec (φ:=(angleEvaluation u).toRingHom)
    (column (spectralWeights n)) ((transfer u).map Complex.ofRealHom)
    (rationalVacuum n) (fun p=>angleEvaluation u (polynomialVacuumVector n p))
    (rationalAt_angle_column u hL) (rationalAt_angle_vacuum u) p
  rw [rationalVacuum_stationary] at hm
  exact hm.unique (rationalAt_angle_vacuum u p)

lemma angleVacuum_empty {n : ℕ} (u : Fin n → ℝ) (h : angleScalar u≠0) :
    angleVacuum u (empty n)=1 := by
  change (angleScalar u / angleScalar u).re = 1
  rw [div_self h, Complex.one_re]

lemma angleVacuum_stationary {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) :
    (transfer u).mulVec (angleVacuum u)=angleVacuum u := by
  funext p
  have hh:=congrArg (fun z : ℂ=>(z/angleScalar u).re) (congrFun (angle_rawVacuum_stationary u hL) p)
  simp only [Matrix.mulVec,dotProduct,Matrix.map_apply,Complex.ofRealHom_eq_coe,Finset.sum_div] at hh
  simpa only [Matrix.mulVec,dotProduct,angleVacuum,mul_div_assoc,Complex.re_sum,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hh

lemma angleVacuum_restricted_stationary {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) (h : angleScalar u≠0) :
    (restrictedColumn (fun i=>physicalWeights (3*lambda-u i))).mulVec
        (fun p=>angleVacuum u p.val)+injectionColumn (fun i=>physicalWeights (3*lambda-u i))=
      fun p=>angleVacuum u p.val := by
  funext p
  have hh:=congrFun (angleVacuum_stationary u hL) p.val
  rw [transfer,column_mulVec_nonempty,angleVacuum_empty u h,mul_one] at hh
  simpa only [Pi.add_apply, add_comm] using hh

lemma continuous_angleScalar {n : ℕ} : Continuous (@angleScalar n) :=
  continuous_angleEvaluation _

lemma continuousOn_angleVacuum {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : ∀u∈S,angleScalar u≠0) : ContinuousOn (fun u=>angleVacuum u) S := by
  apply continuousOn_pi.mpr
  intro p
  exact Complex.continuous_re.continuousOn.comp
    ((continuous_angleEvaluation _).continuousOn.div continuous_angleScalar.continuousOn h)
    (Set.mapsTo_univ _ _)

lemma continuousOn_angleNorthSource {n : ℕ} {S : Set (Fin n → ℝ)}
    (h : ∀u∈S,angleScalar u≠0) : ContinuousOn (fun u=>angleNorthSource u) S := by
  apply continuousOn_pi.mpr
  intro p
  exact Complex.continuous_re.continuousOn.comp
    ((continuous_angleEvaluation _).continuousOn.div continuous_angleScalar.continuousOn h)
    (Set.mapsTo_univ _ _)

section
variable {R F K : Type*} [CommRing R] [Field F] [Field K]
  [Algebra R F] {φ : R →+* K}

lemma rationalAt_lastCoefficient [IsDomain R] [IsFractionRing R F]
    {n : ℕ} (w : Fin n → Tile → F) (v : Fin n → Tile → K)
    (h : ∀i t,RationalAt φ (w i t) (v i t)) (p q : Pairing (n+1)) :
    RationalAt φ (lastCoefficient w p q) (lastCoefficient v p q) := by
  unfold lastCoefficient
  apply RationalAt.sum
  intro t _
  split_ifs
  · exact RationalAt.prod _ _ _ (fun i _=>h i (t i))
  · exact RationalAt.zero
end

lemma rationalAt_angle_sourceTransfer {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) (p q : SourcePairing n) :
    RationalAt (angleEvaluation u).toRingHom
      (sourceTransfer (fun i=>(spectralWeights n i).tile) p q)
      ((sourceTransfer (fun i=>(physicalWeights (3*lambda-u i)).tile) p q : ℝ):ℂ) := by
  have hh:=rationalAt_lastCoefficient (fun i=>(spectralWeights n i).tile)
    (fun i t=>Complex.ofRealHom ((physicalWeights (3*lambda-u i)).tile t))
    (rationalAt_angle_spectralWeights u hL) p.val q.val
  rw [lastCoefficient_map Complex.ofRealHom] at hh
  exact hh

lemma rationalAt_angle_northSource {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) (p : SourcePairing n) (q : Pairing n) :
    RationalAt (angleEvaluation u).toRingHom
      (northSource (fun i=>(spectralWeights n i).tile) p q)
      ((northSource (fun i=>(physicalWeights (3*lambda-u i)).tile) p q : ℝ):ℂ) := by
  have hh:=rationalAt_lastCoefficient (fun i=>(spectralWeights n i).tile)
    (fun i t=>Complex.ofRealHom ((physicalWeights (3*lambda-u i)).tile t))
    (rationalAt_angle_spectralWeights u hL) p.val q.padTop
  rw [lastCoefficient_map Complex.ofRealHom] at hh
  exact hh

lemma polynomialNorthSource_rational_equation (n : ℕ) :
    (sourceTransfer (fun i=>(spectralWeights n i).tile)).mulVec
        (fun p=>evalLaurent (polynomialNorthSource n p))+
      (northSource (fun i=>(spectralWeights n i).tile)).mulVec (rationalVacuum n)=
      fun p=>evalLaurent (polynomialNorthSource n p) := by
  have hs: (1-sourceTransfer (fun i=>(spectralWeights n i).tile)).mulVec (integratedNorthSource n)=
      (northSource (fun i=>(spectralWeights n i).tile)).mulVec (normalizedVacuum (spectralWeights n)) := by
    rw [integratedNorthSource,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (spectral_source_regular n)),Matrix.one_mulVec]
  have ht:=congrArg (fun v=>spectralNormalization n • v) hs
  rw [Matrix.sub_mulVec,Matrix.one_mulVec] at ht
  simp only [smul_sub,←Matrix.mulVec_smul] at ht
  have he : (fun p=>evalLaurent (polynomialNorthSource n p))=
      spectralNormalization n • integratedNorthSource n := funext (polynomialNorthSource_eval n)
  rw [he]
  change _+(northSource _).mulVec (spectralNormalization n • normalizedVacuum (spectralWeights n))=_
  rw [←ht]
  abel

lemma angle_rawNorthSource_equation {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) :
    ((sourceTransfer (fun i=>(physicalWeights (3*lambda-u i)).tile)).map Complex.ofRealHom).mulVec
        (fun p=>angleEvaluation u (polynomialNorthSource n p))+
      ((northSource (fun i=>(physicalWeights (3*lambda-u i)).tile)).map Complex.ofRealHom).mulVec
        (fun p=>angleEvaluation u (polynomialVacuumVector n p))=
      fun p=>angleEvaluation u (polynomialNorthSource n p) := by
  funext p
  have hm:=RationalAt.mulVec (φ:=(angleEvaluation u).toRingHom)
    (sourceTransfer (fun i=>(spectralWeights n i).tile))
    ((sourceTransfer (fun i=>(physicalWeights (3*lambda-u i)).tile)).map Complex.ofRealHom)
    (fun q=>evalLaurent (polynomialNorthSource n q))
    (fun q=>angleEvaluation u (polynomialNorthSource n q))
    (rationalAt_angle_sourceTransfer u hL) (fun q=>RationalAt.algebraMap _) p
  have hn:=RationalAt.mulVec (φ:=(angleEvaluation u).toRingHom)
    (northSource (fun i=>(spectralWeights n i).tile))
    ((northSource (fun i=>(physicalWeights (3*lambda-u i)).tile)).map Complex.ofRealHom)
    (rationalVacuum n) (fun q=>angleEvaluation u (polynomialVacuumVector n q))
    (rationalAt_angle_northSource u hL) (rationalAt_angle_vacuum u) p
  have hh:=hm.add hn
  have he:=congrFun (polynomialNorthSource_rational_equation n) p
  simp only [Pi.add_apply] at he
  rw [he] at hh
  exact hh.unique (RationalAt.algebraMap _)

lemma angleNorthSource_stationary {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) :
    (sourceTransfer (fun i=>(physicalWeights (3*lambda-u i)).tile)).mulVec (angleNorthSource u)+
      (northSource (fun i=>(physicalWeights (3*lambda-u i)).tile)).mulVec (angleVacuum u)=
      angleNorthSource u := by
  funext p
  have hh:=congrArg (fun z : ℂ=>(z/angleScalar u).re) (congrFun (angle_rawNorthSource_equation u hL) p)
  simpa only [Pi.add_apply,Matrix.mulVec,dotProduct,Matrix.map_apply,Complex.ofRealHom_eq_coe,
    add_div,Finset.sum_div,mul_div_assoc,Complex.add_re,Complex.re_sum,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,angleNorthSource,angleVacuum] using hh


 

 

 


namespace Pairing

structure ArcAddition {n : ℕ} (p q : Pairing n) (a b : Fin n) : Prop where
  lt : a < b
  vacant : ∀ i, a ≤ i → i ≤ b → ¬ p.Occupied i
  adj : ∀ i j, q.Adj i j ↔
    (i=a ∧ j=b) ∨ (i=b ∧ j=a) ∨ p.Adj i j

lemma ArcAddition.occupied {n : ℕ} {p q : Pairing n} {a b : Fin n}
    (h : ArcAddition p q a b) (i : Fin n) :
    q.Occupied i ↔ i=a ∨ i=b ∨ p.Occupied i := by
  simp only [Occupied,h.adj]
  aesop

lemma ArcAddition.old {n : ℕ} {p q : Pairing n} {a b i j : Fin n}
    (h : ArcAddition p q a b) (hp : p.Adj i j) : q.Adj i j :=
  (h.adj i j).mpr (Or.inr (Or.inr hp))

lemma ArcAddition.arc {n : ℕ} {p q : Pairing n} {a b : Fin n}
    (h : ArcAddition p q a b) : q.Adj a b := (h.adj a b).mpr (Or.inl ⟨rfl,rfl⟩)

end Pairing

 

def arcColumn {n : ℕ} (p : Pairing n) (a b : Fin n) : Configuration n := fun i=>
  if i=a then .cup else if i=b then .vertical₀ else
  if a < i ∧ i < b then .diagonal₀ else if p.Occupied i then .diagonal₁ else .vacant

namespace ArcColumn
variable {n : ℕ} {p q : Pairing n} {a b : Fin n} (h : Pairing.ArcAddition p q a b)

include h

omit h in
lemma at_a : arcColumn p a b a=.cup := by simp [arcColumn]
lemma at_b : arcColumn p a b b=.vertical₀ := by simp [arcColumn,ne_of_gt h.lt]
omit h in
lemma at_inside (i : Fin n) (ha : a < i) (hb : i < b) : arcColumn p a b i=.diagonal₀ := by
  simp [arcColumn,ne_of_gt ha,ne_of_lt hb,ha,hb]
lemma at_old (i : Fin n) (hi : p.Occupied i) : arcColumn p a b i=.diagonal₁ := by
  have hn : ¬(a ≤ i ∧ i ≤ b) := fun hh=>h.vacant i hh.1 hh.2 hi
  have hab:=h.lt
  simp only [arcColumn]
  split_ifs <;> first | rfl | omega

lemma west (i : Fin n) : (arcColumn p a b i).Occupied 1 ↔ p.Occupied i := by
  have ha:=h.lt
  have hv:=h.vacant i
  unfold arcColumn
  split_ifs <;> simp_all [Tile.Occupied,Tile.Adj,Tile.edges]
  all_goals apply hv <;> omega

lemma east (i : Fin n) : (arcColumn p a b i).Occupied 2 ↔ q.Occupied i := by
  rw [h.occupied]
  have ha:=h.lt
  have hv:=h.vacant i
  unfold arcColumn
  split_ifs <;> simp_all [Tile.Occupied,Tile.Adj,Tile.edges]
  all_goals apply hv <;> omega

lemma south (i : Fin n) : (arcColumn p a b i).Occupied 0 ↔ a < i ∧ i ≤ b := by
  have ha:=h.lt
  unfold arcColumn
  split_ifs <;> simp_all [Tile.Occupied,Tile.Adj,Tile.edges] <;> omega

lemma north (i : Fin n) : (arcColumn p a b i).Occupied 3 ↔ a ≤ i ∧ i < b := by
  have ha:=h.lt
  unfold arcColumn
  split_ifs <;> simp_all [Tile.Occupied,Tile.Adj,Tile.edges] <;> omega

omit h in
lemma tile_edge {i : Fin n} {r s : Fin 4} (ht : (arcColumn p a b i).Adj r s) :
    Wiring p (arcColumn p a b) (i,r) (i,s) := Or.inl ⟨rfl,ht⟩

lemma reach_north (i : Fin n) (hai : a ≤ i) (hib : i < b) :
    Reach p (arcColumn p a b) (a,2) (i,3) := by
  induction k : i.val using Nat.strong_induction_on generalizing i with
  | h k ih =>
    by_cases he : i=a
    · subst i
      exact .single (tile_edge (by simp [at_a,Tile.Adj,Tile.edges]))
    · have hip : 0 < i.val := by omega
      let j : Fin n:=⟨i.val-1,by omega⟩
      have hji : j.val+1=i.val := by dsimp [j]; omega
      have hj : a ≤ j ∧ j < b := by dsimp [j]; constructor <;> omega
      have hr:=ih j.val (by dsimp [j]; omega) j hj.1 hj.2 rfl
      have hg : Wiring p (arcColumn p a b) (j,3) (i,0) :=
        Or.inr (Or.inr (Or.inl ⟨rfl,rfl,hji,(north h j).mpr hj⟩))
      have hi : arcColumn p a b i=.diagonal₀ := at_inside i (by omega) hib
      exact (hr.tail hg).tail (tile_edge (by simp [hi,Tile.Adj,Tile.edges]))

lemma reach_south (i : Fin n) (hai : a < i) (hib : i ≤ b) :
    Reach p (arcColumn p a b) (a,2) (i,0) := by
  have hip : 0 < i.val := by omega
  let j : Fin n:=⟨i.val-1,by omega⟩
  have hji : j.val+1=i.val := by dsimp [j]; omega
  have hj : a ≤ j ∧ j < b := by dsimp [j]; constructor <;> omega
  exact (reach_north h j hj.1 hj.2).tail
    (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,hji,(north h j).mpr hj⟩)))

lemma reach_arc : Reach p (arcColumn p a b) (a,2) (b,2) :=
  (reach_south h b h.lt le_rfl).tail (tile_edge (by simp [at_b h,Tile.Adj,Tile.edges]))

lemma reach_old (i : Fin n) (hi : p.Occupied i) :
    Reach p (arcColumn p a b) (i,1) (i,2) :=
  .single (tile_edge (by simp [at_old h i hi,Tile.Adj,Tile.edges]))

def label (a : Fin n) (v : Vertex n) : Fin n := if v.2=0 ∨ v.2=3 then a else v.1

lemma edge_label {v w : Vertex n} (hw : Wiring p (arcColumn p a b) v w) :
    label a v=label a w ∨ q.Adj (label a v) (label a w) := by
  rcases v with ⟨i,r⟩; rcases w with ⟨j,s⟩
  rcases hw with ⟨rfl,ht⟩ | ⟨rfl,rfl,hp⟩ | ⟨rfl,rfl,_,_⟩ | ⟨rfl,rfl,_,_⟩
  · by_cases hi : i=a
    · subst i
      simp only [at_a,Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
      rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [label]
    · by_cases hj : i=b
      · subst i
        rw [at_b h] at ht
        simp only [Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
        rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr h.arc
        · exact Or.inr (Pairing.adj_symm h.arc)
      · by_cases hm : a < i ∧ i < b
        · rw [at_inside i hm.1 hm.2] at ht
          simp only [Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
          rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [label]
        · by_cases hp : p.Occupied i
          · rw [at_old h i hp] at ht
            simp only [Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
            rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [label]
          · simp [arcColumn,hi,hj,hm,hp] at ht
  · exact Or.inr (h.old hp)
  · exact Or.inl rfl
  · exact Or.inl rfl

lemma reach_label {v w : Vertex n} (hr : Reach p (arcColumn p a b) v w) :
    label a v=label a w ∨ q.Adj (label a v) (label a w) := by
  induction hr with
  | refl => exact Or.inl rfl
  | @tail w z _ hw ih =>
    obtain he | he := edge_label h hw
    · simpa only [←he] using ih
    obtain hi | hi := ih
    · exact Or.inr (hi ▸ he)
    · exact Or.inl (Pairing.adj_unique (Pairing.adj_symm hi) he)

lemma no_loop (v w : Vertex n) (hw : Wiring p (arcColumn p a b) v w) :
    ∃ j, q.Occupied j ∧ Reach p (arcColumn p a b) v (j,2) := by
  have ha : q.Occupied a:=⟨b,h.arc⟩
  have hb : q.Occupied b:=⟨a,Pairing.adj_symm h.arc⟩
  rcases v with ⟨i,r⟩; rcases w with ⟨j,s⟩
  rcases hw with ⟨rfl,ht⟩ | ⟨rfl,rfl,hp⟩ | ⟨rfl,rfl,_,hn⟩ | ⟨rfl,rfl,hji,hn⟩
  · by_cases hi : i=a
    · subst i
      simp only [at_a,Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
      rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨a,ha,.refl⟩
      · exact ⟨a,ha,reach_symm (reach_north h a le_rfl h.lt)⟩
    · by_cases hj : i=b
      · subst i
        rw [at_b h] at ht
        simp only [Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
        rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨b,hb,.single (tile_edge (by simp [at_b h,Tile.Adj,Tile.edges]))⟩
        · exact ⟨b,hb,.refl⟩
      · by_cases hm : a < i ∧ i < b
        · rw [at_inside i hm.1 hm.2] at ht
          simp only [Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
          rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · exact ⟨a,ha,reach_symm (reach_south h i hm.1 hm.2.le)⟩
          · exact ⟨a,ha,reach_symm (reach_north h i hm.1.le hm.2)⟩
        · by_cases hp : p.Occupied i
          · rw [at_old h i hp] at ht
            simp only [Tile.Adj,Tile.edges,mem_singleton,Prod.mk.injEq] at ht
            rcases ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
            · exact ⟨i,(h.occupied i).mpr (Or.inr (Or.inr hp)),reach_old h i hp⟩
            · exact ⟨i,(h.occupied i).mpr (Or.inr (Or.inr hp)),.refl⟩
          · simp [arcColumn,hi,hj,hm,hp] at ht
  · exact ⟨i,⟨j,h.old hp⟩,reach_old h i ⟨j,hp⟩⟩
  · obtain ⟨hi,hb'⟩:=(north h i).mp hn
    exact ⟨a,ha,reach_symm (reach_north h i hi hb')⟩
  · obtain ⟨hj,hb'⟩:=(north h j).mp hn
    change j.val+1=i.val at hji
    exact ⟨a,ha,reach_symm (reach_south h i (by omega) (by omega))⟩

lemma realizes : Realizes p q (arcColumn p a b) := by
  refine ⟨west h,east h,?_,?_,?_,no_loop h,?_⟩
  · intro i hi ht
    have hh:=(south h i).mp ht
    omega
  · intro i hi ht
    have hh:=(north h i).mp ht
    have:=b.isLt
    omega
  · intro i j hij
    rw [north h i,south h j]
    omega
  · intro i j hij
    constructor
    · intro ht
      rcases (h.adj i j).mp ht with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | hp
      · exact reach_arc h
      · exact reach_symm (reach_arc h)
      · exact ((reach_symm (reach_old h i ⟨j,hp⟩)).tail
          (Or.inr (Or.inl ⟨rfl,rfl,hp⟩))).trans (reach_old h j ⟨i,Pairing.adj_symm hp⟩)
    · intro hr
      have hh:=reach_label h hr
      simpa [label,hij] using hh

end ArcColumn

namespace Pairing

 

lemma exists_arcAddition {n : ℕ} (q : Pairing n) (hq : q ≠ empty n) :
    ∃ (p : Pairing n) (a b : Fin n), p.val.card < q.val.card ∧ ArcAddition p q a b := by
  have hne : q.val.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    exact hq (Subtype.ext he)
  obtain ⟨⟨a,b⟩,hab,hmin⟩:=Finset.exists_min_image q.val
    (fun e : Fin n × Fin n=>e.2.val-e.1.val) hne
  have hlt : a < b:=q.property.1 _ hab
  have hqab : q.Adj a b:=Or.inl hab
  refine ⟨q.omitTwo a b,a,b,?_,hlt,?_,?_⟩
  · apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _,?_⟩
    intro he
    have hh : (a,b) ∈ (q.omitTwo a b).val:=he ▸ hab
    simp [omitTwo] at hh
  · intro i hai hib ⟨j,hij⟩
    obtain ⟨hij,hia,hib',hja,hjb⟩:=(omitTwo_adj q a b i j).mp hij
    have hai' : a < i:=lt_of_le_of_ne hai (Ne.symm hia)
    have hib'' : i < b:=lt_of_le_of_ne hib hib'
    rcases hij with hf | hf
    · have hf_lt := q.property.1 _ hf
      have hc := q.property.2.2 _ hab _ hf
      have hm := hmin _ hf
      dsimp only at hf_lt hc hm
      omega
    · have hf_lt := q.property.1 _ hf
      have hc := q.property.2.2 _ hf _ hab
      have hm := hmin _ hf
      dsimp only at hf_lt hc hm
      omega
  · intro i j
    rw [omitTwo_adj]
    constructor
    · intro hij
      by_cases hia : i=a
      · subst i
        exact Or.inl ⟨rfl,adj_unique hij hqab⟩
      by_cases hib : i=b
      · subst i
        exact Or.inr (Or.inl ⟨rfl,adj_unique hij (adj_symm hqab)⟩)
      have hja : j ≠ a:= by
        rintro rfl
        exact hib (adj_unique (adj_symm hij) hqab)
      have hjb : j ≠ b:= by
        rintro rfl
        exact hia (adj_unique (adj_symm hij) (adj_symm hqab))
      exact Or.inr (Or.inr ⟨hij,hia,hib,hja,hjb⟩)
    · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨hh,_⟩)
      · exact hqab
      · exact adj_symm hqab
      · exact hh

end Pairing

 

def ColumnNonnegative {n : ℕ} (w : Fin n → Weights ℝ) : Prop :=
  ∀ (p q : Pairing n) (t : Configuration n), Realizes p q t →
    0 ≤ ∏ i, (w i).tile (t i)

lemma ColumnNonnegative.column {n : ℕ} {w : Fin n → Weights ℝ}
    (hw : ColumnNonnegative w) : PositiveMatrix.Nonnegative (column w) := by
  intro q p
  apply Finset.sum_nonneg
  intro t _
  split_ifs with ht
  · exact hw p q t ht
  · exact le_rfl

lemma ColumnNonnegative.restricted {n : ℕ} {w : Fin n → Weights ℝ}
    (hw : ColumnNonnegative w) : PositiveMatrix.Nonnegative (restrictedColumn w) :=
  fun p q=>hw.column p.val q.val

lemma ColumnNonnegative.injection {n : ℕ} {w : Fin n → Weights ℝ}
    (hw : ColumnNonnegative w) : ∀ p, 0 ≤ injectionColumn w p :=
  fun p=>hw.column p.val (empty n)

lemma arcColumn_weight_pos {n : ℕ} (w : Fin n → Weights ℝ)
    (hA : ∀ i,0 < (w i).A) (hB : ∀ i,0 < (w i).B)
    (hU : ∀ i,i.val+1 < n → 0 < (w i).U)
    {p q : Pairing n} {a b : Fin n} (h : Pairing.ArcAddition p q a b) :
    0 < ∏ i, (w i).tile (arcColumn p a b i) := by
  apply Finset.prod_pos
  intro i _
  have hab:=h.lt
  have hb:=b.isLt
  unfold arcColumn
  split_ifs <;> simp only [Weights.tile]
  · exact hU i (by subst i; omega)
  · exact hA i
  · exact hB i
  · exact hB i
  · exact zero_lt_one

lemma column_arc_pos {n : ℕ} (w : Fin n → Weights ℝ) (hw : ColumnNonnegative w)
    (hA : ∀ i,0 < (w i).A) (hB : ∀ i,0 < (w i).B)
    (hU : ∀ i,i.val+1 < n → 0 < (w i).U)
    {p q : Pairing n} {a b : Fin n} (h : Pairing.ArcAddition p q a b) :
    0 < column w q p := by
  have hl : (∏ i,(w i).tile (arcColumn p a b i)) ≤ column w q p := by
    have := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun t : Configuration n=>if Realizes p q t then ∏ i,(w i).tile (t i) else 0)
      (fun t _=>by split_ifs with ht; exact hw p q t ht; exact le_rfl)
      (Finset.mem_univ (arcColumn p a b))
    simpa only [ite_eq_left (ArcColumn.realizes h),column] using this
  exact (arcColumn_weight_pos w hA hB hU h).trans_le hl

 

theorem column_accessible {n : ℕ} (w : Fin n → Weights ℝ) (hw : ColumnNonnegative w)
    (hA : ∀ i,0 < (w i).A) (hB : ∀ i,0 < (w i).B)
    (hU : ∀ i,i.val+1 < n → 0 < (w i).U) :
    PositiveMatrix.Accessible (restrictedColumn w) (injectionColumn w) := by
  intro q
  induction k : q.val.val.card using Nat.strong_induction_on generalizing q with
  | h k ih =>
    obtain ⟨p,a,b,hcard,hadd⟩:=Pairing.exists_arcAddition q.val q.property
    have hpq:=column_arc_pos w hw hA hB hU hadd
    by_cases hp : p=empty n
    · subst p
      refine ⟨0,?_⟩
      simpa only [pow_zero,Matrix.one_mulVec,injectionColumn] using hpq
    · let p' : NonemptyPairing n:=⟨p,hp⟩
      obtain ⟨m,hm⟩:=ih p.val.card (by omega) p' rfl
      refine ⟨m+1,?_⟩
      rw [pow_succ',←Matrix.mulVec_mulVec]
      exact (mul_pos hpq hm).trans_le
        (PositiveMatrix.entry_mul_le_mulVec hw.restricted
          ((hw.restricted.pow m).mulVec hw.injection) q p')

end
end CriticalStrip.Diagram

end OAI
