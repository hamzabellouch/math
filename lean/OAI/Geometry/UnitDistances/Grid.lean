import OAI.Geometry.UnitDistances.Derivations

namespace OAI

namespace PlanarUnitDistances.CoefficientField
universe u
variable {B U : Type u} [Field B] [Field U] [Algebra B U]

abbrev FieldOf (y : Fin 4 × Fin 5 → U) :=
  algebraicClosure (IntermediateField.adjoin B (Set.range y)) U

noncomputable def entry (y : Fin 4 × Fin 5 → U) (i : Fin 4 × Fin 5) :
    FieldOf (B := B) y :=
  ⟨y i, by
    rw [mem_algebraicClosure_iff]
    let a : IntermediateField.adjoin B (Set.range y) :=
      ⟨y i,IntermediateField.subset_adjoin B _ ⟨i,rfl⟩⟩
    exact isAlgebraic_algebraMap a⟩

@[simp] theorem entry_val (y : Fin 4 × Fin 5 → U) (i : Fin 4 × Fin 5) :
    (entry (B := B) y i : U)=y i := rfl

theorem exists_left_block {δ : Type*} [Fintype δ]
    (x : Fin 21 × δ → U) (hx : AlgebraicIndependent B x)
    (y : Fin 4 × Fin 5 → U) :
    ∃ i : Fin 21, AlgebraicIndependent (FieldOf (B := B) y) (fun j => x (i,j)) :=
  UnitDistanceSurvival.survives_algebraic_closure x hx y (by decide)

variable {k : Type u} [Field k] [Algebra k U]

def parameters (D : Derivation k U U) (a b t : Fin 4 → U) : Fin 4 × Fin 5 → U :=
  fun ij => ![a ij.1,b ij.1,D (a ij.1),D (b ij.1),t ij.1] ij.2

@[simp] theorem parameters_zero (D : Derivation k U U) (a b t : Fin 4 → U) (i : Fin 4) :
    parameters D a b t (i,0)=a i := rfl
@[simp] theorem parameters_one (D : Derivation k U U) (a b t : Fin 4 → U) (i : Fin 4) :
    parameters D a b t (i,1)=b i := rfl
@[simp] theorem parameters_two (D : Derivation k U U) (a b t : Fin 4 → U) (i : Fin 4) :
    parameters D a b t (i,2)=D (a i) := rfl
@[simp] theorem parameters_three (D : Derivation k U U) (a b t : Fin 4 → U) (i : Fin 4) :
    parameters D a b t (i,3)=D (b i) := rfl
@[simp] theorem parameters_four (D : Derivation k U U) (a b t : Fin 4 → U) (i : Fin 4) :
    parameters D a b t (i,4)=t i := rfl
end PlanarUnitDistances.CoefficientField

namespace PlanarUnitDistances.GridObstruction
open CoefficientField
universe u
variable {k B U : Type u} [Field k] [CharZero k] [Field B] [CharZero B]
  [Field U] [Algebra k U] [Algebra B U]

theorem plane (x : Fin 21 × Fin 2 → U) (hx : AlgebraicIndependent B x)
    (a b : Fin 4 → U) (hab : Function.Injective (fun j => (a j,b j)))
    (l : Fin 21 → Fin 4 → U) (htrans : ∀ i j, Transcendental k (l i j))
    (hrect : ∀ i j, ∃ c : k, l i j*l 0 0=l i 0*l 0 j*algebraMap k U c)
    (hdist : ∀ i j, (x (i,0)-a j)*(x (i,1)-b j)=2-l i j-(l i j)⁻¹) : False := by
  obtain ⟨D,A,t,hD,hlog⟩ := GridDerivation.exists_derivation_log l htrans hrect
  let y := parameters D a b t
  let K := FieldOf (B := B) y
  let a' : Fin 4 → K := fun j => entry y (j,0)
  let b' : Fin 4 → K := fun j => entry y (j,1)
  let da' : Fin 4 → K := fun j => entry y (j,2)
  let db' : Fin 4 → K := fun j => entry y (j,3)
  let t' : Fin 4 → K := fun j => entry y (j,4)
  have ha' (j) : algebraMap K U (a' j)=a j := rfl
  have hb' (j) : algebraMap K U (b' j)=b j := rfl
  have hda' (j) : algebraMap K U (da' j)=D (a j) := rfl
  have hdb' (j) : algebraMap K U (db' j)=D (b j) := rfl
  have ht' (j) : algebraMap K U (t' j)=t j := rfl
  obtain ⟨i,hi⟩ := exists_left_block x hx y
  apply Radicals.plane_differential_obstruction D (fun j => x (i,j)) hi
    a' b' da' db' t' ?_ (l i) (A i) ?_ ?_ ?_ ?_ ?_ (hD i)
  · intro j j' he
    apply hab
    have hh := congrArg (fun q : K × K => (algebraMap K U q.1,algebraMap K U q.2)) he
    simpa only [ha',hb'] using hh
  · intro j h
    exact htrans i j (h ▸ isAlgebraic_zero)
  · intro j
    rw [ha',hb']
    exact hdist i j
  · intro j
    rw [ha',hda']
  · intro j
    rw [hb',hdb']
  · intro j
    rw [ht']
    exact hlog i j
end PlanarUnitDistances.GridObstruction

namespace PlanarUnitDistances.GridObstruction
open Polynomial BivariateMaps CoefficientField
universe u
variable {k B U : Type u} [Field k] [CharZero k] [Field B] [CharZero B]
  [Field U] [IsAlgClosed U] [Algebra k U] [Algebra B U]

theorem curve_plane (f : B[X][X]) (hfU : Irreducible (bimap (algebraMap B U) f))
    (hfdeg : f.natDegree≠0)
    (z w : Fin 21 → U) (hz : AlgebraicIndependent B z)
    (hroot : ∀ i, f.eval₂ (aeval (z i)).toRingHom (w i)=0)
    (x : Fin 4 × Fin 2 → U) (hx : AlgebraicIndependent B x)
    (l : Fin 21 → Fin 4 → U) (htrans : ∀ i j, Transcendental k (l i j))
    (hrect : ∀ i j, ∃ c : k, l i j*l 0 0=l i 0*l 0 j*algebraMap k U c)
    (hdist : ∀ i j, (z i-x (j,0))*(w i-x (j,1))=2-l i j-(l i j)⁻¹) : False := by
  obtain ⟨D,A,t,hD,hlog⟩ := GridDerivation.exists_derivation_log l htrans hrect
  let a : Fin 4 → U := fun j => x (j,0)
  let b : Fin 4 → U := fun j => x (j,1)
  let y := parameters D a b t
  let K := FieldOf (B := B) y
  let : IsAlgClosed K := IsAlgClosure.isAlgClosed (IntermediateField.adjoin B (Set.range y))
  let : IsScalarTower B K U := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let a' : Fin 4 → K := fun j => entry y (j,0)
  let b' : Fin 4 → K := fun j => entry y (j,1)
  let da' : Fin 4 → K := fun j => entry y (j,2)
  let db' : Fin 4 → K := fun j => entry y (j,3)
  let t' : Fin 4 → K := fun j => entry y (j,4)
  have ha' (j) : algebraMap K U (a' j)=a j := rfl
  have hb' (j) : algebraMap K U (b' j)=b j := rfl
  have hda' (j) : algebraMap K U (da' j)=D (a j) := rfl
  have hdb' (j) : algebraMap K U (db' j)=D (b j) := rfl
  have ht' (j) : algebraMap K U (t' j)=t j := rfl
  let x' : Fin 4 × Fin 2 → K := fun ij => ![a' ij.1,b' ij.1] ij.2
  have hx'val (ij) : algebraMap K U (x' ij)=x ij := by
    rcases ij with ⟨j,q⟩
    fin_cases q <;> rfl
  have hx' : AlgebraicIndependent B x' :=
    AlgebraicIndependent.of_comp (IsScalarTower.toAlgHom B K U) (by
      change AlgebraicIndependent B (fun ij => algebraMap K U (x' ij))
      simpa only [hx'val] using hx)
  have hzz : AlgebraicIndependent B (fun iq : Fin 21 × Fin 1 => z iq.1) :=
    hz.comp Prod.fst (by intro ⟨i,q⟩ ⟨j,r⟩ h; exact Prod.ext h (Subsingleton.elim _ _))
  obtain ⟨i,hi⟩ := exists_left_block _ hzz y
  have hi' : Transcendental K (z i) := hi.transcendental 0
  have hfK : Irreducible (bimap (algebraMap B K) f) := by
    apply irreducible_of_bimap (algebraMap K U)
    rw [bimap_comp,← IsScalarTower.algebraMap_eq B K U]
    exact hfU
  have hr : (bimap (algebraMap B K) f).eval₂ (aeval (z i)).toRingHom (w i)=0 := by
    rw [eval_bimap]
    exact hroot i
  apply Radicals.curve_plane_differential_obstruction D f hfK hfdeg (z i) (w i) hi' hr
    x' hx' da' db' t' (l i) (A i) ?_ ?_ ?_ ?_ ?_ (hD i)
  · intro j h
    exact htrans i j (h ▸ isAlgebraic_zero)
  · intro j
    change (z i-algebraMap K U (a' j))*(w i-algebraMap K U (b' j))=_
    rw [ha',hb']
    exact hdist i j
  · intro j
    change D (algebraMap K U (a' j))=algebraMap K U (da' j)
    rw [ha',hda']
  · intro j
    change D (algebraMap K U (b' j))=algebraMap K U (db' j)
    rw [hb',hdb']
  · intro j
    rw [ht']
    exact hlog i j
end PlanarUnitDistances.GridObstruction

namespace PlanarUnitDistances.GridObstruction
open Polynomial BivariateMaps CoefficientField
universe u
variable {k B U : Type u} [Field k] [CharZero k] [Field B] [CharZero B]
  [Field U] [IsAlgClosed U] [Algebra k U] [Algebra B U]

theorem curve_curve (f g : B[X][X])
    (hfU : Irreducible (bimap (algebraMap B U) f)) (hfdeg : f.natDegree≠0)
    (hfsym : (Bivariate.swap f).natDegree=f.natDegree)
    (hgU : Irreducible (bimap (algebraMap B U) g))
    (hgdeg : g.natDegree≠0) (hgswap : (Bivariate.swap g).natDegree≠0)
    (z w : Fin 21 → U) (hz : AlgebraicIndependent B z)
    (hroot : ∀ i, f.eval₂ (aeval (z i)).toRingHom (w i)=0)
    (hunit : g ∣ f → ∀ u v : B, ∃ i, (z i-algebraMap B U u)*(w i-algebraMap B U v)≠1)
    (a b : Fin 4 → U) (ha : AlgebraicIndependent B a)
    (hb : ∀ j, g.eval₂ (aeval (a j)).toRingHom (b j)=0)
    (l : Fin 21 → Fin 4 → U) (htrans : ∀ i j, Transcendental k (l i j))
    (hrect : ∀ i j, ∃ c : k, l i j*l 0 0=l i 0*l 0 j*algebraMap k U c)
    (hdist : ∀ i j, (z i-a j)*(w i-b j)=2-l i j-(l i j)⁻¹) : False := by
  obtain ⟨D,A,t,hD,hlog⟩ := GridDerivation.exists_derivation_log l htrans hrect
  let y := parameters D a b t
  let K := FieldOf (B := B) y
  let : IsAlgClosed K := IsAlgClosure.isAlgClosed (IntermediateField.adjoin B (Set.range y))
  let : IsScalarTower B K U := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let a' : Fin 4 → K := fun j => entry y (j,0)
  let b' : Fin 4 → K := fun j => entry y (j,1)
  let da' : Fin 4 → K := fun j => entry y (j,2)
  let db' : Fin 4 → K := fun j => entry y (j,3)
  let t' : Fin 4 → K := fun j => entry y (j,4)
  have ha' (j) : algebraMap K U (a' j)=a j := rfl
  have hb' (j) : algebraMap K U (b' j)=b j := rfl
  have hda' (j) : algebraMap K U (da' j)=D (a j) := rfl
  have hdb' (j) : algebraMap K U (db' j)=D (b j) := rfl
  have ht' (j) : algebraMap K U (t' j)=t j := rfl
  have hai : AlgebraicIndependent B a' :=
    AlgebraicIndependent.of_comp (IsScalarTower.toAlgHom B K U) (by
      change AlgebraicIndependent B (fun j => algebraMap K U (a' j))
      simpa only [ha'] using ha)
  have hbb (j) : g.eval₂ (aeval (a' j)).toRingHom (b' j)=0 := by
    apply (algebraMap K U).injective
    rw [eval_transport,ha',hb',map_zero]
    exact hb j
  have hzz : AlgebraicIndependent B (fun iq : Fin 21 × Fin 1 => z iq.1) :=
    hz.comp Prod.fst (by intro ⟨i,q⟩ ⟨j,r⟩ h; exact Prod.ext h (Subsingleton.elim _ _))
  obtain ⟨i,hi⟩ := exists_left_block _ hzz y
  have hi' : Transcendental K (z i) := hi.transcendental 0
  have hfK : Irreducible (bimap (algebraMap B K) f) := by
    apply irreducible_of_bimap (algebraMap K U)
    rw [bimap_comp,← IsScalarTower.algebraMap_eq B K U]
    exact hfU
  have hgK : Irreducible (bimap (algebraMap B K) g) := by
    apply irreducible_of_bimap (algebraMap K U)
    rw [bimap_comp,← IsScalarTower.algebraMap_eq B K U]
    exact hgU
  apply Radicals.curve_locus_differential_obstruction D f g hfK hfdeg hfsym hgK
    hgdeg hgswap ?_ (z i) (w i) hi' (hroot i) a' b' da' db' t' hai hbb
    (l i) (A i) ?_ ?_ ?_ ?_ ?_ (hD i)
  · intro hgf u v
    obtain ⟨j,hj⟩ := hunit hgf u v
    exact ⟨z j,w j,hroot j,hj⟩
  · intro j h
    exact htrans i j (h ▸ isAlgebraic_zero)
  · intro j
    rw [ha',hb']
    exact hdist i j
  · intro j
    rw [ha',hda']
  · intro j
    rw [hb',hdb']
  · intro j
    rw [ht']
    exact hlog i j
end PlanarUnitDistances.GridObstruction

namespace UnitDistances.UltraField
open Filter

variable {ι : Type*} (U : Ultrafilter ι) (K : ι → Type*) [∀ i, Field (K i)]

def zeroIdeal : Ideal (∀ i, K i) where
  carrier := {f | ∀ᶠ i in U, f i = 0}
  zero_mem' := Eventually.of_forall fun _ => rfl
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf, hg] with i hi hj
    simp [hi, hj]
  smul_mem' := by
    intro f g hg
    filter_upwards [hg] with i hi
    simp [hi]

@[simp] theorem mem_zeroIdeal (f : ∀ i, K i) :
    f ∈ zeroIdeal U K ↔ ∀ᶠ i in U, f i = 0 := Iff.rfl

instance zeroIdeal_maximal : (zeroIdeal U K).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · simpa using U.neBot.ne
  intro I f hle hf hfI
  have hn : ∀ᶠ i in U, f i ≠ 0 := Ultrafilter.eventually_not.mpr hf
  have hdiff : (1 - (fun i => (f i)⁻¹) * f) ∈ zeroIdeal U K := by
    filter_upwards [hn] with i hi
    simp [hi]
  have hinv : (fun i => (f i)⁻¹) * f ∈ I := I.mul_mem_left _ hfI
  simpa using I.add_mem (hle hdiff) hinv

abbrev FieldProduct := (∀ i, K i) ⧸ zeroIdeal U K

noncomputable instance : Field (FieldProduct U K) := Ideal.Quotient.field (zeroIdeal U K)

abbrev mk : (∀ i, K i) →+* FieldProduct U K := Ideal.Quotient.mk (zeroIdeal U K)

@[simp] theorem mk_eq_mk (f g : ∀ i, K i) : mk U K f = mk U K g ↔ ∀ᶠ i in U, f i = g i := by
  rw [Ideal.Quotient.eq]
  simp only [mem_zeroIdeal, Pi.sub_apply, sub_eq_zero]

@[simp] theorem mk_eq_zero (f : ∀ i, K i) : mk U K f = 0 ↔ ∀ᶠ i in U, f i = 0 := by
  rw [← (mk U K).map_zero, mk_eq_mk]
  rfl

instance [∀ i, CharZero (K i)] : CharZero (FieldProduct U K) := by
  constructor
  intro m n h
  have hh : mk U K (m : ∀ i, K i) = mk U K n := by simpa using h
  have he := (mk_eq_mk U K _ _).mp hh
  obtain ⟨i, hi⟩ := he.exists
  exact Nat.cast_injective hi

@[simp] theorem mk_inv (f : ∀ i, K i) : mk U K (fun i => (f i)⁻¹) = (mk U K f)⁻¹ := by
  by_cases h : mk U K f = 0
  · rw [h, inv_zero]
    apply (mk_eq_zero U K _).mpr
    filter_upwards [(mk_eq_zero U K _).mp h] with i hi
    simp [hi]
  · apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    change mk U K ((fun i => (f i)⁻¹) * f) = mk U K 1
    apply (mk_eq_mk U K _ _).mpr
    have hn := Ultrafilter.eventually_not.mpr (by simpa using h : ¬ ∀ᶠ i in U, f i = 0)
    filter_upwards [hn] with i hi
    simp [hi]

noncomputable instance [∀ i, IsAlgClosed (K i)] : IsAlgClosed (FieldProduct U K) := by
  classical
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  obtain ⟨q, hq⟩ := Polynomial.map_surjective (mk U K)
    Ideal.Quotient.mk_surjective p
  have hn : 0 < p.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hirr)
  have hc : mk U K (q.coeff p.natDegree) ≠ 0 := by
    rw [← Polynomial.coeff_map, hq, Polynomial.coeff_natDegree, hp.leadingCoeff]
    exact one_ne_zero
  have hev : ∀ᶠ i in U, q.coeff p.natDegree i ≠ 0 :=
    Ultrafilter.eventually_not.mpr ((mk_eq_zero U K _).not.mp hc)
  have hroot : ∀ᶠ i in U, ∃ x : K i,
      (q.map (Pi.evalRingHom K i)).IsRoot x := by
    filter_upwards [hev] with i hi
    apply IsAlgClosed.exists_root
    have hb : (p.natDegree : WithBot ℕ) ≤ (q.map (Pi.evalRingHom K i)).degree := by
      apply Polynomial.le_degree_of_ne_zero
      simpa using hi
    have hz : (0 : WithBot ℕ) < p.natDegree := by exact_mod_cast hn
    exact ne_of_gt (lt_of_lt_of_le hz hb)
  let r : ∀ i, K i := fun i => if h : ∃ x : K i,
      (q.map (Pi.evalRingHom K i)).IsRoot x then Classical.choose h else 0
  refine ⟨mk U K r, ?_⟩
  rw [← hq, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  apply (mk_eq_zero U K _).mpr
  filter_upwards [hroot] with i hi
  have hr : (q.map (Pi.evalRingHom K i)).eval (r i) = 0 := by
    dsimp only [r]
    rw [dite_eq_left hi]
    exact Classical.choose_spec hi
  rw [Polynomial.eval_map] at hr
  change (Pi.evalRingHom K i) (q.eval r) = 0
  rw [← Polynomial.eval₂_at_apply]
  exact hr

end UnitDistances.UltraField

namespace PlanarUnitDistances.UltraPolynomial
open Polynomial Filter
open UnitDistances.UltraField

noncomputable abbrev bimapping {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    R[X][X] →+* S[X][X] := Polynomial.mapRingHom (Polynomial.mapRingHom φ)

lemma polynomial_map_zero_iff {R S ι : Type*} {K : ι → Type*}
    [CommRing R] [CommRing S] [∀ i, CommRing (K i)]
    (F : Filter ι) (φ : R →+* S) (ψ : ∀ i,R →+* K i)
    (h : ∀ r, φ r=0 ↔ ∀ᶠ i in F, ψ i r=0) (p : R[X]) :
    p.map φ=0 ↔ ∀ᶠ i in F,p.map (ψ i)=0 := by
  classical
  constructor
  · intro hz
    have hc (j : ℕ) : ∀ᶠ i in F,ψ i (p.coeff j)=0 := by
      apply (h _).mp
      simpa only [coeff_map,coeff_zero] using congrArg (fun p : S[X] => p.coeff j) hz
    filter_upwards [(eventually_all_finset p.support).mpr (fun j _ => hc j)] with i hi
    ext j
    rw [coeff_map,coeff_zero]
    by_cases hj : j ∈ p.support
    · exact hi j hj
    · rw [notMem_support_iff.mp hj,map_zero]
  · intro hz
    ext j
    rw [coeff_map,coeff_zero,h]
    filter_upwards [hz] with i hi
    simpa only [coeff_map,coeff_zero] using congrArg (fun p : (K i)[X] => p.coeff j) hi

variable {ι : Type*} (U : Ultrafilter ι) (K : ι → Type*) [∀ i,Field (K i)]

lemma bimap_zero_iff (p : (∀ i,K i)[X][X]) :
    bimapping (mk U K) p=0 ↔ ∀ᶠ i in U,bimapping (Pi.evalRingHom K i) p=0 := by
  apply polynomial_map_zero_iff (U : Filter ι) (Polynomial.mapRingHom (mk U K))
    (fun i => Polynomial.mapRingHom (Pi.evalRingHom K i))
  intro q
  exact polynomial_map_zero_iff (U : Filter ι) (mk U K) (Pi.evalRingHom K)
    (fun r => by simpa only [Pi.evalRingHom_apply] using mk_eq_zero U K r) q

lemma bimap_eq_iff (p q : (∀ i,K i)[X][X]) :
    bimapping (mk U K) p=bimapping (mk U K) q ↔
      ∀ᶠ i in U,bimapping (Pi.evalRingHom K i) p=bimapping (Pi.evalRingHom K i) q := by
  simpa only [map_sub,sub_eq_zero] using bimap_zero_iff U K (p-q)

lemma bivariate_isUnit_iff {F : Type*} [Field F] (p : F[X][X]) :
    IsUnit p ↔ p=C (C ((p.coeff 0).coeff 0)) ∧ (p.coeff 0).coeff 0 ≠ 0 := by
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Polynomial.isUnit_iff.mp hp
    obtain ⟨c,hc,rfl⟩ := Polynomial.isUnit_iff.mp hq
    simp only [coeff_C_zero, true_and]
    exact hc.ne_zero
  · rintro ⟨he,hn⟩
    rw [he]
    exact isUnit_C.mpr (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hn))

lemma bimap_unit_iff (p : (∀ i,K i)[X][X]) :
    IsUnit (bimapping (mk U K) p) ↔ ∀ᶠ i in U,IsUnit (bimapping (Pi.evalRingHom K i) p) := by
  simp_rw [bivariate_isUnit_iff]
  have he := bimap_eq_iff U K p (C (C ((p.coeff 0).coeff 0)))
  have hn : mk U K ((p.coeff 0).coeff 0) ≠ 0 ↔
      ∀ᶠ i in U, (p.coeff 0).coeff 0 i ≠ 0 := by
    rw [ne_eq,mk_eq_zero,Ultrafilter.eventually_not]
  simpa only [bimapping,coe_mapRingHom,map_C,coeff_map,Pi.evalRingHom_apply,
    ← eventually_and] using he.and hn

lemma bimap_surjective : Function.Surjective (bimapping (mk U K)) :=
  Polynomial.map_surjective _ (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective)

theorem irreducible_of_eventually (p : (∀ i,K i)[X][X])
    (hp : ∀ᶠ i in U,Irreducible (bimapping (Pi.evalRingHom K i) p)) :
    Irreducible (bimapping (mk U K) p) := by
  refine ⟨?_,?_⟩
  · intro hu
    have hev := (bimap_unit_iff U K p).mp hu
    obtain ⟨i,hi,hi'⟩ := (hp.and hev).exists
    exact hi.not_isUnit hi'
  · intro g h hmul
    obtain ⟨g',rfl⟩ := bimap_surjective U K g
    obtain ⟨h',rfl⟩ := bimap_surjective U K h
    have he := (bimap_eq_iff U K p (g'*h')).mp (by simpa only [map_mul] using hmul)
    have hu : ∀ᶠ i in U, IsUnit (bimapping (Pi.evalRingHom K i) g') ∨
        IsUnit (bimapping (Pi.evalRingHom K i) h') := by
      filter_upwards [hp,he] with i hi he
      exact hi.isUnit_or_isUnit (by simpa only [map_mul] using he)
    rcases Ultrafilter.eventually_or.mp hu with hg|hh
    · exact Or.inl ((bimap_unit_iff U K g').mpr hg)
    · exact Or.inr ((bimap_unit_iff U K h').mpr hh)

noncomputable def pack (f : ∀ i,(K i)[X][X]) (D : ℕ) : (∀ i,K i)[X][X] :=
  ∑ m ∈ Finset.range (D+1),monomial m
    (∑ n ∈ Finset.range (D+1),monomial n (fun i => ((f i).coeff m).coeff n))

lemma pack_eval (f : ∀ i,(K i)[X][X]) (D : ℕ) (i : ι)
    (hf : (f i).natDegree ≤ D) (hc : ∀ m,((f i).coeff m).natDegree ≤ D) :
    bimapping (Pi.evalRingHom K i) (pack K f D)=f i := by
  simp only [pack,bimapping,coe_mapRingHom,map_sum,map_monomial]
  rw [as_sum_range' (f i) (D+1) (by omega)]
  apply Finset.sum_congr rfl
  intro m _
  simp only [Pi.evalRingHom_apply, ← map_sum]
  congr 1
  exact (as_sum_range' ((f i).coeff m) (D+1) (by have := hc m; omega)).symm

end PlanarUnitDistances.UltraPolynomial

namespace PlanarUnitDistances.UltraPolynomial
open Polynomial Filter
open UnitDistances.UltraField
variable {ι R S : Type*} {K : ι → Type*} [CommRing R] [CommRing S]
  [∀ i, CommRing (K i)]

lemma eventually_natDegree_map (U : Ultrafilter ι) (φ : R →+* S)
    (ψ : ∀ i, R →+* K i)
    (h : ∀ r, φ r=0 ↔ ∀ᶠ i in U, ψ i r=0) (p : R[X]) :
    ∀ᶠ i in U, (p.map (ψ i)).natDegree=(p.map φ).natDegree := by
  have hc (m : ℕ) : ∀ᶠ i in U, ψ i (p.coeff m)=0 ↔ φ (p.coeff m)=0 := by
    by_cases hz : φ (p.coeff m)=0
    · filter_upwards [(h _).mp hz] with i hi
      exact iff_of_true hi hz
    · have hn := Ultrafilter.eventually_not.mpr ((h _).not.mp hz)
      filter_upwards [hn] with i hi
      exact iff_of_false hi hz
  filter_upwards [(eventually_all_finset (Finset.range (p.natDegree+1))).mpr
    (fun m _ => hc m)] with i hi
  have hh (m : ℕ) : (p.map (ψ i)).coeff m=0 ↔ (p.map φ).coeff m=0 := by
    simp only [coeff_map]
    by_cases hm : m≤p.natDegree
    · exact hi m (Finset.mem_range.mpr (by omega))
    · simp only [coeff_eq_zero_of_natDegree_lt (not_le.mp hm),map_zero]
  apply Nat.le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    exact (hh m).mpr (coeff_eq_zero_of_natDegree_lt hm)
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    exact (hh m).mp (coeff_eq_zero_of_natDegree_lt hm)

variable (U : Ultrafilter ι) (F : ι → Type*) [∀ i, Field (F i)]
lemma eventually_outer_degree (p : (∀ i,F i)[X][X]) :
    ∀ᶠ i in U, (bimapping (Pi.evalRingHom F i) p).natDegree=
      (bimapping (mk U F) p).natDegree := by
  apply eventually_natDegree_map U (Polynomial.mapRingHom (mk U F))
    (fun i => Polynomial.mapRingHom (Pi.evalRingHom F i))
  intro p
  exact polynomial_map_zero_iff (U : Filter ι) (mk U F) (Pi.evalRingHom F)
    (fun r => mk_eq_zero U F r) p

end PlanarUnitDistances.UltraPolynomial

namespace PlanarUnitDistances.CountableCoefficients
open Polynomial
variable {U : Type*} [Field U]

noncomputable def field (f g : U[X][X]) : Subfield U :=
  Subfield.closure (Set.range (fun mn : ℕ × ℕ => (f.coeff mn.1).coeff mn.2) ∪
    Set.range (fun mn : ℕ × ℕ => (g.coeff mn.1).coeff mn.2))

instance (f g : U[X][X]) : Countable (field f g) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  apply (Subfield.cardinalMk_closure_le_max _).trans
  apply max_le _ le_rfl
  exact Cardinal.le_aleph0_iff_set_countable.mpr
    ((Set.countable_range _).union (Set.countable_range _))

lemma coeff_mem_left (f g : U[X][X]) (m n : ℕ) :
    (f.coeff m).coeff n ∈ field f g :=
  Subfield.subset_closure (Or.inl ⟨(m,n),rfl⟩)

lemma coeff_mem_right (f g : U[X][X]) (m n : ℕ) :
    (g.coeff m).coeff n ∈ field f g :=
  Subfield.subset_closure (Or.inr ⟨(m,n),rfl⟩)

noncomputable def descend (B : Subfield U) (f : U[X][X])
    (h : ∀ m n, (f.coeff m).coeff n ∈ B) : B[X][X] :=
  ∑ m ∈ f.support, monomial m
    (∑ n ∈ (f.coeff m).support, monomial n ⟨(f.coeff m).coeff n,h m n⟩)

lemma descend_map (B : Subfield U) (f : U[X][X])
    (h : ∀ m n, (f.coeff m).coeff n ∈ B) :
    (descend B f h).map (Polynomial.mapRingHom B.subtype)=f := by
  classical
  simp only [descend,Polynomial.map_sum,Polynomial.map_monomial,coe_mapRingHom,Subfield.subtype_apply]
  change (∑ m ∈ f.support, monomial m ((f.coeff m).sum fun n c => monomial n c))=f
  simp only [sum_monomial_eq]
  exact f.sum_monomial_eq

end PlanarUnitDistances.CountableCoefficients

end OAI
