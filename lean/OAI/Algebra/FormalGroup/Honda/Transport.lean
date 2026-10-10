import OAI.Algebra.FormalGroup.Honda.SmallExtension

namespace OAI

noncomputable section

namespace HeightThree.CoordinateTransport
open MvPowerSeries HondaTarget DeformationRigidity OriginalDifferentialSupport
variable {R S : Type*} [CommRing R] [CommRing S]

lemma constantCoeff_pderiv {σ : Type*} (f : MvPowerSeries σ R) (i : σ) :
    constantCoeff (pderiv i f) = coeff (Finsupp.single i 1) f := by
  rw [←coeff_zero_eq_constantCoeff,coeff_pderiv]; simp

lemma linear_subst {σ τ : Type*} [Fintype σ] (f : MvPowerSeries σ R)
    (a : σ → MvPowerSeries τ R) (ha : ∀ i, (a i).constantCoeff = 0) (j : τ) :
    coeff (Finsupp.single j 1) (f.subst a) =
      ∑ i, coeff (Finsupp.single i 1) f * coeff (Finsupp.single j 1) (a i) := by
  rw [←constantCoeff_pderiv, pderiv_subst a (hasSubst_of_constantCoeff_zero ha)]
  simp only [map_sum,map_mul,constantCoeff_subst_zero_axis _ (hasSubst_of_constantCoeff_zero ha) ha,
    constantCoeff_pderiv]

lemma unilinear_subst {σ : Type*} (f : PowerSeries R) (a : MvPowerSeries σ R)
    (ha : a.constantCoeff = 0) (i : σ) :
    coeff (Finsupp.single i 1) (f.subst a) = f.coeff 1*coeff (Finsupp.single i 1) a := by
  simpa [PowerSeries.subst,PowerSeries.coeff] using linear_subst f (fun _ : Unit => a) (fun _ => ha) i

structure Coordinate (R : Type*) [CommRing R] where
  series : PowerSeries R
  inverse : PowerSeries R
  zero_series : series.constantCoeff = 0
  zero_inverse : inverse.constantCoeff = 0
  left_inv : series.subst inverse = PowerSeries.X
  right_inv : inverse.subst series = PowerSeries.X

namespace Coordinate
variable (c : Coordinate R)
def ofSeries (u : PowerSeries R) (hu : u.constantCoeff=0) (hunit : IsUnit (u.coeff 1)) : Coordinate R where
  series := u
  inverse := u.substInvOfIsUnit hunit
  zero_series := hu
  zero_inverse := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  left_inv := PowerSeries.subst_substInvOfIsUnit_right _ hu hunit
  right_inv := PowerSeries.subst_substInvOfIsUnit_left _ hu hunit

def symm : Coordinate R := ⟨c.inverse,c.series,c.zero_inverse,c.zero_series,c.right_inv,c.left_inv⟩

lemma hasSubst : PowerSeries.HasSubst c.series := .of_constantCoeff_zero c.zero_series
lemma inv_hasSubst : PowerSeries.HasSubst c.inverse := .of_constantCoeff_zero c.zero_inverse
lemma series_const {σ} (a : MvPowerSeries σ R) (ha : a.constantCoeff=0) :
    (c.series.subst a).constantCoeff=0 := PowerSeries.constantCoeff_subst_eq_zero ha _ c.zero_series
lemma inverse_const {σ} (a : MvPowerSeries σ R) (ha : a.constantCoeff=0) :
    (c.inverse.subst a).constantCoeff=0 := PowerSeries.constantCoeff_subst_eq_zero ha _ c.zero_inverse

lemma series_inverse {σ} (a : MvPowerSeries σ R) (ha : PowerSeries.HasSubst a) :
    c.series.subst (c.inverse.subst a)=a := by
  rw [←PowerSeries.subst_comp_subst_apply c.inv_hasSubst ha,c.left_inv,PowerSeries.subst_X ha]
lemma inverse_series {σ} (a : MvPowerSeries σ R) (ha : PowerSeries.HasSubst a) :
    c.inverse.subst (c.series.subst a)=a := by
  rw [←PowerSeries.subst_comp_subst_apply c.hasSubst ha,c.right_inv,PowerSeries.subst_X ha]
lemma inverse_injective {σ} (a b : MvPowerSeries σ R)
    (ha : PowerSeries.HasSubst a) (hb : PowerSeries.HasSubst b)
    (he : c.inverse.subst a=c.inverse.subst b) : a=b := by
  have hh := congrArg (fun z => c.series.subst z) he
  simpa only [c.series_inverse _ ha,c.series_inverse _ hb] using hh

lemma linear_inverse : c.series.coeff 1*c.inverse.coeff 1=1 := by
  have hh := congrArg (PowerSeries.coeff 1) c.left_inv
  rw [show PowerSeries.coeff 1 (c.series.subst c.inverse) = c.series.coeff 1*c.inverse.coeff 1 from
    unilinear_subst _ _ c.zero_inverse (), PowerSeries.coeff_one_X] at hh
  exact hh

def law (F : FormalGroup R) : MvPowerSeries (Fin 2) R :=
  c.series.subst (F.toPowerSeries.subst ![c.inverse.subst (X 0), c.inverse.subst (X 1)])

lemma formal_pair_const (F : FormalGroup R) {σ} (a b : MvPowerSeries σ R)
    (ha : a.constantCoeff=0) (hb : b.constantCoeff=0) :
    (F.toPowerSeries.subst ![a,b]).constantCoeff=0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> assumption))
    (by intro i; fin_cases i <;> assumption) F.zero_constantCoeff

lemma law_const (F : FormalGroup R) : (c.law F).constantCoeff=0 :=
  c.series_const _ (formal_pair_const F _ _ (c.inverse_const _ (by simp)) (c.inverse_const _ (by simp)))

lemma law_pair (F : FormalGroup R) {σ} (a b : MvPowerSeries σ R)
    (ha : a.constantCoeff=0) (hb : b.constantCoeff=0) :
    (c.law F).subst ![a,b] =
      c.series.subst (F.toPowerSeries.subst ![c.inverse.subst a,c.inverse.subst b]) := by
  have hab : HasSubst ![a,b] := hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> assumption)
  have hi (i : Fin 2) : (c.inverse.subst (X i : MvPowerSeries (Fin 2) R)).constantCoeff=0 := c.inverse_const _ (by simp)
  have his : HasSubst ![c.inverse.subst (X 0 : MvPowerSeries (Fin 2) R),c.inverse.subst (X 1)] :=
    hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> exact hi _)
  rw [law,subst_after_mv _ _ (.of_constantCoeff_zero (formal_pair_const F _ _ (hi _) (hi _))) _ hab,
    MvPowerSeries.subst_comp_subst_apply his hab]
  congr 2
  funext i; fin_cases i
  · change (c.inverse.subst (X 0 : MvPowerSeries (Fin 2) R)).subst ![a,b] = c.inverse.subst a
    rw [subst_after_mv _ _ (PowerSeries.HasSubst.X _) _ hab,subst_X hab]; rfl
  · change (c.inverse.subst (X 1 : MvPowerSeries (Fin 2) R)).subst ![a,b] = c.inverse.subst b
    rw [subst_after_mv _ _ (PowerSeries.HasSubst.X _) _ hab,subst_X hab]; rfl
  
lemma law_pair_const (F : FormalGroup R) {σ} (a b : MvPowerSeries σ R)
    (ha : a.constantCoeff=0) (hb : b.constantCoeff=0) :
    ((c.law F).subst ![a,b]).constantCoeff=0 := by
  rw [c.law_pair F a b ha hb]
  exact c.series_const _ (formal_pair_const F _ _ (c.inverse_const _ ha) (c.inverse_const _ hb))

lemma inverse_law_pair (F : FormalGroup R) {σ} (a b : MvPowerSeries σ R)
    (ha : a.constantCoeff=0) (hb : b.constantCoeff=0) :
    c.inverse.subst ((c.law F).subst ![a,b]) =
      F.toPowerSeries.subst ![c.inverse.subst a,c.inverse.subst b] := by
  rw [c.law_pair F a b ha hb]
  exact c.inverse_series _ (.of_constantCoeff_zero
    (formal_pair_const F _ _ (c.inverse_const _ ha) (c.inverse_const _ hb)))

lemma law_linear (F : FormalGroup R) (i : Fin 2) :
    coeff (Finsupp.single i 1) (c.law F)=1 := by
  rw [law,unilinear_subst _ _ (formal_pair_const F _ _ (c.inverse_const _ (by simp)) (c.inverse_const _ (by simp)))]
  rw [linear_subst _ _ (by intro j; fin_cases j <;> exact c.inverse_const _ (by simp))]
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,F.lin_coeff_X,F.lin_coeff_Y,one_mul]
  change c.series.coeff 1*(coeff (Finsupp.single i 1) (c.inverse.subst (X 0)) +
    coeff (Finsupp.single i 1) (c.inverse.subst (X 1)))=1
  rw [unilinear_subst _ _ (constantCoeff_X 0),unilinear_subst _ _ (constantCoeff_X 1)]
  fin_cases i <;> simpa [coeff_index_single_X] using c.linear_inverse

def transport (F : FormalGroup R) : FormalGroup R where
  toPowerSeries := c.law F
  zero_constantCoeff := c.law_const F
  lin_coeff_X := c.law_linear F 0
  lin_coeff_Y := c.law_linear F 1
  assoc := by
    have hx (i : Fin 3) : (X i : MvPowerSeries (Fin 3) R).constantCoeff=0 := by simp
    apply c.inverse_injective _ _
      (.of_constantCoeff_zero (c.law_pair_const F _ _ (c.law_pair_const F _ _ (hx 0) (hx 1)) (hx 2)))
      (.of_constantCoeff_zero (c.law_pair_const F _ _ (hx 0) (c.law_pair_const F _ _ (hx 1) (hx 2))))
    rw [c.inverse_law_pair F _ _ (c.law_pair_const F _ _ (hx 0) (hx 1)) (hx 2),
      c.inverse_law_pair F _ _ (hx 0) (c.law_pair_const F _ _ (hx 1) (hx 2)),
      c.inverse_law_pair F _ _ (hx 0) (hx 1),c.inverse_law_pair F _ _ (hx 1) (hx 2)]
    exact F.assoc' (.of_constantCoeff_zero (c.inverse_const _ (hx 0)))
      (.of_constantCoeff_zero (c.inverse_const _ (hx 1))) (.of_constantCoeff_zero (c.inverse_const _ (hx 2)))

instance transport_isComm (F : FormalGroup R) [F.IsComm] : (c.transport F).IsComm where
  comm := by
    change c.law F = (c.law F).subst ![X 1,X 0]
    rw [c.law_pair F _ _ (by simp) (by simp)]
    exact congrArg (fun z => c.series.subst z) (F.comm'
      (.of_constantCoeff_zero (c.inverse_const _ (by simp))) (.of_constantCoeff_zero (c.inverse_const _ (by simp))))

def iso (F : FormalGroup R) : CoordinateIso F (c.transport F) where
  series := c.series
  inverse := c.inverse
  zero_series := c.zero_series
  zero_inverse := c.zero_inverse
  left_inv := c.left_inv
  right_inv := c.right_inv
  preserves_addition := by
    change c.series.subst F.toPowerSeries = (c.law F).subst ![c.series.subst (X 0),c.series.subst (X 1)]
    rw [c.law_pair F _ _ (c.series_const _ (by simp)) (c.series_const _ (by simp)),
      c.inverse_series _ (PowerSeries.HasSubst.X _),c.inverse_series _ (PowerSeries.HasSubst.X _)]
    have hX : ![X 0,X 1] = (X : Fin 2 → MvPowerSeries (Fin 2) R) := by
      funext i; fin_cases i <;> rfl
    rw [hX,MvPowerSeries.subst_self]
    rfl

def map (π : R →+* S) : Coordinate S where
  series := c.series.map π
  inverse := c.inverse.map π
  zero_series := by
    change π (PowerSeries.constantCoeff c.series)=0
    rw [c.zero_series,map_zero]
  zero_inverse := by
    change π (PowerSeries.constantCoeff c.inverse)=0
    rw [c.zero_inverse,map_zero]
  left_inv := by
    change (c.series.map π).subst (MvPowerSeries.map π c.inverse)=PowerSeries.X
    rw [←PowerSeries.map_subst c.inv_hasSubst,c.left_inv]
    exact PowerSeries.map_X π
  right_inv := by
    change (c.inverse.map π).subst (MvPowerSeries.map π c.series)=PowerSeries.X
    rw [←PowerSeries.map_subst c.hasSubst,c.right_inv]
    exact PowerSeries.map_X π

lemma transport_map (F : FormalGroup R) (π : R →+* S) :
    (c.transport F).map π = (c.map π).transport (F.map π) := by
  apply FormalGroup.ext
  change MvPowerSeries.map π (c.law F) = (c.map π).law (F.map π)
  have hi (i : Fin 2) : (c.inverse.subst (X i : MvPowerSeries (Fin 2) R)).constantCoeff=0 := c.inverse_const _ (by simp)
  rw [law,PowerSeries.map_subst (.of_constantCoeff_zero (formal_pair_const F _ _ (hi _) (hi _))),
    MvPowerSeries.map_subst (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> exact hi _))]
  change (c.series.map π).subst _ = (c.series.map π).subst ((F.map π).toPowerSeries.subst _)
  congr 2
  funext i; fin_cases i
  · change (c.inverse.subst (X 0 : MvPowerSeries (Fin 2) R)).map π = (c.inverse.map π).subst (X 0)
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.X _),MvPowerSeries.map_X]
  · change (c.inverse.subst (X 1 : MvPowerSeries (Fin 2) R)).map π = (c.inverse.map π).subst (X 1)
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.X _),MvPowerSeries.map_X]

def ofIso {F G : FormalGroup R} (e : CoordinateIso F G) : Coordinate R :=
  ⟨e.series,e.inverse,e.zero_series,e.zero_inverse,e.left_inv,e.right_inv⟩

lemma transport_ofIso {F G : FormalGroup R} (e : CoordinateIso F G) :
    (ofIso e).transport F=G := by
  apply FormalGroup.ext
  change e.series.subst (F.toPowerSeries.subst ![e.inverse.subst (X 0),e.inverse.subst (X 1)])=G.toPowerSeries
  rw [coordinate_add F G e (e.inverse.subst (X 0 : MvPowerSeries (Fin 2) R))
    (e.inverse.subst (X 1)) ((ofIso e).inverse_const _ (by simp)) ((ofIso e).inverse_const _ (by simp))]
  change G.toPowerSeries.subst ![(ofIso e).series.subst ((ofIso e).inverse.subst (X 0)),
    (ofIso e).series.subst ((ofIso e).inverse.subst (X 1))]=G.toPowerSeries
  rw [(ofIso e).series_inverse _ (PowerSeries.HasSubst.X _),
    (ofIso e).series_inverse _ (PowerSeries.HasSubst.X _)]
  have hX : ![X 0,X 1] = (X : Fin 2 → MvPowerSeries (Fin 2) R) := by
    funext i; fin_cases i <;> rfl
  rw [hX,MvPowerSeries.subst_self]; rfl

lemma map_eq_of_series_eq (π : R →+* S) (d : Coordinate S)
    (he : c.series.map π=d.series) : c.map π=d := by
  have hi : c.inverse.map π=d.inverse := by
    have hh := congrArg (fun z => d.inverse.subst z) (c.map π).left_inv
    rw [show (c.map π).series=d.series from he,d.inverse_series _ (c.map π).inv_hasSubst,
      PowerSeries.X_subst] at hh
    exact hh
  cases c; cases d
  cases he; cases hi
  rfl

def ident : Coordinate R :=
  ⟨PowerSeries.X,PowerSeries.X,by simp,by simp,PowerSeries.X_subst _,PowerSeries.X_subst _⟩

lemma transport_ident (F : FormalGroup R) : (ident (R := R)).transport F=F := by
  apply FormalGroup.ext
  change PowerSeries.X.subst (F.toPowerSeries.subst ![PowerSeries.X.subst (X 0),PowerSeries.X.subst (X 1)])=F.toPowerSeries
  rw [PowerSeries.subst_X (PowerSeries.HasSubst.X _),PowerSeries.subst_X (PowerSeries.HasSubst.X _)]
  have hX : ![X 0,X 1] = (X : Fin 2 → MvPowerSeries (Fin 2) R) := by
    funext i; fin_cases i <;> rfl
  rw [hX,MvPowerSeries.subst_self]
  exact PowerSeries.subst_X (.of_constantCoeff_zero F.zero_constantCoeff)

lemma transport_map_eq_self (F : FormalGroup R) (π : R →+* S)
    (he : c.series.map π=PowerSeries.X) : (c.transport F).map π=F.map π := by
  rw [c.transport_map, c.map_eq_of_series_eq π ident he, transport_ident]

def comp (d : Coordinate R) : Coordinate R where
  series := d.series.subst c.series
  inverse := c.inverse.subst d.inverse
  zero_series := d.series_const _ c.zero_series
  zero_inverse := c.inverse_const _ d.zero_inverse
  left_inv := by
    rw [PowerSeries.subst_comp_subst_apply c.hasSubst
      (.of_constantCoeff_zero (c.inverse_const _ d.zero_inverse)),
      c.series_inverse _ d.inv_hasSubst,d.left_inv]
  right_inv := by
    rw [PowerSeries.subst_comp_subst_apply d.inv_hasSubst
      (.of_constantCoeff_zero (d.series_const _ c.zero_series)),
      d.inverse_series _ c.hasSubst,c.right_inv]

end Coordinate

namespace CoordinateIso
open Coordinate

def refl (F : FormalGroup R) : CoordinateIso F F := by
  have e := (Coordinate.ident (R := R)).iso F
  rw [Coordinate.transport_ident] at e
  exact e

def symm {F G : FormalGroup R} (e : CoordinateIso F G) : CoordinateIso G F where
  __ := (Coordinate.ofIso e).symm
  preserves_addition := by
    have hh := coordinate_add F G e (e.inverse.subst (X 0 : MvPowerSeries (Fin 2) R)) (e.inverse.subst (X 1))
      ((Coordinate.ofIso e).inverse_const _ (by simp)) ((Coordinate.ofIso e).inverse_const _ (by simp))
    have hX : ![X 0,X 1] = (X : Fin 2 → MvPowerSeries (Fin 2) R) := by
      funext i; fin_cases i <;> rfl
    have hi0 := (Coordinate.ofIso e).series_inverse (X 0 : MvPowerSeries (Fin 2) R) (PowerSeries.HasSubst.X _)
    have hi1 := (Coordinate.ofIso e).series_inverse (X 1 : MvPowerSeries (Fin 2) R) (PowerSeries.HasSubst.X _)
    change e.series.subst (e.inverse.subst (X 0))=X 0 at hi0
    change e.series.subst (e.inverse.subst (X 1))=X 1 at hi1
    rw [hi0,hi1,hX,MvPowerSeries.subst_self] at hh
    have hh' := congrArg (fun z : MvPowerSeries (Fin 2) R => e.inverse.subst z) hh
    have hc : (F.toPowerSeries.subst ![e.inverse.subst (X 0 : MvPowerSeries (Fin 2) R),
        e.inverse.subst (X 1)]).constantCoeff=0 :=
      Coordinate.formal_pair_const F _ _ ((Coordinate.ofIso e).inverse_const _ (by simp))
        ((Coordinate.ofIso e).inverse_const _ (by simp))
    have hi := (Coordinate.ofIso e).inverse_series _ (PowerSeries.HasSubst.of_constantCoeff_zero hc)
    change e.inverse.subst (e.series.subst _) = _ at hi
    rw [hi] at hh'
    exact hh'.symm

lemma trans_add {F G H : FormalGroup R} (e : CoordinateIso F G) (d : CoordinateIso G H) :
    PowerSeries.subst F.toPowerSeries (d.series.subst e.series) =
      H.toPowerSeries.subst ![PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) R) (d.series.subst e.series),
        PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) R) (d.series.subst e.series)] := by
  have h₁ := PowerSeries.subst_comp_subst_apply (.of_constantCoeff_zero e.zero_series)
      (.of_constantCoeff_zero F.zero_constantCoeff) d.series
  rw [h₁,e.preserves_addition]
  have h₂ := coordinate_add G H d (e.series.subst (X 0 : MvPowerSeries (Fin 2) R))
        (e.series.subst (X 1)) ((Coordinate.ofIso e).series_const _ (by simp))
        ((Coordinate.ofIso e).series_const _ (by simp))
  rw [h₂]
  apply congrArg (fun z : Fin 2 → MvPowerSeries (Fin 2) R => H.toPowerSeries.subst z)
  funext i; fin_cases i <;>
    exact (PowerSeries.subst_comp_subst_apply (.of_constantCoeff_zero e.zero_series)
      (PowerSeries.HasSubst.X _) d.series).symm

def trans {F G H : FormalGroup R} (e : CoordinateIso F G) (d : CoordinateIso G H) : CoordinateIso F H where
  series := d.series.subst e.series
  inverse := e.inverse.subst d.inverse
  zero_series := ((Coordinate.ofIso e).comp (Coordinate.ofIso d)).zero_series
  zero_inverse := ((Coordinate.ofIso e).comp (Coordinate.ofIso d)).zero_inverse
  left_inv := ((Coordinate.ofIso e).comp (Coordinate.ofIso d)).left_inv
  right_inv := ((Coordinate.ofIso e).comp (Coordinate.ofIso d)).right_inv
  preserves_addition := trans_add e d

def map {F G : FormalGroup R} (e : CoordinateIso F G) (π : R →+* S) : CoordinateIso (F.map π) (G.map π) where
  __ := (Coordinate.ofIso e).map π
  preserves_addition := by
    have hh := congrArg (MvPowerSeries.map π) e.preserves_addition
    rw [PowerSeries.map_subst (.of_constantCoeff_zero F.zero_constantCoeff),
      MvPowerSeries.map_subst (hasSubst_of_constantCoeff_zero (by
        intro i; fin_cases i <;> exact (Coordinate.ofIso e).series_const _ (by simp)))] at hh
    have he : (fun i : Fin 2 => MvPowerSeries.map π
        (![e.series.subst (X 0),e.series.subst (X 1)] i)) =
        ![(e.series.map π).subst (X 0 : MvPowerSeries (Fin 2) S),
          (e.series.map π).subst (X 1)] := by
      funext i; fin_cases i <;>
        simp [PowerSeries.map_subst (PowerSeries.HasSubst.X _)]
    rw [he] at hh
    exact hh

end CoordinateIso
end HeightThree.CoordinateTransport

namespace HeightThree.CoordinateTransport
open MvPowerSeries HondaTarget
variable {R S K : Type*} [CommRing R] [CommRing S] [CommRing K]

lemma unimap_comp (π : R →+* S) (ρ : S →+* K) (f : PowerSeries R) :
    (f.map π).map ρ=f.map (ρ.comp π) := MvPowerSeries.map_map _ _ _

lemma Coordinate.lift (π : R →+* S) (surj : Function.Surjective π)
    (ρ : R →+* K) (σ : S →+* K) (fac : σ.comp π=ρ)
    (hnil : ∀ a, ρ a=0 → IsNilpotent a) (d : Coordinate S)
    (hd : d.series.map σ=PowerSeries.X) :
    ∃ c : Coordinate R, c.map π=d ∧ c.series.map ρ=PowerSeries.X := by
  classical
  let u : PowerSeries R := PowerSeries.mk (fun n => if n=0 then 0 else (surj (d.series.coeff n)).choose)
  have hu0 : u.constantCoeff=0 := by simp [u,PowerSeries.constantCoeff_mk]
  have huπ : u.map π=d.series := by
    ext n
    rw [PowerSeries.coeff_map]
    simp only [u,PowerSeries.coeff_mk]
    split_ifs with hn
    · subst n; simpa using d.zero_series.symm
    · exact (surj _).choose_spec
  have huρ : u.map ρ=PowerSeries.X := by
    rw [←fac,←unimap_comp,huπ,hd]
  have hu1 : IsUnit (u.coeff 1) := by
    have hh := congrArg (PowerSeries.coeff 1) huρ
    simp only [PowerSeries.coeff_map,PowerSeries.coeff_one_X] at hh
    have hn := hnil (u.coeff 1-1) (by simp [hh])
    simpa using hn.isUnit_add_one
  let c := Coordinate.ofSeries u hu0 hu1
  refine ⟨c,?_,huρ⟩
  exact c.map_eq_of_series_eq π d huπ

lemma formal_map_comp (F : FormalGroup R) (π : R →+* S) (ρ : S →+* K) :
    (F.map π).map ρ=F.map (ρ.comp π) := by
  apply FormalGroup.ext
  exact MvPowerSeries.map_map _ _ _

lemma formal_map_injective (π : R →+* S) (hi : Function.Injective π) :
    Function.Injective (fun F : FormalGroup R => F.map π) := by
  intro F G he
  apply FormalGroup.ext
  ext d
  apply hi
  exact congrArg (MvPowerSeries.coeff d ∘ FormalGroup.toPowerSeries) he

end HeightThree.CoordinateTransport

end

end OAI
