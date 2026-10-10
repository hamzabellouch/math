import OAI.Geometry.UnitDistances.GenericCurves

namespace OAI

namespace PlanarUnitDistances.BivariateDegree
open Polynomial
variable {K : Type*} [Field K]
attribute [local instance] Classical.propDecidable

lemma coeff_swap (f : K[X][X]) (i j : ℕ) :
    ((Bivariate.swap f).coeff i).coeff j=(f.coeff j).coeff i := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add,coeff_add,hf,hg]
  | monomial n p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add,coeff_add,hp,hq]
    | monomial m a =>
      rw [Bivariate.swap_monomial_monomial]
      simp only [coeff_monomial]
      split_ifs <;> simp_all [coeff_monomial]

lemma coeff_natDegree_le_swap (f : K[X][X]) (i : ℕ) :
    (f.coeff i).natDegree ≤ (Bivariate.swap f).natDegree := by
  by_cases hi : f.coeff i=0
  · simp [hi]
  apply le_natDegree_of_ne_zero
  intro hz
  apply leadingCoeff_ne_zero.mpr hi
  have hh := congrArg (fun p : K[X] => p.coeff i) hz
  simpa only [coeff_zero,coeff_swap,coeff_natDegree] using hh

noncomputable def size (f : K[X][X]) : ℕ := f.natDegree+(Bivariate.swap f).natDegree

lemma size_mul {f g : K[X][X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    size (f*g)=size f+size g := by
  unfold size
  have hf' : Bivariate.swap f ≠ 0 := fun h => hf (Bivariate.swap.injective (h.trans (map_zero _).symm))
  have hg' : Bivariate.swap g ≠ 0 := fun h => hg (Bivariate.swap.injective (h.trans (map_zero _).symm))
  rw [natDegree_mul hf hg,map_mul,natDegree_mul hf' hg']
  omega

lemma size_eq_zero_iff (f : K[X][X]) : size f=0 ↔ ∃ c : K,f=C (C c) := by
  constructor
  · intro hs
    have hs' : f.natDegree+(Bivariate.swap f).natDegree=0 := hs
    have hd : f.natDegree=0 := by omega
    obtain ⟨p,hp⟩ := natDegree_eq_zero.mp hd
    subst f
    have hd' : p.natDegree=0 := by
      simpa only [size,Bivariate.swap_C,natDegree_C,zero_add,
        natDegree_map_eq_of_injective C_injective] using hs
    obtain ⟨c,hc⟩ := natDegree_eq_zero.mp hd'
    exact ⟨c,by rw [← hc]⟩
  · rintro ⟨c,rfl⟩
    simp only [size,natDegree_C,Bivariate.swap_C_C,Nat.add_zero]

lemma size_pos_iff (f : K[X][X]) (hf : f ≠ 0) : 0<size f ↔ ¬ IsUnit f := by
  rw [Nat.pos_iff_ne_zero,not_iff_not,size_eq_zero_iff]
  constructor
  · rintro ⟨c,rfl⟩
    apply isUnit_C.mpr
    apply isUnit_C.mpr
    exact isUnit_iff_ne_zero.mpr (by simpa using hf)
  · intro hh
    obtain ⟨p,hp,hpe⟩ := isUnit_iff.mp hh
    obtain ⟨c,hc,hce⟩ := isUnit_iff.mp hp
    exact ⟨c,by rw [← hpe,← hce]⟩

lemma size_le_of_dvd {f g : K[X][X]} (hg : g ≠ 0) (h : f ∣ g) : size f ≤ size g := by
  obtain ⟨q,rfl⟩ := h
  have hf : f ≠ 0 := left_ne_zero_of_mul hg
  have hq : q ≠ 0 := right_ne_zero_of_mul hg
  rw [size_mul hf hq]
  omega

theorem irreducible_zero_capture {α : Type*} (S : Finset α) (z w : α → K)
    (f : K[X][X]) (hf : f ≠ 0) (hnu : ¬IsUnit f) :
    ∃ g : K[X][X], Irreducible g ∧ g ∣ f ∧ size g ≤ size f ∧
    (S.filter (fun a => f.eval₂ (evalRingHom (z a)) (w a)=0)).card ≤
      size f*(S.filter (fun a => g.eval₂ (evalRingHom (z a)) (w a)=0)).card := by
  classical
  generalize hd : size f=d
  induction d using Nat.strong_induction_on generalizing f with
  | h d ih =>
    by_cases hi : Irreducible f
    · refine ⟨f,hi,dvd_refl _,hd.le,?_⟩
      have hs := (size_pos_iff f hf).mpr hnu
      rw [hd] at hs
      exact Nat.le_mul_of_pos_left _ hs
    · obtain ⟨g,h,hfgh,hgnu,hhnu⟩ : ∃ g h, f=g*h ∧ ¬IsUnit g ∧ ¬IsUnit h := by
        simpa [irreducible_iff,hnu] using hi
      have hg : g ≠ 0 := left_ne_zero_of_mul (hfgh ▸ hf)
      have hh : h ≠ 0 := right_ne_zero_of_mul (hfgh ▸ hf)
      have hsz : size g+size h=d := by rw [← size_mul hg hh,← hfgh,hd]
      have hgp := (size_pos_iff g hg).mpr hgnu
      have hhp := (size_pos_iff h hh).mpr hhnu
      obtain ⟨g',hgi,hgd,hgs,hgc⟩ := ih (size g) (by omega) g hg hgnu rfl
      obtain ⟨h',hhi,hhd,hhs,hhc⟩ := ih (size h) (by omega) h hh hhnu rfl
      let Z (p : K[X][X]) := S.filter fun a => p.eval₂ (evalRingHom (z a)) (w a)=0
      have hc : (Z f).card ≤ (Z g).card+(Z h).card := by
        apply (Finset.card_le_card (t := Z g ∪ Z h) ?_).trans (Finset.card_union_le _ _)
        intro a ha
        simp only [Z,Finset.mem_filter,Finset.mem_union,hfgh,eval₂_mul,mul_eq_zero] at ha ⊢
        aesop
      rcases le_total (Z g').card (Z h').card with hle|hle
      · refine ⟨h',hhi,hhd.trans (hfgh ▸ dvd_mul_left h g),hhs.trans ?_,?_⟩
        · omega
        · change (Z f).card ≤ d*(Z h').card
          rw [← hsz,add_mul]
          exact hc.trans (Nat.add_le_add (hgc.trans (Nat.mul_le_mul_left _ hle)) hhc)
      · refine ⟨g',hgi,hgd.trans (hfgh ▸ dvd_mul_right g h),hgs.trans ?_,?_⟩
        · omega
        · change (Z f).card ≤ d*(Z g').card
          rw [← hsz,add_mul]
          exact hc.trans (Nat.add_le_add hgc (hhc.trans (Nat.mul_le_mul_left _ hle)))

end PlanarUnitDistances.BivariateDegree

namespace PlanarUnitDistances.BiAffine
open Polynomial
variable {K U : Type*} [Field K] [Field U] [Algebra K U]

lemma expansion (f : K[X][X]) (hw : f.natDegree ≤ 1)
    (hz : (Bivariate.swap f).natDegree ≤ 1) :
    f = C (C ((f.coeff 1).coeff 1)*X+C ((f.coeff 1).coeff 0))*X+
      C (C ((f.coeff 0).coeff 1)*X+C ((f.coeff 0).coeff 0)) := by
  have h1 := eq_X_add_C_of_natDegree_le_one
    ((BivariateDegree.coeff_natDegree_le_swap f 1).trans hz)
  have h0 := eq_X_add_C_of_natDegree_le_one
    ((BivariateDegree.coeff_natDegree_le_swap f 0).trans hz)
  calc
    f = C (f.coeff 1)*X+C (f.coeff 0) := eq_X_add_C_of_natDegree_le_one hw
    _ = _ := congrArg₂ (fun p q : K[X] => C p*X+C q) h1 h0

lemma linear_not_unit {a d : K} (ha : a ≠ 0) : ¬ IsUnit (C a*X+C d) := by
  apply not_isUnit_of_natDegree_pos
  have hh : (C a*X+C d).coeff 1 ≠ 0 := by simpa using ha
  exact lt_of_lt_of_le (by decide : 0<1) (le_natDegree_of_ne_zero hh)

lemma determinant_ne_zero (f : K[X][X]) (hf : Irreducible f)
    (hw : f.natDegree ≤ 1) (hz : (Bivariate.swap f).natDegree ≤ 1)
    (ha : (f.coeff 1).coeff 1 ≠ 0) :
    (f.coeff 1).coeff 1*(f.coeff 0).coeff 0 ≠
      (f.coeff 0).coeff 1*(f.coeff 1).coeff 0 := by
  let a := (f.coeff 1).coeff 1
  let c := (f.coeff 0).coeff 1
  let d := (f.coeff 1).coeff 0
  let e := (f.coeff 0).coeff 0
  change a ≠ 0 at ha
  intro he
  have he' : d*(c/a)=e := by
    rw [← mul_div_assoc, div_eq_iff ha]
    change a*e=c*d at he
    linear_combination -he
  have hac : a*(c/a)=c := by field_simp
  have hp : C c*X+C e=(C a*X+C d)*C (c/a) := by
    rw [add_mul,mul_assoc,mul_comm X,← mul_assoc,← C_mul,← C_mul,hac,he']
  have hex : f=C (C a*X+C d)*(X+C (C (c/a))) := by
    rw [expansion f hw hz]
    change C (C a*X+C d)*X+C (C c*X+C e)=_
    rw [mul_add,← C_mul,hp]
  rcases hf.isUnit_or_isUnit hex with hl | hr
  · exact linear_not_unit ha (isUnit_C.mp hl)
  · exact not_isUnit_of_natDegree_pos _ (by simp) hr

theorem line_or_circle (f : K[X][X]) (hf : Irreducible f)
    (hw : f.natDegree=1) (hz : (Bivariate.swap f).natDegree=1) :
    (∃ e e' : K, e ≠ 0 ∧ ∀ z w : U,
      f.eval₂ (aeval z).toRingHom w=0 ↔ w=algebraMap K U e*z+algebraMap K U e') ∨
    (∃ u v b : K, b ≠ 0 ∧ ∀ z w : U,
      f.eval₂ (aeval z).toRingHom w=0 ↔
        (z-algebraMap K U u)*(w-algebraMap K U v)=algebraMap K U b) := by
  let a := (f.coeff 1).coeff 1
  let c := (f.coeff 0).coeff 1
  let d := (f.coeff 1).coeff 0
  let e := (f.coeff 0).coeff 0
  have hex := expansion f hw.le hz.le
  change f=C (C a*X+C d)*X+C (C c*X+C e) at hex
  have hev (z w : U) : f.eval₂ (aeval z).toRingHom w=
      (algebraMap K U a*z+algebraMap K U d)*w+
        (algebraMap K U c*z+algebraMap K U e) := by
    rw [hex]
    simp only [eval₂_add,eval₂_mul,eval₂_C,eval₂_X,AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom,map_add,map_mul,aeval_C,aeval_X,a,c,d,e]
  by_cases ha : a=0
  · have hd : d ≠ 0 := by
      intro hd
      have hh : f.coeff 1 ≠ 0 := by rw [← hw]; exact coeff_natDegree (p := f) ▸ leadingCoeff_ne_zero.mpr hf.ne_zero
      apply hh
      have h := eq_X_add_C_of_natDegree_le_one
        ((BivariateDegree.coeff_natDegree_le_swap f 1).trans hz.le)
      change f.coeff 1=C a*X+C d at h
      simpa only [ha,hd,map_zero,zero_mul,add_zero] using h
    have hc : c ≠ 0 := by
      intro hc
      have hs : Bivariate.swap f=C (C d*X+C e) := by
        rw [hex]
        simp only [ha,hc,map_zero,zero_mul,zero_add,map_add,map_mul]
        simp [Bivariate.swap_C, Bivariate.swap_Y]
      rw [hs,natDegree_C] at hz
      omega
    left
    refine ⟨-c/d,-e/d,div_ne_zero (neg_ne_zero.mpr hc) hd,?_⟩
    intro z w
    have hd' : algebraMap K U d ≠ 0 := (_root_.map_ne_zero _).mpr hd
    rw [hev]
    simp only [ha,map_zero,zero_mul,zero_add,map_div₀,map_neg]
    constructor <;> intro h
    · field_simp
      linear_combination h
    · rw [h]
      field_simp
      ring
  · right
    have hb : (d*c-a*e)/a^2 ≠ 0 := by
      apply div_ne_zero _ (pow_ne_zero _ ha)
      intro h
      apply determinant_ne_zero f hf hw.le hz.le ha
      change a*e=c*d
      linear_combination -sub_eq_zero.mp h
    refine ⟨-d/a,-c/a,(d*c-a*e)/a^2,hb,?_⟩
    intro z w
    have ha' : algebraMap K U a ≠ 0 := (_root_.map_ne_zero _).mpr ha
    rw [hev]
    simp only [map_neg,map_div₀,map_sub,map_mul,map_pow]
    constructor <;> intro h
    · field_simp
      linear_combination h * algebraMap K U a
    · field_simp at h
      apply mul_left_cancel₀ ha'
      linear_combination h
end PlanarUnitDistances.BiAffine

namespace PlanarUnitDistances.CurveSeparation
open Polynomial
variable {B K : Type*} [Field B] [Field K] [Algebra B K]

lemma resultant_ne_zero (g f : B[X][X]) (hg : Irreducible g)
    (hd : g.natDegree ≠ 0) (hgf : ¬ g ∣ f) : g.resultant f ≠ 0 := by
  let φ := algebraMap B[X] (RatFunc B)
  have hi : Irreducible (g.map φ) :=
    (hg.isPrimitive hd).irreducible_iff_irreducible_map_fraction_map.mp hg
  have hnd : ¬ g.map φ ∣ f.map φ := by
    intro hh
    exact hgf ((hg.isPrimitive hd).dvd_iff_fraction_map_dvd_fraction_map (RatFunc B) |>.mpr hh)
  have hr := Polynomial.resultant_ne_zero (g.map φ) (f.map φ)
    (hi.coprime_iff_not_dvd.mpr hnd)
  have hm (p : B[X][X]) : (p.map φ).natDegree=p.natDegree :=
    natDegree_map_eq_of_injective (IsFractionRing.injective B[X] (RatFunc B)) p
  rw [hm g,hm f,resultant_map_map] at hr
  intro hz
  apply hr
  rw [hz,map_zero]

theorem eval_ne_zero (g f : B[X][X]) (hg : Irreducible g)
    (hd : g.natDegree ≠ 0) (hgf : ¬ g ∣ f) (a b : K)
    (ha : Transcendental B a) (hgroot : g.eval₂ (aeval a).toRingHom b=0) :
    f.eval₂ (aeval a).toRingHom b≠0 := by
  intro hfroot
  obtain ⟨p,q,_,_,he⟩ := exists_mul_add_mul_eq_C_resultant g f le_rfl le_rfl (Or.inl hd)
  have hh := congrArg (fun h : B[X][X] => h.eval₂ (aeval a).toRingHom b) he
  simp only [eval₂_add,eval₂_mul,eval₂_C] at hh
  rw [hgroot,hfroot,zero_mul,zero_mul,zero_add] at hh
  have hz : aeval a (g.resultant f)=0 := hh.symm
  exact (resultant_ne_zero g f hg hd hgf)
    (transcendental_iff_injective.mp ha (hz.trans (map_zero _).symm))

end PlanarUnitDistances.CurveSeparation

namespace PlanarUnitDistances.BivariateMaps
open Polynomial
variable {B K L : Type*} [Field B] [Field K] [Field L]
  [Algebra B K] [Algebra B L] [Algebra K L] [IsScalarTower B K L]

lemma eval_transport (f : B[X][X]) (a b : K) :
    algebraMap K L (f.eval₂ (aeval a).toRingHom b)=
      f.eval₂ (aeval (algebraMap K L a)).toRingHom (algebraMap K L b) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [eval₂_add,map_add,hf,hg]
  | monomial n p =>
    simp only [eval₂_monomial,map_mul,map_pow]
    congr 1
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add,hp,hq]
    | monomial m c =>
      simp [aeval_monomial,IsScalarTower.algebraMap_apply B K L]
end PlanarUnitDistances.BivariateMaps

namespace PlanarUnitDistances.Radicals
open Polynomial BivariateMaps
universe u
variable {k B K L : Type u} [Field k] [Field B] [CharZero B] [Field K] [CharZero K]
  [Field L] [Algebra k L] [Algebra B K] [Algebra K L] [IsAlgClosed K]
  [Algebra B L] [IsScalarTower B K L]

theorem curve_locus_differential_obstruction (D : Derivation k L L)
    (f g : B[X][X]) (hfK : Irreducible (bimap (algebraMap B K) f))
    (hfdeg : f.natDegree≠0) (hfsym : (Bivariate.swap f).natDegree=f.natDegree)
    (hgK : Irreducible (bimap (algebraMap B K) g))
    (hgdeg : g.natDegree≠0) (hgswap : (Bivariate.swap g).natDegree≠0)
    (hunit : g ∣ f → ∀ u v : B, ∃ z' w' : L, f.eval₂ (aeval z').toRingHom w'=0 ∧
      (z'-algebraMap B L u)*(w'-algebraMap B L v)≠1)
    (z w : L) (hz : Transcendental K z)
    (hroot : f.eval₂ (aeval z).toRingHom w=0)
    (a b da db t : Fin 4 → K) (ha : AlgebraicIndependent B a)
    (hb : ∀ i, g.eval₂ (aeval (a i)).toRingHom (b i)=0)
    (l : Fin 4 → L) (A : L) (hl : ∀ i, l i≠0)
    (hdist : ∀ i, (z-algebraMap K L (a i))*(w-algebraMap K L (b i))=2-l i-(l i)⁻¹)
    (hda : ∀ i, D (algebraMap K L (a i))=algebraMap K L (da i))
    (hdb : ∀ i, D (algebraMap K L (b i))=algebraMap K L (db i))
    (hlog : ∀ i, D (l i)/l i=A-algebraMap K L (t i))
    (hD : ∀ i, D (l i)≠0) : False := by
  have hf := irreducible_of_bimap (algebraMap B K) hfK
  have hg := irreducible_of_bimap (algebraMap B K) hgK
  have hrootK : (bimap (algebraMap B K) f).eval₂ (aeval z).toRingHom w=0 := by
    rwa [eval_bimap]
  by_cases hgf : g ∣ f
  · by_cases hdegree : 2≤f.natDegree
    · exact curve_curve_differential_obstruction D f g hfK hfdeg hgK hgswap z w hz
        hrootK a b da db t ha hb (fun _ => Or.inr hdegree) l A hl hdist hda hdb hlog hD
    have hf1 : f.natDegree=1 := by omega
    have hfs1 : (Bivariate.swap f).natDegree=1 := hfsym.trans hf1
    have hbf (i) : f.eval₂ (aeval (a i)).toRingHom (b i)=0 := by
      obtain ⟨q,rfl⟩ := hgf
      rw [eval₂_mul,hb,zero_mul]
    have hbfL (i) : f.eval₂ (aeval (algebraMap K L (a i))).toRingHom
        (algebraMap K L (b i))=0 := by
      rw [← eval_transport,hbf,map_zero]
    rcases BiAffine.line_or_circle (U := L) f hf hf1 hfs1 with he|hc
    · obtain ⟨e,e',he,heq⟩ := he
      have hw : w=algebraMap K L (algebraMap B K e)*z+algebraMap K L (algebraMap B K e') := by
        simpa only [← IsScalarTower.algebraMap_apply B K L] using (heq z w).mp hroot
      have hbr (i) : b i=algebraMap B K e*a i+algebraMap B K e' := by
        apply (algebraMap K L).injective
        simpa only [map_add,map_mul,← IsScalarTower.algebraMap_apply B K L]
          using (heq _ _).mp (hbfL i)
      exact line_differential_obstruction D e e' he z w hz hw a b da db t ha hbr
        l A hl hdist hda hdb hlog hD
    · obtain ⟨u,v,c,hc,heq⟩ := hc
      have hc1 : c≠1 := by
        intro h
        obtain ⟨z',w',hr,hu⟩ := hunit hgf u v
        apply hu
        simpa only [h,map_one] using (heq z' w').mp hr
      have hw : (z-algebraMap K L (algebraMap B K u))*
          (w-algebraMap K L (algebraMap B K v))=algebraMap K L (algebraMap B K c) := by
        simpa only [← IsScalarTower.algebraMap_apply B K L] using (heq z w).mp hroot
      have hbr (i) : (a i-algebraMap B K u)*(b i-algebraMap B K v)=algebraMap B K c := by
        apply (algebraMap K L).injective
        simpa only [map_mul,map_sub,← IsScalarTower.algebraMap_apply B K L]
          using (heq _ _).mp (hbfL i)
      exact circle_differential_obstruction D u v c hc hc1 z w hz hw a b da db t ha hbr
        l A hl hdist hda hdb hlog hD
  · exact curve_curve_differential_obstruction D f g hfK hfdeg hgK hgswap z w hz
      hrootK a b da db t ha hb
      (fun i => Or.inl (CurveSeparation.eval_ne_zero g f hg hgdeg hgf (a i) (b i)
        (ha.transcendental i) (hb i))) l A hl hdist hda hdb hlog hD
end PlanarUnitDistances.Radicals

namespace UnitDistances.DerivationObstruction

open TensorProduct

section Etale
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra.FormallyEtale S T]

noncomputable def extendDerivation (d : Derivation R S T) : Derivation R T T :=
  ((d.liftKaehlerDifferential.liftBaseChange T).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer
      (KaehlerDifferential.D R T)

@[simp] theorem extendDerivation_algebraMap (d : Derivation R S T) (s : S) :
    extendDerivation d (algebraMap S T s) = d s := by
  simp [extendDerivation,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

end Etale

section Fields
variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero k]

theorem exists_derivation_basis_one {ι : Type*} (b : ι → F)
    (hb : IsTranscendenceBasis k b) (i : ι) :
    ∃ d : Derivation k F F, d (b i) = 1 := by
  classical
  let P := MvPolynomial ι k
  let Q := FractionRing P
  let E := IntermediateField.adjoin k (Set.range b)
  let e : Q ≃ₐ[k] E := hb.1.aevalEquivField
  let f : Q →ₐ[k] F := E.val.comp e.toAlgHom
  let : Algebra Q F := f.toRingHom.toAlgebra
  have : IsScalarTower k Q F := IsScalarTower.of_algebraMap_eq fun x => by
    exact (f.commutes x).symm
  have : Algebra.IsAlgebraic E F := hb.isAlgebraic_field
  have : Algebra.IsAlgebraic Q F :=
    Algebra.IsAlgebraic.of_ringHom_of_comp_eq e.toRingHom (RingHom.id F)
      e.surjective Function.injective_id rfl
  have : CharZero Q := inferInstance
  have : Algebra.FormallyEtale Q F := Algebra.FormallyEtale.of_isSeparable Q F
  let dP : Derivation k P Q := MvPolynomial.mkDerivation k (fun j => if j = i then 1 else 0)
  let dQ : Derivation k Q Q := extendDerivation dP
  let dQF : Derivation k Q F := (Algebra.linearMap Q F).compDer dQ
  refine ⟨extendDerivation dQF, ?_⟩
  have hbi : algebraMap Q F (algebraMap P Q (MvPolynomial.X i)) = b i := by
    change (e (algebraMap P Q (MvPolynomial.X i)) : F) = b i
    rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
    simp
  rw [← hbi, extendDerivation_algebraMap]
  change algebraMap Q F (extendDerivation dP
    (algebraMap P Q (MvPolynomial.X i))) = 1
  rw [extendDerivation_algebraMap]
  have heval : dP (MvPolynomial.X i) = 1 := by
    change MvPolynomial.mkDerivation k (fun j => if j = i then (1 : Q) else 0)
      (MvPolynomial.X i) = 1
    rw [MvPolynomial.mkDerivation_X]
    simp
  rw [heval, map_one]

theorem exists_derivation_one {x : F} (hx : Transcendental k x) :
    ∃ d : Derivation k F F, d x = 1 := by
  have hs : AlgebraicIndepOn k id ({x} : Set F) := by
    apply (algebraicIndependent_singleton_iff ⟨x, by simp⟩).mpr
    exact hx
  obtain ⟨b, hxb, hb⟩ := exists_isTranscendenceBasis_superset hs
  exact exists_derivation_basis_one Subtype.val hb ⟨x, hxb (by simp)⟩

theorem exists_common_derivation {ι : Type*} [Finite ι] (x : ι → F)
    (hx : ∀ i, Transcendental k (x i)) :
    ∃ d : Derivation k F F, ∀ i, d (x i) ≠ 0 := by
  have : CharZero F := Algebra.charZero_of_charZero k F
  let ev (i : ι) : Module.Dual F (Derivation k F F) :=
    { toFun := fun d => d (x i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply Module.Dual.exists_forall_ne_zero_of_forall_exists ev
  intro i
  obtain ⟨d, hd⟩ := exists_derivation_one (hx i)
  exact ⟨d, by change d (x i) ≠ 0; rw [hd]; exact one_ne_zero⟩

end Fields

end UnitDistances.DerivationObstruction

namespace PlanarUnitDistances.GridDerivation
universe u
variable {k U : Type u} [Field k] [CharZero k] [Field U] [Algebra k U]

theorem exists_derivation_log (l : Fin 21 → Fin 4 → U)
    (htrans : ∀ i j, Transcendental k (l i j))
    (hrect : ∀ i j, ∃ c : k,
      l i j*l 0 0=l i 0*l 0 j*algebraMap k U c) :
    ∃ D : Derivation k U U, ∃ A : Fin 21 → U, ∃ t : Fin 4 → U,
      (∀ i j, D (l i j)≠0) ∧ (∀ i j, D (l i j)/l i j=A i-t j) := by
  have hl (i j) : l i j≠0 := fun h => htrans i j (h ▸ isAlgebraic_zero)
  obtain ⟨D,hD⟩ := UnitDistances.DerivationObstruction.exists_common_derivation
    (fun ij : Fin 21 × Fin 4 => l ij.1 ij.2) (fun ij => htrans ij.1 ij.2)
  let h : Fin 4 → U := fun j => l 0 0 / l 0 j
  refine ⟨D,(fun i => D (l i 0)/l i 0),(fun j => D (h j)/h j),(fun i j => hD (i,j)),?_⟩
  intro i j
  obtain ⟨c,hc⟩ := hrect i j
  have hc0 : algebraMap k U c≠0 := by
    intro he
    rw [he,mul_zero] at hc
    exact mul_ne_zero (hl i j) (hl 0 0) hc
  apply UnitDistances.DifferentialSystem.logDerivative_factorization D
    (hl i 0) (div_ne_zero (hl 0 0) (hl 0 j)) hc0 (D.map_algebraMap c)
  change l i j = l i 0 * (l 0 0 / l 0 j)⁻¹ * algebraMap k U c
  field_simp [hl 0 0,hl 0 j]
  linear_combination hc
end PlanarUnitDistances.GridDerivation

namespace UnitDistanceSurvival
open Set

lemma free_subset {α : Type*} (M : Matroid α) (I C : Set α)
    (hI : M.Indep I) (hIf : I.Finite) (hCf : C.Finite) (hC : C ⊆ M.E) :
    ∃ B D : Set α, M.IsBasis B C ∧ D ⊆ I ∧ Disjoint D C ∧
      M.Indep (D ∪ B) ∧ (I \ D).ncard ≤ C.ncard := by
  obtain ⟨B, hB⟩ := M.exists_isBasis C hC
  obtain ⟨J, hJ, hJB⟩ := hB.exists_isBasis_inter_eq_of_superset
    (Y := I ∪ C) subset_union_right (union_subset hI.subset_ground hC)
  have hJf : J.Finite := (hIf.union hCf).subset hJ.subset
  have hBf : B.Finite := hCf.subset hB.subset
  have hDI : J \ C ⊆ I := by
    intro a ha
    exact (hJ.subset ha.1).resolve_right ha.2
  have hIJcard : I.ncard ≤ J.ncard := by
    have h := hI.encard_le_eRk_of_subset (X := I ∪ C) subset_union_left
    rw [← hJ.encard_eq_eRk, ← hIf.cast_ncard_eq, ← hJf.cast_ncard_eq] at h
    exact_mod_cast h
  have hcardJ : (J \ C).ncard + B.ncard = J.ncard := by
    have h := Set.encard_sdiff_add_encard_inter J C
    rw [hJB, ← (hJf.sdiff).cast_ncard_eq, ← hBf.cast_ncard_eq,
      ← hJf.cast_ncard_eq] at h
    exact_mod_cast h
  have hcardI : (I \ (J \ C)).ncard + (J \ C).ncard = I.ncard := by
    simpa only [union_eq_self_of_subset_right hDI] using
      Set.ncard_sdiff_add_ncard I (J \ C) hIf hJf.sdiff
  refine ⟨B, J \ C, hB, hDI, disjoint_sdiff_left, ?_, ?_⟩
  · convert hJ.indep using 1
    rw [← hJB, sdiff_union_inter]
  · have := Set.ncard_le_ncard hB.subset hCf
    omega

lemma surviving_block {α : Type*} (M : Matroid α) {ι δ : Type*} [Fintype ι] [Fintype δ]
    (x : ι × δ → α) (hx : Function.Injective x)
    (hind : M.Indep (Set.range x)) (C : Set α) (hCf : C.Finite)
    (hC : C ⊆ M.E) (hcard : C.ncard < Fintype.card ι) :
    ∃ i : ι, ∃ B : Set α, M.IsBasis B C ∧
      Disjoint (Set.range (fun j : δ => x (i,j))) B ∧
      M.Indep (Set.range (fun j : δ => x (i,j)) ∪ B) := by
  classical
  obtain ⟨B,D,hB,hDI,hDC,hDB,hsmall⟩ :=
    free_subset M (Set.range x) C hind (Set.finite_range x) hCf hC
  have hex : ∃ i : ι, ∀ j : δ, x (i,j) ∈ D := by
    by_contra hn
    push Not at hn
    choose j hj using hn
    let f : ι → ↥(Set.range x \ D) := fun i => ⟨x (i,j i), ⟨⟨(i,j i),rfl⟩,hj i⟩⟩
    have hf : Function.Injective f := by
      intro i i' h
      have hh := hx (congrArg Subtype.val h)
      exact congrArg Prod.fst hh
    let : Fintype ↥(Set.range x \ D) := (Set.finite_range x).sdiff.fintype
    have hc := Fintype.card_le_of_injective f hf
    have hncard : Fintype.card ↥(Set.range x \ D) = (Set.range x \ D).ncard := by
      exact Set.fintypeCard_eq_ncard _
    rw [hncard] at hc
    omega
  obtain ⟨i,hi⟩ := hex
  have hRD : Set.range (fun j : δ => x (i,j)) ⊆ D := by
    rintro a ⟨j,rfl⟩
    exact hi j
  refine ⟨i,B,hB,?_,hDB.subset (union_subset_union_left B hRD)⟩
  exact (hDC.mono hRD hB.subset)

lemma independent_over_basis {F K δ : Type*} [Field F] [Field K] [Algebra F K]
    (x : δ → K) (hx : Function.Injective x) (B C : Set K)
    (hB : (AlgebraicIndependent.matroid F K).IsBasis B C)
    (hd : Disjoint (Set.range x) B)
    (hu : (AlgebraicIndependent.matroid F K).Indep (Set.range x ∪ B)) :
    AlgebraicIndependent (algebraicClosure (IntermediateField.adjoin F C) K) x := by
  let f : δ ⊕ B → ↥(Set.range x ∪ B) := Sum.elim
    (fun j => ⟨x j, Or.inl ⟨j,rfl⟩⟩) (fun b => ⟨b,Or.inr b.2⟩)
  have hf : Function.Injective f := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (hx (congrArg Subtype.val h))
      | inr b =>
        exfalso
        have h' : x a = (b : K) := congrArg Subtype.val h
        exact Set.disjoint_left.mp hd ⟨a,rfl⟩ (h'.symm ▸ b.2)
    | inr a =>
      cases b with
      | inl b =>
        exfalso
        have h' : (a : K) = x b := congrArg Subtype.val h
        exact Set.disjoint_left.mp hd ⟨b,rfl⟩ (h' ▸ a.2)
      | inr b =>
        have h' : (a : K) = (b : K) :=
          congrArg (fun z : ↥(Set.range x ∪ B) => (z : K)) h
        exact congrArg Sum.inr (Subtype.ext h')
  have hg : AlgebraicIndependent F (Sum.elim x (fun b : B => (b : K))) := by
    convert hu.comp f hf using 1
    funext u
    cases u <;> rfl
  have hb := (AlgebraicIndependent.sumElim_iff.mp hg).2
  rw [Subtype.range_coe] at hb
  have hbf : AlgebraicIndependent (IntermediateField.adjoin F B) x :=
    IntermediateField.algebraicIndependent_adjoin_iff.mpr hb
  have hBC : IntermediateField.adjoin F B ≤ IntermediateField.adjoin F C :=
    IntermediateField.adjoin_le_iff.mpr fun a ha =>
      IntermediateField.subset_adjoin F C (hB.subset ha)
  let : Algebra (IntermediateField.adjoin F B) (IntermediateField.adjoin F C) :=
    (IntermediateField.inclusion hBC).toAlgebra
  let : IsScalarTower (IntermediateField.adjoin F B)
      (IntermediateField.adjoin F C) K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halg : ∀ a ∈ C, IsAlgebraic (IntermediateField.adjoin F B) a := by
    intro a ha
    exact IntermediateField.isAlgebraic_adjoin_iff.mpr
      ((AlgebraicIndependent.matroid_isBasis_iff.mp hB).2.2 a ha)
  let : Algebra.IsAlgebraic (IntermediateField.adjoin F B)
      (IntermediateField.adjoin F C) := by
    refine ⟨fun a => (isAlgebraic_algHom_iff
      (IsScalarTower.toAlgHom (IntermediateField.adjoin F B)
        (IntermediateField.adjoin F C) K) Subtype.val_injective).mp ?_⟩
    rcases a with ⟨a,ha⟩
    change IsAlgebraic (IntermediateField.adjoin F B) a
    induction ha using IntermediateField.adjoin_induction with
    | mem x hx => exact halg x hx
    | algebraMap a =>
      exact isAlgebraic_algebraMap (⟨algebraMap F K a,
        IntermediateField.algebraMap_mem _ a⟩ : IntermediateField.adjoin F B)
    | add x y hx hy hx' hy' => exact hx'.add hy'
    | inv x hx hx' => exact hx'.inv
    | mul x y hx hy hx' hy' => exact hx'.mul hy'
  exact (hbf.extendScalars (IntermediateField.adjoin F C)).algebraicClosure

theorem survives_algebraic_closure {F K ι δ κ : Type*}
    [Field F] [Field K] [Algebra F K]
    [Fintype ι] [Fintype δ] [Fintype κ]
    (x : ι × δ → K) (hx : AlgebraicIndependent F x) (y : κ → K)
    (hcard : Fintype.card κ < Fintype.card ι) :
    ∃ i : ι, AlgebraicIndependent
      (algebraicClosure (IntermediateField.adjoin F (Set.range y)) K)
        (fun j : δ => x (i,j)) := by
  classical
  have hcle : (Set.range y).ncard ≤ Fintype.card κ := by
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using
      (Set.ncard_image_le (s := Set.univ) (f := y))
  have hc : (Set.range y).ncard < Fintype.card ι := lt_of_le_of_lt hcle hcard
  obtain ⟨i,B,hB,hd,hu⟩ := surviving_block (AlgebraicIndependent.matroid F K)
    x hx.injective hx.coe_range (Set.range y) (Set.finite_range y)
    (by simp) hc
  refine ⟨i,independent_over_basis _ ?_ B (Set.range y) hB hd hu⟩
  intro a b h
  exact congrArg Prod.snd (hx.injective h)

end UnitDistanceSurvival

end OAI
