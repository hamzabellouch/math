import OAI.Geometry.UnitDistances.Valuations

namespace OAI

namespace PlanarUnitDistances.GenericNoncoincidence
open Polynomial
variable {K U : Type*} [Field K] [Field U] [Algebra K U]

noncomputable def poleTest (f : K[X][X]) (a b k : K) : K[X] :=
  (f.scaleRoots (X - C a)).eval (C b * (X - C a) + C k)

lemma poleTest_eval_center (f : K[X][X]) (a b k : K)
    (hlead : f.leadingCoeff.eval a ≠ 0) :
    (poleTest f a b k).eval a = f.leadingCoeff.eval a * k ^ f.natDegree := by
  change (evalRingHom a) ((f.scaleRoots (X - C a)).eval
    (C b * (X - C a) + C k)) = _
  rw [← eval₂_at_apply (evalRingHom a)]
  simp only [coe_evalRingHom, eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero,
    zero_add]
  rw [← eval_map, map_scaleRoots f (X - C a) (evalRingHom a) hlead]
  simp only [coe_evalRingHom, eval_sub, eval_X, eval_C, sub_self, scaleRoots_zero,
    eval_smul, eval_pow, eval_X, smul_eq_mul,
    leadingCoeff_map_of_leadingCoeff_ne_zero (evalRingHom a) hlead,
    natDegree_map_of_leadingCoeff_ne_zero (evalRingHom a) hlead]

lemma poleTest_nonzero (f : K[X][X]) (a b k : K)
    (hlead : f.leadingCoeff.eval a ≠ 0) (hk : k ≠ 0) :
    poleTest f a b k ≠ 0 := by
  intro h
  have he := poleTest_eval_center f a b k hlead
  rw [h, eval_zero] at he
  exact mul_ne_zero hlead (pow_ne_zero _ hk) he.symm

theorem distance_ne_nonzero (f : K[X][X]) (a b k : K)
    (hlead : f.leadingCoeff.eval a ≠ 0) (hk : k ≠ 0)
    (d e : U) (hd : Transcendental K d)
    (hroot : f.eval₂ (aeval d).toRingHom e = 0) :
    (algebraMap K U a - d) * (algebraMap K U b - e) ≠ algebraMap K U k := by
  intro he
  have hmul : (aeval d) (C b * (X - C a) + C k) =
      (aeval d) (X - C a) * e := by
    simp only [map_add, map_mul, map_sub, aeval_C, aeval_X]
    linear_combination -he
  have hzero : aeval d (poleTest f a b k) = 0 := by
    change (aeval d).toRingHom ((f.scaleRoots (X - C a)).eval
      (C b * (X - C a) + C k)) = 0
    rw [← eval₂_at_apply (aeval d).toRingHom]
    change (f.scaleRoots (X - C a)).eval₂ (aeval d).toRingHom
      ((aeval d) (C b * (X - C a) + C k)) = 0
    rw [hmul]
    exact scaleRoots_eval₂_eq_zero (aeval d).toRingHom hroot
  exact poleTest_nonzero f a b k hlead hk
    (transcendental_iff_injective.mp hd (hzero.trans (map_zero _).symm))

lemma primitive_fiber_ne_zero (g : K[X][X]) (hg : g.IsPrimitive) (b : U) :
    g.map (aeval b).toRingHom ≠ 0 := by
  intro hz
  apply minpoly.not_isUnit K b
  apply hg
  rw [C_dvd_iff_dvd_coeff]
  intro n
  apply minpoly.dvd K b
  have hh := congrArg (fun p : U[X] => p.coeff n) hz
  simpa only [coeff_map, coeff_zero, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hh

lemma aevalAeval_eq_eval₂ (x y : U) (p : K[X][X]) :
    p.aevalAeval x y = p.eval₂ (aeval x).toRingHom y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | monomial n p =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, aevalAeval_C, aevalAeval_Y,
      eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
    rfl

theorem generic_ordinate_ne_constant (f : K[X][X])
    (hf : (Bivariate.swap f).IsPrimitive) (b : K)
    (d e : U) (hd : Transcendental K d)
    (hroot : f.aevalAeval d e = 0) : e ≠ algebraMap K U b := by
  intro he
  let g : K[X] := (Bivariate.swap f).map (aeval b).toRingHom
  have hg : g ≠ 0 := primitive_fiber_ne_zero (Bivariate.swap f) hf b
  have heval : aeval d g = 0 := by
    have hs := Bivariate.aevalAeval_swap (algebraMap K U b) d f
    rw [he] at hroot
    rw [hroot] at hs
    have hh : (algebraMap K U).comp (aeval b : K[X] →ₐ[K] K).toRingHom =
        (aeval (algebraMap K U b) : K[X] →ₐ[K] U).toRingHom := by
      ext c <;> simp
    rw [aevalAeval_eq_eval₂] at hs
    simpa only [g, aeval_def, eval₂_map, hh] using hs
  exact hg (transcendental_iff_injective.mp hd (heval.trans (map_zero _).symm))

end PlanarUnitDistances.GenericNoncoincidence

namespace PlanarUnitDistances.BivariateMaps
open Polynomial
variable {B K L : Type*} [Field B] [Field K] [Field L]

noncomputable abbrev bimap (φ : B →+* K) : B[X][X] →+* K[X][X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom φ)

lemma bimap_injective (φ : B →+* K) : Function.Injective (bimap φ) :=
  Polynomial.map_injective _ (Polynomial.map_injective _ φ.injective)

lemma isUnit_bimap_iff (φ : B →+* K) (p : B[X][X]) :
    IsUnit (bimap φ p) ↔ IsUnit p := by
  constructor
  · intro h
    obtain ⟨q,hq,he⟩ := Polynomial.isUnit_iff.mp h
    obtain ⟨c,hc,rfl⟩ := Polynomial.isUnit_iff.mp hq
    have he' : bimap φ p=bimap φ (C (C ((p.coeff 0).coeff 0))) := by
      have hcoeff := congrArg (fun p : K[X][X] => (p.coeff 0).coeff 0) he
      simp only [bimap,coe_mapRingHom,coeff_map,coeff_C_zero] at hcoeff
      simpa only [bimap,coe_mapRingHom,map_C,hcoeff] using he.symm
    have hp := bimap_injective φ he'
    have hn : (p.coeff 0).coeff 0 ≠ 0 := by
      intro hz
      have hcoeff := congrArg (fun p : K[X][X] => (p.coeff 0).coeff 0) he
      simp only [bimap,coe_mapRingHom,coeff_map,coeff_C_zero,hz,map_zero] at hcoeff
      exact hc.ne_zero hcoeff
    rw [hp]
    exact isUnit_C.mpr <| isUnit_C.mpr <| isUnit_iff_ne_zero.mpr hn
  · exact fun h => h.map (bimap φ)

lemma irreducible_of_bimap (φ : B →+* K) {p : B[X][X]}
    (h : Irreducible (bimap φ p)) : Irreducible p := by
  refine ⟨fun hu => h.not_isUnit (hu.map _), ?_⟩
  intro a b he
  rcases h.isUnit_or_isUnit (by simpa only [map_mul] using congrArg (bimap φ) he)
    with ha|hb
  · exact Or.inl ((isUnit_bimap_iff φ a).mp ha)
  · exact Or.inr ((isUnit_bimap_iff φ b).mp hb)

lemma bimap_comp (φ : B →+* K) (ψ : K →+* L) (p : B[X][X]) :
    bimap ψ (bimap φ p)=bimap (ψ.comp φ) p := by
  simp only [bimap, coe_mapRingHom, map_map, mapRingHom_comp]

lemma bimap_natDegree (φ : B →+* K) (p : B[X][X]) :
    (bimap φ p).natDegree=p.natDegree :=
  natDegree_map_eq_of_injective (Polynomial.map_injective _ φ.injective) _

lemma bimap_swap (φ : B →+* K) (p : B[X][X]) :
    Bivariate.swap (bimap φ p)=bimap φ (Bivariate.swap p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial n p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add,hp,hq]
    | monomial m c =>
      simp only [bimap,coe_mapRingHom,map_monomial,Bivariate.swap_monomial_monomial]

lemma eval_bimap [Algebra B K] [Algebra B L] [Algebra K L] [IsScalarTower B K L]
    (p : B[X][X]) (x y : L) :
    (bimap (algebraMap B K) p).eval₂ (aeval x).toRingHom y =
      p.eval₂ (aeval x).toRingHom y := by
  simp only [bimap,coe_mapRingHom,eval₂_map]
  congr 1
  ext c <;> simp [IsScalarTower.algebraMap_apply B K L]

end PlanarUnitDistances.BivariateMaps

namespace PlanarUnitDistances.GenericSheets
open Polynomial BivariateMaps
variable {B K : Type*} [Field B] [Field K] [Algebra B K]

lemma fiber_algebraic (f : B[X][X]) (hf : f ≠ 0)
    (a b : K) (ha : Transcendental B a)
    (hroot : f.eval₂ (aeval a).toRingHom b = 0) :
    IsAlgebraic (IntermediateField.adjoin B ({a} : Set K)) b := by
  let E := IntermediateField.adjoin B ({a} : Set K)
  let a' : E := ⟨a, IntermediateField.subset_adjoin B _ (Set.mem_singleton _)⟩
  have ha' : Transcendental B a' := by
    intro h
    exact ha (h.algHom E.val)
  let q := f.map (aeval a').toRingHom
  refine ⟨q, ?_, ?_⟩
  · exact fun he => hf (Polynomial.map_injective _ (transcendental_iff_injective.mp ha')
      (he.trans (Polynomial.map_zero _).symm))
  · have hh : (algebraMap E K).comp (aeval a' : B[X] →ₐ[B] E).toRingHom=(aeval a : B[X] →ₐ[B] K).toRingHom := by
      ext c <;> simp [a']
    change q.eval₂ (algebraMap E K) b=0
    dsimp only [q]
    rw [eval₂_map,hh]
    exact hroot

lemma other_transcendental {ι : Type*} {a : ι → K} (ha : AlgebraicIndependent B a)
    {i j : ι} (hji : j ≠ i) :
    Transcendental (algebraicClosure (IntermediateField.adjoin B ({a i} : Set K)) K) (a j) := by
  apply Transcendental.algebraicClosure
  apply IntermediateField.transcendental_adjoin_iff.mpr
  have hh := ha.transcendental_adjoin (s := {i}) (i := j) (by simpa using hji)
  rw [Set.image_singleton] at hh
  exact hh

theorem exists_private_sheet_curve [CharZero B] [CharZero K] [IsAlgClosed K]
    {ι : Type*} (f g : B[X][X]) (hf : Irreducible f) (hfdeg : f.natDegree ≠ 0)
    (hgK : Irreducible (bimap (algebraMap B K) g))
    (hgswap : (Bivariate.swap g).natDegree ≠ 0)
    (a c : ι → K) (ha : AlgebraicIndependent B a)
    (hc : ∀ i, g.eval₂ (aeval (a i)).toRingHom (c i)=0)
    (i : ι) (halt : f.eval₂ (aeval (a i)).toRingHom (c i) ≠ 0 ∨ 2 ≤ f.natDegree) :
    ∃ b : K, f.eval₂ (aeval (a i)).toRingHom b=0 ∧
      f.derivative.eval₂ (aeval (a i)).toRingHom b≠0 ∧ b≠c i ∧
      ∀ j, j≠i → (a i-a j)*(b-c j)≠0 ∧ (a i-a j)*(b-c j)≠4 := by
  obtain ⟨b,hb,hbd,hbc⟩ := GenericCurve.exists_distinct_smooth_sheet f hf hfdeg
    (a i) (c i) (ha.transcendental i) halt
  refine ⟨b,hb,hbd,hbc,?_⟩
  let F := IntermediateField.adjoin B ({a i} : Set K)
  let E := algebraicClosure F K
  let : IsScalarTower B E K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ai : F := ⟨a i, IntermediateField.subset_adjoin B _ (Set.mem_singleton _)⟩
  let a' : E := algebraMap F E ai
  have ha' : algebraMap E K a'=a i := by simp [a',ai]
  have hbalg : IsAlgebraic F b := fiber_algebraic f hf.ne_zero (a i) b (ha.transcendental i) hb
  let b' : E := ⟨b, mem_algebraicClosure_iff.mpr hbalg⟩
  let g' := bimap (algebraMap B E) g
  have hge : bimap (algebraMap E K) g'=bimap (algebraMap B K) g := by
    simp only [g',bimap_comp,← IsScalarTower.algebraMap_eq B E K]
  have hg' : Irreducible g' := irreducible_of_bimap (algebraMap E K) (hge.symm ▸ hgK)
  have hgs' : (Bivariate.swap g').IsPrimitive := by
    apply ((MulEquiv.irreducible_iff Bivariate.swap).mpr hg').isPrimitive
    simpa only [g',bimap_swap,bimap_natDegree] using hgswap
  have hlead : g'.leadingCoeff.eval a' ≠ 0 := by
    intro hz
    have hz' := congrArg (algebraMap E K) hz
    have hg0 : g ≠ 0 := (irreducible_of_bimap (algebraMap B K) hgK).ne_zero
    apply GenericCurve.fiber_leadingCoeff_ne_zero g hg0 (a i) (ha.transcendental i)
    have hh : algebraMap E K (g'.leadingCoeff.eval a')=aeval (a i) g.leadingCoeff := by
      dsimp only [g', BivariateMaps.bimap,coe_mapRingHom]
      rw [leadingCoeff_map_of_injective (f := Polynomial.mapRingHom (algebraMap B E))
        (Polynomial.map_injective _ (algebraMap B E).injective)]
      change algebraMap E K ((g.leadingCoeff.map (algebraMap B E)).eval a')=_
      rw [← eval₂_hom, eval₂_map, ← IsScalarTower.algebraMap_eq B E K,ha',← aeval_def]
    simpa only [hh,map_zero] using hz'
  intro j hji
  have haj : Transcendental E (a j) := other_transcendental ha hji
  have hcj : g'.eval₂ (aeval (a j)).toRingHom (c j)=0 := by
    simpa only [g',eval_bimap] using hc j
  have hcz : c j≠(b' : K) :=
    GenericNoncoincidence.generic_ordinate_ne_constant g' hgs' b' (a j) (c j) haj
      (by simpa only [GenericNoncoincidence.aevalAeval_eq_eval₂] using hcj)
  have hdz : a i ≠ a j := fun hh => hji (ha.injective hh).symm
  refine ⟨mul_ne_zero (sub_ne_zero.mpr hdz) (sub_ne_zero.mpr hcz.symm),?_⟩
  have hn := GenericNoncoincidence.distance_ne_nonzero g' a' b' (4 : E) hlead
    (by norm_num) (a j) (c j) haj hcj
  simpa only [map_ofNat,ha',show algebraMap E K b'=b from rfl] using hn

end PlanarUnitDistances.GenericSheets

namespace PlanarUnitDistances.GenericSheets
open Polynomial
variable {B K : Type*} [Field B] [Field K] [Algebra B K]

lemma bivariate_eval_ne_zero (f : B[X][X]) (hf : f≠0)
    (x : Fin 2 → K) (hx : AlgebraicIndependent B x) :
      f.eval₂ (aeval (x 0)).toRingHom (x 1)≠0 := by
  have hh : (MvPolynomial.aeval x).comp (Bivariate.equivMvPolynomial B).toAlgHom =
      aevalAeval (x 0) (x 1) := by
    ext <;> simp
  intro h
  apply hf
  apply (Bivariate.equivMvPolynomial B).injective
  apply hx
  simpa only [map_zero,← GenericNoncoincidence.aevalAeval_eq_eval₂,
    ← hh,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom] using h

lemma other_block_independent {ι : Type*} {x : ι × Fin 2 → K}
    (hx : AlgebraicIndependent B x) {i j : ι} (hji : j≠i) :
    AlgebraicIndependent
      (algebraicClosure (IntermediateField.adjoin B ({x (i,0)} : Set K)) K)
      (fun k : Fin 2 => x (j,k)) := by
  apply AlgebraicIndependent.algebraicClosure
  apply IntermediateField.algebraicIndependent_adjoin_iff.mpr
  have hh := (AlgebraicIndependent.iff_adjoin_image {(i,(0 : Fin 2))}).mp hx
  let φ : Fin 2 → ↥(({(i,(0 : Fin 2))} : Set (ι × Fin 2))ᶜ) := fun k =>
    ⟨(j,k), by
      simp only [Set.mem_compl_iff,Set.mem_singleton_iff,Prod.mk.injEq,not_and]
      exact fun he => (hji he).elim⟩
  have hinj : Function.Injective φ := by
    intro a b he
    exact congrArg Prod.snd (congrArg Subtype.val he)
  have hh' := hh.2.comp φ hinj
  rw [Set.image_singleton] at hh'
  exact hh'

lemma independent_distance_ne (x : Fin 2 → K) (hx : AlgebraicIndependent B x)
    (a b k : B) (hk : k≠0) :
    (algebraMap B K a-x 0)*(algebraMap B K b-x 1)≠algebraMap B K k := by
  intro he
  let p : MvPolynomial (Fin 2) B :=
    (MvPolynomial.C a-MvPolynomial.X 0)*(MvPolynomial.C b-MvPolynomial.X 1)-MvPolynomial.C k
  have hp : p=0 := hx (by simpa [p,sub_eq_zero] using he)
  have hv := congrArg (MvPolynomial.eval (fun _ : Fin 2 => a)) hp
  simp only [p,map_sub,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,sub_self,
    zero_mul,zero_sub,map_zero,neg_eq_zero] at hv
  exact hk hv

theorem exists_private_sheet_plane [CharZero B] [CharZero K] [IsAlgClosed K]
    {ι : Type*} (f : B[X][X]) (hf : Irreducible f) (hfdeg : f.natDegree≠0)
    (x : ι × Fin 2 → K) (hx : AlgebraicIndependent B x) (i : ι) :
    ∃ b : K, f.eval₂ (aeval (x (i,0))).toRingHom b=0 ∧
      f.derivative.eval₂ (aeval (x (i,0))).toRingHom b≠0 ∧ b≠x (i,1) ∧
      ∀ j, j≠i → (x (i,0)-x (j,0))*(b-x (j,1))≠0 ∧
        (x (i,0)-x (j,0))*(b-x (j,1))≠4 := by
  have hi : AlgebraicIndependent B (fun k : Fin 2 => x (i,k)) :=
    hx.comp _ (fun _ _ he => Prod.mk.inj he |>.2)
  have halt := bivariate_eval_ne_zero f hf.ne_zero _ hi
  obtain ⟨b,hb,hbd,hbc⟩ := GenericCurve.exists_distinct_smooth_sheet f hf hfdeg
    (x (i,0)) (x (i,1)) (hi.transcendental 0) (Or.inl halt)
  refine ⟨b,hb,hbd,hbc,?_⟩
  let F := IntermediateField.adjoin B ({x (i,0)} : Set K)
  let E := algebraicClosure F K
  let ai : F := ⟨x (i,0), IntermediateField.subset_adjoin B _ (Set.mem_singleton _)⟩
  let a' : E := algebraMap F E ai
  have ha' : algebraMap E K a'=x (i,0) := by simp [a',ai]
  have hbalg : IsAlgebraic F b := fiber_algebraic f hf.ne_zero (x (i,0)) b
    (hi.transcendental 0) hb
  let b' : E := ⟨b, mem_algebraicClosure_iff.mpr hbalg⟩
  intro j hji
  have hj : AlgebraicIndependent E (fun k : Fin 2 => x (j,k)) :=
    other_block_independent hx hji
  have hn0 : x (i,0)≠x (j,0) := by
    intro he
    exact hji (congrArg Prod.fst (hx.injective he)).symm
  have hn1 : b≠x (j,1) := by
    intro he
    apply hj.transcendental 1
    rw [← he]
    exact isAlgebraic_algebraMap (R := E) b'
  refine ⟨mul_ne_zero (sub_ne_zero.mpr hn0) (sub_ne_zero.mpr hn1),?_⟩
  have hn := independent_distance_ne _ hj a' b' (4 : E) (by norm_num)
  simpa only [ha',map_ofNat,show algebraMap E K b'=b from rfl] using hn

end PlanarUnitDistances.GenericSheets

namespace PlanarUnitDistances.CurveValuations

universe u
variable {K : Type u} [Field K]

open Polynomial

theorem powerSeries_simple_root (f : (PowerSeries K)[X])
    (hlc : IsUnit f.leadingCoeff) (b : K)
    (hroot : f.eval₂ (PowerSeries.constantCoeff) b = 0)
    (hderiv : f.derivative.eval₂ (PowerSeries.constantCoeff) b ≠ 0) :
    ∃ w : PowerSeries K, f.eval w = 0 ∧ PowerSeries.constantCoeff w = b := by
  let I : Ideal (PowerSeries K) := Ideal.span {PowerSeries.X}
  let u : (PowerSeries K)ˣ := hlc.unit
  let g : (PowerSeries K)[X] := u⁻¹ • f
  have hg : g.Monic := monic_of_isUnit_leadingCoeff_inv_smul hlc
  have hb : g.eval (PowerSeries.C b) ∈ I := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simp only [g, Units.smul_def, eval_smul, smul_eq_mul, map_mul]
    rw [← eval₂_at_apply]
    simp only [PowerSeries.constantCoeff_C, hroot, mul_zero]
  have hd : IsUnit (g.derivative.eval (PowerSeries.C b)) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp only [g, Units.smul_def, derivative_smul, eval_smul, smul_eq_mul, map_mul]
    apply IsUnit.mul
    · exact (u⁻¹).isUnit.map PowerSeries.constantCoeff
    · apply isUnit_iff_ne_zero.mpr
      simpa only [← eval₂_at_apply, PowerSeries.constantCoeff_C] using hderiv
  obtain ⟨w, hw, hwmod⟩ := HenselianRing.is_henselian g hg (PowerSeries.C b) hb
    (hd.map (Ideal.Quotient.mk I))
  refine ⟨w, ?_, ?_⟩
  · change g.eval w = 0 at hw
    simpa [g, Units.smul_def] using hw
  · rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub,
      PowerSeries.constantCoeff_C, sub_eq_zero] at hwmod
    exact hwmod

open scoped LaurentSeries nonZeroDivisors

noncomputable def shiftPowerSeries (a : K) : K[X] →+* PowerSeries K :=
  Polynomial.coeToPowerSeries.ringHom.comp (algEquivAevalXAddC a).toRingHom

lemma shiftPowerSeries_injective (a : K) : Function.Injective (shiftPowerSeries a) :=
  (Polynomial.coe_injective K).comp (algEquivAevalXAddC a).injective

@[simp] lemma shiftPowerSeries_C (a c : K) :
    shiftPowerSeries a (C c) = PowerSeries.C c := by
  simp [shiftPowerSeries, algEquivAevalXAddC_apply]

@[simp] lemma shiftPowerSeries_X (a : K) :
    shiftPowerSeries a X = PowerSeries.X + PowerSeries.C a := by
  simp [shiftPowerSeries, algEquivAevalXAddC_apply]

lemma constantCoeff_comp_shiftPowerSeries (a : K) :
    PowerSeries.constantCoeff.comp (shiftPowerSeries a) = evalRingHom a := by
  ext c <;> simp

@[simp] lemma constantCoeff_shiftPowerSeries (a : K) (p : K[X]) :
    PowerSeries.constantCoeff (shiftPowerSeries a p) = p.eval a :=
  congrArg (fun φ : K[X] →+* K => φ p) (constantCoeff_comp_shiftPowerSeries a)

noncomputable def shiftLaurent (a : K) : K[X] →+* K⸨X⸩ :=
  (HahnSeries.ofPowerSeries ℤ K).comp (shiftPowerSeries a)

lemma shiftLaurent_injective (a : K) : Function.Injective (shiftLaurent a) :=
  HahnSeries.ofPowerSeries_injective.comp (shiftPowerSeries_injective a)

lemma shiftLaurent_regular (a : K) :
    K[X]⁰ ≤ (K⸨X⸩)⁰.comap (shiftLaurent a) := by
  intro p hp
  change shiftLaurent a p ∈ (K⸨X⸩)⁰
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro he
  apply (mem_nonZeroDivisors_iff_ne_zero.mp hp)
  apply shiftLaurent_injective a
  simpa using he

noncomputable def shiftRatFunc (a : K) : RatFunc K →+* K⸨X⸩ :=
  RatFunc.liftRingHom (shiftLaurent a) (shiftLaurent_regular a)

@[simp] lemma shiftRatFunc_polynomial (a : K) (p : K[X]) :
    shiftRatFunc a (algebraMap K[X] (RatFunc K) p) = shiftLaurent a p :=
  RatFunc.liftRingHom_algebraMap _ _ _

lemma shiftRatFunc_comp_algebraMap (a : K) :
    (shiftRatFunc a).comp (algebraMap K[X] (RatFunc K)) = shiftLaurent a := by
  exact RingHom.ext (shiftRatFunc_polynomial a)

theorem exists_smooth_branch (f : K[X][X]) (a b : K)
    (hlead : f.leadingCoeff.eval a ≠ 0)
    (hroot : f.eval₂ (evalRingHom a) b = 0)
    (hderiv : f.derivative.eval₂ (evalRingHom a) b ≠ 0) :
    ∃ w : PowerSeries K,
      (f.map (shiftPowerSeries a)).eval w = 0 ∧ PowerSeries.constantCoeff w = b := by
  apply powerSeries_simple_root
  · apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [leadingCoeff_map_of_injective (shiftPowerSeries_injective a),
      constantCoeff_shiftPowerSeries]
    exact isUnit_iff_ne_zero.mpr hlead
  · simpa only [eval₂_map, constantCoeff_comp_shiftPowerSeries] using hroot
  · simpa only [derivative_map, eval₂_map, constantCoeff_comp_shiftPowerSeries] using hderiv

abbrev CurveField (f : K[X][X]) := AdjoinRoot (f.map (algebraMap K[X] (RatFunc K)))

theorem exists_curve_branch_map (f : K[X][X]) (a b : K)
    (hlead : f.leadingCoeff.eval a ≠ 0)
    (hroot : f.eval₂ (evalRingHom a) b = 0)
    (hderiv : f.derivative.eval₂ (evalRingHom a) b ≠ 0) :
    ∃ (w : PowerSeries K) (φ : CurveField f →+* K⸨X⸩),
      PowerSeries.constantCoeff w = b ∧
      φ (AdjoinRoot.root _) = HahnSeries.ofPowerSeries ℤ K w ∧
      φ.comp (AdjoinRoot.of _) = shiftRatFunc a := by
  obtain ⟨w, hw, hwc⟩ := exists_smooth_branch f a b hlead hroot hderiv
  have he : (f.map (algebraMap K[X] (RatFunc K))).eval₂ (shiftRatFunc a)
      (HahnSeries.ofPowerSeries ℤ K w) = 0 := by
    rw [eval₂_map, shiftRatFunc_comp_algebraMap]
    have hh := congrArg (HahnSeries.ofPowerSeries ℤ K) hw
    simpa only [map_zero, ← eval₂_at_apply, eval₂_map, shiftLaurent] using hh
  exact ⟨w, AdjoinRoot.lift (shiftRatFunc a) (HahnSeries.ofPowerSeries ℤ K w) he,
    hwc, AdjoinRoot.lift_root he, AdjoinRoot.lift_comp_of he⟩

open WithZero Multiplicative

lemma laurent_valuation_powerSeries_unit {w : PowerSeries K}
    (hw : PowerSeries.constantCoeff w ≠ 0) :
    (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰) (HahnSeries.ofPowerSeries ℤ K w) = 1 := by
  rw [LaurentSeries.valuation_def, ← LaurentSeries.coe_algebraMap]
  apply (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
    (PowerSeries.idealX K)).mpr
  simpa [PowerSeries.idealX, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] using hw

lemma laurent_valuation_powerSeries_X :
    (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰)
      (HahnSeries.ofPowerSeries ℤ K PowerSeries.X) = WithZero.exp (-1 : ℤ) := by
  simpa using LaurentSeries.valuation_X_pow K 1

noncomputable def curveZ (f : K[X][X]) : CurveField f :=
  AdjoinRoot.of _ (algebraMap K[X] (RatFunc K) X)

noncomputable def curveC (f : K[X][X]) (c : K) : CurveField f :=
  AdjoinRoot.of _ (algebraMap K[X] (RatFunc K) (C c))

noncomputable def curveL (f : K[X][X]) (a c : K) : CurveField f :=
  (curveZ f - curveC f a) * (AdjoinRoot.root _ - curveC f c)

noncomputable def curveD (f : K[X][X]) (a c : K) : CurveField f :=
  curveL f a c * (curveL f a c - 4)

lemma curve_branch_map_of {f : K[X][X]} {a : K} {φ : CurveField f →+* K⸨X⸩}
    (hφ : φ.comp (AdjoinRoot.of _) = shiftRatFunc a) (p : K[X]) :
    φ (AdjoinRoot.of _ (algebraMap K[X] (RatFunc K) p)) = shiftLaurent a p := by
  have hh := congrArg (fun ψ : RatFunc K →+* K⸨X⸩ =>
    ψ (algebraMap K[X] (RatFunc K) p)) hφ
  simpa only [RingHom.comp_apply, shiftRatFunc_polynomial] using hh

lemma curve_branch_map_L {f : K[X][X]} {a : K} {w : PowerSeries K}
    {φ : CurveField f →+* K⸨X⸩}
    (hφ : φ.comp (AdjoinRoot.of _) = shiftRatFunc a)
    (hwφ : φ (AdjoinRoot.root _) = HahnSeries.ofPowerSeries ℤ K w) (d c : K) :
    φ (curveL f d c) = HahnSeries.ofPowerSeries ℤ K
      ((PowerSeries.X + PowerSeries.C (a-d)) * (w - PowerSeries.C c)) := by
  simp only [curveL, map_mul, map_sub, curveZ, curveC,
    curve_branch_map_of hφ, hwφ, shiftLaurent, RingHom.comp_apply,
    shiftPowerSeries_X, shiftPowerSeries_C]
  simp only [← map_sub, ← map_mul]
  congr 2
  simp only [map_sub]
  ring

theorem exists_curve_private_valuation [CharZero K]
    (f : K[X][X]) (a b c : K)
    (hlead : f.leadingCoeff.eval a ≠ 0)
    (hroot : f.eval₂ (evalRingHom a) b = 0)
    (hderiv : f.derivative.eval₂ (evalRingHom a) b ≠ 0)
    (hbc : b ≠ c) :
    ∃ v : Valuation (CurveField f) ℤᵐ⁰,
      v (curveD f a c) = WithZero.exp (-1 : ℤ) ∧
      ∀ d e : K, (a-d)*(b-e) ≠ 0 → (a-d)*(b-e) ≠ 4 →
        v (curveD f d e) = 1 := by
  obtain ⟨w, φ, hw, hwφ, hφ⟩ := exists_curve_branch_map f a b hlead hroot hderiv
  let v : Valuation (CurveField f) ℤᵐ⁰ :=
    (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).comap φ
  have hL (d e : K) : φ (curveL f d e) = HahnSeries.ofPowerSeries ℤ K
      ((PowerSeries.X + PowerSeries.C (a-d)) * (w - PowerSeries.C e)) :=
    curve_branch_map_L hφ hwφ d e
  have hval {p : PowerSeries K} (hp : PowerSeries.constantCoeff p ≠ 0) :
      (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰) (HahnSeries.ofPowerSeries ℤ K p) = 1 :=
    laurent_valuation_powerSeries_unit hp
  refine ⟨v, ?_, ?_⟩
  · have hLc : v (curveL f a c) = WithZero.exp (-1 : ℤ) := by
      change Valued.v (φ (curveL f a c)) = _
      rw [hL]
      simp only [sub_self, map_zero, add_zero, map_mul]
      rw [laurent_valuation_powerSeries_X, hval, mul_one]
      simpa [hw] using sub_ne_zero.mpr hbc
    have hL4 : v (curveL f a c - 4) = 1 := by
      change Valued.v (φ (curveL f a c - 4)) = _
      rw [map_sub, hL, map_ofNat]
      rw [← map_ofNat (HahnSeries.ofPowerSeries ℤ K) 4, ← map_sub]
      apply hval
      norm_num [hw, map_ofNat]
    rw [curveD, map_mul, hLc, hL4, mul_one]
  · intro d e hne hfour
    have hLc : v (curveL f d e) = 1 := by
      change Valued.v (φ (curveL f d e)) = _
      rw [hL]
      apply hval
      simpa [hw] using hne
    have hL4 : v (curveL f d e - 4) = 1 := by
      change Valued.v (φ (curveL f d e - 4)) = _
      rw [map_sub, hL, map_ofNat]
      rw [← map_ofNat (HahnSeries.ofPowerSeries ℤ K) 4, ← map_sub]
      apply hval
      simpa [hw, map_ofNat] using sub_ne_zero.mpr hfour
    rw [curveD, map_mul, hLc, hL4, one_mul]

end PlanarUnitDistances.CurveValuations

namespace PlanarUnitDistances.Radicals
open Polynomial CurveValuations
universe u
variable {k K L : Type u} [Field k] [Field K] [CharZero K] [Field L]
  [Algebra k L] [Algebra K L]

theorem curve_differential_obstruction (D : Derivation k L L)
    (f : K[X][X]) (hf : Irreducible f) (hfdeg : f.natDegree≠0)
    (z w : L) (hz : Transcendental K z)
    (hroot : f.eval₂ (aeval z).toRingHom w=0)
    (a b da db t : Fin 4 → K)
    (hsheet : ∀ i, ∃ c : K, f.leadingCoeff.eval (a i)≠0 ∧
      f.eval₂ (evalRingHom (a i)) c=0 ∧ f.derivative.eval₂ (evalRingHom (a i)) c≠0 ∧
      c≠b i ∧ ∀ j, j≠i → (a i-a j)*(c-b j)≠0 ∧ (a i-a j)*(c-b j)≠4)
    (l : Fin 4 → L) (A : L) (hl : ∀ i, l i≠0)
    (hdist : ∀ i, (z-algebraMap K L (a i))*(w-algebraMap K L (b i))=2-l i-(l i)⁻¹)
    (hda : ∀ i, D (algebraMap K L (a i))=algebraMap K L (da i))
    (hdb : ∀ i, D (algebraMap K L (b i))=algebraMap K L (db i))
    (hlog : ∀ i, D (l i)/l i=A-algebraMap K L (t i))
    (hD : ∀ i, D (l i)≠0) : False := by
  let : Fact (Irreducible (f.map (algebraMap K[X] (RatFunc K)))) :=
    ⟨GenericCurve.irreducible_fraction_curve f hf hfdeg⟩
  let : CharZero (CurveField f) :=
    charZero_of_injective_algebraMap (algebraMap K (CurveField f)).injective
  obtain ⟨φ,hφ,hφw,hφp⟩ := GenericCurve.exists_curve_embedding f hf hfdeg z w hz hroot
  have hφz : φ (curveZ f)=z := by simpa only [curveZ,aeval_X] using hφp X
  have hφc (c : K) : φ (curveC f c)=algebraMap K L c := by
    simpa only [curveC,aeval_C] using hφp (C c)
  have hind : SquareIndependent (List.ofFn (fun i => curveD f (a i) (b i))) := by
    have hh := squareIndependent_of_private_valuations
      (List.ofFn (id : Fin 4 → Fin 4)) (List.nodup_ofFn.mpr Function.injective_id)
      (fun i => curveD f (a i) (b i)) ?_
    · simpa only [List.map_ofFn,Function.comp_def,id_eq] using hh
    intro i _
    obtain ⟨c,hlead,hc,hcd,hcb,hcs⟩ := hsheet i
    obtain ⟨v,hv,hw⟩ := exists_curve_private_valuation f (a i) c (b i) hlead hc hcd hcb
    exact ⟨v,hv,fun j _ hji => hw _ _ (hcs j hji).1 (hcs j hji).2⟩
  apply differential_distance_obstruction D φ.toRingHom (curveZ f) (AdjoinRoot.root _)
    (curveC f ∘ a) (curveC f ∘ b) (curveC f ∘ da) (curveC f ∘ db) (curveC f ∘ t)
    l A hind hl
  · intro i; simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
      hφz,hφw,Function.comp_apply,hφc] using hdist i
  · intro i; simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
      Function.comp_apply,hφc] using hda i
  · intro i; simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
      Function.comp_apply,hφc] using hdb i
  · intro i; simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
      Function.comp_apply,hφc] using hlog i
  · exact hD
end PlanarUnitDistances.Radicals

namespace PlanarUnitDistances.GenericSheets
open Polynomial BivariateMaps
variable {B K : Type*} [Field B] [Field K] [Algebra B K]

lemma mapped_leading_eval (f : B[X][X]) (a : K) :
    (bimap (algebraMap B K) f).leadingCoeff.eval a=aeval a f.leadingCoeff := by
  dsimp only [BivariateMaps.bimap,coe_mapRingHom]
  rw [leadingCoeff_map_of_injective (f := Polynomial.mapRingHom (algebraMap B K))
    (Polynomial.map_injective _ (algebraMap B K).injective)]
  change (f.leadingCoeff.map (algebraMap B K)).eval a=_
  rw [eval_map,← aeval_def]

lemma mapped_eval (f : B[X][X]) (a b : K) :
    (bimap (algebraMap B K) f).eval₂ (evalRingHom a) b=f.eval₂ (aeval a).toRingHom b := by
  have hh := BivariateMaps.eval_bimap (K := K) f a b
  have he : (aeval a : K[X] →ₐ[K] K).toRingHom=evalRingHom a := by
    ext c <;> simp
  simpa only [he] using hh

lemma mapped_derivative_eval (f : B[X][X]) (a b : K) :
    (bimap (algebraMap B K) f).derivative.eval₂ (evalRingHom a) b=
      f.derivative.eval₂ (aeval a).toRingHom b := by
  change (f.map (Polynomial.mapRingHom (algebraMap B K))).derivative.eval₂ _ _=_
  rw [derivative_map]
  exact mapped_eval f.derivative a b
end PlanarUnitDistances.GenericSheets

namespace PlanarUnitDistances.Radicals
open Polynomial BivariateMaps
universe u
variable {k B K L : Type u} [Field k] [Field B] [CharZero B] [Field K] [CharZero K]
  [Field L] [Algebra k L] [Algebra B K] [Algebra K L] [IsAlgClosed K]

theorem curve_curve_differential_obstruction (D : Derivation k L L)
    (f g : B[X][X]) (hfK : Irreducible (bimap (algebraMap B K) f))
    (hfdeg : f.natDegree≠0) (hgK : Irreducible (bimap (algebraMap B K) g))
    (hgswap : (Bivariate.swap g).natDegree≠0)
    (z w : L) (hz : Transcendental K z)
    (hroot : (bimap (algebraMap B K) f).eval₂ (aeval z).toRingHom w=0)
    (a b da db t : Fin 4 → K) (ha : AlgebraicIndependent B a)
    (hb : ∀ i, g.eval₂ (aeval (a i)).toRingHom (b i)=0)
    (halt : ∀ i, f.eval₂ (aeval (a i)).toRingHom (b i)≠0 ∨ 2≤f.natDegree)
    (l : Fin 4 → L) (A : L) (hl : ∀ i, l i≠0)
    (hdist : ∀ i, (z-algebraMap K L (a i))*(w-algebraMap K L (b i))=2-l i-(l i)⁻¹)
    (hda : ∀ i, D (algebraMap K L (a i))=algebraMap K L (da i))
    (hdb : ∀ i, D (algebraMap K L (b i))=algebraMap K L (db i))
    (hlog : ∀ i, D (l i)/l i=A-algebraMap K L (t i))
    (hD : ∀ i, D (l i)≠0) : False := by
  apply curve_differential_obstruction D _ hfK (by simpa only [bimap_natDegree] using hfdeg)
    z w hz hroot a b da db t ?_ l A hl hdist hda hdb hlog hD
  intro i
  have hf := irreducible_of_bimap (algebraMap B K) hfK
  obtain ⟨c,hc,hcd,hcb,hcs⟩ := GenericSheets.exists_private_sheet_curve f g hf hfdeg hgK
    hgswap a b ha hb i (halt i)
  refine ⟨c,?_,?_,?_,hcb,hcs⟩
  · rw [GenericSheets.mapped_leading_eval]
    exact GenericCurve.fiber_leadingCoeff_ne_zero f hf.ne_zero (a i) (ha.transcendental i)
  · simpa only [GenericSheets.mapped_eval] using hc
  · simpa only [GenericSheets.mapped_derivative_eval] using hcd

theorem curve_plane_differential_obstruction (D : Derivation k L L)
    (f : B[X][X]) (hfK : Irreducible (bimap (algebraMap B K) f)) (hfdeg : f.natDegree≠0)
    (z w : L) (hz : Transcendental K z)
    (hroot : (bimap (algebraMap B K) f).eval₂ (aeval z).toRingHom w=0)
    (x : Fin 4 × Fin 2 → K) (hx : AlgebraicIndependent B x) (da db t : Fin 4 → K)
    (l : Fin 4 → L) (A : L) (hl : ∀ i, l i≠0)
    (hdist : ∀ i, (z-algebraMap K L (x (i,0)))*(w-algebraMap K L (x (i,1)))=2-l i-(l i)⁻¹)
    (hda : ∀ i, D (algebraMap K L (x (i,0)))=algebraMap K L (da i))
    (hdb : ∀ i, D (algebraMap K L (x (i,1)))=algebraMap K L (db i))
    (hlog : ∀ i, D (l i)/l i=A-algebraMap K L (t i))
    (hD : ∀ i, D (l i)≠0) : False := by
  apply curve_differential_obstruction D _ hfK (by simpa only [bimap_natDegree] using hfdeg)
    z w hz hroot (fun i=>x (i,0)) (fun i=>x (i,1)) da db t ?_ l A hl hdist hda hdb hlog hD
  intro i
  have hf := irreducible_of_bimap (algebraMap B K) hfK
  obtain ⟨c,hc,hcd,hcb,hcs⟩ := GenericSheets.exists_private_sheet_plane f hf hfdeg x hx i
  refine ⟨c,?_,?_,?_,hcb,hcs⟩
  · rw [GenericSheets.mapped_leading_eval]
    exact GenericCurve.fiber_leadingCoeff_ne_zero f hf.ne_zero (x (i,0)) (hx.transcendental (i,0))
  · simpa only [GenericSheets.mapped_eval] using hc
  · simpa only [GenericSheets.mapped_derivative_eval] using hcd
end PlanarUnitDistances.Radicals

end OAI
