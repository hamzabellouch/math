import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.PrincipalModules
variable {R : Type*} [Ring R] [IsDomain R]

def IsTorsionModule (R : Type*) [Ring R] (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  ∀ m : M, ∃ a : R, a ≠ 0 ∧ a • m = 0

section LeftPrincipal
variable [IsPrincipalIdealRing R]

lemma ideal_free (I : Ideal R) : Module.Free R I := by
  classical
  by_cases hI : I = ⊥
  · subst I
    infer_instance
  · let d : R := Submodule.IsPrincipal.generator I
    have hd : d ≠ 0 := by
      intro hd
      exact hI ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).mpr hd)
    let f : R →ₗ[R] I := (LinearMap.mulRight R d).codRestrict I
      (fun a => I.smul_mem a (Submodule.IsPrincipal.generator_mem I))
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        have hab' : a * d = b * d := congrArg Subtype.val hab
        exact mul_right_cancel₀ hd hab'
      · intro x
        obtain ⟨a,ha⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp x.property
        exact ⟨a, Subtype.ext ha.symm⟩
    exact Module.Free.of_equiv (LinearEquiv.ofBijective f hf)

def splitEquiv {M P : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] P) (s : P →ₗ[R] M)
    (hs : f.comp s = .id) : (f.ker × P) ≃ₗ[R] M := by
  let u : f.ker × P →ₗ[R] M := f.ker.subtype.coprod s
  have hsf (p : P) : f (s p) = p := LinearMap.congr_fun hs p
  apply LinearEquiv.ofBijective u
  constructor
  · rintro ⟨k,p⟩ ⟨l,q⟩ h
    have hpq : p = q := by
      have := congrArg f h
      simpa [u, hsf, k.property, l.property] using this
    subst q
    have hkl : (k : M) = (l : M) := by simpa [u] using h
    exact Prod.ext (Subtype.ext hkl) rfl
  · intro m
    refine ⟨(⟨m - s (f m), ?_⟩, f m), ?_⟩
    · simp [LinearMap.mem_ker, hsf]
    · simp [u]

theorem finite_free_submodule (n : ℕ) (N : Submodule R (Fin n → R)) :
    Module.Free R N ∧ Module.Finite R N := by
  classical
  constructor
  swap
  · exact Module.Finite.of_injective N.subtype N.subtype_injective
  induction n with
  | zero => infer_instance
  | succ n ih =>
      let f : N →ₗ[R] R := (LinearMap.proj (0 : Fin (n + 1))).comp N.subtype
      let φ : N →ₗ[R] f.range := f.rangeRestrict
      let tail : φ.ker →ₗ[R] (Fin n → R) :=
        LinearMap.pi (fun i => (LinearMap.proj i.succ).comp (N.subtype.comp φ.ker.subtype))
      have ht : Function.Injective tail := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · have hx : ((x : N) : Fin (n + 1) → R) 0 = 0 := by
            have := congrArg Subtype.val x.property
            exact this
          have hy : ((y : N) : Fin (n + 1) → R) 0 = 0 := by
            have := congrArg Subtype.val y.property
            exact this
          exact hx.trans hy.symm
        · exact congrFun hxy j
      have hk : Module.Free R φ.ker := by
        let : Module.Free R tail.range := ih tail.range
        exact Module.Free.of_equiv (LinearEquiv.ofInjective tail ht).symm
      let : Module.Free R φ.ker := hk
      let : Module.Free R f.range := ideal_free f.range
      obtain ⟨s,hs⟩ := φ.exists_rightInverse_of_surjective
        (LinearMap.range_eq_top.mpr (by
          rintro ⟨y, x, rfl⟩
          exact ⟨x, rfl⟩))
      exact Module.Free.of_equiv (splitEquiv φ s hs)

lemma common_left_multiple (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ u v : R, u ≠ 0 ∧ v ≠ 0 ∧ u * a = v * b := by
  classical
  by_contra h
  have hn : ∀ u v : R, u * a = v * b → u = 0 ∧ v = 0 := by
    intro u v huv
    by_cases hu : u = 0
    · exact ⟨hu, (mul_eq_zero.mp (by simpa [hu] using huv.symm)).resolve_right hb⟩
    · have hv : v ≠ 0 := by
        intro hv
        have : u * a = 0 := by simpa [hv] using huv
        exact (mul_ne_zero hu ha) this
      exact False.elim (h ⟨u,v,hu,hv,huv⟩)
  let f : R × R →ₗ[R] R := (LinearMap.mulRight R a).coprod (LinearMap.mulRight R b)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    apply (Submodule.eq_bot_iff _).mpr
    rintro ⟨u,v⟩ huv
    have he : u * a = (-v) * b := by
      have he : u * a + v * b = 0 := huv
      rw [neg_mul]
      exact eq_neg_of_add_eq_zero_left he
    obtain ⟨hu,hv⟩ := hn u (-v) he
    have hv' : v = 0 := neg_eq_zero.mp hv
    simp [hu,hv']
  have : Subsingleton R := IsNoetherian.subsingleton_of_injective hf
  exact (zero_ne_one : (0 : R) ≠ 1) (Subsingleton.elim _ _)

@[instance_reducible]
noncomputable def principalOreSet : OreLocalization.OreSet (nonZeroDivisors R) := by
  classical
  apply Classical.choice
  rw [OreLocalization.nonempty_oreSet_iff_of_noZeroDivisors]
  intro r s
  by_cases hr : r = 0
  · exact ⟨0, 1, by simp [hr]⟩
  · obtain ⟨u,v,hu,hv,h⟩ := common_left_multiple r s hr (nonZeroDivisors.coe_ne_zero s)
    exact ⟨v, ⟨u, mem_nonZeroDivisors_of_ne_zero hu⟩, h⟩

theorem finite_free_resolution
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (n m : ℕ) (f : (Fin m → R) →ₗ[R] (Fin n → R))
      (g : (Fin n → R) →ₗ[R] M),
      Function.Injective f ∧ Function.Surjective g ∧ LinearMap.range f = LinearMap.ker g := by
  classical
  obtain ⟨n,v,hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let g : (Fin n → R) →ₗ[R] M := Fintype.linearCombination R v
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top]
    exact (Fintype.range_linearCombination R v).trans hv
  obtain ⟨hfree,hfin⟩ := finite_free_submodule n g.ker
  let := hfree
  let := hfin
  let m := Module.finrank R g.ker
  let e : (Fin m → R) ≃ₗ[R] g.ker := (Module.finBasis R g.ker).equivFun.symm
  let f : (Fin m → R) →ₗ[R] (Fin n → R) := g.ker.subtype.comp e.toLinearMap
  refine ⟨n,m,f,g,g.ker.subtype_injective.comp e.injective,hg,?_⟩
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact (e y).property
  · intro hx
    exact ⟨e.symm ⟨x,hx⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩

end LeftPrincipal

section Localization
variable [IsPrincipalIdealRing R]
local instance principalModulesOreSet : OreLocalization.OreSet (nonZeroDivisors R) :=
  principalOreSet
open OreLocalization

abbrev FractionRing (R : Type*) [Ring R] [IsDomain R] [IsPrincipalIdealRing R] :=
  OreLocalization (nonZeroDivisors R) R

variable (M : Type*) [AddCommGroup M] [Module R M]

def moduleNumerator : M →ₗ[R] OreLocalization (nonZeroDivisors R) M where
  toFun m := m /ₒ (1 : nonZeroDivisors R)
  map_add' _ _ := add_oreDiv.symm
  map_smul' _ _ := (smul_oreDiv_one _ _).symm

lemma numerator_eq_zero_iff (m : M) : moduleNumerator (R := R) M m = 0 ↔
    ∃ a : R, a ≠ 0 ∧ a • m = 0 := by
  change m /ₒ (1 : nonZeroDivisors R) = 0 ↔ _
  rw [← zero_oreDiv (1 : nonZeroDivisors R), oreDiv_eq_iff]
  constructor
  · rintro ⟨u,v,hu,hv⟩
    have huv : (u : R) = v := by simpa using hv
    exact ⟨v, huv ▸ nonZeroDivisors.coe_ne_zero u, by simpa using hu.symm⟩
  · rintro ⟨a,ha,ham⟩
    exact ⟨⟨a,mem_nonZeroDivisors_of_ne_zero ha⟩,a,by simp [ham],by simp⟩

lemma localization_finite [Module.Finite R M] :
    Module.Finite (FractionRing R) (OreLocalization (nonZeroDivisors R) M) := by
  classical
  obtain ⟨n,v,hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let K := Submodule.span (FractionRing R) (Set.range (moduleNumerator (R := R) M ∘ v))
  have hm (m : M) : moduleNumerator (R := R) M m ∈ K := by
    have hmem : m ∈ Submodule.span R (Set.range v) := by rw [hv]; trivial
    induction hmem using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i,rfl⟩ := hx
        exact Submodule.subset_span ⟨i,rfl⟩
    | zero => simp
    | add x y hx hy hx' hy' => simpa using K.add_mem hx' hy'
    | smul a x hx hx' =>
        have := K.smul_mem (a /ₒ (1 : nonZeroDivisors R)) hx'
        change (a • x) /ₒ (1 : nonZeroDivisors R) ∈ K
        simpa only [moduleNumerator, LinearMap.coe_mk, AddHom.coe_mk, smul_div_one] using this
  have hK : K = ⊤ := by
    apply top_unique
    intro x hx
    induction x using OreLocalization.ind with
    | c m s =>
        have := K.smul_mem ((1 : R) /ₒ s) (hm m)
        simpa [moduleNumerator, smul_div_one] using this
  exact Module.Finite.of_fg_top
    (Submodule.fg_iff_exists_fin_generating_family.mpr ⟨n,_,hK⟩)

variable [IsPrincipalIdealRing Rᵐᵒᵖ]

omit [IsPrincipalIdealRing R] in
lemma common_right_multiple (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ u v : R, u ≠ 0 ∧ v ≠ 0 ∧ a * u = b * v := by
  obtain ⟨u,v,hu,hv,h⟩ := common_left_multiple (MulOpposite.op a) (MulOpposite.op b)
    (by simpa using ha) (by simpa using hb)
  exact ⟨u.unop,v.unop,by simpa using hu,by simpa using hv,
    congrArg MulOpposite.unop h⟩

lemma right_denominator (q : FractionRing R) :
    ∃ b : R, b ≠ 0 ∧ ∃ a : R,
      q * OreLocalization.numeratorRingHom b = OreLocalization.numeratorRingHom a := by
  induction q using OreLocalization.ind with
  | c r s =>
    by_cases hr : r = 0
    · exact ⟨1,one_ne_zero,0,by simp [hr]⟩
    obtain ⟨u,v,hu,hv,h⟩ := common_right_multiple r s hr (nonZeroDivisors.coe_ne_zero s)
    refine ⟨u,hu,v,?_⟩
    change (r /ₒ s) * (u /ₒ (1 : nonZeroDivisors R)) = v /ₒ (1 : nonZeroDivisors R)
    rw [mul_div_one,h]
    simpa [Submonoid.smul_def, smul_eq_mul] using (OreLocalization.expand' v (1 : nonZeroDivisors R) s).symm

lemma common_right_denominator (s : Finset (FractionRing R)) :
    ∃ b : R, b ≠ 0 ∧ ∀ q ∈ s, ∃ a : R,
      q * OreLocalization.numeratorRingHom b = OreLocalization.numeratorRingHom a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1,one_ne_zero,by simp⟩
  | @insert q s hqs ih =>
    obtain ⟨b,hb,hb'⟩ := ih
    obtain ⟨d,hd,a,ha⟩ := right_denominator q
    obtain ⟨u,v,hu,hv,he⟩ := common_right_multiple b d hb hd
    refine ⟨b*u,mul_ne_zero hb hu,?_⟩
    intro z hz
    obtain rfl | hz := Finset.mem_insert.mp hz
    · refine ⟨a*v,?_⟩
      rw [he,map_mul,←mul_assoc,ha,map_mul]
    · obtain ⟨c,hc⟩ := hb' z hz
      refine ⟨c*u,?_⟩
      rw [map_mul,←mul_assoc,hc,map_mul]

lemma integral_coordinate [Module.Finite R M]
    (g : M →ₗ[R] FractionRing R) :
    ∃ f : M →ₗ[R] R, ∀ m, f m = 0 ↔ g m = 0 := by
  classical
  obtain ⟨n,v,hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  obtain ⟨b,hb,hb'⟩ := common_right_denominator (Finset.univ.image (g ∘ v))
  let ν : R →ₗ[R] FractionRing R := moduleNumerator (R := R) R
  have hν : Function.Injective ν := OreLocalization.numeratorHom_inj inf_le_left
  let h : M →ₗ[R] FractionRing R := (LinearMap.mulRight R (ν b)).comp g
  have hmem (m : M) : h m ∈ ν.range := by
    have hvm : m ∈ Submodule.span R (Set.range v) := by rw [hv]; trivial
    induction hvm using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨j,rfl⟩ := hx
        obtain ⟨a,ha⟩ := hb' (g (v j)) (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
        exact ⟨a,ha.symm⟩
    | zero => simp
    | add x y hx hy hx' hy' => simpa only [map_add] using ν.range.add_mem hx' hy'
    | smul a x hx hx' => simpa only [map_smul] using ν.range.smul_mem a hx'
  let e : R ≃ₗ[R] ν.range := LinearEquiv.ofInjective ν hν
  let f : M →ₗ[R] R := e.symm.toLinearMap.comp (h.codRestrict ν.range hmem)
  have hfh (m : M) : ν (f m) = h m := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨h m,hmem m⟩)
  have hνb : ν b ≠ 0 := by
    intro he
    exact hb (hν (he.trans (map_zero ν).symm))
  refine ⟨f,?_⟩
  intro m
  constructor
  · intro hm
    have he : h m = 0 := by rw [←hfh,hm,map_zero]
    exact (mul_eq_zero.mp he).resolve_right hνb
  · intro hm
    apply hν
    rw [hfh,map_zero]
    change g m * ν b = 0
    rw [hm,zero_mul]

lemma torsion_kernel_map [Module.Finite R M] :
    ∃ (n : ℕ) (f : M →ₗ[R] (Fin n → R)),
      ∀ m, f m = 0 ↔ ∃ a : R, a ≠ 0 ∧ a • m = 0 := by
  classical
  let := localization_finite (R := R) M
  let Q := FractionRing R
  let V := OreLocalization (nonZeroDivisors R) M
  let n := Module.finrank Q V
  let e : V ≃ₗ[Q] (Fin n → Q) := (Module.finBasis Q V).equivFun
  let g : M →ₗ[R] (Fin n → Q) :=
    (e.restrictScalars R).toLinearMap.comp (moduleNumerator (R := R) M)
  have hi (i : Fin n) := integral_coordinate M ((LinearMap.proj i).comp g)
  choose f hf using hi
  refine ⟨n,LinearMap.pi f,?_⟩
  intro m
  rw [←numerator_eq_zero_iff]
  constructor
  · intro hm
    apply e.injective
    rw [map_zero]
    funext i
    exact (hf i m).mp (congrFun hm i)
  · intro hm
    apply funext
    intro i
    apply (hf i m).mpr
    change e (moduleNumerator (R := R) M m) i = 0
    rw [hm,map_zero]
    rfl

end Localization

theorem torsion_free_decomposition [IsPrincipalIdealRing R] [IsPrincipalIdealRing Rᵐᵒᵖ]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (T Q : Submodule R M), IsCompl T Q ∧ IsTorsionModule R T ∧
      Module.Free R Q ∧ Module.Finite R Q := by
  classical
  obtain ⟨n,f,hf⟩ := torsion_kernel_map (R := R) M
  obtain ⟨hfree,hfin⟩ := finite_free_submodule n f.range
  let := hfree
  let := hfin
  let φ : M →ₗ[R] f.range := f.rangeRestrict
  have hφ : Function.Surjective φ := by
    rintro ⟨y,x,rfl⟩
    exact ⟨x,rfl⟩
  obtain ⟨s,hs⟩ := φ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hφ)
  have hsf (y : f.range) : φ (s y) = y := LinearMap.congr_fun hs y
  have hsi : Function.Injective s := by
    intro x y hxy
    have := congrArg φ hxy
    simpa [hsf] using this
  refine ⟨φ.ker,s.range,?_,?_,Module.Free.of_equiv (LinearEquiv.ofInjective s hsi),
    Module.Finite.equiv (LinearEquiv.ofInjective s hsi)⟩
  · constructor
    · apply Submodule.disjoint_def.mpr
      intro x hx hxs
      obtain ⟨y,rfl⟩ := hxs
      have hy : y = 0 := (hsf y).symm.trans hx
      simp [hy]
    · rw [codisjoint_iff]
      apply top_unique
      intro m hm
      apply Submodule.mem_sup.mpr
      refine ⟨m-s (φ m),?_,s (φ m),⟨φ m,rfl⟩,by simp⟩
      simp [LinearMap.mem_ker,hsf]
  · intro m
    have hfm : f m = 0 := congrArg Subtype.val m.property
    obtain ⟨a,ha,ham⟩ := (hf m).mp hfm
    exact ⟨a,ha,Subtype.ext ham⟩

end HahnWilson.PrincipalModules

end

end OAI
