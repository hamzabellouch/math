import OAI.Algebra.Determinantal.Monogenic

namespace OAI

namespace PermanentBorder.FrobeniusDVR
open IsDiscreteValuationRing
variable {K B : Type*} [CommRing K] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra K B]
local notation "v" => addVal B

lemma valuation_le_derivation_add_one (D : Derivation K B B) (z : B) :
    v z ≤ v (D z) + 1 := by
  obtain ⟨π,hπ⟩ := exists_irreducible B
  by_cases hz : z = 0
  · simp [hz, map_zero]
  obtain ⟨n,hn⟩ := associated_pow_irreducible hz hπ
  obtain ⟨u,hu⟩ := hn.symm
  rw [← hu]
  cases n with
  | zero => simp [pow_zero, addVal_eq_zero_of_unit]
  | succ n =>
    have hdiv : π^(n+1) ∣ π * D (π^(n+1) * ↑u) := by
      rw [Derivation.leibniz, Derivation.leibniz_pow]
      simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul]
      refine ⟨(n+1 : B) * D π * ↑u + π * D ↑u, ?_⟩
      rw [pow_succ]
      push_cast
      ring
    have hv := (addVal_le_iff_dvd (R := B)).mpr hdiv
    rw [hπ.addVal_pow, addVal_mul, addVal_uniformizer hπ] at hv
    simpa only [addVal_mul, hπ.addVal_pow, addVal_eq_zero_of_unit, add_zero,
      add_comm (1 : ℕ∞)] using hv

variable [CharP B 2]

omit [IsDomain B] [IsDiscreteValuationRing B] in
lemma derivation_square (D : Derivation K B B) (a : B) : D (a^2) = 0 := by
  have htwo : (2 : B) = 0 := CharP.cast_eq_zero _ 2
  simp [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, htwo]

omit [IsDomain B] [IsDiscreteValuationRing B] in
lemma derivation_square_plus (D : Derivation K B B) (x c d : B) :
    D (c^2+x*d^2) = D x * d^2 := by
  rw [map_add, derivation_square, Derivation.leibniz, derivation_square]
  simp only [smul_eq_mul, mul_zero, zero_add]
  exact mul_comm _ _

lemma valuation_square_plus_le (D : Derivation K B B) (x c d : B) :
    v (c^2+x*d^2) ≤ v (D x) + 2*v d + 1 := by
  have h := valuation_le_derivation_add_one D (c^2+x*d^2)
  simpa only [derivation_square_plus, addVal_mul, addVal_pow,
    nsmul_eq_mul, Nat.cast_ofNat] using h

omit [CharP B 2] in
lemma valuation_square_plus_of_lower (x c d : B) (m : ℕ)
    (hx : 1 ≤ v x) (hc : v c = m) (hd : (m : ℕ∞) ≤ v d) :
    v (c^2+x*d^2) = 2*m := by
  have hs : v (c^2) < v (x*d^2) := by
    rw [addVal_pow, addVal_mul, addVal_pow, nsmul_eq_mul, nsmul_eq_mul, hc,
      Nat.cast_ofNat]
    have hh : (2 : ℕ∞)*m+1 ≤ v x+2*v d := by
      calc
        (2 : ℕ∞)*m+1 = 1+2*m := by ac_rfl
        _ ≤ v x+2*v d := add_le_add hx (mul_le_mul_of_nonneg_left hd zero_le)
    have ht : (2 : ℕ∞)*m < 2*m+1 := by norm_cast; omega
    exact ht.trans_le hh
  rw [(addVal B).map_add_eq_of_lt_left hs, addVal_pow, nsmul_eq_mul, hc, Nat.cast_ofNat]

omit [IsDomain B] [IsDiscreteValuationRing B] in
lemma branch_chain (D : Derivation K B B) (x y a b c d : B)
    (h : a^2+x*b^2+y*c^2+x*y*d^2 = 0) :
    (b^2+y*d^2) * D x + (c^2+x*d^2)*D y = 0 := by
  have hh := congrArg D h
  simp only [map_add, Derivation.leibniz, derivation_square, map_zero, zero_add] at hh
  convert hh using 1
  simp only [smul_eq_mul]
  ring

lemma valuation_square_plus_le_square (D : Derivation K B B) (x c d : B)
    (hx : 1 ≤ (v x)) :
    (v (c^2+x*d^2)) ≤ (v (D x)) + (v (c^2)) := by
  by_cases hc : c = 0
  · simp [hc]
  have hcfin : (v c) ≠ ⊤ := (addVal_eq_top_iff (R := B)).not.mpr hc
  have hcEq : (v c) = (v c).toNat := (ENat.natCast_toNat hcfin).symm
  by_cases hcd : (v c) ≤ (v d)
  · rw [valuation_square_plus_of_lower x c d _ hx hcEq (hcEq ▸ hcd)]
    rw [addVal_pow, nsmul_eq_mul, Nat.cast_ofNat, hcEq]
    exact le_add_of_nonneg_left zero_le
  · have hdc : (v d) < (v c) := lt_of_not_ge hcd
    have hdfin : (v d) ≠ ⊤ := ne_top_of_lt hdc
    have hn : (v d).toNat < (v c).toNat := by
      exact_mod_cast (by simpa only [ENat.natCast_toNat hcfin, ENat.natCast_toNat hdfin] using hdc :
        ((v d).toNat : ℕ∞) < (v c).toNat)
    have ht : (2 : ℕ∞)*(v d)+1 ≤ (v (c^2)) := by
      rw [addVal_pow, nsmul_eq_mul, Nat.cast_ofNat,
        ← ENat.natCast_toNat hcfin, ← ENat.natCast_toNat hdfin]
      exact_mod_cast (by omega : 2*(v d).toNat+1 ≤ 2*(v c).toNat)
    calc
      (v (c^2+x*d^2)) ≤ (v (D x))+2*(v d)+1 :=
        valuation_square_plus_le D x c d
      _ = (v (D x))+(2*(v d)+1) := by ac_rfl
      _ ≤ (v (D x))+(v (c^2)) := add_le_add_right ht _

lemma valuation_square_plus_le_coordinate (D : Derivation K B B) (x y c d : B)
    (hy : 1 ≤ (v y)) :
    (v (c^2+x*d^2)) ≤ (v (D x)) + (v (y*d^2)) := by
  have ht : (2 : ℕ∞)*(v d)+1 ≤ (v (y*d^2)) := by
    rw [addVal_mul, addVal_pow, nsmul_eq_mul, Nat.cast_ofNat]
    simpa only [add_comm] using add_le_add_left hy (2*(v d))
  calc
    (v (c^2+x*d^2)) ≤ (v (D x))+2*(v d)+1 :=
      valuation_square_plus_le D x c d
    _ = (v (D x))+(2*(v d)+1) := by ac_rfl
    _ ≤ (v (D x))+(v (y*d^2)) := add_le_add_right ht _

theorem conductor_generators_valuation (D : Derivation K B B) (x y a b c d : B)
    (hx : 1 ≤ (v x)) (hy : 1 ≤ (v y))
    (h : a^2+x*b^2+y*c^2+x*y*d^2 = 0) :
    (v (c^2+x*d^2)) ≤ (v (D x)) + (v (a^2)) ∧
    (v (c^2+x*d^2)) ≤ (v (D x)) + (v (b^2)) ∧
    (v (c^2+x*d^2)) ≤ (v (D x)) + (v (c^2)) ∧
    (v (c^2+x*d^2)) ≤ (v (D x)) + (v (x*d^2)) ∧
    (v (c^2+x*d^2)) ≤ (v (D x)) + (v (y*d^2)) := by
  have hc := valuation_square_plus_le_square D x c d hx
  have hxd := valuation_square_plus_le_coordinate D x x c d hx
  have hyd := valuation_square_plus_le_coordinate D x y c d hy
  have hb : (v (c^2+x*d^2)) ≤ (v (D x))+(v (b^2)) := by
    by_cases hdy : D y = 0
    · by_cases hdx : D x = 0
      · simp [hdx]
      have he := branch_chain D x y a b c d h
      rw [hdy, mul_zero, add_zero] at he
      have hf := (mul_eq_zero.mp he).resolve_right hdx
      have hby : b^2 = y*d^2 := CharTwo.add_eq_zero.mp hf
      rw [hby]
      exact hyd
    have hb' := valuation_square_plus_le_square D y b d hy
    have hh := branch_chain D x y a b c d h
    have he := congrArg (addVal B) (CharTwo.add_eq_zero.mp hh)
    rw [addVal_mul, addVal_mul] at he
    have hdyle : (v (D y)) ≠ ⊤ := (addVal_eq_top_iff (R := B)).not.mpr hdy
    apply ENat.add_le_add_iff_right hdyle |>.mp
    calc
      (v (c^2+x*d^2))+(v (D y)) =
          (v (b^2+y*d^2))+(v (D x)) := he.symm
      _ ≤ ((v (D y))+(v (b^2)))+(v (D x)) :=
        add_le_add_left hb' _
      _ = ((v (D x))+(v (b^2)))+(v (D y)) := by ac_rfl
  refine ⟨?_,hb,hc,hxd,hyd⟩
  have ha : a^2 = x*b^2+y*c^2+x*y*d^2 := by
    apply CharTwo.add_eq_zero.mp
    convert h using 1
    ring
  rw [ha]
  have hxb : (v (c^2+x*d^2)) ≤ (v (D x))+(v (x*b^2)) := by
    rw [addVal_mul]
    exact hb.trans (add_le_add_right (le_add_of_nonneg_left zero_le) _)
  have hyc : (v (c^2+x*d^2)) ≤ (v (D x))+(v (y*c^2)) := by
    rw [addVal_mul]
    exact hc.trans (add_le_add_right (le_add_of_nonneg_left zero_le) _)
  have hxyd : (v (c^2+x*d^2)) ≤ (v (D x))+(v (x*y*d^2)) := by
    rw [show x*y*d^2 = y*(x*d^2) by ring, addVal_mul]
    exact hxd.trans (add_le_add_right (le_add_of_nonneg_left zero_le) _)
  have hs : (v (c^2+x*d^2)) ≤ (v (D x))+ (v (x*b^2+y*c^2)) := by
    have hh := le_min hxb hyc
    rw [← add_min] at hh
    exact hh.trans (add_le_add_right ((addVal B).map_add _ _) _)
  have hh := le_min hs hxyd
  rw [← add_min] at hh
  exact hh.trans (add_le_add_right ((addVal B).map_add _ _) _)

end PermanentBorder.FrobeniusDVR

namespace PermanentBorder.FrobeniusDVR
open IsDiscreteValuationRing
variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

lemma mem_ideal_of_valuation_product {I : Ideal B} {g f z : B}
    (hg : g ≠ 0) (h : I * Ideal.span {g} = Ideal.span {f})
    (hv : addVal B f ≤ addVal B g + addVal B z) : z ∈ I := by
  have hm : z*g ∈ I * Ideal.span {g} := by
    rw [h, Ideal.mem_span_singleton]
    apply (addVal_le_iff_dvd (R := B)).mp
    simpa only [addVal_mul, add_comm (addVal B z)] using hv
  obtain ⟨v,hv,he⟩ := Ideal.mem_mul_span_singleton.mp hm
  have he' : v = z := mul_right_cancel₀ hg he
  rwa [he'] at hv

end PermanentBorder.FrobeniusDVR

namespace PermanentBorder.PlaneConductorDVR
open Polynomial IsDiscreteValuationRing
variable {K S Q L B : Type*} [CommRing K] [CommRing S] [IsDomain S]
  [IsIntegrallyClosed S] [Field Q] [Algebra S Q] [IsFractionRing S Q]
  [Field L] [Algebra Q L] [Algebra S L] [IsScalarTower S Q L]
  [FiniteDimensional Q L] [Algebra.IsSeparable Q L]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra S B] [Module.Finite S B] [Algebra B L] [IsScalarTower S B L]
  [IsIntegralClosure B S L] [Module.IsTorsionFree S B]
  [Algebra K B] [CharP B 2]

include Q L in
omit [Module.Finite S B] in

theorem four_form_conductor_membership (x y a b c d g : B)
    (hygen : Algebra.adjoin Q {algebraMap B L y} = ⊤)
    (hF : aeval y (minpoly S y).derivative = c^2+x*d^2)
    (D : Derivation K B B) (hxD : D x = g) (hg : g ≠ 0)
    (hdiff : differentIdeal S B = Ideal.span {g})
    (hx : 1 ≤ addVal B x) (hy : 1 ≤ addVal B y)
    (h : a^2+x*b^2+y*c^2+x*y*d^2 = 0) :
    a^2 ∈ conductor S y ∧ b^2 ∈ conductor S y ∧ c^2 ∈ conductor S y ∧
      x*d^2 ∈ conductor S y ∧ y*d^2 ∈ conductor S y := by
  have hid := conductor_mul_differentIdeal S Q L y hygen
  rw [hdiff, hF] at hid
  have hv := FrobeniusDVR.conductor_generators_valuation D x y a b c d hx hy h
  rw [hxD] at hv
  exact ⟨FrobeniusDVR.mem_ideal_of_valuation_product hg hid hv.1,
    FrobeniusDVR.mem_ideal_of_valuation_product hg hid hv.2.1,
    FrobeniusDVR.mem_ideal_of_valuation_product hg hid hv.2.2.1,
    FrobeniusDVR.mem_ideal_of_valuation_product hg hid hv.2.2.2.1,
    FrobeniusDVR.mem_ideal_of_valuation_product hg hid hv.2.2.2.2⟩

end PermanentBorder.PlaneConductorDVR

namespace PermanentBorder.FrobeniusDVR
open IsDiscreteValuationRing
variable {K B : Type*} [CommRing K] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra K B] [CharP B 2]
local notation "v" => addVal B

lemma gradient_valuation (D : Derivation K B B) (x y a b c d : B)
    (h : a^2+x*b^2+y*c^2+x*y*d^2 = 0) :
    v (c^2+x*d^2) ≤ v (D x) + v (b^2+y*d^2) := by
  by_cases hdy : D y = 0
  · have hh := branch_chain D x y a b c d h
    rw [hdy,mul_zero,add_zero] at hh
    rcases mul_eq_zero.mp hh with hf|hx
    · simp [hf]
    · simp [hx]
  · have he := congrArg v (CharTwo.add_eq_zero.mp (branch_chain D x y a b c d h))
    rw [addVal_mul,addVal_mul] at he
    calc
      v (c^2+x*d^2) ≤ v (c^2+x*d^2) + v (D y) := le_add_of_nonneg_right zero_le
      _ = v (D x)+v (b^2+y*d^2) := by rw [← he,add_comm]

lemma radical_gradient_valuation (D : Derivation K B B) (x y a b c d z : B)
    (h : a^2+x*b^2+y*c^2+x*y*d^2 = 0)
    (hz : z ∈ (Ideal.span {b^2+y*d^2,c^2+x*d^2}).radical) :
    v (c^2+x*d^2) ≤ v (D x) + v (d^2*z) := by
  by_cases hz1 : 1 ≤ v z
  · have hh := valuation_square_plus_le D x c d
    rw [addVal_mul,addVal_pow,nsmul_eq_mul]
    calc
      v (c^2+x*d^2) ≤ v (D x)+2*v d+1 := hh
      _ ≤ v (D x)+2*v d+v z := add_le_add le_rfl hz1
      _ = v (D x)+(2*v d+v z) := by ac_rfl
  · have hz0 : v z = 0 := by
      have hh := lt_of_not_ge hz1
      exact le_antisymm (Order.le_of_lt_add_one hh) zero_le
    have hzu : IsUnit z := (addVal_eq_zero_iff (R := B)).mp hz0
    have hI : Ideal.span {b^2+y*d^2,c^2+x*d^2} = ⊤ := by
      obtain ⟨n,hn⟩ := Ideal.mem_radical_iff.mp hz
      exact (Ideal.span {b^2+y*d^2,c^2+x*d^2}).eq_top_of_isUnit_mem hn (hzu.pow n)
    have hu : IsUnit (b^2+y*d^2) ∨ IsUnit (c^2+x*d^2) := by
      by_contra! hh
      have hm : Ideal.span {b^2+y*d^2,c^2+x*d^2} ≤ IsLocalRing.maximalIdeal B := by
        apply Ideal.span_le.mpr
        intro w hw
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hw
        rcases hw with rfl|rfl
        · exact hh.1
        · exact hh.2
      rw [hI] at hm
      exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.mp hm)
    rcases hu with hfx|hfy
    · have hh := gradient_valuation D x y a b c d h
      rw [(addVal_eq_zero_iff (R := B)).mpr hfx,add_zero] at hh
      exact hh.trans (le_add_of_nonneg_right zero_le)
    · rw [(addVal_eq_zero_iff (R := B)).mpr hfy]
      exact zero_le

theorem radical_gradient_conductor (D : Derivation K B B)
    (x y a b c d g : B) (C : Ideal B)
    (hx : D x = g) (hg : g ≠ 0)
    (hC : C * Ideal.span {g} = Ideal.span {c^2+x*d^2})
    (h : a^2+x*b^2+y*c^2+x*y*d^2 = 0) :
    b^2+y*d^2 ∈ C ∧ c^2+x*d^2 ∈ C ∧
      ∀ z ∈ (Ideal.span {b^2+y*d^2,c^2+x*d^2}).radical, d^2*z ∈ C := by
  refine ⟨?_,?_,?_⟩
  · apply mem_ideal_of_valuation_product hg hC
    simpa only [hx] using gradient_valuation D x y a b c d h
  · apply mem_ideal_of_valuation_product hg hC
    exact le_add_of_nonneg_left zero_le
  · intro z hz
    apply mem_ideal_of_valuation_product hg hC
    simpa only [hx] using radical_gradient_valuation D x y a b c d z h hz

end PermanentBorder.FrobeniusDVR
namespace PermanentBorder.FrobeniusDVR
open IsDiscreteValuationRing
variable {K B : Type*} [CommRing K] [CommRing B] [IsDedekindDomain B]
  [Algebra K B] [CharP B 2]

theorem radical_gradient_conductor_dedekind (D : Derivation K B B)
    (x y a b c d g : B) (C : Ideal B)
    (hx : D x = g) (hg : g ≠ 0) (hC0 : C ≠ ⊥)
    (hC : C * Ideal.span {g} = Ideal.span {c^2+x*d^2})
    (h : a^2+x*b^2+y*c^2+x*y*d^2 = 0) :
    b^2+y*d^2 ∈ C ∧ c^2+x*d^2 ∈ C ∧
      ∀ z ∈ (Ideal.span {b^2+y*d^2,c^2+x*d^2}).radical, d^2*z ∈ C := by
  have hloc (P : Ideal B) [P.IsMaximal] (hP : P ≠ ⊥) :
      let φ := algebraMap B (Localization.AtPrime P)
      φ (b^2+y*d^2) ∈ C.map φ ∧ φ (c^2+x*d^2) ∈ C.map φ ∧
        ∀ z ∈ (Ideal.span {b^2+y*d^2,c^2+x*d^2}).radical,
          φ (d^2*z) ∈ C.map φ := by
    let T := Localization.AtPrime P
    let φ := algebraMap B T
    have : IsDiscreteValuationRing T :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP T
    have hinj : Function.Injective φ := IsLocalization.injective T P.primeCompl_le_nonZeroDivisors
    have : CharP T 2 := charP_of_injective_algebraMap hinj 2
    let D' := NormalizationDerivation.extendEtale (T := T) D
    have hx' : D' (φ x) = φ g := by
      simp only [D',φ,NormalizationDerivation.extendEtale_algebraMap,hx]
    have hC' : C.map φ * Ideal.span {φ g} = Ideal.span {(φ c)^2+φ x*(φ d)^2} := by
      have hh := congrArg (Ideal.map φ) hC
      rw [Ideal.map_mul φ C (Ideal.span {g})] at hh
      simpa only [Ideal.map_span,Set.image_singleton,map_add,map_mul,map_pow] using hh
    have h' : (φ a)^2+φ x*(φ b)^2+φ y*(φ c)^2+φ x*φ y*(φ d)^2 = 0 := by
      simpa only [map_add,map_mul,map_pow,map_zero] using congrArg φ h
    obtain ⟨hfx,hfy,hz⟩ := radical_gradient_conductor D' (φ x) (φ y)
      (φ a) (φ b) (φ c) (φ d) (φ g) (C.map φ) hx' (by simpa only [map_zero] using hinj.ne hg) hC' h'
    refine ⟨by simpa only [map_add,map_mul,map_pow] using hfx,
      by simpa only [map_add,map_mul,map_pow] using hfy,?_⟩
    intro z hzm
    have hz' : φ z ∈ (Ideal.span {(φ b)^2+φ y*(φ d)^2,
        (φ c)^2+φ x*(φ d)^2}).radical := by
      have hh := Ideal.map_radical_le φ (Ideal.mem_map_of_mem φ hzm)
      simpa only [Ideal.map_span,Set.image_insert_eq,Set.image_singleton,
        map_add,map_mul,map_pow] using hh
    simpa only [map_mul,map_pow] using hz (φ z) hz'
  have hmem (z : B)
      (hz : ∀ (P : Ideal B) [P.IsMaximal], P ≠ ⊥ →
        algebraMap B (Localization.AtPrime P) z ∈
          C.map (algebraMap B (Localization.AtPrime P))) : z ∈ C := by
    apply Ideal.mem_of_localization_maximal
    intro P hP
    by_cases hP0 : P = ⊥
    · have hCt : C = ⊤ := by
        by_contra hCt
        exact hC0 ((hP.eq_of_le hCt (hP0 ▸ bot_le)).symm.trans hP0)
      exact Ideal.mem_map_of_mem _ (hCt ▸ Submodule.mem_top)
    · exact hz P hP0
  refine ⟨hmem _ (fun P _ hP => (hloc P hP).1),
    hmem _ (fun P _ hP => (hloc P hP).2.1),?_⟩
  intro z hz
  exact hmem _ (fun P _ hP => (hloc P hP).2.2 z hz)

end PermanentBorder.FrobeniusDVR
namespace PermanentBorder.ReducedBranchConductor
open Polynomial
section Branch
variable {K S Q L B : Type*} [CommRing K] [CommRing S] [IsDomain S]
  [IsIntegrallyClosed S] [IsLocalRing S] [IsAlgClosed (IsLocalRing.ResidueField S)]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
  [Field L] [Algebra Q L] [Algebra S L] [IsScalarTower S Q L]
  [FiniteDimensional Q L] [Algebra.IsSeparable Q L]
  [CommRing B] [IsDedekindDomain B] [IsPrincipalIdealRing B]
  [Algebra S B] [Module.Finite S B] [Algebra B L] [IsScalarTower S B L]
  [IsIntegralClosure B S L] [Module.IsTorsionFree S B]
  [Algebra K S] [Algebra K B] [IsScalarTower K S B] [CharP B 2]

include Q L in

theorem branch_conductor (δ : Derivation K S S) (x : S) (hx : δ x = 1)
    (y a b c d : B) (f w : S[X])
    (hygen : Algebra.adjoin Q {algebraMap B L y} = ⊤)
    (hfactor : f = minpoly S y * w)
    (hsep : (f.map (algebraMap S Q)).Separable)
    (hfy : aeval y f.derivative = c^2+algebraMap S B x*d^2)
    (h : a^2+algebraMap S B x*b^2+y*c^2+algebraMap S B x*y*d^2=0) :
    let J := conductor S y * Ideal.span {aeval y w}
    b^2+y*d^2 ∈ J ∧ c^2+algebraMap S B x*d^2 ∈ J ∧
      ∀ z ∈ (Ideal.span {b^2+y*d^2,c^2+algebraMap S B x*d^2}).radical,
        d^2*z ∈ J := by
  have hyf : aeval y f = 0 := by
    rw [hfactor,map_mul,minpoly.aeval,zero_mul]
  have hder0 : aeval y f.derivative ≠ 0 := by
    have hz : aeval (algebraMap B L y) (f.map (algebraMap S Q)) = 0 := by
      rw [aeval_map_algebraMap]
      change aeval ((IsScalarTower.toAlgHom S B L) y) f = 0
      rw [aeval_algHom_apply,hyf,map_zero]
    have hh := hsep.aeval_derivative_ne_zero hz
    intro he
    apply hh
    rw [derivative_map,aeval_map_algebraMap]
    change aeval ((IsScalarTower.toAlgHom S B L) y) f.derivative = 0
    rw [aeval_algHom_apply,he,map_zero]
  obtain ⟨g,D,hgD,hD⟩ :=
    NormalizationDerivation.exists_scaled_normalization_derivation (Q := Q) (L := L) (B := B) δ
  have hd : conductor S y * Ideal.span {g} = Ideal.span {aeval y (minpoly S y).derivative} := by
    rw [← hgD]
    exact conductor_mul_differentIdeal S Q L y hygen
  have hJ : (conductor S y * Ideal.span {aeval y w}) * Ideal.span {g} =
      Ideal.span {c^2+algebraMap S B x*d^2} := by
    rw [mul_right_comm,hd,Ideal.span_singleton_mul_span_singleton,← map_mul]
    rw [← hfy]
    congr 1
    simp only [hfactor,derivative_mul,map_add,map_mul,minpoly.aeval,zero_mul,add_zero]
  have hg : g ≠ 0 := by
    intro hg
    rw [hg,Ideal.span_singleton_zero,Ideal.mul_bot] at hJ
    have hz : c^2+algebraMap S B x*d^2=0 := Ideal.span_singleton_eq_bot.mp hJ.symm
    exact hder0 (hfy.trans hz)
  have hJ0 : conductor S y * Ideal.span {aeval y w} ≠ ⊥ := by
    intro hJ0
    rw [hJ0,Ideal.bot_mul] at hJ
    exact hder0 (hfy.trans (Ideal.span_singleton_eq_bot.mp hJ.symm))
  apply FrobeniusDVR.radical_gradient_conductor_dedekind D
    (algebraMap S B x) y a b c d g _ _ hg hJ0 hJ h
  rw [hD,hx,map_one,mul_one]
end Branch
end PermanentBorder.ReducedBranchConductor

end OAI
