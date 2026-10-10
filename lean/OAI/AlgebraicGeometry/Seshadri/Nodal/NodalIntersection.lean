import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.FormalAdic

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri
namespace NodalLocal

open PowerSeries

noncomputable section

variable (K : Type*) [Field K]

def multiples {A : Type*} [CommRing A] [Algebra K A] (f : A) : Submodule K A :=
  LinearMap.range (LinearMap.mulLeft K f)

@[simp] theorem mem_multiples {A : Type*} [CommRing A] [Algebra K A] (f g : A) :
    g ∈ multiples K f ↔ f ∣ g := by
  simp only [multiples, LinearMap.mem_range, LinearMap.mulLeft_apply, dvd_def]
  exact exists_congr (fun _ => eq_comm)

def nodeAlgebra : Subalgebra K (PowerSeries K × PowerSeries K) where
  carrier := {p | constantCoeff p.1 = constantCoeff p.2}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' {a b} (ha : constantCoeff a.1 = constantCoeff a.2)
      (hb : constantCoeff b.1 = constantCoeff b.2) := by
    change constantCoeff (a.1 + b.1) = constantCoeff (a.2 + b.2)
    simp only [map_add, ha, hb]
  mul_mem' {a b} (ha : constantCoeff a.1 = constantCoeff a.2)
      (hb : constantCoeff b.1 = constantCoeff b.2) := by
    change constantCoeff (a.1 * b.1) = constantCoeff (a.2 * b.2)
    simp only [map_mul, ha, hb]
  algebraMap_mem' := by intro a; rfl

abbrev Node := nodeAlgebra K

def branchX : Node K →ₐ[K] PowerSeries K where
  toFun := fun f => f.val.1
  map_zero' := rfl
  map_one' := rfl
  map_add' := by intros; rfl
  map_mul' := by intros; rfl
  commutes' := by intros; rfl

def branchZ : Node K →ₐ[K] PowerSeries K where
  toFun := fun f => f.val.2
  map_zero' := rfl
  map_one' := rfl
  map_add' := by intros; rfl
  map_mul' := by intros; rfl
  commutes' := by intros; rfl

@[ext] theorem node_ext {f g : Node K}
    (hx : branchX K f = branchX K g) (hz : branchZ K f = branchZ K g) : f = g :=
  Subtype.ext (Prod.ext hx hz)

lemma branch_constant (f : Node K) :
    constantCoeff (branchX K f) = constantCoeff (branchZ K f) := f.property

def includeX : PowerSeries K →ₗ[K] Node K where
  toFun := fun f => ⟨(X * f, 0), by change constantCoeff (X * f) = constantCoeff 0; simp⟩
  map_add' := by intro f g; apply Subtype.ext; ext <;> simp [mul_add]
  map_smul' := by intro a f; apply Subtype.ext; ext <;> simp

@[simp] theorem branchX_includeX (f : PowerSeries K) :
    branchX K (includeX K f) = X * f := rfl
@[simp] theorem branchZ_includeX (f : PowerSeries K) :
    branchZ K (includeX K f) = 0 := rfl

def liftZ : PowerSeries K →ₗ[K] Node K where
  toFun := fun f => ⟨(C (constantCoeff f), f), by
    change constantCoeff (C (constantCoeff f)) = constantCoeff f
    simp⟩
  map_add' := by intro f g; apply Subtype.ext; ext <;> simp
  map_smul' := by
    intro a f
    apply Subtype.ext
    change (C (constantCoeff (a • f)), a • f) = (a • C (constantCoeff f), a • f)
    congr 1
    simp only [Algebra.smul_def, map_mul, PowerSeries.algebraMap_apply,
      constantCoeff_C]

@[simp] theorem branchX_liftZ (f : PowerSeries K) :
    branchX K (liftZ K f) = C (constantCoeff f) := rfl
@[simp] theorem branchZ_liftZ (f : PowerSeries K) :
    branchZ K (liftZ K f) = f := rfl

theorem range_includeX_eq_ker_branchZ :
    (includeX K).range = (branchZ K).toLinearMap.ker := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    simp
  · intro hf
    have hz : branchZ K f = 0 := hf
    have hx : constantCoeff (branchX K f) = 0 := by rw [branch_constant, hz, map_zero]
    obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr hx
    refine ⟨g, ?_⟩
    apply node_ext <;> simp [hg, hz]

lemma includeX_mul (f : Node K) (g : PowerSeries K) :
    includeX K (branchX K f * g) = f * includeX K g := by
  apply node_ext <;> simp [mul_left_comm]

def coefficientJet (n : ℕ) : PowerSeries K →ₗ[K] (Fin n → K) :=
  LinearMap.pi (fun i => coeff i.val)

@[simp] lemma coefficientJet_apply (n : ℕ) (f : PowerSeries K) (i : Fin n) :
    coefficientJet K n f i = coeff i.val f := rfl

lemma coefficientJet_surjective (n : ℕ) : Function.Surjective (coefficientJet K n) := by
  intro v
  refine ⟨PowerSeries.mk (fun j => if h : j < n then v ⟨j, h⟩ else 0), ?_⟩
  ext i
  simp [i.isLt]

lemma ker_coefficientJet (n : ℕ) :
    (coefficientJet K n).ker = multiples K (X ^ n : PowerSeries K) := by
  ext f
  simp only [LinearMap.mem_ker, mem_multiples, PowerSeries.X_pow_dvd_iff]
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    ext i
    exact h i.val i.isLt

lemma multiples_eq_order (f : PowerSeries K) (hf : f ≠ 0) :
    multiples K f = multiples K (X ^ f.order.toNat : PowerSeries K) := by
  ext g
  simp only [mem_multiples]
  obtain ⟨u, hu⟩ := PowerSeries.isUnit_divided_by_X_pow_order hf
  have he : X ^ f.order.toNat * (u : PowerSeries K) = f := by
    rw [hu]
    exact PowerSeries.X_pow_order_mul_divXPowOrder
  conv_lhs => rw [← he]
  constructor
  · exact dvd_trans (dvd_mul_right _ _)
  · rintro ⟨a, rfl⟩
    refine ⟨(↑u⁻¹ : PowerSeries K) * a, ?_⟩
    simp [mul_assoc]

noncomputable def branchQuotientEquiv (f : PowerSeries K) (hf : f ≠ 0) :
    (PowerSeries K ⧸ multiples K f) ≃ₗ[K] (Fin f.order.toNat → K) :=
  (Submodule.quotEquivOfEq (multiples K f) (coefficientJet K f.order.toNat).ker
    ((multiples_eq_order K f hf).trans (ker_coefficientJet K f.order.toNat).symm)).trans
      ((coefficientJet K f.order.toNat).quotKerEquivOfSurjective
        (coefficientJet_surjective K f.order.toNat))

lemma finite_branch_quotient (f : PowerSeries K) (hf : f ≠ 0) :
    FiniteDimensional K (PowerSeries K ⧸ multiples K f) :=
  FiniteDimensional.of_injective (branchQuotientEquiv K f hf).toLinearMap
    (branchQuotientEquiv K f hf).injective

lemma finrank_branch_quotient (f : PowerSeries K) (hf : f ≠ 0) :
    Module.finrank K (PowerSeries K ⧸ multiples K f) = f.order.toNat := by
  rw [(branchQuotientEquiv K f hf).finrank_eq, Module.finrank_pi]
  simp

def quotientZ (f : Node K) :
    (Node K ⧸ multiples K f) →ₗ[K]
      (PowerSeries K ⧸ multiples K (branchZ K f)) :=
  (multiples K f).liftQ
    ((multiples K (branchZ K f)).mkQ.comp (branchZ K).toLinearMap) (by
      rintro y ⟨a, rfl⟩
      change (Submodule.Quotient.mk (branchZ K (f * a)) :
        PowerSeries K ⧸ multiples K (branchZ K f)) = 0
      simp only [map_mul, Submodule.Quotient.mk_eq_zero, mem_multiples]
      exact dvd_mul_right _ _)

@[simp] lemma quotientZ_mk (f g : Node K) :
    quotientZ K f (Submodule.Quotient.mk g) = Submodule.Quotient.mk (branchZ K g) := rfl

def quotientX (f : Node K) :
    (PowerSeries K ⧸ multiples K (branchX K f)) →ₗ[K]
      (Node K ⧸ multiples K f) :=
  (multiples K (branchX K f)).liftQ
    ((multiples K f).mkQ.comp (includeX K)) (by
      rintro y ⟨a, rfl⟩
      change (Submodule.Quotient.mk (includeX K (branchX K f * a)) :
        Node K ⧸ multiples K f) = 0
      rw [includeX_mul, Submodule.Quotient.mk_eq_zero, mem_multiples]
      exact dvd_mul_right _ _)

@[simp] lemma quotientX_mk (f : Node K) (g : PowerSeries K) :
    quotientX K f (Submodule.Quotient.mk g) = Submodule.Quotient.mk (includeX K g) := rfl

lemma quotientZ_surjective (f : Node K) : Function.Surjective (quotientZ K f) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H g =>
    exact ⟨Submodule.Quotient.mk (liftZ K g), by simp⟩

lemma quotientX_injective (f : Node K) (hfz : branchZ K f ≠ 0) :
    Function.Injective (quotientX K f) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm ?_ bot_le
  intro q hq
  change q = 0
  induction q using Submodule.Quotient.induction_on with
  | H h =>
    have hh : includeX K h ∈ multiples K f := by
      exact (Submodule.Quotient.mk_eq_zero _).mp hq
    obtain ⟨g, hg⟩ := (mem_multiples K f (includeX K h)).mp hh
    have hgz : branchZ K g = 0 := by
      have hz : branchZ K f * branchZ K g = 0 := by
        simpa using (congrArg (branchZ K) hg).symm
      exact (mul_eq_zero.mp hz).resolve_left hfz
    have hgc : constantCoeff (branchX K g) = 0 := by
      rw [branch_constant, hgz, map_zero]
    obtain ⟨a, ha⟩ := PowerSeries.X_dvd_iff.mpr hgc
    have hh' : h = branchX K f * a := by
      apply mul_left_cancel₀ (PowerSeries.X_ne_zero : (X : PowerSeries K) ≠ 0)
      calc
        X * h = branchX K f * branchX K g := by
          simpa using congrArg (branchX K) hg
        _ = X * (branchX K f * a) := by rw [ha]; ring
    change (Submodule.Quotient.mk h : PowerSeries K ⧸ multiples K (branchX K f)) = 0
    rw [Submodule.Quotient.mk_eq_zero, mem_multiples]
    exact ⟨a, hh'⟩

lemma branch_quotient_exact (f : Node K) :
    Function.Exact (quotientX K f) (quotientZ K f) := by
  rw [LinearMap.exact_iff]
  ext q
  constructor
  · intro hq
    induction q using Submodule.Quotient.induction_on with
    | H g =>
      have hg : branchZ K g ∈ multiples K (branchZ K f) := by
        exact (Submodule.Quotient.mk_eq_zero _).mp hq
      obtain ⟨b, hb⟩ := (mem_multiples K _ _).mp hg
      let g' := g - f * liftZ K b
      have hz : branchZ K g' = 0 := by simp [g', hb]
      have hmem : g' ∈ (includeX K).range := by
        rw [range_includeX_eq_ker_branchZ]
        exact hz
      obtain ⟨a, ha⟩ := hmem
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      rw [quotientX_mk, Submodule.Quotient.eq]
      rw [ha]
      change g - f * liftZ K b - g ∈ multiples K f
      rw [show g - f * liftZ K b - g = f * (-liftZ K b) by ring]
      rw [mem_multiples]
      exact dvd_mul_right _ _
  · rintro ⟨a, rfl⟩
    induction a using Submodule.Quotient.induction_on with
    | H a =>
      change quotientZ K f (quotientX K f (Submodule.Quotient.mk a)) = 0
      simp

lemma finite_node_quotient (f : Node K)
    (hfx : branchX K f ≠ 0) (hfz : branchZ K f ≠ 0) :
    FiniteDimensional K (Node K ⧸ multiples K f) := by
  have := finite_branch_quotient K (branchX K f) hfx
  have := finite_branch_quotient K (branchZ K f) hfz
  exact Module.Finite.of_exact (branch_quotient_exact K f) (quotientZ_surjective K f)

theorem finrank_node_quotient (f : Node K)
    (hfx : branchX K f ≠ 0) (hfz : branchZ K f ≠ 0) :
    Module.finrank K (Node K ⧸ multiples K f) =
      (branchX K f).order.toNat + (branchZ K f).order.toNat := by
  have := finite_node_quotient K f hfx hfz
  have hex := LinearMap.exact_iff.mp (branch_quotient_exact K f)
  have hs : (quotientZ K f).range = ⊤ :=
    LinearMap.range_eq_top.mpr (quotientZ_surjective K f)
  have h := (quotientZ K f).finrank_range_add_finrank_ker
  rw [hs, finrank_top, hex,
    LinearMap.finrank_range_of_inj (quotientX_injective K f hfz),
    finrank_branch_quotient K _ hfz, finrank_branch_quotient K _ hfx] at h
  omega

abbrev Bivariate := PowerSeries (PowerSeries K)

def constAlg : PowerSeries K →ₐ[K] K where
  toRingHom := constantCoeff
  commutes' := by intro a; simp

def restrictX : Bivariate K →ₐ[K] PowerSeries K where
  toRingHom := constantCoeff
  commutes' := by intro a; simp [PowerSeries.algebraMap_apply]

def restrictZ : Bivariate K →ₐ[K] PowerSeries K :=
  PowerSeries.mapAlgHom (constAlg K)

@[simp] lemma restrictX_apply (f : Bivariate K) : restrictX K f = constantCoeff f := rfl
@[simp] lemma restrictZ_apply (f : Bivariate K) :
    restrictZ K f = PowerSeries.map constantCoeff f := rfl

lemma restrict_constants (f : Bivariate K) :
    constantCoeff (restrictX K f) = constantCoeff (restrictZ K f) := by
  simp only [restrictX_apply, restrictZ_apply, ← coeff_zero_eq_constantCoeff_apply,
    coeff_map]

def toNode : Bivariate K →ₐ[K] Node K where
  toFun f := ⟨(restrictX K f, restrictZ K f), restrict_constants K f⟩
  map_zero' := by
    apply Subtype.ext
    exact Prod.ext (map_zero (restrictX K)) (map_zero (restrictZ K))
  map_one' := by
    apply Subtype.ext
    exact Prod.ext (map_one (restrictX K)) (map_one (restrictZ K))
  map_add' := by intro f g; apply node_ext <;> simp
  map_mul' := by intro f g; apply node_ext <;> simp
  commutes' := by
    intro a
    apply Subtype.ext
    exact Prod.ext ((restrictX K).commutes a) ((restrictZ K).commutes a)

@[simp] lemma branchX_toNode (f : Bivariate K) :
    branchX K (toNode K f) = restrictX K f := rfl
@[simp] lemma branchZ_toNode (f : Bivariate K) :
    branchZ K (toNode K f) = restrictZ K f := rfl

lemma toNode_surjective : Function.Surjective (toNode K) := by
  intro f
  refine ⟨C (branchX K f) + PowerSeries.map C (branchZ K f) -
    C (C (constantCoeff (branchX K f))), ?_⟩
  apply node_ext
  · rw [branchX_toNode, restrictX_apply]
    simp only [map_sub, map_add, constantCoeff_C]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, ← branch_constant]
    abel
  · rw [branchZ_toNode, restrictZ_apply]
    simp only [map_sub, map_add, map_C, constantCoeff_C]
    have hm : PowerSeries.map constantCoeff (PowerSeries.map C (branchZ K f)) =
        branchZ K f := by ext n; simp
    rw [hm]
    abel

def nodeEquation : Bivariate K := C (X : PowerSeries K) * X

@[simp] lemma toNode_nodeEquation : toNode K (nodeEquation K) = 0 := by
  apply node_ext <;> simp [nodeEquation]

theorem toNode_eq_zero_iff (f : Bivariate K) :
    toNode K f = 0 ↔ nodeEquation K ∣ f := by
  constructor
  · intro hf
    have hx : constantCoeff f = 0 := by
      simpa using congrArg (branchX K) hf
    obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr hx
    have hz : PowerSeries.map constantCoeff g = 0 := by
      have h : X * PowerSeries.map constantCoeff g = (0 : PowerSeries K) := by
        simpa [hg] using congrArg (branchZ K) hf
      exact (mul_eq_zero.mp h).resolve_left PowerSeries.X_ne_zero
    have hc : ∀ n, X ∣ coeff n g := by
      intro n
      apply PowerSeries.X_dvd_iff.mpr
      have h := congrArg (coeff n) hz
      simpa using h
    choose h hh using hc
    have hge : g = C (X : PowerSeries K) * PowerSeries.mk h := by
      apply PowerSeries.ext
      intro n
      simpa only [coeff_C_mul, coeff_mk] using hh n
    refine ⟨PowerSeries.mk h, ?_⟩
    rw [hg, hge, nodeEquation]
    ring
  · rintro ⟨g, rfl⟩
    simp

lemma ker_toNode : RingHom.ker (toNode K).toRingHom =
    Ideal.span ({nodeEquation K} : Set (Bivariate K)) := by
  ext f
  simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    toNode_eq_zero_iff, Ideal.mem_span_singleton]

noncomputable def nodePresentation :
    (Bivariate K ⧸ Ideal.span ({nodeEquation K} : Set (Bivariate K))) ≃ₐ[K] Node K :=
  (Ideal.quotientEquivAlgOfEq K (ker_toNode K).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (toNode_surjective K))

def intersectionIdeal (f : Bivariate K) : Ideal (Bivariate K) :=
  Ideal.span {f, nodeEquation K}

def intersectionRestriction (f : Bivariate K) : Bivariate K →ₗ[K]
    (Node K ⧸ multiples K (toNode K f)) :=
  (multiples K (toNode K f)).mkQ.comp (toNode K).toLinearMap

lemma intersectionRestriction_surjective (f : Bivariate K) :
    Function.Surjective (intersectionRestriction K f) :=
  (Submodule.mkQ_surjective (multiples K (toNode K f))).comp (toNode_surjective K)

lemma ker_intersectionRestriction (f : Bivariate K) :
    (intersectionRestriction K f).ker = (intersectionIdeal K f).restrictScalars K := by
  ext g
  change (Submodule.Quotient.mk (toNode K g) : Node K ⧸ multiples K (toNode K f)) = 0 ↔
    g ∈ Ideal.span {f, nodeEquation K}
  rw [Submodule.Quotient.mk_eq_zero, mem_multiples, Ideal.mem_span_pair]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, rfl⟩ := toNode_surjective K a
    have hz : toNode K (g - f * b) = 0 := by simp [ha]
    obtain ⟨c, hc⟩ := (toNode_eq_zero_iff K _).mp hz
    refine ⟨b, c, ?_⟩
    calc
      b * f + c * nodeEquation K = f * b + nodeEquation K * c := by ring
      _ = f * b + (g - f * b) := by rw [hc]
      _ = g := by ring
  · rintro ⟨a, b, rfl⟩
    refine ⟨toNode K a, ?_⟩
    simp [mul_comm]

noncomputable def intersectionQuotientEquiv (f : Bivariate K) :
    (Bivariate K ⧸ intersectionIdeal K f) ≃ₗ[K]
      (Node K ⧸ multiples K (toNode K f)) :=
  (Submodule.Quotient.restrictScalarsEquiv K (intersectionIdeal K f)).symm.trans
    ((Submodule.quotEquivOfEq ((intersectionIdeal K f).restrictScalars K)
      (intersectionRestriction K f).ker (ker_intersectionRestriction K f).symm).trans
        ((intersectionRestriction K f).quotKerEquivOfSurjective
          (intersectionRestriction_surjective K f)))

lemma finite_intersection_quotient (f : Bivariate K)
    (hx : restrictX K f ≠ 0) (hz : restrictZ K f ≠ 0) :
    FiniteDimensional K (Bivariate K ⧸ intersectionIdeal K f) := by
  have := finite_node_quotient K (toNode K f) hx hz
  exact FiniteDimensional.of_injective (intersectionQuotientEquiv K f).toLinearMap
    (intersectionQuotientEquiv K f).injective

theorem nodal_intersection_colength (f : Bivariate K)
    (hx : restrictX K f ≠ 0) (hz : restrictZ K f ≠ 0) :
    Module.finrank K (Bivariate K ⧸ intersectionIdeal K f) =
      (restrictX K f).order.toNat + (restrictZ K f).order.toNat := by
  rw [(intersectionQuotientEquiv K f).finrank_eq]
  exact finrank_node_quotient K (toNode K f) hx hz

end

end NodalLocal
end MaximalSeshadri

namespace MaximalSeshadri.LocalComparison
noncomputable section
open IsLocalRing
open MaximalSeshadri.NodalLocal
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
  [IsLocalRing A] [IsNoetherianRing A]

omit [IsLocalRing A] [IsNoetherianRing A] in

lemma map_nodal_intersection_ideal (τ : A →ₐ[K] Bivariate K) (f g : A)
    {u : Bivariate K} (hu : IsUnit u) (hg : τ g = u * nodeEquation K) :
    (Ideal.span {f, g}).map τ.toRingHom = intersectionIdeal K (τ f) := by
  rw [Ideal.map_span, Set.image_pair]
  change Ideal.span {τ f, τ g} = _
  rw [hg, intersectionIdeal, Ideal.span_insert, Ideal.span_insert,
    Ideal.span_singleton_mul_left_unit hu]

theorem actual_nodal_intersection_colength (τ : A →ₐ[K] Bivariate K)
    (hs : ∀ n : ℕ, Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal (Bivariate K) ^ n)).comp τ.toRingHom))
    (hk : ∀ n : ℕ, RingHom.ker
      ((Ideal.Quotient.mk (maximalIdeal (Bivariate K) ^ n)).comp τ.toRingHom) =
        maximalIdeal A ^ n) (f g : A)
    {u : Bivariate K} (hu : IsUnit u) (hg : τ g = u * nodeEquation K)
    (hx : restrictX K (τ f) ≠ 0) (hz : restrictZ K (τ f) ≠ 0) :
    Module.finrank K (A ⧸ Ideal.span {f, g}) =
      (restrictX K (τ f)).order.toNat + (restrictZ K (τ f)).order.toNat := by
  have heq := map_nodal_intersection_ideal τ f g hu hg
  let : FiniteDimensional K (Bivariate K ⧸ (Ideal.span {f, g}).map τ.toRingHom) := by
    rw [heq]
    exact finite_intersection_quotient K (τ f) hx hz
  calc
    Module.finrank K (A ⧸ Ideal.span {f, g}) =
        Module.finrank K (Bivariate K ⧸ (Ideal.span {f, g}).map τ.toRingHom) :=
      (finiteQuotientEquiv τ hs hk (Ideal.span {f, g})).toLinearEquiv.finrank_eq
    _ = Module.finrank K (Bivariate K ⧸ intersectionIdeal K (τ f)) := by rw [heq]
    _ = _ := nodal_intersection_colength K (τ f) hx hz

theorem actual_nodal_intersection_finite (τ : A →ₐ[K] Bivariate K)
    (hs : ∀ n : ℕ, Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal (Bivariate K) ^ n)).comp τ.toRingHom))
    (hk : ∀ n : ℕ, RingHom.ker
      ((Ideal.Quotient.mk (maximalIdeal (Bivariate K) ^ n)).comp τ.toRingHom) =
        maximalIdeal A ^ n) (f g : A)
    {u : Bivariate K} (hu : IsUnit u) (hg : τ g = u * nodeEquation K)
    (hx : restrictX K (τ f) ≠ 0) (hz : restrictZ K (τ f) ≠ 0) :
    FiniteDimensional K (A ⧸ Ideal.span {f, g}) := by
  have heq := map_nodal_intersection_ideal τ f g hu hg
  let : FiniteDimensional K (Bivariate K ⧸ (Ideal.span {f, g}).map τ.toRingHom) := by
    rw [heq]
    exact finite_intersection_quotient K (τ f) hx hz
  exact FiniteDimensional.of_injective (finiteQuotientEquiv τ hs hk
    (Ideal.span {f, g})).toLinearMap (finiteQuotientEquiv τ hs hk (Ideal.span {f, g})).injective

end
end MaximalSeshadri.LocalComparison
end


end
end

end OAI
