import Mathlib

namespace OAI

/-! Free intersections, power localizations and finite glued lattices. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators TensorProduct

namespace FiberFunctorProof
section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma tensor_span_pair (x y : R) (I : Ideal R) (hI : I = Ideal.span {x,y})
    (z : I ⊗[R] M) :
    ∃ u v : M, z = (⟨x, by rw [hI]; exact Ideal.subset_span (by simp)⟩ : I) ⊗ₜ[R] u +
      (⟨y, by rw [hI]; exact Ideal.subset_span (by simp)⟩ : I) ⊗ₜ[R] v := by
  let ix : I := ⟨x, by rw [hI]; exact Ideal.subset_span (by simp)⟩
  let iy : I := ⟨y, by rw [hI]; exact Ideal.subset_span (by simp)⟩
  change ∃ u v, z = ix ⊗ₜ[R] u + iy ⊗ₜ[R] v
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
    have ha : a.val ∈ Ideal.span {x,y} := hI ▸ a.property
    obtain ⟨b,c,hbc⟩ := Ideal.mem_span_pair.mp ha
    have heq : a = b • ix + c • iy := by
      apply Subtype.ext
      exact hbc.symm
    refine ⟨b • m, c • m, ?_⟩
    rw [heq, TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
  | add a b ha hb =>
    obtain ⟨u,v,rfl⟩ := ha
    obtain ⟨u',v',rfl⟩ := hb
    exact ⟨u+u', v+v', by simp only [TensorProduct.tmul_add]; abel⟩

 

theorem free_of_two_generators [IsLocalRing R] [Module.FinitePresentation R M]
    (x y : R) (hm : IsLocalRing.maximalIdeal R = Ideal.span {x,y})
    (hx : Function.Injective (fun m : M => x • m))
    (hy : ∀ v n : M, y • v = x • n → ∃ w : M, v = x • w) :
    Module.Free R M := by
  apply Module.free_of_maximalIdeal_rTensor_injective
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  let I := IsLocalRing.maximalIdeal R
  let ix : I := ⟨x, by dsimp [I]; rw [hm]; exact Ideal.subset_span (by simp)⟩
  let iy : I := ⟨y, by dsimp [I]; rw [hm]; exact Ideal.subset_span (by simp)⟩
  obtain ⟨u,v,hz'⟩ := tensor_span_pair x y I hm z
  change z = ix ⊗ₜ[R] u + iy ⊗ₜ[R] v at hz'
  have huv : x • u + y • v = 0 := by
    have h := congrArg (TensorProduct.lid R M) hz
    rw [hz'] at h
    simpa [LinearMap.rTensor_tmul, ix, iy] using h
  have hv : y • v = x • (-u) := by
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_right huv
  obtain ⟨w,hw⟩ := hy v (-u) hv
  have hu : u = -(y • w) := by
    apply hx
    change x • u = x • (-(y • w))
    rw [smul_neg]
    have := huv
    rw [hw, smul_comm y x] at this
    exact eq_neg_of_add_eq_zero_left this
  rw [hz', hu, hw]
  simp only [TensorProduct.tmul_neg, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  have heq : y • ix = x • iy := by
    apply Subtype.ext
    exact mul_comm y x
  rw [heq]
  exact neg_add_cancel _

end

section

variable {R K W : Type*} [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]

 

theorem intersection_regular (A B : Submodule R W) (x y : R)
    (hx : algebraMap R K x ≠ 0) (hy : algebraMap R K y ≠ 0)
    (hA : ∀ v ∈ A, (algebraMap R K x)⁻¹ • v ∈ A)
    (hB : ∀ v ∈ B, (algebraMap R K y)⁻¹ • v ∈ B) :
    Function.Injective (fun m : ↥(A ⊓ B) => x • m) ∧
      ∀ v n : ↥(A ⊓ B), y • v = x • n → ∃ w : ↥(A ⊓ B), v = x • w := by
  constructor
  · intro a b hab
    apply Subtype.ext
    have h : (algebraMap R K x) • (a : W) = (algebraMap R K x) • (b : W) := by
      simpa only [algebraMap_smul, Submodule.coe_smul] using congrArg Subtype.val hab
    exact (smul_right_injective W hx) h
  · intro v n hvn
    have h : (algebraMap R K y) • (v : W) = (algebraMap R K x) • (n : W) := by
      simpa only [algebraMap_smul, Submodule.coe_smul] using congrArg Subtype.val hvn
    have hw : (algebraMap R K x)⁻¹ • (v : W) =
        (algebraMap R K y)⁻¹ • (n : W) := by
      apply (smul_right_injective W hx)
      simp only [smul_inv_smul₀ hx]
      rw [smul_comm, ← h, inv_smul_smul₀ hy]
    refine ⟨⟨(algebraMap R K x)⁻¹ • (v : W),
      hA v v.property.1, hw ▸ hB n n.property.2⟩, ?_⟩
    apply Subtype.ext
    change (v : W) = x • ((algebraMap R K x)⁻¹ • (v : W))
    rw [← algebraMap_smul K x, smul_inv_smul₀ hx]

 

theorem intersection_free [IsLocalRing R]
    (A B : Submodule R W) [Module.FinitePresentation R ↥(A ⊓ B)] (x y : R)
    (hm : IsLocalRing.maximalIdeal R = Ideal.span {x,y})
    (hx : algebraMap R K x ≠ 0) (hy : algebraMap R K y ≠ 0)
    (hA : ∀ v ∈ A, (algebraMap R K x)⁻¹ • v ∈ A)
    (hB : ∀ v ∈ B, (algebraMap R K y)⁻¹ • v ∈ B) :
    Module.Free R ↥(A ⊓ B) := by
  obtain ⟨h1,h2⟩ := intersection_regular A B x y hx hy hA hB
  exact free_of_two_generators x y hm h1 h2

end

 

section PowerLocalization
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

 
def powerLocalization (x : R) (L : Submodule R W) : Submodule R W where
  carrier := {v | ∃ n : ℕ, x ^ n • v ∈ L}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨n,hn⟩ ⟨m,hm⟩
    refine ⟨n+m, ?_⟩
    rw [smul_add, pow_add]
    exact L.add_mem
      (by rw [mul_comm, mul_smul]; exact L.smul_mem _ hn)
      (by rw [mul_smul]; exact L.smul_mem _ hm)
  smul_mem' := by
    rintro c a ⟨n,hn⟩
    exact ⟨n, by rw [smul_comm]; exact L.smul_mem c hn⟩

lemma le_powerLocalization (x : R) (L : Submodule R W) : L ≤ powerLocalization x L := by
  intro v hv
  exact ⟨0, by simpa using hv⟩

lemma powerLocalization_mono (x : R) {L L' : Submodule R W} (h : L ≤ L') :
    powerLocalization x L ≤ powerLocalization x L' := by
  rintro v ⟨n,hn⟩
  exact ⟨n,h hn⟩

end PowerLocalization

section Field
variable {R K W : Type*} [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]

lemma powerLocalization_div (x : R) (L : Submodule R W)
    (hx : algebraMap R K x ≠ 0) {v : W} (hv : v ∈ powerLocalization x L) :
    (algebraMap R K x)⁻¹ • v ∈ powerLocalization x L := by
  obtain ⟨n,hn⟩ := hv
  refine ⟨n+1, ?_⟩
  rw [pow_succ, mul_smul, ← algebraMap_smul K x, smul_inv_smul₀ hx]
  exact hn

end Field

section
variable {R K ι : Type*} [CommRing R] [Field K] [Algebra R K]

 
def coordinateMap : (ι → R) →ₗ[R] (ι → K) where
  toFun v i := algebraMap R K (v i)
  map_add' v w := by ext i; exact map_add _ _ _
  map_smul' c v := by ext i; simp [Algebra.smul_def]

def coordinateLattice : Submodule R (ι → K) :=
  LinearMap.range (coordinateMap (R := R) (K := K) (ι := ι))

lemma mem_coordinateLattice (v : ι → K) : v ∈ coordinateLattice (R := R) ↔
    ∀ i, ∃ r : R, algebraMap R K r = v i := by
  constructor
  · rintro ⟨w,rfl⟩ i
    exact ⟨w i,rfl⟩
  · intro hv
    choose w hw using hv
    exact ⟨w,funext hw⟩

instance coordinateLattice_finite [Finite ι] :
    Module.Finite R (coordinateLattice (R := R) (K := K) (ι := ι)) := by
  exact Module.Finite.range _

 

theorem coordinateLattice_intersection [IsDomain R] [GCDMonoid R] [IsFractionRing R K]
    (x y : R) (hx : x ≠ 0) (hxy : IsRelPrime x y) :
    powerLocalization x (coordinateLattice (R := R) (K := K) (ι := ι)) ⊓
      powerLocalization y (coordinateLattice (R := R) (K := K) (ι := ι)) =
      coordinateLattice (R := R) (K := K) (ι := ι) := by
  apply le_antisymm
  · rintro v ⟨⟨n,hn⟩,⟨m,hm⟩⟩
    apply (mem_coordinateLattice v).mpr
    intro i
    obtain ⟨a,ha⟩ := (mem_coordinateLattice _).mp hn i
    obtain ⟨b,hb⟩ := (mem_coordinateLattice _).mp hm i
    have hinj : Function.Injective (algebraMap R K) := FaithfulSMul.algebraMap_injective R K
    have hab : y ^ m * a = x ^ n * b := by
      apply hinj
      simp only [map_mul, ha, hb]
      change algebraMap R K (y ^ m) * (x^n • v i) =
        algebraMap R K (x ^ n) * (y^m • v i)
      simp only [Algebra.smul_def]
      ring
    have hdiv : x ^ n ∣ a :=
      (hxy.pow (m := n) (n := m)).dvd_of_dvd_mul_left ⟨b, hab⟩
    obtain ⟨c,hc⟩ := hdiv
    refine ⟨c, ?_⟩
    have hxn : algebraMap R K (x^n) ≠ 0 := by
      exact fun h => pow_ne_zero n hx (hinj (h.trans (map_zero _).symm))
    apply mul_left_cancel₀ hxn
    rw [← map_mul, ← hc, ha]
    exact Algebra.smul_def _ _
  · exact le_inf (le_powerLocalization ..) (le_powerLocalization ..)

end

section
variable {R K ι : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
    [Field K] [Algebra R K] [IsFractionRing R K]

 
def gluedLattice (x y : R) (P : (ι → K) ≃ₗ[K] (ι → K)) : Submodule R (ι → K) :=
  powerLocalization x coordinateLattice ⊓
    (powerLocalization y coordinateLattice).map (P.toLinearMap.restrictScalars R)

 

lemma gluedLattice_bound (x y : R) (hx : x ≠ 0) (hxy : IsRelPrime x y)
    (P : (ι → K) ≃ₗ[K] (ι → K)) (d : ℕ)
    (hP : ∀ v ∈ coordinateLattice (R := R), (x*y)^d • P v ∈ coordinateLattice (R := R))
    {z : ι → K} (hz : z ∈ gluedLattice x y P) :
    x^d • z ∈ coordinateLattice (R := R) := by
  change z ∈ powerLocalization x coordinateLattice ∧
    z ∈ (powerLocalization y coordinateLattice).map (P.toLinearMap.restrictScalars R) at hz
  rw [← coordinateLattice_intersection x y hx hxy]
  constructor
  · exact (powerLocalization x (coordinateLattice (R := R) (K := K) (ι := ι))).smul_mem (x^d) hz.1
  change ∃ m : ℕ, y^m • (x^d • z) ∈ coordinateLattice (R := R)
  obtain ⟨v,hv,hvP⟩ := hz.2
  obtain ⟨m,hm⟩ := hv
  refine ⟨d+m, ?_⟩
  have h := hP (y^m • v) hm
  have hlin : P (y^m • v) = y^m • P v := (P.restrictScalars R).map_smul _ _
  rw [hlin, mul_pow, mul_smul] at h
  change P v = z at hvP
  rw [hvP, ← mul_smul (y^d) (y^m), ← pow_add, smul_comm (x^d)] at h
  exact h

theorem gluedLattice_finite [Finite ι] [IsNoetherianRing R]
    (x y : R) (hx : x ≠ 0) (hxy : IsRelPrime x y)
    (P : (ι → K) ≃ₗ[K] (ι → K)) (d : ℕ)
    (hP : ∀ v ∈ coordinateLattice (R := R), (x*y)^d • P v ∈ coordinateLattice (R := R)) :
    Module.Finite R (gluedLattice x y P) := by
  let f : (ι → K) →ₗ[R] (ι → K) :=
    (algebraMap R K (x ^ d))⁻¹ • LinearMap.id
  let L := (coordinateLattice (R := R) (K := K) (ι := ι)).map f
  have hle : gluedLattice x y P ≤ L := by
    intro z hz
    refine ⟨x^d • z, gluedLattice_bound x y hx hxy P d hP hz, ?_⟩
    change (algebraMap R K (x^d))⁻¹ • (x^d • z) = z
    rw [← algebraMap_smul K (x^d), inv_smul_smul₀]
    exact fun h => pow_ne_zero d hx
      ((FaithfulSMul.algebraMap_injective R K) (h.trans (map_zero _).symm))
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

end

variable {R K ι : Type*} [CommRing R] [IsDomain R] [GCDMonoid R]
    [Field K] [Algebra R K] [IsFractionRing R K]

 

theorem gluedLattice_free [Finite ι] [IsNoetherianRing R] [IsLocalRing R]
    (x y : R) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : IsRelPrime x y)
    (hm : IsLocalRing.maximalIdeal R = Ideal.span {x,y})
    (P : (ι → K) ≃ₗ[K] (ι → K)) (d : ℕ)
    (hP : ∀ v ∈ coordinateLattice (R := R), (x*y)^d • P v ∈ coordinateLattice (R := R)) :
    Module.Free R (gluedLattice x y P) := by
  have hinj := FaithfulSMul.algebraMap_injective R K
  have hxK : algebraMap R K x ≠ 0 := fun h => hx (hinj (h.trans (map_zero _).symm))
  have hyK : algebraMap R K y ≠ 0 := fun h => hy (hinj (h.trans (map_zero _).symm))
  have : Module.Finite R (gluedLattice x y P) := gluedLattice_finite x y hx hxy P d hP
  have : Module.FinitePresentation R (gluedLattice x y P) :=
    Module.finitePresentation_of_finite R (gluedLattice x y P)
  have hB : ∀ z ∈ (powerLocalization y coordinateLattice).map (P.toLinearMap.restrictScalars R),
      (algebraMap R K y)⁻¹ • z ∈
        (powerLocalization y coordinateLattice).map (P.toLinearMap.restrictScalars R) := by
    rintro z ⟨v,hv,rfl⟩
    refine ⟨(algebraMap R K y)⁻¹ • v, powerLocalization_div y _ hyK hv, ?_⟩
    exact P.map_smul _ _
  have : Module.FinitePresentation R
      ↥(powerLocalization x (coordinateLattice (R := R) (K := K) (ι := ι)) ⊓
        (powerLocalization y coordinateLattice).map (P.toLinearMap.restrictScalars R)) := by
    change Module.FinitePresentation R (gluedLattice x y P)
    infer_instance
  exact intersection_free _ _ x y hm hxK hyK (fun _ hv => powerLocalization_div x _ hxK hv) hB

end FiberFunctorProof
end

end OAI
