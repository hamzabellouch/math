import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorExact

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]
variable {F G H M : Type*}
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [IsScalarTower k Rᵐᵒᵖ F]
variable [AddCommGroup G] [Module k G] [Module Rᵐᵒᵖ G] [IsScalarTower k Rᵐᵒᵖ G]
variable [AddCommGroup H] [Module k H] [Module Rᵐᵒᵖ H] [IsScalarTower k Rᵐᵒᵖ H]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]

def mapLeft (a : F →ₗ[Rᵐᵒᵖ] G) : BalancedTensor k R F M →ₗ[k] BalancedTensor k R G M :=
  map (a.restrictScalars k) LinearMap.id (fun r f => a.map_smul r f) (fun _ _ => rfl)

omit [IsScalarTower k R M] in
@[simp] theorem mapLeft_tmul (a : F →ₗ[Rᵐᵒᵖ] G) (f : F) (m : M) :
    mapLeft (k := k) a (tmul f m) = tmul (a f) m := rfl

omit [IsScalarTower k R M] in
@[simp] theorem mapLeft_comp (a : F →ₗ[Rᵐᵒᵖ] G) (b : G →ₗ[Rᵐᵒᵖ] H) :
    mapLeft (k := k) (M := M) (b.comp a) = (mapLeft b).comp (mapLeft a) := by
  apply hom_ext
  intro f m
  rfl

omit [IsScalarTower k R M] in
@[simp] theorem mapLeft_zero : mapLeft (k := k) (M := M) (0 : F →ₗ[Rᵐᵒᵖ] G) = 0 := by
  apply hom_ext
  intro f m
  exact zero_tmul m

variable {n : ℕ}

def leftCoefficients (s : M →ₗ[R] (Fin n → R)) :
    BalancedTensor k R F M →ₗ[k] (Fin n → F) :=
  lift
    { toFun f :=
        { toFun m i := MulOpposite.op (s m i) • f
          map_add' m m' := by
            ext i
            simp only [map_add, Pi.add_apply, MulOpposite.op_add, add_smul]
          map_smul' c m := by
            ext i
            simp only [LinearMap.map_smul_of_tower, Pi.smul_apply, MulOpposite.op_smul,
              smul_assoc, RingHom.id_apply] }
      map_add' f f' := by ext m i; exact smul_add _ _ _
      map_smul' c f := by
        ext m i
        exact (smul_comm c (MulOpposite.op (s m i)) f).symm }
    (by
      intro f r m
      ext i
      change MulOpposite.op (s m i) • (MulOpposite.op r • f) = MulOpposite.op (s (r • m) i) • f
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, MulOpposite.op_mul, mul_smul])

@[simp] theorem leftCoefficients_tmul (s : M →ₗ[R] (Fin n → R)) (f : F) (m : M) (i : Fin n) :
    leftCoefficients (k := k) s (tmul f m) i = MulOpposite.op (s m i) • f := rfl

def leftRecombine (p : (Fin n → R) →ₗ[R] M) :
    (Fin n → F) →ₗ[k] BalancedTensor k R F M :=
  ∑ i, (((mk (k := k) (R := R)).flip (p (Pi.single i 1))).comp (LinearMap.proj i))

omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ F] [IsScalarTower k R M] in
@[simp] theorem leftRecombine_apply (p : (Fin n → R) →ₗ[R] M) (f : Fin n → F) :
    leftRecombine (k := k) p f = ∑ i, tmul (f i) (p (Pi.single i 1)) := by
  simp [leftRecombine, mk]

theorem leftRecombine_leftCoefficients (s : M →ₗ[R] (Fin n → R))
    (p : (Fin n → R) →ₗ[R] M) (h : p.comp s = LinearMap.id) (z : BalancedTensor k R F M) :
    leftRecombine p (leftCoefficients s z) = z := by
  induction z using induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul f m =>
    rw [leftRecombine_apply]
    calc
      (∑ i, tmul (leftCoefficients s (tmul f m) i) (p (Pi.single i 1))) =
          ∑ i, tmul f (p (Pi.single i (s m i))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [leftCoefficients_tmul, balance, ← p.map_smul]
        congr 2
        ext j
        by_cases hij : j = i
        · subst j; simp
        · simp [hij]
      _ = tmul f (p (∑ i, Pi.single i (s m i))) := by
        simp only [map_sum]
        exact (map_sum (mk (k := k) (R := R) f) _ _).symm
      _ = tmul f m := by
        rw [Finset.univ_sum_single]
        exact congrArg (fun m => tmul (k := k) (R := R) f m) (DFunLike.congr_fun h m)

theorem leftCoefficients_natural (s : M →ₗ[R] (Fin n → R)) (a : F →ₗ[Rᵐᵒᵖ] G)
    (z : BalancedTensor k R F M) :
    leftCoefficients s (mapLeft a z) = fun i => a (leftCoefficients s z i) := by
  induction z using induction_on with
  | zero => ext i; simp
  | tmul f m => ext i; simp
  | add x y hx hy => ext i; simp only [map_add, Pi.add_apply, hx, hy]

omit [IsScalarTower k R M] in
theorem leftRecombine_natural (p : (Fin n → R) →ₗ[R] M) (a : F →ₗ[Rᵐᵒᵖ] G) (z : Fin n → F) :
    mapLeft a (leftRecombine p z) = leftRecombine (k := k) p (fun i => a (z i)) := by
  simp only [leftRecombine_apply, map_sum, mapLeft_tmul]

theorem mapLeft_exact [Module.Finite R M] [Module.Projective R M]
    (a : F →ₗ[Rᵐᵒᵖ] G) (b : G →ₗ[Rᵐᵒᵖ] H) (hex : Function.Exact a b) :
    Function.Exact (mapLeft (k := k) (M := M) a) (mapLeft b) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
  intro z
  constructor
  · intro hz
    have hcoords : ∀ i, b (leftCoefficients s z i) = 0 := by
      have hnat := leftCoefficients_natural s b z
      rw [hz, map_zero] at hnat
      intro i
      exact (congrFun hnat i).symm
    choose w hw using fun i => (hex (leftCoefficients s z i)).mp (hcoords i)
    refine ⟨leftRecombine p w, ?_⟩
    rw [leftRecombine_natural]
    convert leftRecombine_leftCoefficients s p hs z using 1
    exact congrArg (leftRecombine (k := k) p) (funext hw)
  · rintro ⟨w, rfl⟩
    have hba : b.comp a = 0 := by ext f; exact (hex (a f)).mpr ⟨f, rfl⟩
    change ((mapLeft b).comp (mapLeft a)) w = 0
    rw [← mapLeft_comp, hba, mapLeft_zero, LinearMap.zero_apply]

omit [IsScalarTower k R M] in
theorem mapLeft_surjective (a : F →ₗ[Rᵐᵒᵖ] G) (ha : Function.Surjective a) :
    Function.Surjective (mapLeft (k := k) (M := M) a) :=
  map_surjective (a.restrictScalars k) LinearMap.id
    (fun r f => a.map_smul r f) (fun _ _ => rfl) ha Function.surjective_id

theorem mapLeft_injective [Module.Finite R M] [Module.Projective R M]
    (a : F →ₗ[Rᵐᵒᵖ] G) (ha : Function.Injective a) :
    Function.Injective (mapLeft (k := k) (M := M) a) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
  intro x y hxy
  have hc : leftCoefficients s x = leftCoefficients s y := by
    ext i
    apply ha
    have hh := congrArg (fun z => leftCoefficients s z i) hxy
    simpa only [leftCoefficients_natural] using hh
  rw [← leftRecombine_leftCoefficients s p hs x, ← leftRecombine_leftCoefficients s p hs y, hc]

end ArExplicit.BalancedTensor

end

end OAI
