import Mathlib
import OAI.NumberTheory.CubicGauss.Eisenstein

namespace OAI

/-! Primitive multiplicative characters of finite rings and Gauss-sum norms. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment.HeckeTheta

lemma finite_exists_idempotent_pow {M : Type*} [Monoid M] [Finite M] (a : M) :
    ∃ n : ℕ, 0 < n ∧ a ^ (2*n) = a ^ n := by
  have hh : ∃ i j : ℕ, i < j ∧ a^i = a^j := by
    obtain ⟨i,j,hij,he⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => a^n)
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i,j,h,he⟩
    · exact ⟨j,i,h,he.symm⟩
  obtain ⟨i,j,hij,he⟩ := hh
  let k := j-i
  have hk : 0 < k := Nat.sub_pos_of_lt hij
  have hik : i+k = j := Nat.add_sub_of_le hij.le
  have hper (m : ℕ) : a^(i+k*m) = a^i := by
    induction m with
    | zero => simp
    | succ m ih =>
      calc
        _ = a^(i+k*m) * a^k := by rw [← pow_add]; congr 1; ring
        _ = a^i * a^k := by rw [ih]
        _ = a^i := by rw [← pow_add, hik]; exact he.symm
  let n := k*(i+1)
  have hn : 0 < n := Nat.mul_pos hk (Nat.succ_pos _)
  have hni : i ≤ n := by dsimp [n]; nlinarith
  have hl := congrArg (fun x : M => x * a^(n-i)) (hper (i+1))
  simp only [← pow_add] at hl
  refine ⟨n, hn, ?_⟩
  convert hl using 1 <;> congr 1 <;> dsimp [n, k] at * <;> omega

 

lemma finite_units_map_surjective {R S : Type*} [CommRing R] [CommRing S]
    [Finite R] (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (Units.map f.toMonoidHom) := by
  intro u
  obtain ⟨a,ha⟩ := hf (u : S)
  obtain ⟨n,hn,he⟩ := finite_exists_idempotent_pow a
  have hp : a^n * a^n = a^n := by rwa [← pow_add, ← two_mul]
  have hx : a * a^(n-1) = a^n := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  have hp3 : a^n * a^n * a^n = a^n := by rw [hp,hp]
  have hi : (a * a^n + (1-a^n)) * (a^(n-1)*a^n+(1-a^n)) = 1 := by
    calc
      _ = (a*a^(n-1))*(a^n*a^n) +
          a*(a^n-a^n*a^n) + a^(n-1)*(a^n-a^n*a^n) +
          (1-2*a^n+a^n*a^n) := by ring
      _ = 1 := by rw [hx,hp,hp]; ring
  let v : Rˣ := ⟨a*a^n+(1-a^n),a^(n-1)*a^n+(1-a^n),hi,by rw [mul_comm]; exact hi⟩
  refine ⟨v, Units.ext ?_⟩
  have heu : (u : S)^n = 1 := by
    have hem := congrArg f hp
    simp only [map_mul,map_pow,ha] at hem
    exact (u.isUnit.pow n).mul_right_inj.mp (by simpa using hem)
  change f (a*a^n+(1-a^n)) = u
  simp [ha,heu]

variable {R : Type*} [CommRing R] [Finite R]

 
def FiniteFactorsThrough (χ : MulChar R ℂ) (J : Ideal R) : Prop :=
  ∃ ψ : MulChar (R ⧸ J) ℂ, ∀ u : Rˣ, ψ (Ideal.Quotient.mk J u) = χ u

 

def FinitePrimitive (χ : MulChar R ℂ) : Prop :=
  ∀ J : Ideal R, FiniteFactorsThrough χ J → J = ⊥

lemma finite_factorsThrough_of_kernel (χ : MulChar R ℂ) (J : Ideal R)
    (hk : ∀ u : Rˣ, Ideal.Quotient.mk J (u : R) = 1 → χ u = 1) :
    FiniteFactorsThrough χ J := by
  let f := Units.map (Ideal.Quotient.mk J).toMonoidHom
  have hf : Function.Surjective f := finite_units_map_surjective _ Ideal.Quotient.mk_surjective
  have hker : f.ker ≤ χ.toUnitHom.ker := by
    intro u hu
    apply Units.ext
    apply hk
    exact congrArg (fun x : (R ⧸ J)ˣ => (x : R ⧸ J)) hu
  let ψ := MonoidHom.liftOfSurjective f hf ⟨χ.toUnitHom, hker⟩
  refine ⟨MulChar.ofUnitHom ψ, ?_⟩
  intro u
  have hψ : ψ (f u) = χ.toUnitHom u := by
    exact MonoidHom.liftOfRightInverse_comp_apply ..
  change (MulChar.ofUnitHom ψ) ((f u : (R ⧸ J)ˣ) : R ⧸ J) = χ u
  rw [MulChar.ofUnitHom_coe]
  exact congrArg (fun x : ℂˣ => (x : ℂ)) hψ

 
def frequencyAnnihilator (a : R) : Ideal R where
  carrier := {x | a*x=0}
  add_mem' := by intro x y hx hy; simp only [Set.mem_ofPred_eq] at *; rw [mul_add,hx,hy,add_zero]
  zero_mem' := mul_zero _
  smul_mem' := by
    intro c x hx
    change a * (c*x) = 0
    change a*x=0 at hx
    rw [mul_left_comm,hx,mul_zero]

lemma frequencyAnnihilator_ne_bot {a : R} (ha : ¬IsUnit a) :
    frequencyAnnihilator a ≠ ⊥ := by
  intro he
  have hinj : Function.Injective (fun x : R => a*x) := by
    intro x y hxy
    change a*x=a*y at hxy
    apply sub_eq_zero.mp
    have hm : x-y ∈ frequencyAnnihilator a := by
      change a*(x-y)=0
      rw [mul_sub,hxy,sub_self]
    rw [he] at hm
    exact hm
  obtain ⟨b,hb⟩ := Finite.injective_iff_surjective.mp hinj 1
  exact ha (isUnit_iff_exists_inv.mpr ⟨b,hb⟩)

lemma primitive_gaussSum_nonunit (χ : MulChar R ℂ) (hχ : FinitePrimitive χ)
    (ψ : AddChar R ℂ) [Fintype R] {a : R} (ha : ¬IsUnit a) :
    gaussSum χ (ψ.mulShift a) = 0 := by
  by_contra hg
  apply frequencyAnnihilator_ne_bot ha
  apply hχ
  apply finite_factorsThrough_of_kernel
  intro u hu
  have hau : a * (u : R) = a := by
    have hh : (u : R)-1 ∈ frequencyAnnihilator a := by
      apply Ideal.Quotient.eq.mp
      simpa using hu
    change a*((u : R)-1)=0 at hh
    simpa only [mul_sub,mul_one,sub_eq_zero] using hh
  have hs : (ψ.mulShift a).mulShift u = ψ.mulShift a := by
    rw [AddChar.mulShift_mulShift,hau]
  have hh := gaussSum_mulShift χ (ψ.mulShift a) u
  rw [hs] at hh
  exact mul_right_cancel₀ hg (by simpa using hh)

 

theorem primitive_gaussSum_mulShift (χ : MulChar R ℂ) (hχ : FinitePrimitive χ)
    (ψ : AddChar R ℂ) [Fintype R] (a : R) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : IsUnit a
  · simpa [ha.unit_spec] using gaussSum_mulShift_eq χ ψ ha.unit
  · rw [MulChar.map_nonunit _ ha,zero_mul]
    exact primitive_gaussSum_nonunit χ hχ ψ ha

 

theorem primitive_gaussSum_mul_star (χ : MulChar R ℂ) (hχ : FinitePrimitive χ)
    (ψ : AddChar R ℂ) [Fintype R] (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * star (gaussSum χ ψ) = (Fintype.card R : ℂ) := by
  classical
  rw [star_gaussSum_eq]
  change gaussSum χ ψ * (∑ a : R, χ⁻¹ a * ψ⁻¹ a) = _
  rw [Finset.mul_sum]
  simp_rw [← mul_assoc, mul_comm (gaussSum χ ψ),
    ← primitive_gaussSum_mulShift χ hχ ψ, gaussSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner (x : R) :
      (∑ a : R, χ x * ψ (a*x) * ψ⁻¹ a) =
        χ x * (if x=1 then (Fintype.card R : ℂ) else 0) := by
    have hh (a : R) : χ x * ψ (a*x) * ψ⁻¹ a = χ x * ψ (a*(x-1)) := by
      rw [AddChar.inv_apply, mul_assoc, ← ψ.map_add_eq_mul]
      congr 2
      ring
    simp_rw [hh]
    rw [← Finset.mul_sum, AddChar.sum_mulShift (x-1) hψ]
    simp only [sub_eq_zero, Nat.cast_ite, Nat.cast_zero]
  simp_rw [AddChar.mulShift_apply, hinner]
  simp

theorem primitive_gaussSum_norm (χ : MulChar R ℂ) (hχ : FinitePrimitive χ)
    (ψ : AddChar R ℂ) [Fintype R] (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card R) := by
  have hh := primitive_gaussSum_mul_star χ hχ ψ hψ
  rw [Complex.star_def, Complex.mul_conj] at hh
  have hn : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card R : ℝ) := by
    have hre := congrArg Complex.re hh
    simpa only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.natCast_re,
      Complex.normSq_eq_norm_sq] using hre
  rw [← hn, Real.sqrt_sq (_root_.norm_nonneg _)]

end CubicFirstMoment.HeckeTheta
end

end OAI
